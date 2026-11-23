module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0011
public import Formalism.LocalToGlobal.Columns.Bundle0014
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeMulOnSymmetricLevelAtTypePrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharSymMulInvEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
public import Formalism.LocalToGlobal.Columns.Bundle0013
public import Formalism.LocalToGlobal.Columns.RecLevelCls
public import Formalism.LocalToGlobal.Columns.MtAdWtIrr
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefDualPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0356
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Formalism.LocalToGlobal.Columns.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
public import Formalism.SatakeDualWeyl.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseWeightEqForcedLiftWeight
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open Formalism.L2.Col

namespace GlobalTheory.Mem.LiftWt

theorem lamLdef_eq_lamV (X : Stages) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ X.B.R.m) (τ) (i : Fin (X.toD7.sp.V j).rank)
    (i' : Fin X.B.R.nV) (e : (i : ℕ) = i') :
    (Bridge.lamLdef (D := X.toD7) (X.toD7.sp.V j).rank j τ).w i = (X.B.wts.lamV j τ).w i' := by
  obtain ⟨hj, W, hk, hm, ht, hjj, he, hv, hb, hw⟩ := GlobalTheory.ForcedWeights.lamLForced X.toD7 j h1 h2 τ
  have hk : W.k = X.B.R.k := hk
  have hm : W.m = X.B.R.m := hm
  have ht : W.t = X.B.R.t := ht
  have he : (W.e : ℚ) = (X.B.hc τ).e ⟨j - 1, hj.2⟩ := he
  have hv : ∀ a : Fin (X.B.R.k - 1), (W.v (a + 2) : ℚ) = (X.B.hc τ).v a := hv
  have hb : ∀ a : Fin X.B.R.m, (W.b (a + 1) : ℚ) = (X.B.hc τ).b a := hb
  have hkm := X.B.R.m_add_three_le_k
  have q := RowPar.lamV_eq (X.B.hc τ) h1 h2 i'
  have hi := i'.2
  have hE : (RowPar.of (X.B.hc τ)).eAt (j - 1) = W.e := by
    rw [he]; exact dif_pos hj.2
  have hB : ∀ n, n < X.B.R.m → (RowPar.of (X.B.hc τ)).bAt n = W.b (n + 1) := fun n hn => by
    rw [hb ⟨n, hn⟩]; exact dif_pos hn
  have key : W.lamPrime (i'.1 + 1) = (RowPar.of (X.B.hc τ)).lamVQ j i' := by
    unfold Ranks.nV Ranks.r at hi
    unfold IndefiniteWeightData.WeightData.lamPrime IndefiniteWeightData.WeightData.thetaWt IndefiniteWeightData.WeightData.dTau IndefiniteWeightData.WeightData.aPlus IndefiniteWeightData.WeightData.aMinus
      IndefiniteWeightData.WeightData.lam IndefiniteWeightData.WeightData.nV IndefiniteWeightData.WeightData.r IndefiniteWeightData.WeightData.p IndefiniteWeightData.WeightData.q
      RowPar.lamVQ RowPar.aPlus RowPar.aMinusRev RowPar.dV RowPar.vb RowPar.pOf RowPar.qOf
    rw [hk, hm, ht, hjj, hE]
    congr 1
    by_cases a : i'.1 < X.B.R.k + j - 1
    · rw [if_pos a, if_pos (show i'.1 + 1 ≤ _ from a), Nat.add_sub_cancel]
      by_cases b : i'.1 < X.B.R.k - 1
      · rw [dif_pos b, if_pos (show i'.1 + 1 ≤ _ from b), hv ⟨_, b⟩]
        rfl
      · rw [dite_eq_right b, if_neg (show ¬ i'.1 + 1 ≤ _ from b), hB _ (by omega), Int.cast_neg,
          show i'.1 + 1 - (X.B.R.k - 1) = i'.1 - (X.B.R.k - 1) + 1 by omega]
        rfl
    · rw [if_neg a, if_neg (show ¬ i'.1 + 1 ≤ _ from a)]
      by_cases b : i'.1 < X.B.R.k + j - 1 + X.B.R.t
      · rw [if_pos b, if_pos (show i'.1 + 1 ≤ _ from b)]
      · rw [if_neg b, if_neg (show ¬ i'.1 + 1 ≤ _ from b), hB _ (by omega),
          show X.B.R.m - j + 1 - (X.B.R.m - j + 1 - (i'.1 + 1 - (X.B.R.k + j - 1) - X.B.R.t)) =
            i'.1 - (X.B.R.k + j - 1 + X.B.R.t) + 1 by omega,
          show j + (i'.1 - (X.B.R.k + j - 1 + X.B.R.t) + 1) - 1 + 1 = j + (i'.1 - (X.B.R.k + j - 1 + X.B.R.t) + 1) by omega]
  have := (hw i).trans ((e ▸ key).trans q.symm)
  exact_mod_cast this

theorem lamV_eq_lamLdef : ∀ (X : Stages) (i : Fin X.toD7.R.m) (τ : X.B.fields.Tau) (a : Fin X.B.R.nV),
    (X.B.wts.lamV ((i : ℕ) + 1) τ).w a =
      (Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ).w (Fin.cast (LiftBrg.rkEq X i) a) := by
  intro X i τ a
  exact (lamLdef_eq_lamV X ((i : ℕ) + 1) (by omega) i.2 τ _ a rfl).symm

end GlobalTheory.Mem.LiftWt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainLevelFamilyExtension
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3 GlobalTheory.Mem.ColTie

noncomputable section

namespace GlobalTheory.Mem.ColTie

theorem map_pairV_one {E K ι : Type} [Field E] [Field K] [StarRing K] [Fintype ι] {n : ℕ} (emb : ι → E →+* K)
    (lam : ι → DomWeight n) (σ : K →+* ℂ) (hσ : ∀ x, σ (star x) = starRingEnd ℂ (σ x)) (x y : VV K lam) :
    σ (pairV emb lam 1 x y) =
      pairB lam (MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map σ x.1)) (MvPolynomial.map σ y.1) := by
  have e : gramK emb (1 : Matrix (Fin n) (Fin n) E) = fun τ => (((1 : ι → GL (Fin n) K) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    funext τ
    rw [gramK, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  show σ (pairK lam (gramK emb 1) x y) = _
  rw [pairK_apply, e, pairP_eq_pairB, polyAction_one₂, GlobalTheory.PeriodOnStep.map_pairB, MvPolynomial.map_map,
    MvPolynomial.map_map]
  congr 2
  exact congrArg (fun f => MvPolynomial.map f (x : Pol K ι n)) (RingHom.ext fun a => hσ a)

end GlobalTheory.Mem.ColTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChrLast
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Proof.LastStepChar

open Loc LocE GlobalTheory.SymLevelInv

theorem sum_sd {κ : Type} [AddCommMonoid κ] {n a k : ℕ} (hk : 1 ≤ k) (hka : k < a) (ha : a ≤ n)
    (N : Matrix (Fin n) (Fin n) κ) (f : ℕ → ℕ → κ) (hf : ∀ x y (hx : x < n) (hy : y < n), N ⟨x, hx⟩ ⟨y, hy⟩ = f x y) :
    (∑ x : Fin n, ∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < a ∧ (y : ℕ) ≠ k then N x y else 0) =
      ∑ i ∈ Finset.range (k - 1), f i (i + 1) + ∑ i ∈ Finset.range (a - k - 1), f (k + i) (k + i + 1) := by
  have h1 : ∀ x : Fin n, (∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < a ∧ (y : ℕ) ≠ k then N x y else 0) =
      if (x : ℕ) + 1 < a ∧ (x : ℕ) + 1 ≠ k then f x (x + 1) else 0 := by
    intro x
    by_cases hx : (x : ℕ) + 1 < a ∧ (x : ℕ) + 1 ≠ k
    · rw [if_pos hx, Finset.sum_eq_single (⟨x.1 + 1, by omega⟩ : Fin n), if_pos ⟨rfl, hx.1, hx.2⟩, hf]
      · intro y _ hy
        exact if_neg fun h => hy (Fin.ext h.1.symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [if_neg hx]
      refine Finset.sum_eq_zero fun y _ => if_neg fun h => hx ?_
      obtain ⟨h1, h2, h3⟩ := h
      omega
  rw [Finset.sum_congr rfl fun x _ => h1 x,
    Fin.sum_univ_eq_sum_range (fun x => if x + 1 < a ∧ x + 1 ≠ k then f x (x + 1) else 0) n]
  have e : n = (k - 1) + (1 + ((a - k - 1) + (n - (a - 1)))) := by omega
  rw [e, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_one]
  rw [if_neg (by omega), zero_add, Finset.sum_eq_zero (s := Finset.range (n - (a - 1))), add_zero]
  · congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [if_pos (by omega)]
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [if_pos (by omega), show k - 1 + (1 + i) = k + i by omega]
  · intro i hi
    rw [if_neg (by omega)]

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem red_mat {n : ℕ} (g : Sp E n ≃ₗ[E] Sp E n) (r : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0))
    (hrg : ∀ x, r (Loc.inX E n 0 x) = Loc.inX E n 0 (g x)) (M : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal))
    (hred : ∀ x ∈ stdAt E n P, redV P (g x) = M.mulVec (redV P x)) (p p' : ℕ) (hp : p < n) (hp' : p' < n) :
    redP P (mat r p p') = M ⟨p, hp⟩ ⟨p', hp'⟩ := by
  have he : Loc.eN E (n + 0) p' = Loc.inX E n 0 (Loc.eN E n p') := by
    funext l
    rw [GlobalTheory.QNormal.inX_apply, dif_pos (show (l : ℕ) < n from l.2)]
    rfl
  have hv : redV P (Loc.eN E n p') = Pi.single ⟨p', hp'⟩ 1 := by
    funext l
    simp only [redV, Loc.eN, Pi.single_apply, Fin.ext_iff]
    split_ifs
    · exact reduction_one' P
    · exact redP_zero' P
  have h5 := congrFun (hred _ (GlobalTheory.GO.ChRoot.eN_mem (i := p'))) ⟨p, hp⟩
  rw [hv, Matrix.mulVec_single_one] at h5
  unfold mat
  rw [he, hrg, Loc.atN, dif_pos (show p < n + 0 from hp), GlobalTheory.QNormal.inX_apply, dif_pos hp]
  exact h5

theorem lam_loc {K : Type} [Field K] (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ₀ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {κ : Type} [Field κ] (e : (𝓞 E ⧸ P.asIdeal) ≃+* κ) (σ : K →+* ℂ) (ψ : AddChar κ ℂ) (χ : ℕ → MulChar κ ℂ)
    {k rS r t nb n c : ℕ} (hc : c = 0) (hr : r = k + 2 * rS + 1) (hk : 1 ≤ k) (hn : r + nb * t ≤ n)
    (hψ : ∀ a, ψ (e a) = σ (ψ₀ a)) (hχ : ∀ i, i < nb → ∀ a : (𝓞 E ⧸ P.asIdeal)ˣ, χ i (e a) = σ ((χ₀ i a : Kˣ) : K))
    (g : Sp E n ≃ₗ[E] Sp E n) (h : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (hh : h ∈ JGsym P (qOf P) k rS r t n c)
    (hhg : ∀ x, h (Loc.inX E n c x) = Loc.inX E n c (g x)) (M : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal))
    (hred : ∀ x ∈ stdAt E n P, redV P (g x) = M.mulVec (redV P x)) :
    σ (lamGBS (qOf P) ψ₀ χ₀ k r t nb n c h.toLinearMap) = Formalism.L2.Forms.lamSym ψ χ k rS t nb (M.map e) := by
  subst hc hr
  have hM := red_mat g h hhg M hred
  have hrn : k + 2 * rS + 1 ≤ n := le_trans (Nat.le_add_right _ _) hn
  unfold lamGBS lamGvS Formalism.L2.Forms.lamSym Formalism.L2.Forms.lamJ Formalism.L2.Forms.rSym
  rw [map_mul]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [redP_superdiag (by omega) hrn hh, ← hψ, map_add (f := _), map_sum, map_sum]
      congr 1
      refine (sum_sd hk (by omega) hrn _ (fun x y => e (redP P (mat h x y))) fun x y hx hy => ?_).symm
      rw [Matrix.map_apply, hM x y hx hy]
  · rw [map_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hi' : k + 2 * rS + 1 + i * t + t ≤ n := by
      have : (i + 1) * t ≤ nb * t := Nat.mul_le_mul_right t hi
      rw [add_mul, one_mul] at this
      omega
    have hb : Formalism.L2.Forms.blkMat (k + 2 * rS + 1) t i (M.map e) =
        e.toRingHom.mapMatrix (Matrix.of fun s s' : Fin t => redP P (mat h (k + 2 * rS + 1 + i * t + s.1) (k + 2 * rS + 1 + i * t + s'.1))) := by
      ext s s'
      have := s.2
      have := s'.2
      unfold Formalism.L2.Forms.blkMat Formalism.L2.Forms.entN
      rw [dif_pos ⟨by omega, by omega⟩, Matrix.map_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
        hM (k + 2 * rS + 1 + i * t + s.1) (k + 2 * rS + 1 + i * t + s'.1) (by omega) (by omega)]
      rfl
    rw [hb, ← RingHom.map_det]
    unfold unitV
    rw [redP_det_blk hi' hh]
    split_ifs with hu
    · rw [← hχ i hi, IsUnit.unit_spec]
      rfl
    · rw [map_zero, MulChar.map_nonunit]
      exact fun h' => hu ((isUnit_map_iff e _).1 h')

end Loc

end GlobalTheory.Proof.LastStepChar

theorem GlobalTheory.Proof.LastStepChar.chr_last : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → cst.sharp = true → ∀ (j : ℕ), j + 1 = R.m → ∀ (b : L.β j) (w : {w // w ∈ Pr.vGs}) (κ : Type) [Field κ] (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* κ) (σ : X.K →+* ℂ) (ψ : AddChar κ ℂ) (χ : ℕ → MulChar κ ℂ), (∀ c, ψ (e c) = σ (Ch.psi0 w c)) → (∀ (s : Fin R.m) (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ), χ s.1 (e c) = σ ((Ch.chi s w c : X.Kˣ) : X.K)) → ∀ M : (L.levG j b w).H, σ (((L.levG j b w).lam M : X.Kˣ) : X.K) = lamSym ψ χ R.k (rSD R) R.t j (M.1.1.map e) := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hL hsh j hj b w κ _ e σ ψ χ hψ hχ M
  have hm := hL.hm
  obtain rfl : j = m2 + 1 := by omega
  obtain ⟨g, hg, hred⟩ := (hL.grpG (m2 + 1) b w M.1).1 M.2
  obtain ⟨r, hrC, hrg⟩ := hg
  have hlam := hL.chrG (m2 + 1) b w M g r hrC hrg hred
  rw [hlam]
  rw [hL.last_h] at hrC ⊢
  have hc : cOf R (m2 + 1) = 0 := by unfold cOf; omega
  have hJ0 : r ∈ Jat (Pr := Pr) (R := R) cst.sharp (m2 + 1) w.1 := by
    unfold Loc.Cbe at hrC
    rw [Subgroup.mem_inf, Subgroup.mem_comap] at hrC
    simpa using hrC.2
  unfold Jat at hJ0
  rw [if_pos w.2, hsh, if_pos rfl] at hJ0
  have hn1 : Loc.n1Arg r = 0 := by
    unfold Loc.n1Arg
    rw [show cOf R (m2 + 1) - 1 = 0 by omega, Finset.sum_range_zero]
  unfold chiInv
  rw [hn1, hL.cst_ok.psi_int _ _ (GlobalTheory.SymLevelInv.intAt_zero _), inv_one, one_mul]
  unfold lamRow
  simp only [if_pos w.2, hsh, if_true]
  rw [inv_one, one_mul, mul_one]
  have hk := R.m_add_three_le_k
  have hr : R.r = R.k + 2 * R.rS + 1 := by
    obtain ⟨a, ha⟩ := R.m_even
    unfold Ranks.r Ranks.rS
    omega
  have hn : R.r + (m2 + 1) * R.t ≤ R.N (m2 + 1) := by
    unfold Ranks.r Ranks.N
    rw [mul_add, mul_one]
    omega
  refine lam_loc (psi0P Ch w.1) (chiP Ch w.1) e σ ψ χ hc hr (by omega) hn (fun a => ?_) (fun i hi a => ?_) g r hJ0 hrg M.1.1 hred
  · rw [hψ]
    unfold psi0P
    rw [dif_pos w.2]
  · rw [hχ ⟨i, by omega⟩ a]
    unfold chiP chiAt extChi
    rw [dif_pos w.2]
    simp only [dif_pos (show i < R.m by omega)]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientSpaceDefiniteFormIrreducibleAlgebraic
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn

open _root_.Formalism.L2.Col

theorem map_inv_mat {E K : Type} [Field E] [Field K] (f : E →+* K) {n : ℕ} (γE : GL (Fin n) E) :
    ((γE : Matrix (Fin n) (Fin n) E).map f)⁻¹ = ((γE : Matrix (Fin n) (Fin n) E)⁻¹).map f := by
  have h := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) (map_inv (Matrix.GeneralLinearGroup.map f) γE)
  have h1 : ((Matrix.GeneralLinearGroup.map f γE : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (γE : Matrix (Fin n) (Fin n) E).map f := rfl
  have h2 : ((Matrix.GeneralLinearGroup.map f γE⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((γE⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map f := rfl
  simp only [Matrix.coe_units_inv] at h h2
  rw [h1] at h
  rw [h2] at h
  exact h.symm

theorem isAlgWeight_of_equiv {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W W' : Type}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) W) (ρ' : Representation ℂ (ReciprocityTheory.Aut.GQ L n) W')
    (T : W ≃ₗ[ℂ] W') (hT : ∀ γ x, T (ρ γ x) = ρ' γ (T x)) (h : Formalism.AUTREP.IsAlgWeight L n ρ) :
    Formalism.AUTREP.IsAlgWeight L n ρ' := by
  obtain ⟨hf, κ, hfi, hd, bs, P, hP⟩ := h
  refine ⟨LinearEquiv.finiteDimensional T, κ, hfi, hd, bs.map T, P, fun γ γ₀ hm => ?_⟩
  rw [← hP γ γ₀ hm]
  ext i j
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, Module.Basis.map_apply, ← hT, Module.Basis.map_repr,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

theorem exists_weight_of_coefMap {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι]
    {K : Type} [Field K] (φ : K →+* ℂ) (lab : ι → L →+* K) (emb : ι → L →+* ℂ) (hlab : ∀ τ x, φ (lab τ x) = emb τ x)
    (hinj : Function.Injective emb) (hcm : ∀ τ τ', emb τ ≠ ComplexEmbedding.conjugate (emb τ'))
    (lam : ι → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) W)
    (c0 : VV K lam →ₛₗ[φ] W)
    (h0 : ∀ γ v, c0 (rhoVr lab lam (mtwRat (L := L) (n := n) γ) v) = ρ γ (c0 v))
    (h1 : LinearIndependent ℂ fun i => c0 (bVV K lam i))
    (h2 : Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) = ⊤) :
    ∃ (alg : Formalism.AUTREP.IsAlgWeight L n ρ) (irr : ρ.IsIrreducible), ∀ (a : NG.AlgWt L n) (τ : ι) (lam0 : Fin n → ℤ),
      NG.AlgWt.IsDual { W := W, ρ := ρ, alg := alg, irr := irr } a → a.HWAt (emb τ) lam0 → lam0 = (lam τ).w := by
  obtain ⟨T, hT⟩ := GlobalTheory.CoefReal.exists_scalarExt φ lam c0 h1 h2
  have hint : ∀ (γ : ReciprocityTheory.Aut.GQ L n) (x : VV ℂ lam), T (mtRep emb lam γ x) = ρ γ (T x) := by
    intro γ x
    have hfam : (fun τ => Formalism.UG.bc φ (invTrK (embGL lab (mtwRat (L := L) (n := n) γ)) τ)) =
        mtwInvTr (mtwEmb emb (mtwRat (L := L) (n := n) γ)) := by
      funext τ
      apply Units.ext
      ext a b
      simp [mtwInvTr, mtwEmb, inside₂, invTrK_coe, bc_coe, embGL_coe, hlab, map_inv_mat]
    have hL : T.toLinearMap ∘ₗ mtRep emb lam γ = ρ γ ∘ₗ T.toLinearMap := by
      refine LinearMap.ext_on_range (GlobalTheory.CoefModel.span_mapVV φ lam) fun i => ?_
      show T (rhoK lam (mtwInvTr (mtwEmb emb (mtwRat (L := L) (n := n) γ)))
        (GlobalTheory.CoefModel.mapVV φ lam _)) = ρ γ (T _)
      rw [← hfam, ← GlobalTheory.CoefModel.mapVV_rhoK, hT, hT]
      exact h0 γ _
    exact LinearMap.congr_fun hL x
  have hi : TenIrr emb lam := tenIrr_of' highest_weight_fixed_exists highest_weight_fixed_line emb hinj hcm lam
  have alg : Formalism.AUTREP.IsAlgWeight L n ρ := isAlgWeight_of_equiv (mtRep emb lam) ρ T hint (mtRep_alg emb lam)
  have irr : ρ.IsIrreducible :=
    GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv (mtRep emb lam) ρ T (fun g v => (hint g v).symm) hi
  refine ⟨alg, irr, fun a τ lam0 hd hw => ?_⟩
  obtain ⟨B, hB0, hB⟩ : ∃ B : W →ₗ[ℂ] a.W →ₗ[ℂ] ℂ, B ≠ 0 ∧ ∀ γ x y, B (ρ γ x) (a.ρ γ y) = B x y := hd
  have hd' : ∃ B : VV ℂ lam →ₗ[ℂ] a.W →ₗ[ℂ] ℂ, B ≠ 0 ∧ ∀ γ x y, B (mtRep emb lam γ x) (a.ρ γ y) = B x y := by
    refine ⟨B ∘ₗ T.toLinearMap, fun h => hB0 (LinearMap.ext fun w => ?_), fun γ x y => ?_⟩
    · obtain ⟨x, rfl⟩ := T.surjective w
      exact LinearMap.congr_fun h x
    · show B (T (mtRep emb lam γ x)) (a.ρ γ y) = B (T x) y
      rw [hint]
      exact hB γ (T x) y
  exact mtWtOf_hw_dual highest_weight_fixed_exists highest_weight_fixed_line emb hinj hcm lam τ a lam0 hd' hw

theorem wt_main : ∀ (D : D7) (V : HSp D) (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V), RatIso P e → ∀ (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W), Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → ∃ (alg : Formalism.AUTREP.IsAlgWeight D.host.E V.rank (wtRep c e)) (irr : (wtRep c e).IsIrreducible), ∀ (a : NG.AlgWt D.host.E V.rank) (τ : D.what₂.Tau) (lam0 : Fin V.rank → ℤ), NG.AlgWt.IsDual { W := c.W, ρ := wtRep c e, alg := alg, irr := irr } a → a.HWAt (Formalism.L2.embT D τ) lam0 → lam0 = (lam τ).w := by
  intro D V P e hR c lam c0 ht
  exact exists_weight_of_coefMap D.what₂.embLL (labLL D) (tauE D) GlobalTheory.CoefSpace.embLL_labLL (GlobalTheory.StdRat.tauE_injective D)
    (fun τ τ' h => (GlobalTheory.StdRat.tauE_cm D (tauE D τ')).1 ⟨τ', rfl⟩ ⟨τ, h⟩) lam (wtRep c e) c0
    (fun γ v => ht.1 (e γ) (mtwRat (L := D.host.E) (n := V.rank) γ)
      ((hR γ).2 _ (congrArg Units.val (mtwInc_mtwRatFun γ)).symm) v) ht.2.1 ht.2.2

end GlobalTheory.MtIn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnFaceLevelsBaseLevelSymmetricLevelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnFaceLevels_baseLevel_symmetricLevel : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → Formalism.IndefR.Seed.LevelsL (famR X I hX U Xg tr) L eG (face0 X I hX U Xg tr).lv2 := by
  first | exact @GlobalTheory.Mem.R3.LevelsFace.levelsL_face0 | exact GlobalTheory.Mem.R3.LevelsFace.levelsL_face0 | (intros; apply GlobalTheory.Mem.R3.LevelsFace.levelsL_face0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrimeIdempotentMulEqZeroOfVanishingAtPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
noncomputable section

namespace GlobalTheory.IdemSupp

variable {D : D7}

def singleL (v : HeightOneSpectrum (𝓞 D.host.F)) : Fv D.host.F v →ₗ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F where
  toFun y := singleV D.host.F v y
  map_add' x y := by
    have h := GlobalTheory.IdemModTwo.singleV_sub (D := D) v (x + y) y
    rw [add_sub_cancel_right] at h
    rw [h, sub_add_cancel]
  map_smul' c y := by
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, GlobalTheory.IdemModTwo.singleV_mul (D := D), AlgHom.commutes]

theorem pl_mul_eq (v : HeightOneSpectrum (𝓞 D.host.F)) (z : Formalism.IndefR.Lev.EAf D) :
    swapAE D (finPart D (GlobalTheory.IdemModTwo.pl D v)) * z =
      TensorProduct.map (LinearMap.id : D.host.E →ₗ[D.host.F] D.host.E) (singleL (D := D) v) (Formalism.UG.prV v z) := by
  change ((1 : D.host.E) ⊗ₜ[D.host.F] singleV D.host.F v 1) * z = _
  induction z using TensorProduct.induction_on with
  | zero => rw [mul_zero, map_zero, map_zero]
  | tmul x a =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    change _ = x ⊗ₜ[D.host.F] singleV D.host.F v (evalV D.host.F v a)
    rw [mul_comm, GlobalTheory.IdemModTwo.singleV_mul (D := D), mul_one]
  | add x y hx hy => simp only [mul_add, hx, hy, map_add (f := _)]

theorem idem_mul_eq_zero : ∀ {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (e : Formalism.L2.Theta.AE D), Formalism.L2.Col.IsOver v Pb → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → ∀ z : Formalism.IndefR.Lev.EAf D, Formalism.UG.prV v z = 0 → swapAE D (finPart D e) * z = 0 := by
  intro D v Pb e hov he z hz
  have hov' := Formalism.L2.Col.IsOver.conj D.sp.cm hov
  have hsp := GlobalTheory.GridIdem.splitAt_under he
  have hu : (Formalism.L2.Col.conjPrime₂ Pb).under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hov'.symm
  rw [hu] at hsp
  rw [← hsp.pl_mul, map_mul, map_mul, mul_comm (swapAE D _), mul_assoc, pl_mul_eq, hz, map_zero, mul_zero]

end GlobalTheory.IdemSupp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjUniformizerIsUniformizerConjPrime
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.UnifConj

theorem conj_unif_isUnif : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (Pb : Formalism.L2.DIV.Pl E) (Ut : Formalism.L2.Col.MhlUnif Pb), Formalism.L2.Col.cO E Ut.π ∈ (Formalism.L2.Col.conjPrime₂ Pb).asIdeal ∧ Formalism.L2.Col.cO E Ut.π ∉ (Formalism.L2.Col.conjPrime₂ Pb).asIdeal ^ 2 := by
  intro E _ _ _ Pb Ut
  refine ⟨(Formalism.L2.Col.mem_conjP Pb _).2 (by rw [Formalism.L2.Col.cO_cO]; exact Ut.hπ), ?_⟩
  intro h
  have h2 : Ut.π ∈ Pb.asIdeal ^ 2 := by
    have h1 : Formalism.L2.Col.cO E Ut.π ∈ (Pb.asIdeal ^ 2).comap (Formalism.L2.Col.cO E) :=
      Ideal.le_comap_pow (Formalism.L2.Col.cO E) 2 h
    rw [Ideal.mem_comap, Formalism.L2.Col.cO_cO] at h1
    exact h1
  have hle : Pb.asIdeal ≤ Pb.asIdeal ^ 2 := by
    intro p hp
    obtain ⟨t, ht⟩ := Ut.hcπ p hp
    have hcp : Ut.c * p ∈ Pb.asIdeal ^ 2 := by
      rw [ht]; exact Ideal.mul_mem_right t _ h2
    obtain ⟨a, e, he, hae⟩ := Pb.isMaximal.exists_inv Ut.hc
    have hee : e * e ∈ Pb.asIdeal ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul he he
    have hp' : p = a * (a * Ut.c + 2 * e) * (Ut.c * p) + (e * e) * p := by
      linear_combination (-(p) * (a * Ut.c + e + 1)) * hae
    rw [hp']
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hcp) (Ideal.mul_mem_right _ _ hee)
  have hlt : Pb.asIdeal ^ 2 < Pb.asIdeal ^ 1 :=
    Ideal.pow_right_strictAnti Pb.asIdeal Pb.ne_bot Pb.isPrime.ne_top (by norm_num)
  rw [pow_one] at hlt
  exact hlt.not_ge hle

end GlobalTheory.Mem.UnifConj
end

