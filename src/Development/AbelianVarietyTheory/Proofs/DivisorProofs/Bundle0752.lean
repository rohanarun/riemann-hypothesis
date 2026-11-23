module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Formalism.LocalToGlobal.Divisibility.NumbersLink
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Mathlib
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0732
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfNumReads
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ColRows.NumReads

open Formalism.LatticeIndexTer (ph)

theorem ph_zero : ph 0 = 0 := by simp [ph]

theorem N_pred_le (N : NumDatum) (j : ℕ) (hj : j < N.R.m) : N.R.N ((j + 1) - 1) ≤ N.Nm := by
  unfold NumDatum.Nm Ranks.N
  rw [Nat.add_sub_cancel]
  have := Nat.mul_le_mul_right (N.R.t + 1) hj.le
  omega

theorem ofNum_reads : ∀ (N : NumDatum) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (δ : Code N) (T : ℕ)
    (Nc lam0 C0 ce Ch Sw C1 : ℝ) (H : N.NumFacts δ Nc lam0 C0 ce Ch Sw C1),
    Reads N eJ δ T (RecNums.ofNum N eJ δ T Nc lam0 C0 ce Ch Sw C1 H) := by
  intro N J _ eJ δ T Nc lam0 C0 ce Ch Sw C1 H
  refine ⟨?_, ?_, rfl, ?_, ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · intro z
    exact N.mem_topsPl z
  · intro t _
    rfl
  · intro j z
    have hle := N_pred_le N (eJ j).1 (eJ j).2
    show ∑ i : Fin N.Nm, ph (N.nuPad δ ((eJ j).1 + 1) z i) = _
    unfold NumDatum.nuPad
    have e : ∀ i : Fin N.Nm, ph (if i.1 < N.R.N ((eJ j).1 + 1 - 1) then ((N.nu δ ((eJ j).1 + 1) z i.1 : ℚ) : ℝ) else 0) =
        (if i.1 < N.R.N ((eJ j).1 + 1 - 1) then ph ((N.nu δ ((eJ j).1 + 1) z i.1 : ℚ) : ℝ) else 0) := by
      intro i
      split_ifs
      · rfl
      · exact ph_zero
    rw [Finset.sum_congr rfl (fun i _ => e i),
      NumDatum.sum_pad (fun i => ph ((N.nu δ ((eJ j).1 + 1) z i : ℚ) : ℝ)) hle, Nat.add_sub_cancel]
  · intro j z
    have hle := N_pred_le N (eJ j).1 (eJ j).2
    show ∑ i : Fin N.Nm, N.nuPad δ ((eJ j).1 + 1) z i = _
    unfold NumDatum.nuPad NumDatum.nuAbs
    rw [NumDatum.sum_pad (fun i => ((N.nu δ ((eJ j).1 + 1) z i : ℚ) : ℝ)) hle]
    push_cast
    rfl

end GlobalTheory.ColRows.NumReads
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagonalRamifiedBoundAlongFamily
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.RamifiedOffD

open Formalism.MainNotions.G GlobalTheory.HCEntries GlobalTheory.FockDegreeGap GlobalTheory.RamifiedLoss

variable {D : D7} {L : SizeData₂ D}

theorem offDiagonalRamified_bound_const_four (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) : Formalism.MainNotions.WeightDegreeSizes.DiscriminantOffsetBound D L 4 := by
  intro j hj
  have hp : D.host.d.Prime := D.host.hyp.2.1
  have hb := one_le_b L
  have hL := one_le_scL L
  have hn := one_le_n D
  have hf : (1 : ℝ) ≤ D.R.f := by linarith [f_eq D, one_le_n D]
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hE := abs_EatD_le h P hx j hj
  have hlog : Real.log D.host.d ≤ L.sc.L := by
    obtain ⟨-, -, -, -, -, -, hQ, -⟩ := h
    refine hQ.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le ?_)
    unfold szTh
    linarith [L.sc.eps_pos]
  have hlog0 : 0 ≤ Real.log (D.host.d : ℝ) := Real.log_natCast_nonneg _
  have hE2 : |EatD D j| ≤ 2 * ((D.R.f : ℝ) * L.sc.b) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hS, -⟩ := h
    have a1 : (D.host.TT.card : ℝ) ≤ D.R.n := by
      rw [← card_HH]
      exact_mod_cast Finset.card_le_univ _
    have a2 : (D.host.TT.card : ℝ) * L.sc.b ≤ D.R.f * L.sc.b :=
      mul_le_mul_of_nonneg_right (by linarith [f_eq D]) (by linarith)
    have a3 : (D.R.f : ℝ) * (D.R.k * L.sc.b') ≤ D.R.f * L.sc.b :=
      mul_le_mul_of_nonneg_left (k_b'_le hS) (by linarith)
    linarith
  have hB : L.B0 = D.R.f * D.R.m * L.sc.b * L.sc.L := rfl
  have hB1 : D.R.f * L.sc.b * L.sc.L ≤ L.B0 := by
    rw [hB, show (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L = D.R.m * (D.R.f * L.sc.b * L.sc.L) by ring]
    exact le_mul_of_one_le_left (by positivity) hm
  have h1 : Real.log (D.host.d : ℝ) * |EatD D j| ≤ L.sc.L * (2 * ((D.R.f : ℝ) * L.sc.b)) :=
    mul_le_mul hlog hE2 (abs_nonneg _) (by linarith)
  nlinarith

theorem offDiagonalRamified_bound_along_family : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.DiscriminantOffsetBound (Fm.D x i) (Fm.L x i) C := by
  intro eps Fm _ _
  refine ⟨4, 2, by norm_num, fun x hx0 hx i => ?_⟩
  exact offDiagonalRamified_bound_const_four (Fm.sizes x hx i) (Fm.params x hx i) (by rw [Fm.L_x x i hx]; exact hx0)

end GlobalTheory.RamifiedOffD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpNormAtPairingSqLeOfValueBound
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.PairingOpNorm
open Matrix

theorem pairing_eq {K : Type} [Field K] (c n : ℕ) (g : (Fin c → K) →ₗ[K] Module.Dual K (Fin n → K))
    (y : Fin c → K) (F : Fin n → K) :
    g y F = F ⬝ᵥ (LinearMap.toMatrix (Pi.basisFun K (Fin c)) (Pi.basisFun K (Fin n)).dualBasis g *ᵥ y) := by
  have h := LinearMap.toMatrix_mulVec_repr (Pi.basisFun K (Fin c)) (Pi.basisFun K (Fin n)).dualBasis g y
  rw [show (Pi.basisFun K (Fin c)).repr y = y from rfl] at h
  rw [h]
  conv_lhs => rw [← (Pi.basisFun K (Fin n)).sum_repr F]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dotProduct, map_sum, Basis.dualBasis_repr]

theorem continuous_cnorm {ι : Type} [Fintype ι] : Continuous (Formalism.HermitianLatticesTheory.cnorm : (ι → ℂ) → ℝ) := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  fun_prop

theorem cnorm_nonneg {ι : Type} [Fintype ι] (u : ι → ℂ) : 0 ≤ Formalism.HermitianLatticesTheory.cnorm u := Real.sqrt_nonneg _

theorem bilin_bound {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (c n : ℕ)
    (X : Matrix (Fin c) (Fin c) ℂ) (X0 : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin n) (Fin c) ℂ)
    (v : InfinitePlace K) (C : ℝ)
    (h : ∀ (y : Fin c → K) (F : Fin n → K), ‖(fun j => v.embedding (F j)) ⬝ᵥ (S *ᵥ fun i => v.embedding (y i))‖ ≤
      C * Formalism.HermitianLatticesTheory.cnorm (X0⁻¹ *ᵥ fun j => v.embedding (F j)) * Formalism.HermitianLatticesTheory.cnorm (X⁻¹ *ᵥ fun i => v.embedding (y i)))
    (u : Fin n → ℂ) (z : Fin c → ℂ) :
    ‖u ⬝ᵥ (S *ᵥ z)‖ ≤ C * Formalism.HermitianLatticesTheory.cnorm (X0⁻¹ *ᵥ u) * Formalism.HermitianLatticesTheory.cnorm (X⁻¹ *ᵥ z) := by
  have hv : v.IsComplex := IsTotallyComplex.isComplex v
  have hd : DenseRange (Prod.map (Pi.map (fun _ : Fin n => (v.embedding : K → ℂ)))
      (Pi.map (fun _ : Fin c => (v.embedding : K → ℂ)))) :=
    DenseRange.prodMap (DenseRange.piMap (fun _ => denseRange_embedding_of_isComplex v hv))
      (DenseRange.piMap (fun _ => denseRange_embedding_of_isComplex v hv))
  have key : ∀ p : (Fin n → ℂ) × (Fin c → ℂ),
      ‖p.1 ⬝ᵥ (S *ᵥ p.2)‖ ≤ C * Formalism.HermitianLatticesTheory.cnorm (X0⁻¹ *ᵥ p.1) * Formalism.HermitianLatticesTheory.cnorm (X⁻¹ *ᵥ p.2) := by
    intro p
    induction p using hd.induction_on with
    | hp =>
      apply isClosed_le
      · exact (Continuous.dotProduct continuous_fst
          (Continuous.matrix_mulVec continuous_const continuous_snd)).norm
      · exact (continuous_const.mul (continuous_cnorm.comp
          (Continuous.matrix_mulVec continuous_const continuous_fst))).mul
          (continuous_cnorm.comp (Continuous.matrix_mulVec continuous_const continuous_snd))
    | ih q => exact h q.2 q.1
  exact key (u, z)

end GlobalTheory.PairingOpNorm

namespace GlobalTheory.PairingOpNorm
open Matrix

theorem opNormAt_pairing_sq_le : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (c n : ℕ) (X : InfinitePlace K → Matrix (Fin c) (Fin c) ℂ) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (g : (Fin c → K) →ₗ[K] Module.Dual K (Fin n → K)) (v : InfinitePlace K) (A : ℝ), IsUnit (X v).det → IsUnit (X0 v).det → (∀ y F, v (g y F) ^ 2 ≤ Real.exp A * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin c)) X v y ^ 2 * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X0 v F ^ 2) → Formalism.HN.opNormAt (Pi.basisFun K (Fin c)) X (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X0) v g ^ 2 ≤ Real.exp A := by
  intro K _ _ _ _ c n X X0 g v A hX hX0 hb
  set σ : K →+* ℂ := v.embedding with hσ
  set S : Matrix (Fin n) (Fin c) ℂ :=
    (LinearMap.toMatrix (Pi.basisFun K (Fin c)) (Pi.basisFun K (Fin n)).dualBasis g).map σ with hS
  set C : ℝ := Real.exp (A / 2) with hC
  have hC0 : 0 ≤ C := (Real.exp_pos _).le
  have hCsq : C ^ 2 = Real.exp A := by rw [hC, sq, ← Real.exp_add]; ring_nf
  have hnorm : ∀ {m : ℕ} (Y : InfinitePlace K → Matrix (Fin m) (Fin m) ℂ) (x : Fin m → K),
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin m)) Y v x = Formalism.HermitianLatticesTheory.cnorm ((Y v)⁻¹ *ᵥ fun i => σ (x i)) := by
    intro m Y x; rfl
  have hK : ∀ (y : Fin c → K) (F : Fin n → K), ‖(fun j => σ (F j)) ⬝ᵥ (S *ᵥ fun i => σ (y i))‖ ≤
      C * Formalism.HermitianLatticesTheory.cnorm ((X0 v)⁻¹ *ᵥ fun j => σ (F j)) * Formalism.HermitianLatticesTheory.cnorm ((X v)⁻¹ *ᵥ fun i => σ (y i)) := by
    intro y F
    have e1 : (fun j => σ (F j)) ⬝ᵥ (S *ᵥ fun i => σ (y i)) = σ (g y F) := by
      rw [pairing_eq, RingHom.map_dotProduct]
      congr 1
      funext i
      exact (RingHom.map_mulVec σ _ y i).symm
    rw [e1, hσ, InfinitePlace.norm_embedding_eq]
    have h1 := hb y F
    rw [hnorm, hnorm] at h1
    have hpos : 0 ≤ C * Formalism.HermitianLatticesTheory.cnorm ((X0 v)⁻¹ *ᵥ fun j => σ (F j)) *
        Formalism.HermitianLatticesTheory.cnorm ((X v)⁻¹ *ᵥ fun i => σ (y i)) :=
      mul_nonneg (mul_nonneg hC0 (cnorm_nonneg _)) (cnorm_nonneg _)
    refine (pow_le_pow_iff_left₀ (apply_nonneg v _) hpos (by norm_num : (2:ℕ) ≠ 0)).1 ?_
    calc v (g y F) ^ 2 ≤ _ := h1
      _ = _ := by rw [mul_pow, mul_pow, hCsq]; ring
  have hB := bilin_bound c n (X v) (X0 v) S v C hK
  have hinv : (Formalism.HN.dualFrame X0 v)⁻¹ = (X0 v)ᵀ := by
    unfold Formalism.HN.dualFrame
    rw [Matrix.nonsing_inv_nonsing_inv]
    rwa [Matrix.det_transpose]
  unfold Formalism.HN.opNormAt
  rw [hinv]
  suffices hT : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((X0 v)ᵀ * S * X v))‖ ≤ C by
    rw [← hCsq]
    exact pow_le_pow_left₀ (norm_nonneg _) hT 2
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 (fun ξ => ?_)
  set M : Matrix (Fin n) (Fin c) ℂ := (X0 v)ᵀ * S * X v with hM
  set w : Fin c → ℂ := WithLp.ofLp ξ with hw
  set m : Fin n → ℂ := M *ᵥ w with hm
  have hTx : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M) ξ‖ = Formalism.HermitianLatticesTheory.cnorm m := by
    simp [LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply, EuclideanSpace.norm_eq,
      Formalism.HermitianLatticesTheory.cnorm, hm, hw]
  have hξ : ‖ξ‖ = Formalism.HermitianLatticesTheory.cnorm w := by
    simp [EuclideanSpace.norm_eq, Formalism.HermitianLatticesTheory.cnorm, hw]
  rw [hTx, hξ]
  have h1 := hB ((X0 v) *ᵥ star m) ((X v) *ᵥ w)
  have i0 : (X0 v)⁻¹ *ᵥ ((X0 v) *ᵥ star m) = star m := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hX0, Matrix.one_mulVec]
  have i1 : (X v)⁻¹ *ᵥ ((X v) *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hX, Matrix.one_mulVec]
  rw [i0, i1] at h1
  have e2 : ((X0 v) *ᵥ star m) ⬝ᵥ (S *ᵥ ((X v) *ᵥ w)) = star m ⬝ᵥ m := by
    rw [hm, hM, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hsum : 0 ≤ ∑ i, ‖m i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hcn : Formalism.HermitianLatticesTheory.cnorm m ^ 2 = ∑ i, ‖m i‖ ^ 2 := by
    unfold Formalism.HermitianLatticesTheory.cnorm; rw [Real.sq_sqrt hsum]
  have e3 : ‖star m ⬝ᵥ m‖ = Formalism.HermitianLatticesTheory.cnorm m ^ 2 := by
    rw [hcn]
    have : star m ⬝ᵥ m = ((∑ i, ‖m i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Complex.star_def, Complex.conj_mul']
    rw [this, Complex.norm_of_nonneg hsum]
  have e4 : Formalism.HermitianLatticesTheory.cnorm (star m) = Formalism.HermitianLatticesTheory.cnorm m := by
    simp [Formalism.HermitianLatticesTheory.cnorm]
  rw [e2, e3, e4] at h1
  rcases (cnorm_nonneg m).eq_or_lt with h0 | h0
  · rw [← h0]; exact mul_nonneg hC0 (cnorm_nonneg w)
  · refine le_of_mul_le_mul_left ?_ h0
    nlinarith [h1]

end GlobalTheory.PairingOpNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAtInvNatSmulSelf
section
noncomputable section

namespace GlobalTheory.ColNorms.SumBound

open NumberField IsDedekindDomain
open Formalism.L2.DIV _root_.Formalism.L2.Col GlobalTheory.ColNorms
open scoped ComplexOrder Matrix

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (v : InfinitePlace K)

theorem pairAt_add_left (x y z : S.V) : S.pairAt v (x + y) z = S.pairAt v x z + S.pairAt v y z := by
  simp only [GSD.pairAt, map_add (f := _), Finsupp.add_apply, add_mul, Finset.sum_add_distrib]

theorem pairAt_add_right (x y z : S.V) : S.pairAt v x (y + z) = S.pairAt v x y + S.pairAt v x z := by
  simp only [GSD.pairAt, map_add (f := _), Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

theorem pairAt_smul_left (a : K) (x y : S.V) :
    S.pairAt v (a • x) y = starRingEnd ℂ (v.embedding a) * S.pairAt v x y := by
  simp only [GSD.pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem pairAt_smul_right (a : K) (x y : S.V) :
    S.pairAt v x (a • y) = v.embedding a * S.pairAt v x y := by
  simp only [GSD.pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem pairAt_zero_left (y : S.V) : S.pairAt v 0 y = 0 := by
  simp [GSD.pairAt]

theorem pairAt_zero_right (y : S.V) : S.pairAt v y 0 = 0 := by
  simp [GSD.pairAt]

theorem pairAt_sum_left {α : Type*} (s : Finset α) (x : α → S.V) (y : S.V) :
    S.pairAt v (∑ i ∈ s, x i) y = ∑ i ∈ s, S.pairAt v (x i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pairAt_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pairAt_add_left, ih]

theorem pairAt_sum_right {α : Type*} (s : Finset α) (x : α → S.V) (y : S.V) :
    S.pairAt v y (∑ i ∈ s, x i) = ∑ i ∈ s, S.pairAt v y (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pairAt_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pairAt_add_right, ih]

theorem pairAt_self_nonneg (h : PosAt S v) (x : S.V) : 0 ≤ (S.pairAt v x x).re := by
  have h1 := h.dotProduct_mulVec_nonneg (fun i => v.embedding (S.bV.repr x i))
  have h2 : S.pairAt v x x = star (fun i => v.embedding (S.bV.repr x i)) ⬝ᵥ
      (S.gramV.map v.embedding) *ᵥ (fun i => v.embedding (S.bV.repr x i)) := by
    simp only [GSD.pairAt, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Pi.star_apply, mul_assoc]
    rfl
  rw [h2]
  exact (Complex.nonneg_iff.mp h1).1

theorem pairAt_smul_self (a : K) (x : S.V) :
    (S.pairAt v (a • x) (a • x)).re = ‖v.embedding a‖ ^ 2 * (S.pairAt v x x).re := by
  rw [pairAt_smul_left, pairAt_smul_right, ← mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow, Complex.re_ofReal_mul]

theorem pairAt_inv_nat_smul_self (n : ℕ) (x : S.V) :
    (S.pairAt v (((n : K))⁻¹ • x) (((n : K))⁻¹ • x)).re = ((n : ℝ)⁻¹) ^ 2 * (S.pairAt v x x).re := by
  rw [pairAt_smul_self]
  simp

theorem pairAt_cross_le (h : PosAt S v) (x y : S.V) :
    (S.pairAt v x y).re + (S.pairAt v y x).re ≤ (S.pairAt v x x).re + (S.pairAt v y y).re := by
  have h1 := pairAt_self_nonneg S v h (x + (-1 : K) • y)
  rw [pairAt_add_left, pairAt_add_right, pairAt_add_right, pairAt_smul_left, pairAt_smul_left,
    pairAt_smul_right, pairAt_smul_right] at h1
  simp at h1
  linarith

theorem pairAt_sum_le (h : PosAt S v) {α : Type*} (s : Finset α) (x : α → S.V) :
    (S.pairAt v (∑ i ∈ s, x i) (∑ i ∈ s, x i)).re ≤ (s.card : ℝ) * ∑ i ∈ s, (S.pairAt v (x i) (x i)).re := by
  have e1 : (S.pairAt v (∑ i ∈ s, x i) (∑ i ∈ s, x i)).re = ∑ i ∈ s, ∑ j ∈ s, (S.pairAt v (x i) (x j)).re := by
    rw [pairAt_sum_left, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pairAt_sum_right, Complex.re_sum]
  have e2 : (S.pairAt v (∑ i ∈ s, x i) (∑ i ∈ s, x i)).re = ∑ i ∈ s, ∑ j ∈ s, (S.pairAt v (x j) (x i)).re := by
    rw [e1, Finset.sum_comm]
  have e3 : ∑ i ∈ s, ∑ j ∈ s, ((S.pairAt v (x i) (x j)).re + (S.pairAt v (x j) (x i)).re) ≤
      ∑ i ∈ s, ∑ j ∈ s, ((S.pairAt v (x i) (x i)).re + (S.pairAt v (x j) (x j)).re) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => pairAt_cross_le S v h _ _
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at e3
  linarith

theorem ipAt_re (h : S.Ok) (φ ψ : S.D → S.V) :
    (S.ipAt h v φ ψ).re = ∑ c ∈ @Finset.univ _ h.fintypeCl,
      (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ * (S.pairAt v (φ (S.outSec.rep c)) (ψ (S.outSec.rep c))).re := by
  unfold GSD.ipAt
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]

theorem inv_nat_le_one (n : ℕ) : ((n : ℝ))⁻¹ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast hn)

theorem ipAt_self_nonneg (h : S.Ok) (hp : PosAt S v) (φ : S.D → S.V) : 0 ≤ (S.ipAt h v φ φ).re := by
  rw [ipAt_re]
  exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (pairAt_self_nonneg S v hp _)

theorem ipAt_self_le (h : S.Ok) (hp : PosAt S v) (φ : S.D → S.V) (B : ℝ)
    (hB : ∀ d, (S.pairAt v (φ d) (φ d)).re ≤ B) : (S.ipAt h v φ φ).re ≤ (Nat.card S.Cl : ℝ) * B := by
  rw [ipAt_re]
  letI := h.fintypeCl
  calc _ ≤ ∑ _c : S.Cl, B := Finset.sum_le_sum fun c _ => by
        have h0 := pairAt_self_nonneg S v hp (φ (S.outSec.rep c))
        exact ((mul_le_mul_of_nonneg_right (inv_nat_le_one _) h0).trans (by rw [one_mul])).trans (hB _)
    _ = _ := by simp [Nat.card_eq_fintype_card]


variable {S} in
theorem appOf_le {S' : GSD K} (A : ClsKer S S') (h : S.Ok) (hp : PosAt S v) (hp' : PosAt S' v) (t : ℝ) (ht : 0 ≤ t)
    (φ : S.D → S.V) (d' : S'.D) (hA : ∀ d, OpLe S S' v (A.k d d') t) :
    (S'.pairAt v (A.appOf h S.outSec φ d') (A.appOf h S.outSec φ d')).re ≤
      (Nat.card S.Cl : ℝ) * (t * (S.ipAt h v φ φ).re) := by
  letI := h.fintypeCl
  unfold ClsKer.appOf
  refine (pairAt_sum_le S' v hp' _ _).trans ?_
  rw [Finset.card_univ, Nat.card_eq_fintype_card, ipAt_re, Finset.mul_sum _ _ t]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => ?_) (by positivity)
  rw [pairAt_inv_nat_smul_self]
  have h0 := pairAt_self_nonneg S v hp (φ (S.outSec.rep c))
  have h1 := hA (S.outSec.rep c) (φ (S.outSec.rep c))
  have h2 := inv_nat_le_one ((S.toCSD h).wt c)
  have h3 : (0 : ℝ) ≤ (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ := by positivity
  change (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ ^ 2 * _ ≤ _
  generalize (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ = w at *
  calc _ ≤ w ^ 2 * (t * (S.pairAt v (φ (S.outSec.rep c)) (φ (S.outSec.rep c))).re) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ w * (t * (S.pairAt v (φ (S.outSec.rep c)) (φ (S.outSec.rep c))).re) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ = _ := by ring

end GlobalTheory.ColNorms.SumBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFreeResolutionsHomotopyEquivalent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem resolution_lift_of_exact {O : Type} [CommRing O] {P A B C : Type}
    [AddCommGroup P] [Module O P] [Module.Projective O P]
    [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B] [AddCommGroup C] [Module O C]
    {u : A →ₗ[O] B} {v : B →ₗ[O] C} (huv : Function.Exact u v) (w : P →ₗ[O] B)
    (hw : v ∘ₗ w = 0) : ∃ l : P →ₗ[O] A, u ∘ₗ l = w := by
  have hr : ∀ x, w x ∈ LinearMap.range u := fun x => by
    rw [← LinearMap.exact_iff.mp huv, LinearMap.mem_ker]
    exact LinearMap.congr_fun hw x
  obtain ⟨l, hl⟩ := Module.projective_lifting_property u.rangeRestrict (w.codRestrict _ hr)
    u.surjective_rangeRestrict
  refine ⟨l, ?_⟩
  ext x
  have := congrArg Subtype.val (LinearMap.congr_fun hl x)
  simpa using this

theorem resolutions_homotopy_equivalent : ∀ (O : Type) [CommRing O] (N : Type) [AddCommGroup N] [Module O N] (F₀ : Type) [AddCommGroup F₀] [Module O F₀] [Module.Free O F₀] [Module.Finite O F₀] (F₁ : Type) [AddCommGroup F₁] [Module O F₁] [Module.Free O F₁] [Module.Finite O F₁] (F₂ : Type) [AddCommGroup F₂] [Module O F₂] [Module.Free O F₂] [Module.Finite O F₂] (F₃ : Type) [AddCommGroup F₃] [Module O F₃] [Module.Free O F₃] [Module.Finite O F₃] (G₀ : Type) [AddCommGroup G₀] [Module O G₀] [Module.Free O G₀] [Module.Finite O G₀] (G₁ : Type) [AddCommGroup G₁] [Module O G₁] [Module.Free O G₁] [Module.Finite O G₁] (G₂ : Type) [AddCommGroup G₂] [Module O G₂] [Module.Free O G₂] [Module.Finite O G₂] (ε : F₀ →ₗ[O] N) (d₁ : F₁ →ₗ[O] F₀) (d₂ : F₂ →ₗ[O] F₁) (d₃ : F₃ →ₗ[O] F₂) (ν : G₀ →ₗ[O] N) (e₁ : G₁ →ₗ[O] G₀) (e₂ : G₂ →ₗ[O] G₁), Function.Surjective ε → Function.Exact d₁ ε → Function.Exact d₂ d₁ → Function.Exact d₃ d₂ → Function.Surjective ν → Function.Exact e₁ ν → Function.Exact e₂ e₁ → ∃ (a₀ : F₀ →ₗ[O] G₀) (a₁ : F₁ →ₗ[O] G₁) (a₂ : F₂ →ₗ[O] G₂) (b₀ : G₀ →ₗ[O] F₀) (b₁ : G₁ →ₗ[O] F₁) (b₂ : G₂ →ₗ[O] F₂) (h₀ : F₀ →ₗ[O] F₁) (h₁ : F₁ →ₗ[O] F₂) (h₂ : F₂ →ₗ[O] F₃) (k₀ : G₀ →ₗ[O] G₁) (k₁ : G₁ →ₗ[O] G₂), e₁ ∘ₗ a₁ = a₀ ∘ₗ d₁ ∧ e₂ ∘ₗ a₂ = a₁ ∘ₗ d₂ ∧ d₁ ∘ₗ b₁ = b₀ ∘ₗ e₁ ∧ d₂ ∘ₗ b₂ = b₁ ∘ₗ e₂ ∧ LinearMap.id - b₁ ∘ₗ a₁ = d₂ ∘ₗ h₁ + h₀ ∘ₗ d₁ ∧ LinearMap.id - b₂ ∘ₗ a₂ = d₃ ∘ₗ h₂ + h₁ ∘ₗ d₂ ∧ LinearMap.id - a₁ ∘ₗ b₁ = e₂ ∘ₗ k₁ + k₀ ∘ₗ e₁ := by
  intro O _ N _ _ F₀ _ _ _ _ F₁ _ _ _ _ F₂ _ _ _ _ F₃ _ _ _ _ G₀ _ _ _ _ G₁ _ _ _ _ G₂ _ _ _ _
    ε d₁ d₂ d₃ ν e₁ e₂ hε hd1 hd2 hd3 hν he1 he2
  obtain ⟨a₀, ha₀⟩ := Module.projective_lifting_property ν ε hν
  obtain ⟨b₀, hb₀⟩ := Module.projective_lifting_property ε ν hε
  have ha₀' : ∀ x, ν (a₀ x) = ε x := fun x => LinearMap.congr_fun ha₀ x
  have hb₀' : ∀ x, ε (b₀ x) = ν x := fun x => LinearMap.congr_fun hb₀ x
  obtain ⟨a₁, ha₁⟩ := resolution_lift_of_exact he1 (a₀ ∘ₗ d₁) (by
    ext x; simp [ha₀', Function.Exact.apply_apply_eq_zero hd1])
  have ha₁' : ∀ x, e₁ (a₁ x) = a₀ (d₁ x) := fun x => LinearMap.congr_fun ha₁ x
  obtain ⟨a₂, ha₂⟩ := resolution_lift_of_exact he2 (a₁ ∘ₗ d₂) (by
    ext x; simp [ha₁', Function.Exact.apply_apply_eq_zero hd2])
  obtain ⟨b₁, hb₁⟩ := resolution_lift_of_exact hd1 (b₀ ∘ₗ e₁) (by
    ext x; simp [hb₀', Function.Exact.apply_apply_eq_zero he1])
  have hb₁' : ∀ x, d₁ (b₁ x) = b₀ (e₁ x) := fun x => LinearMap.congr_fun hb₁ x
  obtain ⟨b₂, hb₂⟩ := resolution_lift_of_exact hd2 (b₁ ∘ₗ e₂) (by
    ext x; simp [hb₁', Function.Exact.apply_apply_eq_zero he2])
  obtain ⟨h₀, hh₀⟩ := resolution_lift_of_exact hd1 (LinearMap.id - b₀ ∘ₗ a₀) (by
    ext x; simp [hb₀', ha₀'])
  have hh₀' : ∀ x, d₁ (h₀ x) = x - b₀ (a₀ x) := fun x => by
    simpa using LinearMap.congr_fun hh₀ x
  obtain ⟨h₁, hh₁⟩ := resolution_lift_of_exact hd2 (LinearMap.id - b₁ ∘ₗ a₁ - h₀ ∘ₗ d₁) (by
    ext x; simp [hb₁', ha₁', hh₀'])
  have hh₁' : ∀ x, d₂ (h₁ x) = x - b₁ (a₁ x) - h₀ (d₁ x) := fun x => by
    simpa using LinearMap.congr_fun hh₁ x
  obtain ⟨h₂, hh₂⟩ := resolution_lift_of_exact hd3 (LinearMap.id - b₂ ∘ₗ a₂ - h₁ ∘ₗ d₂) (by
    ext x
    have e1 := LinearMap.congr_fun hb₂ (a₂ x)
    have e2 := LinearMap.congr_fun ha₂ x
    simp only [LinearMap.comp_apply] at e1 e2
    simp [hh₁', e1, e2, Function.Exact.apply_apply_eq_zero hd2])
  obtain ⟨k₀, hk₀⟩ := resolution_lift_of_exact he1 (LinearMap.id - a₀ ∘ₗ b₀) (by
    ext x; simp [hb₀', ha₀'])
  have hk₀' : ∀ x, e₁ (k₀ x) = x - a₀ (b₀ x) := fun x => by
    simpa using LinearMap.congr_fun hk₀ x
  obtain ⟨k₁, hk₁⟩ := resolution_lift_of_exact he2 (LinearMap.id - a₁ ∘ₗ b₁ - k₀ ∘ₗ e₁) (by
    ext x; simp [hb₁', ha₁', hk₀'])
  refine ⟨a₀, a₁, a₂, b₀, b₁, b₂, h₀, h₁, h₂, k₀, k₁, ha₁, ha₂, hb₁, hb₂, ?_, ?_, ?_⟩
  · rw [hh₁, sub_add_cancel]
  · rw [hh₂, sub_add_cancel]
  · rw [hk₁, sub_add_cancel]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSectionsGroupSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_sections_group_scheme : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k mA : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))), IsBCBasis A L k bA → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) [GrpObj A'] (φA' : A'.left ⟶ A.left) (ψA : A'.left ⟶ (topS Rg ⊗ A).left), IsGrpPullback A' A t φA' → ψA ≫ (snd (topS Rg) A).left = φA' → ∀ (d : Fin mA → Γ(Sp R, ⊤)), (∀ (j : Fin 1 → L.ι) (x : A'.left), x ∈ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j → ∃ (W : A'.left.Opens) (hW : W ≤ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j), x ∈ W ∧ ∑ i, (A'.hom.appLE ⊤ W (by simp)).hom (d i) * (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j) W (hW.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j))).hom ((bA i).f j) = 0) → d = 0 := by
  first | (exact @GlobalTheory.HomFixIndep.pulled_basis_indep) | (exact GlobalTheory.HomFixIndep.pulled_basis_indep) | (intros; apply GlobalTheory.HomFixIndep.pulled_basis_indep  <;> assumption)
end

