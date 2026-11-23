module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0336
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0582
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0339
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0433
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0345
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0551
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0530
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0546
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0576
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0557
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0558
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0591
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002
public import GroundTheory.GlobalFields.LocalAtPlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedLanglandsFactorsSquareIntegrable
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.TemperedCore

theorem exists_lFactors_unitary : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSocleGL k → Zl.CasselmanNecTemp k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible → IsTemperedCoeff π → IsL 𝔪 π → ∃ (h : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x ∧ ∀ (a : Fin h) (t : kˣ) (c : ℂ), Zl.ScalarBy (x a) t c → ‖c‖ = 1 := by
  intro k _ _ _ _ hSoc hCas hSeg 𝔪 N V _ _ π hN hsm hirr htemp hL
  have hy : ∀ Δ : Segment k, ∃ y : IrrGL (k := k), IsLSeg Δ y.rep := fun Δ => by
    obtain ⟨ρ, hρ⟩ := hSeg Δ
    exact ⟨IrrGL.of ρ.ρ ρ.smooth ρ.irr, hρ.of_equiv (IrrGL.equivOf _ _ _)⟩
  choose y hyL using hy
  have hypos : ∀ Δ : Segment k, 0 < (y Δ).1 := fun Δ => by
    rw [← (hyL Δ).deg_eq]
    exact Nat.mul_pos Δ.len_pos Δ.d_pos
  have hs : ∀ Δ : Segment k, ∃ s : ℝ, ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy (y Δ) t c →
      ‖c‖ = nabs k t ^ (((y Δ).1 : ℝ) * s) := fun Δ => GlobalTheory.T.central_character_norm_eq_pow k (y Δ) (hypos Δ)
  choose f hf using hs
  obtain ⟨h, Δ, hΔ, hanti, hnp⟩ := GlobalTheory.T.multiset_antitone_enumeration 𝔪 f Segment.Precedes (fun a b hab =>
    GlobalTheory.T.exponent_lt_of_precedes_of_isLSeg k a b (y a) (y b) (f a) (f b) (hyL a) (hyL b) (hf a) (hf b) hab)
  let x : Fin h → IrrGL (k := k) := fun a => y (Δ a)
  have hLF : LFactors 𝔪 x := ⟨Δ, ⟨hΔ, hnp⟩, fun i => hyL _⟩
  have hsumdeg : ∀ {h' : ℕ} (Δ' : Fin h' → Segment k) (x' : Fin h' → IrrGL (k := k)),
      Finset.univ.val.map Δ' = 𝔪 → (∀ i, IsLSeg (Δ' i) (x' i).rep) →
      ∑ a, (x' a).1 = (𝔪.map Segment.deg).sum := by
    intro h' Δ' x' hm hx'
    rw [← hm, Multiset.map_map]
    exact Finset.sum_congr rfl fun a _ => ((hx' a).deg_eq).symm
  have hdeg : ∑ a, (x a).1 = N := by
    obtain ⟨h', x', hd', ⟨Δ', ⟨hΔ', -⟩, hx'⟩, -⟩ := hL
    rw [hsumdeg Δ x hΔ (fun i => hyL _), ← hsumdeg Δ' x' hΔ' hx', hd']
  have hdrev : ∑ a, (x (Fin.rev a)).1 = N := by
    rw [← hdeg]
    exact Equiv.sum_comp Fin.revPerm (fun a => (x a).1)
  have hsoc := hSoc 𝔪 h N x hdrev hLF π hL
  have hjm := GlobalTheory.T.jacquet_multiplicity_pos_of_socle k h N (x ∘ Fin.rev) hdrev π hsm (fun a => hypos _) hsoc
  have hW := hCas N π hN hsm hirr htemp h (x ∘ Fin.rev) hdrev (fun a => hypos _) hjm
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.CompanionTheory.LocalFieldPow.exists_unit_pow_tendsto_zero k
  have ht1 : nabs k t < 1 := _root_.GlobalTheory.CompanionTheory.NabsContract.nabs_lt_one_of_tendsto_pow k t ht
  have ht0 : 0 < nabs k t := by
    have h0 : (MeasureTheory.distribHaarChar k t : NNReal) ≠ 0 := fun h0 => by
      have := map_mul (MeasureTheory.distribHaarChar k) t t⁻¹
      simp [h0] at this
    exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 h0)
  have hge : ∀ r : ℝ, nabs k t ^ r ≤ 1 → 0 ≤ r := fun r hr => by
    by_contra hneg
    exact absurd hr (not_le.2 (Real.one_lt_rpow_of_pos_of_lt_one_of_neg ht0 ht1 (not_le.1 hneg)))
  choose c hc using fun a => GlobalTheory.T.central_character_exists k (x a) t
  obtain ⟨hpart, htot⟩ := hW t ht (c ∘ Fin.rev) (fun i => hc _)
  let e : Fin h → ℝ := fun i => f (Δ i)
  let d : Fin h → ℝ := fun i => ((x i).1 : ℝ)
  have hnorm : ∀ i, ‖c i‖ = nabs k t ^ (d i * e i) := fun i => hf (Δ i) t (c i) (hc i)
  have hprod : ∀ S : Finset (Fin h), ∏ i ∈ S, ‖c i‖ = nabs k t ^ (∑ i ∈ S, d i * e i) := fun S => by
    rw [Real.rpow_sum_of_pos ht0]
    exact Finset.prod_congr rfl fun i _ => hnorm i
  have hsum : ∑ i, d i * e i = 0 := by
    have h1 : ∏ i, ‖c i‖ = 1 := by
      rw [← htot]
      exact (Equiv.prod_comp Fin.revPerm (fun i => ‖c i‖)).symm
    rw [hprod] at h1
    refine le_antisymm ?_ (hge _ h1.le)
    have := hge (-∑ i, d i * e i) (by rw [Real.rpow_neg ht0.le, h1, inv_one])
    linarith
  have htail : ∀ j : Fin h, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i := by
    intro j
    by_cases hj : (Fin.rev j).val + 1 < h
    · have h1 := hpart (Fin.rev j) hj
      have h2 := _root_.GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev h (fun i => ‖c i‖) (Fin.rev j)
      rw [Fin.rev_rev] at h2
      have h3 : ∏ i ∈ Finset.univ.filter (fun i => i ≤ Fin.rev j), ‖(c ∘ Fin.rev) i‖ =
          ∏ i ∈ Finset.univ.filter (fun i => j ≤ i), ‖c i‖ := h2
      rw [h3, hprod] at h1
      exact hge _ h1
    · have hj0 : j.val = 0 := by
        have := j.isLt
        rw [Fin.val_rev] at hj
        omega
      have hf' : Finset.univ.filter (fun i => j ≤ i) = Finset.univ := by
        ext i
        simp [Fin.le_def, hj0]
      rw [hf', hsum]
  have he := _root_.GlobalTheory.CompanionTheory.Tempered.weighted_antitone_eq_zero_of_tails_nonneg h d e (fun i => Nat.cast_pos.2 (hypos (Δ i))) hanti hsum htail
  refine ⟨h, x, hdeg, hLF, fun a t' c' hsc => ?_⟩
  have h1 := hf (Δ a) t' c' hsc
  have h2 : f (Δ a) = 0 := he a
  rw [h1, h2, mul_zero, Real.rpow_zero]

end GlobalTheory.CompanionTheory.TemperedCore
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionSumZetaBoundDelta
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU

variable {E : Type} [Field E] [NumberField E] {m : ℕ}

theorem fibre_bound (c : Matrix (Fin m) (Fin m) E) (b : (Fin m → E) ⧸ lam c) :
    Finite {U : (Fin m → E) ⧸ intVec E m //
        (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b} ∧
      Nat.card {U : (Fin m → E) ⧸ intVec E m //
        (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b} ≤ delta c := by
  obtain ⟨hne, hidx⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_index E m c
  set H := (intVec E m).toAddSubgroup with hH
  set Kg := (lam c).toAddSubgroup with hK
  have hidx' : delta c = (H.addSubgroupOf Kg).index := hidx
  have hcard : Nat.card (Kg ⧸ H.addSubgroupOf Kg) = delta c := by
    rw [hidx']; rfl
  haveI : Finite (Kg ⧸ H.addSubgroupOf Kg) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hne)
  have hw : (Submodule.Quotient.mk (Quotient.out b) : (Fin m → E) ⧸ lam c) = b :=
    Quotient.out_eq' b
  have hmem : ∀ a : {U : (Fin m → E) ⧸ intVec E m //
      (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b},
      Quotient.out a.1 - Quotient.out b ∈ Kg := by
    intro a
    have : (Submodule.Quotient.mk (Quotient.out a.1) : (Fin m → E) ⧸ lam c) =
        Submodule.Quotient.mk (Quotient.out b) := a.2.trans hw.symm
    exact (Submodule.Quotient.eq _).1 this
  let φ : {U : (Fin m → E) ⧸ intVec E m //
      (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b} →
      Kg ⧸ H.addSubgroupOf Kg := fun a => QuotientAddGroup.mk ⟨_, hmem a⟩
  have hφ : Function.Injective φ := by
    intro a a' h
    have h1 := QuotientAddGroup.eq.1 h
    have h2 : -(Quotient.out a.1 - Quotient.out b) + (Quotient.out a'.1 - Quotient.out b) ∈ H :=
      AddSubgroup.mem_addSubgroupOf.1 h1
    have h3 : Quotient.out a.1 - Quotient.out a'.1 ∈ intVec E m := by
      have h4 := neg_mem h2
      have h5 : -(-(Quotient.out a.1 - Quotient.out b) + (Quotient.out a'.1 - Quotient.out b)) =
          Quotient.out a.1 - Quotient.out a'.1 := by abel
      rw [h5] at h4
      exact h4
    apply Subtype.ext
    have h6 : (Submodule.Quotient.mk (Quotient.out a.1) : (Fin m → E) ⧸ intVec E m) =
        Submodule.Quotient.mk (Quotient.out a'.1) := (Submodule.Quotient.eq _).2 h3
    have e1 : (Submodule.Quotient.mk (Quotient.out a.1) : (Fin m → E) ⧸ intVec E m) = a.1 :=
      Quotient.out_eq' _
    have e2 : (Submodule.Quotient.mk (Quotient.out a'.1) : (Fin m → E) ⧸ intVec E m) = a'.1 :=
      Quotient.out_eq' _
    rw [← e1, ← e2, h6]
  refine ⟨Finite.of_injective φ hφ, ?_⟩
  rw [← hcard]
  exact Nat.card_le_card_of_injective φ hφ

theorem sum_tor : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (c : Matrix (Fin m) (Fin m) E) (r : ℝ), 1 < r → Summable (fun U : (Fin m → E) ⧸ intVec E m => (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r))) ∧ ∑' U : (Fin m → E) ⧸ intVec E m, (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) ≤ delta c * zetaR E r := by
  intro E _ _ m c r hr
  obtain ⟨hs, hle⟩ := GlobalTheory.T.torsion_norm_zeta_bound E m (lam c) (_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isLat_lam_of_matrix E m c) r hr
  have hg : ∀ x : (Fin m → E) ⧸ lam c,
      0 ≤ (Ideal.absNorm (Ideal.torsionOf (𝓞 E) ((Fin m → E) ⧸ lam c) x) : ℝ) ^
        (-((m : ℝ) + r)) := fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre.summable_comp_of_bounded_fibres ((Fin m → E) ⧸ intVec E m) ((Fin m → E) ⧸ lam c)
    (fun U => Submodule.Quotient.mk (Quotient.out U)) (delta c) (fibre_bound c)
    (fun x => (Ideal.absNorm (Ideal.torsionOf (𝓞 E) ((Fin m → E) ⧸ lam c) x) : ℝ) ^
      (-((m : ℝ) + r))) hg hs
  refine ⟨h1, h2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDualAtPlace
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Gunr.TraceDual

open NumberField IsDedekindDomain PositivityTheory.SiegelWeilFormula.Gunr HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct

section Abstract

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] {d : ℕ}

theorem repr_mul_mem (O : Subring K) (b : Module.Basis (Fin d) K A)
    (hc : ∀ i j k, b.repr (b i * b j) k ∈ O) {x y : A}
    (hx : ∀ k, b.repr x k ∈ O) (hy : ∀ k, b.repr y k ∈ O) (k : Fin d) :
    b.repr (x * y) k ∈ O := by
  have hxy : x * y = ∑ i, ∑ j, (b.repr x i * b.repr y j) • (b i * b j) := by
    conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm]
  have h : b.repr (x * y) k = ∑ i, ∑ j, b.repr x i * b.repr y j * b.repr (b i * b j) k := by
    rw [hxy]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Finsupp.finsetSum_apply]
  rw [h]
  exact O.sum_mem fun i _ => O.sum_mem fun j _ => O.mul_mem (O.mul_mem (hx i) (hy j)) (hc i j k)

theorem repr_basis_mem (O : Subring K) (b : Module.Basis (Fin d) K A) (j k : Fin d) :
    b.repr (b j) k ∈ O := by
  rw [b.repr_self, Finsupp.single_apply]
  split_ifs
  · exact O.one_mem
  · exact O.zero_mem

theorem trace_mem (O : Subring K) (b : Module.Basis (Fin d) K A)
    (hc : ∀ i j k, b.repr (b i * b j) k ∈ O) {x : A} (hx : ∀ k, b.repr x k ∈ O) :
    Algebra.trace K A x ∈ O := by
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine O.sum_mem fun i _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  exact repr_mul_mem O b hc hx (repr_basis_mem O b i) i

theorem adjugate_mem (O : Subring K) (M : Matrix (Fin d) (Fin d) K) (hM : ∀ i j, M i j ∈ O) (i j : Fin d) :
    M.adjugate i j ∈ O := by
  let N : Matrix (Fin d) (Fin d) O := Matrix.of fun i j => ⟨M i j, hM i j⟩
  have hN : O.subtype.mapMatrix N = M := by
    ext i j
    rfl
  rw [← hN, ← RingHom.map_adjugate]
  exact (N.adjugate i j).2

theorem dual_iff (O : Subring K) (b : Module.Basis (Fin d) K A)
    (hc : ∀ i j k, b.repr (b i * b j) k ∈ O) (u : K) (huO : u ∈ O)
    (hu : u * (Algebra.traceMatrix K b).det = 1) (a : A) :
    (∀ y : A, (∀ k, b.repr y k ∈ O) → Algebra.trace K A (a * y) ∈ O) ↔ ∀ k, b.repr a k ∈ O := by
  constructor
  · intro h k
    set M := Algebra.traceMatrix K b with hMdef
    have hMij : ∀ i j, M i j = Algebra.trace K A (b i * b j) := fun i j => by
      simp [hMdef, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    have hMO : ∀ i j, M i j ∈ O := fun i j => by
      rw [hMij]
      exact trace_mem O b hc (hc i j)
    let c : Fin d → K := fun i => b.repr a i
    let t : Fin d → K := fun j => Algebra.trace K A (a * b j)
    have ht : Matrix.vecMul c M = t := by
      funext j
      have ha : a * b j = ∑ i, c i • (b i * b j) := by
        conv_lhs => rw [← b.sum_repr a, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc]
      simp only [t, Matrix.vecMul, dotProduct, hMij]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [ha, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul]
    have hc' : M.det • c = Matrix.vecMul t M.adjugate := by
      rw [← ht, Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]
    have hk : b.repr a k = u * ∑ j, t j * M.adjugate j k := by
      have h1 := congrFun hc' k
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct] at h1
      rw [← h1, ← mul_assoc, hu, one_mul]
    rw [hk]
    refine O.mul_mem huO (O.sum_mem fun j _ => O.mul_mem ?_ (adjugate_mem O M hMO j k))
    exact h _ (repr_basis_mem O b j)
  · intro ha y hy
    exact trace_mem O b hc (repr_mul_mem O b hc ha hy)

end Abstract

section Base

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {K : Type*} [Field K] [Algebra F K] {d : ℕ}

theorem trace_one_tmul [FiniteDimensional F E] (e : E) :
    Algebra.trace K (K ⊗[F] E) ((1 : K) ⊗ₜ[F] e) = algebraMap F K (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem traceMatrix_base (bs : Module.Basis (Fin d) F E) :
    Algebra.traceMatrix K (Algebra.TensorProduct.basis K bs) =
      (Algebra.traceMatrix F bs).map (algebraMap F K) := by
  haveI : FiniteDimensional F E := Module.Basis.finiteDimensional_of_finite bs
  ext i j
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.map_apply,
    Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_one_tmul]

theorem det_traceMatrix_base (bs : Module.Basis (Fin d) F E) :
    (Algebra.traceMatrix K (Algebra.TensorProduct.basis K bs)).det =
      algebraMap F K (Algebra.discr F (⇑bs)) := by
  rw [traceMatrix_base, Algebra.discr_def, RingHom.map_det]
  rfl

theorem repr_base (bs : Module.Basis (Fin d) F E) (i j k : Fin d) :
    (Algebra.TensorProduct.basis K bs).repr
        (Algebra.TensorProduct.basis K bs i * Algebra.TensorProduct.basis K bs j) k =
      algebraMap F K (bs.repr (bs i * bs j) k) := by
  simp [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.basis_repr_tmul]

end Base

theorem traceDualAt : TraceDualAt := by
  intro F E _ _ _ _ _ σ _ d bs v hv a
  let O : Subring (Fv F v) := (v.adicCompletionIntegers F).toSubring
  have hc : ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) bs).repr
      (Algebra.TensorProduct.basis (Fv F v) bs i * Algebra.TensorProduct.basis (Fv F v) bs j) k ∈ O := by
    intro i j k
    rw [repr_base]
    refine hv _ ?_
    simp only [basisSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inl (Or.inl ⟨(i, j, k), rfl⟩))
  have hD : Algebra.discr F (⇑bs) ≠ 0 := by
    exact Algebra.discr_not_zero_of_basis F bs
  have hu : algebraMap F (Fv F v) (Algebra.discr F (⇑bs))⁻¹ ∈ O := by
    refine hv _ ?_
    simp [basisSet]
  have h1 : algebraMap F (Fv F v) (Algebra.discr F (⇑bs))⁻¹ *
      (Algebra.traceMatrix (Fv F v) (Algebra.TensorProduct.basis (Fv F v) bs)).det = 1 := by
    rw [det_traceMatrix_base, ← map_mul, inv_mul_cancel₀ hD, map_one]
  have key := dual_iff O (Algebra.TensorProduct.basis (Fv F v) bs) hc _ hu h1 a
  exact key

end GlobalTheory.CompanionTheory.Gunr.TraceDual

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumExhaustionUnramified
section
namespace GlobalTheory.CompanionTheory.Exhaustion

open Filter _root_.Topology

variable {α E : Type*} [NormedAddCommGroup E]

theorem exists_subset_of_exhaustion {C : ℕ → Finset α} (hC : Monotone C) (hex : ∀ a, ∃ k, a ∈ C k)
    (s : Finset α) : ∃ k, s ⊆ C k :=
  ((tendsto_atTop_finset_of_monotone hC hex).eventually (eventually_ge_atTop s)).exists

theorem summable_norm_of_exhaustion {f : α → E} {C : ℕ → Finset α} (hC : Monotone C)
    (hex : ∀ a, ∃ k, a ∈ C k) {K : ℝ} (hK : ∀ k, ∑ a ∈ C k, ‖f a‖ ≤ K) :
    Summable fun a => ‖f a‖ := by
  refine summable_of_sum_le (c := K) (fun a => norm_nonneg _) fun s => ?_
  obtain ⟨k, hk⟩ := exists_subset_of_exhaustion hC hex s
  exact (Finset.sum_le_sum_of_subset_of_nonneg hk fun _ _ _ => norm_nonneg _).trans (hK k)

theorem tsum_exhaust [CompleteSpace E] {f : α → E} {C : ℕ → Finset α} (hC : Monotone C)
    (hex : ∀ a, ∃ k, a ∈ C k) {K : ℝ} (hK : ∀ k, ∑ a ∈ C k, ‖f a‖ ≤ K) :
    Summable f ∧ Tendsto (fun k => ∑ a ∈ C k, f a) atTop (𝓝 (∑' a, f a)) := by
  have hs : Summable f := (summable_norm_of_exhaustion hC hex hK).of_norm
  exact ⟨hs, hs.hasSum.comp (tendsto_atTop_finset_of_monotone hC hex)⟩

theorem tsum_exhaust_prop : PositivityTheory.SiegelWeilFormula.Gunr.TsumExhaust := by
  intro α f C hC hex ⟨K, hK⟩
  exact ⟨summable_norm_of_exhaustion hC hex hK, (tsum_exhaust hC hex hK).2⟩

end GlobalTheory.CompanionTheory.Exhaustion
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerExistence
section
noncomputable section

namespace GlobalTheory.CompanionTheory.LocalUnif

open NumberField IsDedekindDomain HeckeCharacterZeroLocus.SiegelWeilU

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem isUnit_iff_valued_eq_one (x : v.adicCompletionIntegers F) :
    IsUnit x ↔ Valued.v (x : v.adicCompletion F) = 1 := by
  have hv : (Valued.v : Valuation (v.adicCompletion F) _).Integers (v.adicCompletionIntegers F) :=
    ⟨Subtype.coe_injective, fun y => y.2, fun r hr => ⟨⟨r, hr⟩, rfl⟩⟩
  exact hv.isUnit_iff_valuation_eq_one

theorem norm_lt_one_iff_not_isUnit (x : v.adicCompletionIntegers F) :
    ‖(x : v.adicCompletion F)‖ < 1 ↔ ¬ IsUnit x := by
  rw [isUnit_iff_valued_eq_one, Valued.toNormedField.norm_lt_one_iff]
  have h := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2
  exact ⟨ne_of_lt, fun h' => lt_of_le_of_ne h h'⟩

theorem natCard_quotient_span_irreducible {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) = Ideal.absNorm v.asIdeal := by
  rw [← hϖ.maximalIdeal_eq]
  exact GroundTheory.Global.natCard_residueField_adicCompletionIntegers v

theorem unifEx : PositivityTheory.SiegelWeilFormula.Gunr.UnifEx := by
  unfold PositivityTheory.SiegelWeilFormula.Gunr.UnifEx
  intro F _ _ v
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  refine ⟨ϖ, ?_, ?_, ?_, natCard_quotient_span_irreducible v hϖ⟩
  · intro h
    exact hϖ.ne_zero (Subtype.ext h)
  · exact (norm_lt_one_iff_not_isUnit v ϖ).2 hϖ.not_isUnit
  · intro x hx
    have hm : x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) :=
      (IsLocalRing.mem_maximalIdeal x).2 (mem_nonunits_iff.2 ((norm_lt_one_iff_not_isUnit v x).1 hx))
    rw [hϖ.maximalIdeal_eq] at hm
    exact Ideal.mem_span_singleton.1 hm

end GlobalTheory.CompanionTheory.LocalUnif

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalHaarFromProductStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_haar_from_product : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (radN d)] (κ : Measure (skewA D t)) (β : Measure (Mx D t W.rank)), κ.IsAddHaarMeasure → β.IsAddHaarMeasure → ∃ Ψ : (skewA D t × Mx D t W.rank) ≃ₜ radN d, (∀ p, (((Ψ p : GlobalTheory.RegSW.stab d) : GA D B)) = d.nC p.1 * d.nB p.2) ∧ ((κ.prod β).map Ψ).IsHaarMeasure ∧ ((κ.prod β).map Ψ).IsMulRightInvariant := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.RadHaar.exists_coord | exact GlobalTheory.CompanionTheory.QKAvg.RadHaar.exists_coord | (intros; apply GlobalTheory.CompanionTheory.QKAvg.RadHaar.exists_coord <;> assumption)
end

