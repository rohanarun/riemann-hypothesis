module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StepBoxIffStepSuppDeg
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MoveCompare

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions
open GlobalTheory.IndefiniteRowSideFullHecke

section Clauses

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem mulLat_le_divLat {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (cA cB : ℕ) (M : Submodule (𝓞 E) H) :
    mulLat cB M ≤ divLat cA M := by
  rintro _ ⟨z, hz, rfl⟩
  exact M.smul_mem _ (M.smul_mem _ hz)


open Classical in
theorem inRange_indicator (K : Type) [Field K] {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) :
    MovementLaw.InRangeOf S cA cB N N' (fun x => if x ∈ divLat cA (homAt S N N') then (1 : K) else 0) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · by_contra h
    exact hx (if_neg h)
  · have hy' := mulLat_le_divLat cA cB _ hy
    have : x + y ∈ divLat cA (homAt S N N') ↔ x ∈ divLat cA (homAt S N N') := Submodule.add_mem_iff_left _ hy'
    simp only [this]

end Clauses


open Classical in
theorem degAt_eq {X : Fields} {a b : ℕ} (m : DVar X.Tau a b →₀ ℕ) (τ : X.Tau) :
    IndexExponentDegree.degAt m τ = ∑ k ∈ m.support.filter (fun k => k.1 = τ), m k := by
  unfold IndexExponentDegree.degAt
  rw [Finset.sum_filter, Finset.sum_subset (Finset.subset_univ m.support) (by
    intro k _ hk
    simp [Finsupp.notMem_support_iff.1 hk]), Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · rw [Fintype.sum_prod_type]
    simp
  · intro σ _ hσ
    simp [hσ]
  · simp

theorem nuW_detShift_nonneg {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (u : Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    0 ≤ (W.nuW u (i + 1) τ).detShift := by
  have hpos : 0 < R.N i := R.N_pos i
  have hlt : R.N i < R.N R.m := by
    unfold Ranks.N
    exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hi (Nat.succ_pos R.t)) _
  have hb : Examples₂.blkN R (R.N i) = i := by
    unfold Examples₂.blkN Ranks.N
    rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel _ (Nat.succ_pos _)]
  have h1 : Examples₂.wtN (W.hc u τ) (R.N i) = -wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1) := by
    unfold Examples₂.wtN
    rw [dite_eq_right (by unfold Ranks.N; omega), dif_pos (by rw [hb]; exact hi)]
    simp only [hb]
  have h2 := Examples₂.wtN_anti (W.hc u τ) (Nat.sub_le (R.N i) 1) hlt
  have h3 := Examples₂.lamOf_eq (W.hc u τ) i hi.le ⟨R.N i - 1, by omega⟩
  rw [Examples₂.wtQ_eq_wtN] at h3
  have h4 : (W.nuW u (i + 1) τ).detShift =
      (Examples₂.lamOf (W.hc u τ) i).w ⟨R.N i - 1, by omega⟩ + ⌊wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1)⌋ := by
    unfold DomWeight.detShift
    rw [dif_pos (show 0 < R.N (i + 1 - 1) from hpos)]
    simp only [Wts.nuW, shiftW, Wts.lamN, RowPar.eAt, RowPar.of, Nat.add_sub_cancel, hi, dif_pos]
    rfl
  rw [h4]
  have h5 : -(Examples₂.lamOf (W.hc u τ) i).w ⟨R.N i - 1, by omega⟩ ≤ ⌊wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1)⌋ := by
    rw [Int.le_floor]
    push_cast
    rw [h3]
    simp only at h2 ⊢
    linarith
  omega

theorem degNu_eq {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (u : Pr.Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    IndexExponentDegree.degNu (W.lamTrue u i) (nuLast W u i) τ = ∑ k, (W.nuW u (i + 1) τ).w k := by
  have hpos : 0 < R.N i := R.N_pos i
  unfold IndexExponentDegree.degNu nuLast
  rw [Int.toNat_of_nonneg (nuW_detShift_nonneg W u hi τ)]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold DomWeight.detShift
  rw [dif_pos (show 0 < R.N (i + 1 - 1) from hpos), dif_pos hpos]
  show ((W.lamN u i τ).w s + _) - ((W.lamN u i τ).w ⟨R.N i - 1, _⟩ + _) + ((W.lamN u i τ).w ⟨R.N i - 1, _⟩ + _) =
    (W.lamN u i τ).w s + _
  ring

section Jets

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ)

def JetsAll (deg : X.Tau → ℤ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : Prop :=
  ∀ Ξ : HomE X.E a b → X.K, MovementLaw.InRangeOf S cA cB N N' Ξ → MovementLaw.JetsIn A S cB deg N N' Ξ

theorem jetsIn_iff (lam : X.Tau → DomWeight a) (n : X.Tau → ℕ) (deg : X.Tau → ℤ) (h : ∀ τ, IndexExponentDegree.degNu lam n τ = deg τ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) :
    IndexExponentDegree.JetsIn A S cA cB lam n N N' ↔ JetsAll A S cA cB deg N N' := by
  constructor
  · intro hJ Ξ hΞ x hx m hm
    refine hJ x (hΞ.1 x hx) m fun τ => ?_
    rw [degAt_eq, h τ, ← hm τ]
  · intro hJ x hx m hm
    refine hJ _ (inRange_indicator X.K S cA cB N N') x (by simp [hx]) m fun τ => ?_
    rw [← h τ, ← hm τ, degAt_eq]


open Classical in
def JetsDeg (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M : ℕ) (deg : X.Tau → ℤ) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), InRange S M c N N' x →
    ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, ((∑ k ∈ m.support.filter (fun k => k.1 = τ), m k : ℕ) : ℤ) = deg τ) →
      ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' c x) m

theorem jetsAll_of_deg (deg : X.Tau → ℤ) (h : JetsDeg A a b S (cA * cB) deg) (hB : 0 < cB)
    {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : IsSdLat N) (hN' : IsSdLat N') :
    JetsAll A S cA cB deg N N' := by
  intro Ξ hΞ x hx m hm
  refine h N N' cB x ⟨hN, hN', hB, Dvd.intro_left _ rfl, ?_⟩ m hm
  have h1 : ((cA : ℕ) : 𝓞 X.E) • x ∈ homAt S N N' := hΞ.1 x hx
  show ((cA * cB : ℕ) : 𝓞 X.E) • x ∈ homAt S N N'
  rw [Nat.cast_mul, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ h1

end Jets

theorem cBof_pos {X : Fields} {Pr : Primes X} (hP : Pr.Ok) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) : 0 < cBof sel mu cst u := by
  unfold cBof
  refine Nat.mul_pos (hP.T_prime u).pos (pow_pos (Finset.prod_pos fun P _ => ?_) _)
  exact Nat.pos_of_ne_zero (by unfold Formalism.L2.Col.qOf; rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.1.ne_bot)

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (A : Amb X) {i : ℕ} {b : ℕ} (lam' : X.Tau → DomWeight b)

end Step

end GlobalTheory.MoveCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SubDSharpInDeg
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

noncomputable section

namespace GlobalTheory.JetDeg

theorem algHom_hom {K σ ρ M N : Type} [CommRing K] [AddCommMonoid M] [AddCommMonoid N] (w : σ → M) (w' : ρ → N)
    (g : M →+ N) (φ : MvPolynomial σ K →ₐ[K] MvPolynomial ρ K)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (g (w v))) {f : MvPolynomial σ K} {d : M}
    (hf : IsWeightedHomogeneous w f d) : IsWeightedHomogeneous w' (φ f) (g d) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  have hd : Finsupp.weight w m = d := hf (mem_support_iff.mp hm)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [monomial_eq, map_mul, algHom_C, algebraMap_eq, Finsupp.prod, map_prod, ← hd, Finsupp.weight_apply,
    Finsupp.sum, map_sum]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun v _ => ?_
  rw [map_pow, map_nsmul]
  exact (hφ v).pow _

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι] {a b : ℕ}

def posW (a : ℕ) (τ : ι) : ι × Fin a × Fin a → ℕ := fun v => if v.1 = τ then 1 else 0

def derW (a b : ℕ) (τ : ι) : (ι × Fin b × Fin b) ⊕ DVar ι a b → ℕ :=
  Sum.elim (fun _ => 0) fun k => if k.1 = τ then 1 else 0

theorem blockEmb_hom (τ τ' : ι) (ν : Fin a → ℕ) {f : MvPolynomial (Fin a × Fin a) K}
    (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW a a) f ν) :
    IsWeightedHomogeneous (posW a τ) (Formalism.GradedWeylDivisibility.blockEmb K τ' f) (if τ' = τ then ∑ i, ν i else 0) := by
  let g : (Fin a → ℕ) →+ ℕ :=
    { toFun := fun x => if τ' = τ then ∑ i, x i else 0
      map_zero' := by simp
      map_add' := by
        intro x y
        split_ifs <;> simp [Finset.sum_add_distrib] }
  refine algHom_hom (Formalism.GradedWeylDivisibility.colW a a) (posW a τ) g _ (fun v => ?_) hf
  have h := isWeightedHomogeneous_X K (posW a τ) (τ', v)
  have e : g (Formalism.GradedWeylDivisibility.colW a a v) = posW a τ (τ', v) := by
    simp [g, Formalism.GradedWeylDivisibility.colW, posW, Pi.single_apply]
  rw [e]
  simpa [Formalism.GradedWeylDivisibility.blockEmb] using h

theorem frDet_hom (τ τ' : ι) :
    IsWeightedHomogeneous (posW a τ) (frDet K a τ') (if τ' = τ then a else 0) := by
  rw [frDet, Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have h : IsWeightedHomogeneous (posW a τ) (∏ i : Fin a, (X (τ', σ i, i) : Pol K ι a))
      (∑ _i : Fin a, if τ' = τ then 1 else 0) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => isWeightedHomogeneous_X K (posW a τ) (τ', σ i, i)
  have e : (∑ _i : Fin a, if τ' = τ then 1 else 0) = if τ' = τ then a else 0 := by
    split_ifs <;> simp
  rw [e] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · simpa [h1] using h
  · simpa [h1] using h.neg

theorem subD_hom (τ : ι) {P : Pol K ι a} {d : ℕ} (hP : IsWeightedHomogeneous (posW a τ) P d) :
    IsWeightedHomogeneous (derW a b τ) (subD K ι a b P) d := by
  refine algHom_hom (posW a τ) (derW a b τ) (AddMonoidHom.id ℕ) _ (fun v => ?_) hP
  rw [subD, aeval_X]
  split_ifs with h
  · refine IsWeightedHomogeneous.sum _ _ _ fun β _ => ?_
    have := (isWeightedHomogeneous_X K (derW a b τ) (Sum.inl (v.1, β, (⟨v.2.2.1, h⟩ : Fin b)))).mul
      (isWeightedHomogeneous_X K (derW a b τ) (Sum.inr (v.1, β, v.2.1)))
    simpa [derW, posW] using this
  · exact isWeightedHomogeneous_zero _ _ _

variable [Fintype ι]

theorem VV_hom (lam : ι → DomWeight a) (τ : ι) {P : Pol K ι a} (hP : P ∈ Formalism.L2.DIV.VV K lam) :
    IsWeightedHomogeneous (posW a τ) P (∑ i, (lam τ).natW i) := by
  have : Formalism.L2.DIV.VV K lam ≤ weightedHomogeneousSubmodule K (posW a τ) (∑ i, (lam τ).natW i) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨F, hF, rfl⟩
    have h := IsWeightedHomogeneous.prod Finset.univ (fun τ' => Formalism.GradedWeylDivisibility.blockEmb K τ' (F τ'))
      (fun τ' => if τ' = τ then ∑ i, (lam τ').natW i else 0) (w := posW a τ)
      fun τ' _ => blockEmb_hom τ τ' _ (hF τ').1
    simpa using h
  exact this hP

theorem sharp_hom (n : ι → ℕ) (τ : ι) {P : Pol K ι a} {d : ℕ} (hP : IsWeightedHomogeneous (posW a τ) P d) :
    IsWeightedHomogeneous (posW a τ) (sharp n P) (d + n τ * a) := by
  refine hP.mul ?_
  have h := IsWeightedHomogeneous.prod Finset.univ (fun τ' => frDet K a τ' ^ n τ')
    (fun τ' => n τ' • if τ' = τ then a else 0) (w := posW a τ)
    fun τ' _ => (frDet_hom τ τ').pow _
  simpa using h

theorem weight_derW (τ : ι) (μ : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) :
    Finsupp.weight (derW a b τ) μ = ∑ β : Fin b, ∑ α : Fin a, μ (Sum.inr (τ, β, α)) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type (α₁ := ι) (α₂ := Fin b × Fin a), Finset.sum_eq_single τ]
  · simp [derW, Fintype.sum_prod_type]
  · intro x _ hx
    simp [derW, hx]
  · simp

theorem natW_cast (lam : DomWeight a) (i : Fin a) : (lam.natW i : ℤ) = lam.w i - lam.detShift := by
  have hi := i.2
  have h : lam.detShift ≤ lam.w i := by
    rw [DomWeight.detShift, dite_eq_left (by omega)]
    exact lam.anti (by rw [Fin.le_def]; simp only; omega)
  rw [DomWeight.natW]
  omega

end GlobalTheory.JetDeg


open GlobalTheory.JetDeg in
theorem GlobalTheory.subD_sharp_inDeg : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b) (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ), WtCompat hab lam lam' s s' n → ∀ P ∈ Formalism.L2.DIV.VV K lam, ∀ μ ∈ (subD K ι a b (sharp n P)).support, InDeg lam s' (Finsupp.comapDomain Sum.inr μ Sum.inr_injective.injOn) := by
  classical
  intro K _ ι _ a b hab lam lam' s s' n hw P hP μ hμ τ
  have h := GlobalTheory.JetDeg.subD_hom (b := b) τ (GlobalTheory.JetDeg.sharp_hom n τ (GlobalTheory.JetDeg.VV_hom lam τ hP)) (mem_support_iff.mp hμ)
  rw [GlobalTheory.JetDeg.weight_derW] at h
  simp only [Finsupp.comapDomain_apply]
  rw [h]
  push_cast
  have e : ∀ i, (lam τ).w i + s' τ = ((lam τ).natW i : ℤ) + n τ := fun i => by
    rw [GlobalTheory.JetDeg.natW_cast, hw.2.2 τ]; ring
  simp [e, Finset.sum_add_distrib, mul_comm]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowCondQdPde
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_cond_qd_pde : SzRow (fun _ _ L => SizeCond L ∧ SizeQD L ∧ SizePde L) := by
  intro eps he he' C hC
  have hC8 : 1 ≤ C.P.Cpde := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨x1, h1⟩ := _root_.GlobalTheory.EX.rank_basic_bounds eps he he'
  obtain ⟨x2, h2⟩ := hostBounds eps C.P.Cpde he he' hC8
  obtain ⟨x3, h3⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 5) eps 60150 72 (1 / 2) 2
    (by positivity) (by linarith) (by norm_num)
  obtain ⟨x4, h4⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow 0 (eps / C.P.Cpde / 100) 2 0 (by positivity)
  obtain ⟨x6, h6⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (eps / 5) (eps / 5 + eps / 100) 1 2 (by linarith)
  obtain ⟨x7, h7⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (eps / 5) eps (2 * C.P.Cpde) 2 (by linarith)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ =>
    ⟨max (max (max x1 x2) (max x3 x4)) (max (max (Real.exp C.P.Cpde) x6) (max x7 (Real.exp 1))), ?_⟩⟩⟩
  intro D L hse hx hV
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hx1, hx2⟩, hx3, hx4⟩, ⟨hx5, hx6⟩, hx7, hx8⟩ := hx
  have hr := h1 L.sc D.R hse hx1 hV.ranks
  have ht : (D.R.t : ℝ) ≤ L.sc.x ^ (401 : ℝ) := hr.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨q1, q2, d1, d2, hN, r1, r2, -, p1, p2⟩ := h2 L.sc D.R D.host hse hx2 hV.ranks hV.host
  have k3 := h3 _ hx3
  have k4 := h4 _ hx4
  have k6 := h6 _ hx6
  have k7 := h7 _ hx7
  subst hse
  have hxpos : 0 < L.sc.x := (Real.exp_pos 1).trans_le hx8
  have hlog : 1 ≤ Real.log L.sc.x := (Real.le_log_iff_exp_le hxpos).mpr hx8
  have hlog2 : 1 ≤ Real.log L.sc.x ^ 2 := one_le_pow₀ hlog
  have hmul : L.sc.x ^ (L.sc.eps / 5) ≤ L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2 :=
    le_mul_of_one_le_right (Real.rpow_nonneg hxpos.le _) hlog2
  simp only [pow_zero, mul_one, one_mul] at k6
  have hx1' : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have hez : L.sc.eps / C.P.Cpde ≤ L.sc.ez := hostBounds_ez hV.host
  have hez0 : 0 ≤ L.sc.ez := le_trans (by positivity) hez
  have k40 : 2 ≤ L.sc.x ^ (L.sc.ez / 100) := by
    simp only [pow_zero, mul_one, Real.rpow_zero] at k4
    exact k4.trans (Real.rpow_le_rpow_of_exponent_le hx1' (by linarith))
  have k5 : 2 * L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100) ≤ L.sc.x ^ (L.sc.ez / 5) := by
    have e : L.sc.x ^ (L.sc.ez / 5) = L.sc.x ^ (L.sc.ez / 100) * L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100) := by
      rw [← Real.rpow_add hxpos]; congr 1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right k40 (Real.rpow_nonneg hxpos.le _)
  have k41 : L.sc.x ^ (L.sc.ez / 6) ≤ L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100) :=
    Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hmz : L.sc.x ^ (L.sc.ez / 5) ≤ L.sc.x ^ (L.sc.ez / 5) * (Real.log L.sc.x / L.sc.J) ^ 2 :=
    le_mul_of_one_le_right (Real.rpow_nonneg hxpos.le _)
      (one_le_pow₀ (hostBounds_one_le_log_div hV.host hx5))
  refine ⟨?_, ?_, ?_⟩
  · unfold SizeCond szCond Scale.b Scale.L
    have hA : ((D.host.QS : ℝ) * D.host.q * D.host.d) ≤
        Real.exp (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) :=
      (Real.le_exp_log _).trans (Real.exp_le_exp.mpr hN)
    have hB : (D.R.t : ℝ) ≤ Real.exp (Real.log L.sc.x * 401) := by
      rwa [Real.rpow_def_of_pos hxpos] at ht
    rw [← Real.exp_half]
    calc ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 36 * (D.R.t : ℝ) ^ 150
        ≤ Real.exp (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) ^ 36 *
            Real.exp (Real.log L.sc.x * 401) ^ 150 := by gcongr
      _ = Real.exp (((36 : ℕ) : ℝ) * (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) +
            ((150 : ℕ) : ℝ) * (Real.log L.sc.x * 401)) := by
          rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]
      _ ≤ Real.exp (L.sc.x ^ L.sc.eps / 2) := by
          apply Real.exp_le_exp.mpr
          push_cast
          linarith
  · unfold SizeQD szTh
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, hV.dlog, r1, r2⟩
  · unfold SizePde Scale.L
    exact ⟨by linarith, by linarith⟩

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowEtaBounds
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_eta_bounds : SzRow (fun C D L => (L.etaSz ≤ L.sc.b / ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3)) ∧ (Real.log L.etaSz ≤ L.sc.x ^ (L.sc.eps / 4)) ∧ ((D.R.t : ℝ) ≤ L.etaSz) ∧ ((D.R.t : ℝ) * L.etaSz ≤ L.sc.w'' D.R.n / L.sc.x) ∧ ((D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n)) := by
  intro eps he0 he1 C _
  refine ⟨0, fun cD _ => ⟨401, fun ch hch => ?_⟩⟩
  obtain ⟨x1, h1⟩ := _root_.GlobalTheory.scale_poly_comparison eps (ch + (1224 : ℕ)) (1 / 2) he0 (by norm_num)
  obtain ⟨x2, h2⟩ := _root_.GlobalTheory.EX.rank_basic_bounds eps he0 he1
  obtain ⟨x3, h3⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 4) (ch + (3 : ℕ)) 0 1 0 le_rfl
    (by positivity) one_pos
  refine ⟨max (max x1 x2) (max x3 2), fun D L hE hx V => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  obtain ⟨-, -, s3, -, -, s6, -⟩ := h1 L.sc hE hx1
  obtain ⟨rf, rm, rr, rk, -, -, -, -, -, -, -, -, -, rt, -⟩ := h2 L.sc D.R hE hx2 V.ranks
  have h3' := h3 L.sc.x hx3
  have heta := V.eta_eq
  have hpos := L.etaSz_pos
  unfold h0v at heta
  push_cast at heta
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hX1 : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hn1 : 1 ≤ D.R.n := D.R.ord_pos
  have hfn : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
  have hn1' : (1 : ℝ) ≤ D.R.n := by exact_mod_cast hn1
  obtain ⟨s7, -⟩ := s6 D.R.n hn1 (by linarith)
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have ht1 : (1 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t
    exact_mod_cast (by omega : 1 ≤ D.R.t)
  have rk' : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := le_trans (by exact_mod_cast rk) rr
  rw [hE]
  generalize L.sc.x = x at *
  generalize L.sc.b = b at *
  generalize L.sc.X' = X at *
  generalize L.sc.w'' D.R.n = w at *
  generalize L.etaSz = η at *
  generalize (D.R.t : ℝ) = t at *
  generalize (D.R.m : ℝ) = m at *
  generalize (D.R.f : ℝ) = f at *
  generalize (D.R.k : ℝ) = k at *
  have hx0 : 0 < x := by linarith
  have hx1' : 1 ≤ x := by linarith
  have hty : t ≤ x ^ ch := rt.trans (Real.rpow_le_rpow_of_exponent_le hx1' hch)
  have e3 : x ^ (ch + (3 : ℕ)) = x ^ ch * x ^ 3 := by rw [Real.rpow_add hx0, Real.rpow_natCast]
  have eB : x ^ (ch + (1224 : ℕ)) = x ^ ch * x ^ 1224 := by rw [Real.rpow_add hx0, Real.rpow_natCast]
  have rf' : f ≤ x ^ 3 := by rw [← Real.rpow_natCast]; exact_mod_cast rf
  have rk'' : k ≤ x ^ 5 := by rw [← Real.rpow_natCast]; exact_mod_cast rk'
  have rt' : t ≤ x ^ 401 := by rw [← Real.rpow_natCast]; exact_mod_cast rt
  have hy1 : 1 ≤ x ^ ch := ht1.trans hty
  have hc1 : x ^ ch ≤ (⌈x ^ ch⌉₊ : ℝ) := Nat.le_ceil _
  have hc2 : (⌈x ^ ch⌉₊ : ℝ) ≤ x ^ ch + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hup : η ≤ x ^ ch * x ^ 3 := by
    rw [heta]
    have a1 : 2 * (⌈x ^ ch⌉₊ : ℝ) ≤ x ^ ch * x ^ 2 := by
      have : 4 ≤ x ^ 2 := by nlinarith
      nlinarith
    calc m * (2 * (⌈x ^ ch⌉₊ : ℝ)) ≤ x * (x ^ ch * x ^ 2) := by gcongr
      _ = _ := by ring
  have hlo : t ≤ η := by rw [heta]; nlinarith
  have hlog : Real.log η ≤ x ^ (eps / 4) := by
    have a1 : Real.log η ≤ (ch + (3 : ℕ)) * Real.log x := by
      rw [← Real.log_rpow hx0, e3]; exact Real.log_le_log hpos hup
    simp only [zero_mul, add_zero, one_mul] at h3'
    exact a1.trans h3'
  rw [eB] at s3 s7
  generalize x ^ ch = y at *
  have hB0 : 0 ≤ y * x ^ 1224 := by positivity
  have hBb : y * x ^ 1224 ≤ b := by
    have a1 : b ^ (1 / 2 : ℝ) ≤ b ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
    rw [Real.rpow_one] at a1
    exact (le_mul_of_one_le_right hB0 hX1).trans (s3.trans a1)
  have hBw : y * x ^ 1224 ≤ w :=
    (le_mul_of_one_le_left hB0 (Real.one_le_rpow hb1 (by norm_num))).trans s7
  have hf0 : 0 < f := by linarith
  refine ⟨?_, hlog, hlo, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    calc η * (t ^ 3 * f * k ^ 3) ≤ (y * x ^ 3) * ((x ^ 401) ^ 3 * x ^ 3 * (x ^ 5) ^ 3) := by gcongr
      _ = y * x ^ 1224 := by ring
      _ ≤ b := hBb
  · rw [le_div_iff₀ hx0]
    calc t * η * x ≤ x ^ 401 * (y * x ^ 3) * x := by gcongr
      _ = y * x ^ 405 := by ring
      _ ≤ y * x ^ 1224 := by gcongr <;> first | assumption | norm_num
      _ ≤ w := hBw
  · have a1 : t + 1 ≤ x * x ^ 401 :=
      calc t + 1 ≤ t + t := by gcongr
        _ = 2 * t := by ring
        _ ≤ x * x ^ 401 := by gcongr
    calc m * (t + 1) * η ≤ x * (x * x ^ 401) * (y * x ^ 3) := by gcongr
      _ = y * x ^ 406 := by ring
      _ ≤ y * x ^ 1224 := by gcongr <;> first | assumption | norm_num
      _ ≤ w := hBw

end GlobalTheory.EX
end

