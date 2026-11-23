module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0081
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormConsMul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0302
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0309
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0284
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0314
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0293
public import GroundTheory.AutomorphicForms.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0312
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0251
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0256
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0254

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoshTransformCasimirReal
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

private theorem sum_amat_first_index_eq {n : ℕ} (l : Fin n → ℂ) (j : Fin n) :
    ∑ a, Formalism.REAL.Amat l a j = l j - ((j : ℕ) : ℂ) := by
  have h : ∀ a, Formalism.REAL.Amat l a j = (if a = j then l j else 0) + (if a < j then -1 else 0) := by
    intro a
    simp only [Formalism.REAL.Amat, Matrix.of_apply]
    by_cases h1 : a = j
    · subst h1
      simp
    · simp [h1]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_gt_eq_Iio,
    Fin.card_Iio]
  simp [sub_eq_add_neg]

private theorem sum_amat_second_index_eq {n : ℕ} (l : Fin n → ℂ) (j : Fin n) :
    ∑ b, Formalism.REAL.Amat l j b = l j - ((n - 1 - j : ℕ) : ℂ) := by
  have h : ∀ b, Formalism.REAL.Amat l j b = (if j = b then l j else 0) + (if j < b then -1 else 0) := by
    intro b
    simp only [Formalism.REAL.Amat, Matrix.of_apply]
    by_cases h1 : j = b
    · subst h1
      simp
    · simp [h1]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_lt_eq_Ioi,
    Fin.card_Ioi]
  simp [sub_eq_add_neg]

private theorem gelfVal_two_eq_sum_sq_sub_sq {n : ℕ} (c : Fin n → ℂ) :
    GlobalTheory.Dec.gelfVal c 2 = ∑ j, (c j ^ 2 - (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) ^ 2) := by
  have key : ∀ j : Fin n,
      (∑ a, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) a j) *
        (∑ b, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) j b) =
        c j ^ 2 - (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) ^ 2 := by
    intro j
    have hj : (j : ℕ) + 1 ≤ n := j.isLt
    rw [sum_amat_first_index_eq, sum_amat_second_index_eq, Nat.sub_sub, Nat.cast_sub (by omega), Nat.cast_add,
      Nat.cast_one]
    ring
  calc GlobalTheory.Dec.gelfVal c 2
      = ∑ j, (∑ a, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) a j) *
          (∑ b, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) j b) := by
        simp only [GlobalTheory.Dec.gelfVal, sq, Matrix.mul_apply, Finset.sum_mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun j _ => key j

theorem conj_cas_of_isHerm {n : ℕ} {χ : Inf n} (h : IsHerm χ) : conj (cas χ) = cas χ := by
  obtain ⟨σ, hσ⟩ := h
  have hT : ∑ a, conj (χ true a) ^ 2 = ∑ a, χ false a ^ 2 := by
    rw [← Equiv.sum_comp σ (fun a => χ false a ^ 2)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hσ a, neg_sq]
  have hF : ∑ a, conj (χ false a) ^ 2 = ∑ a, χ true a ^ 2 := by
    have h2 := congrArg conj hT
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, map_pow] using h2.symm
  have hK : ∀ j : Fin n, conj (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) = ((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ) := by
    intro j
    simp only [map_sub, map_div₀, map_natCast, map_one, map_ofNat]
  have hconj : ∀ x : Fin n → ℂ, conj (GlobalTheory.Dec.gelfVal x 2) =
      ∑ j, (conj (x j) ^ 2 - (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) ^ 2) := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [gelfVal_two_eq_sum_sq_sub_sq, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sub, map_pow, map_pow, hK]
  simp only [cas]
  rw [map_mul, map_add (f := _), hconj, hconj, map_ofNat, gelfVal_two_eq_sum_sq_sub_sq, gelfVal_two_eq_sum_sq_sub_sq]
  simp only [Finset.sum_sub_distrib]
  rw [hT, hF]
  ring

theorem conj_cosh_mul_sqrt {c : ℂ} (hc : conj c = c) (t : ℝ) :
    conj (Complex.cosh (t * c ^ (1 / 2 : ℂ))) = Complex.cosh (t * c ^ (1 / 2 : ℂ)) := by
  have hw2 : (c ^ (1 / 2 : ℂ)) ^ 2 = c := by
    have h := Complex.cpow_nat_inv_pow c (n := 2) two_ne_zero
    simpa [one_div] using h
  have hsq : conj (c ^ (1 / 2 : ℂ)) ^ 2 = (c ^ (1 / 2 : ℂ)) ^ 2 := by
    rw [← map_pow, hw2, hc]
  rw [← Complex.cosh_conj, map_mul, Complex.conj_ofReal]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · rw [h]
  · rw [h, mul_neg, Complex.cosh_neg]

theorem conj_coshT_cas : ∀ (n : ℕ) (χ : Inf n) (g : ℝ → ℝ) (T : ℝ), IsHerm χ → IsBump g T →
    conj (coshT g (cas χ)) = coshT g (cas χ) := by
  intro n χ g T hχ _
  have hc := conj_cas_of_isHerm hχ
  simp only [coshT]
  rw [← integral_conj]
  congr 1
  funext t
  rw [map_mul, Complex.conj_ofReal, conj_cosh_mul_sqrt hc t]

end GlobalTheory.CompanionTheory.WaveMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupMemRelS
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

section Per
variable {K : Type} [Field K] {W Y : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Y}

theorem rs_topIso {V V' : Y.Opens} (h : V' ≤ V) (x : Γ(V, ⊤)) :
    rs h (V.topIso.hom.hom x) = V'.topIso.hom.hom ((Y.homOfLE h).appTop.hom x) := by
  rw [Scheme.homOfLE_appTop]
  simp only [rs, Scheme.Opens.topIso_hom, CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  rfl

def kerI (q : Y ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Y) (V : Y.Opens) : Ideal (Sec q V) := RingHom.ker (i.app V).hom

theorem one_P [CharZero K] [IsClosedImmersion i] (hAR : AffRel) (hQ : Cosieve (On q i)) {V : Y.Opens} {P : ObjectProperty (Thick (smFun Y q))}
    (hP : P = inU q V) {d d' : ℕ} (hc : Nonempty (Coord q V d)) (hc' : Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) d')) (b j : ℕ)
    (hj : j ≠ b) : Subsingleton ((RC (G q b) P hQ).H j) := by
  subst hP
  exact (hAR K W Y q i hQ V d d' hc hc' b).1 j hj

theorem inj_P [CharZero K] [IsClosedImmersion i] (hAR : AffRel) (hQ : Cosieve (On q i)) {V : Y.Opens} {P : ObjectProperty (Thick (smFun Y q))}
    (hP : P = inU q V) {d d' : ℕ} (hc : Nonempty (Coord q V d)) (hc' : Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) d')) (b : ℕ)
    (E : Om K (Sec q V) b →ₗ[K] HV q V b b) (hE : IsOm q V b E) :
    Function.Injective ((incl (G q b) P hQ).mapH b) := by
  subst hP
  exact ((hAR K W Y q i hQ V d d' hc hc' b).2 E hE (incl (G q b) (inU q V) hQ) fun _ _ => rfl).1

theorem range_P [CharZero K] [IsClosedImmersion i] (hAR : AffRel) (hQ : Cosieve (On q i)) {V : Y.Opens} {P : ObjectProperty (Thick (smFun Y q))}
    (hP : P = inU q V) {d d' : ℕ} (hc : Nonempty (Coord q V d)) (hc' : Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) d')) (b : ℕ)
    (E : Om K (Sec q V) b →ₗ[K] HV q V b b) (hE : IsOm q V b E) (ω : Om K (Sec q V) b) :
    castH (G q b) hP b (E ω) ∈ LinearMap.range ((incl (G q b) P hQ).mapH b) ↔
      ω ∈ relOm K (kerI q i V) b := by
  subst hP
  exact ((hAR K W Y q i hQ V d d' hc hc' b).2 E hE (incl (G q b) (inU q V) hQ) fun _ _ => rfl).2 ω

theorem pull_P {V V' : Y.Opens} {P P' : ObjectProperty (Thick (smFun Y q))} (hP : P = inU q V) (hP' : P' = inU q V') (k : P' ≤ P)
    (b : ℕ) (E : Om K (Sec q V) b →ₗ[K] HV q V b b) (E' : Om K (Sec q V') b →ₗ[K] HV q V' b b)
    (φ : Om K (Sec q V) b →ₗ[K] Om K (Sec q V') b)
    (h : ∀ (k' : inU q V' ≤ inU q V) ω, (resU (G q b) k').pull b (E ω) = E' (φ ω)) (ω : Om K (Sec q V) b) :
    (resU (G q b) k).pull b (castH (G q b) hP b (E ω)) = castH (G q b) hP' b (E' (φ ω)) := by
  subst hP hP'
  exact h k ω

theorem cup_P (hFL : FormLaws) (hFU : FormUniq) (hFC : FormCup) {V : Y.Opens} {P U₁ U₂ : ObjectProperty (Thick (smFun Y q))} (hP : P = inU q V)
    (k₁ : P ≤ U₁) (k₂ : P ≤ U₂) (β₁ : CH.Cn (U₁.ι ⋙ G q 1) 1) (β₂ : CH.Cn (U₂.ι ⋙ G q 1) 1) {a : ℕ}
    (E₂ : Om K (Sec q V) a →ₗ[K] HV q V a a) (E₃ : Om K (Sec q V) (a + 1) →ₗ[K] HV q V (a + 1) (a + 1))
    (h₂ : IsOm q V a E₂) (h₃ : IsOm q V (a + 1) E₃) (g₁ t : Sec q V)
    (hf : ∀ (k₁' : inU q V ≤ U₁) (k₂' : inU q V ≤ U₂), ∃ hz, IsForm q V (a := 1) g₁ ![t]
      ((CH.cx ((inU q V).ι ⋙ G q 1)).cls ((resU (G q 1) k₁').pullC 1 β₁ - (resU (G q 1) k₂').pullC 1 β₂) hz))
    (w : Om K (Sec q V) a →ₗ[Sec q V] Om K (Sec q V) (a + 1))
    (hw : ∀ g₀ (g : Fin a → Sec q V), w (form K g₀ g) = form K g₀ (Fin.cons t g))
    (y : CH.Cn (P.ι ⋙ G q a) a) (hy : CH.d _ a y = 0) (ω : Om K (Sec q V) a)
    (hcls : (CH.cx _).cls y hy = castH (G q a) hP a (E₂ ω))
    (hz : CH.d (P.ι ⋙ G q (a + 1)) (a + 1) ((pairU (grOk (smFun Y q) (Nat.add_comm 1 a)).pair P).cupC (Nat.add_comm 1 a)
      ((resU (G q 1) k₁).pullC 1 β₁ - (resU (G q 1) k₂).pullC 1 β₂) y) = 0) :
    (CH.cx (P.ι ⋙ G q (a + 1))).cls ((pairU (grOk (smFun Y q) (Nat.add_comm 1 a)).pair P).cupC (Nat.add_comm 1 a)
      ((resU (G q 1) k₁).pullC 1 β₁ - (resU (G q 1) k₂).pullC 1 β₂) y) hz =
      castH (G q (a + 1)) hP (a + 1) (E₃ (g₁ • w ω)) := by
  subst hP
  obtain ⟨hb, hform⟩ := hf k₁ k₂
  exact cup_form hFL hFU hFC E₂ E₃ h₂ h₃ g₁ t _ hb hform w hw y hy ω hcls hz

theorem cup_mem_relS {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (P : CH.Pairing F₁ F₂ F₃)
    {Q : ObjectProperty C} (hQ : Cosieve Q) {p n m : ℕ} (h : p + n = m) (b : CH.Cn F₁ p) (x : CH.Cn F₂ n) (hx : x ∈ relS F₂ Q n) :
    P.cupC h b x ∈ relS F₃ Q m := by
  intro s hs
  have hx' : x ((CH.back_mono h).functor ⋙ s) = 0 := hx _ (hQ (s.map (homOfLE (Fin.zero_le _))) hs)
  change P.μ _ _ (CH.term F₂ s x (CH.back h) (CH.back_mono h)) = 0
  unfold CH.term
  rw [hx', map_zero, map_zero]

end Per

end GlobalTheory.CompanionTheory.RelKill
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeMulIdempotentRange
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh.DegLam

section Abstract

variable {R : Type} [CommRing R] {n k : ℕ}

def compress (A : Matrix (Fin n) (Fin k) R) (N : Matrix (Fin k) (Fin n) R) (hNA : N * A = 1)
    (t : GL (Fin n) R) (ht : t.val * (A * N) = (A * N) * t.val) : GL (Fin k) R :=
  have key : ∀ u v : GL (Fin n) R, u * v = 1 → u.val * (A * N) = (A * N) * u.val →
      (N * u.val * A) * (N * v.val * A) = 1 := by
    intro u v huv hu
    have h1 : u.val * v.val = 1 := by rw [← Units.val_mul, huv, Units.val_one]
    calc (N * u.val * A) * (N * v.val * A) = N * (u.val * (A * N)) * v.val * A := by
          simp only [Matrix.mul_assoc]
      _ = N * (A * N) * (u.val * v.val) * A := by
          rw [hu]; simp only [Matrix.mul_assoc]
      _ = (N * A) * (N * A) := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = 1 := by rw [hNA, Matrix.mul_one]
  { val := N * t.val * A
    inv := N * (t⁻¹ : GL (Fin n) R).val * A
    val_inv := key t t⁻¹ (mul_inv_cancel t) ht
    inv_val := mul_eq_one_comm.1 (key t t⁻¹ (mul_inv_cancel t) ht) }

theorem compress_val (A : Matrix (Fin n) (Fin k) R) (N : Matrix (Fin k) (Fin n) R) (hNA : N * A = 1)
    (t : GL (Fin n) R) (ht : t.val * (A * N) = (A * N) * t.val) :
    (compress A N hNA t ht).val = N * t.val * A := rfl

theorem mul_frame (A : Matrix (Fin n) (Fin k) R) (N : Matrix (Fin k) (Fin n) R) (hNA : N * A = 1)
    (t : GL (Fin n) R) (ht : t.val * (A * N) = (A * N) * t.val) :
    t.val * A = A * (compress A N hNA t ht).val := by
  rw [compress_val]
  calc t.val * A = t.val * (A * (N * A)) := by rw [hNA, Matrix.mul_one]
    _ = (t.val * (A * N)) * A := by simp only [Matrix.mul_assoc]
    _ = A * (N * t.val * A) := by rw [ht]; simp only [Matrix.mul_assoc]

theorem det_compress (A : Matrix (Fin n) (Fin k) R) (N : Matrix (Fin k) (Fin n) R) (hNA : N * A = 1)
    (t : GL (Fin n) R) (ht : t.val * (A * N) = (A * N) * t.val) :
    (compress A N hNA t ht).val.det = (1 + (A * N) * (t.val - 1)).det := by
  rw [compress_val, Matrix.mul_assoc A N, Matrix.det_one_add_mul_comm, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, hNA, add_sub_cancel]

end Abstract

section Image

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem linInd_basisMat (W : Submodule E (Fin n → E)) : LinearIndependent E (basisMat W)ᵀ := by
  have h := (Module.finBasis E W).linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have h1 : (basisMat W)ᵀ = W.subtype ∘ (Module.finBasis E W) := by
    ext j i
    simp [basisMat]
  rw [h1]
  exact h

theorem exists_coord (W : Submodule E (Fin n → E)) (w : Fin n → E) (hw : w ∈ W) :
    ∃ c, basisMat W *ᵥ c = w := by
  refine ⟨(Module.finBasis E W).repr ⟨w, hw⟩, ?_⟩
  have h := (Module.finBasis E W).sum_repr ⟨w, hw⟩
  ext i
  have h2 : ((∑ j, (Module.finBasis E W).repr ⟨w, hw⟩ j • Module.finBasis E W j : W) : Fin n → E) i = w i := by
    rw [h]
  rw [Submodule.coe_sum, Finset.sum_apply] at h2
  rw [← h2]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => by simp [basisMat, mul_comm]

theorem idem_mul_basisMat {e : Matrix (Fin n) (Fin n) E} (he : e * e = e) :
    e * basisMat (LinearMap.range (Matrix.toLin' e)) = basisMat (LinearMap.range (Matrix.toLin' e)) := by
  ext i j
  have h := (mem_range_idem he _).1
    (Module.finBasis E (LinearMap.range (Matrix.toLin' e)) j).2
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, basisMat] using congrFun h i

theorem basisMat_mul_idem {e : Matrix (Fin n) (Fin n) E}
    {L : Matrix (Fin (Module.finrank E (LinearMap.range (Matrix.toLin' e)))) (Fin n) E}
    (hL : L * basisMat (LinearMap.range (Matrix.toLin' e)) = 1) :
    basisMat (LinearMap.range (Matrix.toLin' e)) * (L * e) = e := by
  refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  obtain ⟨c, hc⟩ := exists_coord (LinearMap.range (Matrix.toLin' e)) (e *ᵥ y)
    ⟨y, by rw [Matrix.toLin'_apply]⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hc, Matrix.mulVec_mulVec c L, hL, Matrix.one_mulVec]

end Image

theorem deg_lam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), DegAdelic →
    ∀ (e : Matrix (Fin n) (Fin n) E), e * e = e → ∀ t x : GA E n, t.val * rm e = rm e * t.val →
      deg (t * x) (LinearMap.range (Matrix.toLin' e)) = deg x (LinearMap.range (Matrix.toLin' e)) + lam e t := by
  intro E _ _ _ n hA e he t x ht
  have hM := linInd_basisMat (LinearMap.range (Matrix.toLin' e))
  obtain ⟨L, hLM⟩ := GlobalTheory.CompanionTheory.DegAdelicProof.exists_leftInv _ hM
  have hNM : (L * e) * basisMat (LinearMap.range (Matrix.toLin' e)) = 1 := by
    rw [Matrix.mul_assoc, idem_mul_basisMat he, hLM]
  have hBA : (L * e).map (algebraMap E (Ad E)) *
      (basisMat (LinearMap.range (Matrix.toLin' e))).map (algebraMap E (Ad E)) = 1 := by
    rw [← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero _) (map_one _)]
  have hAB : (basisMat (LinearMap.range (Matrix.toLin' e))).map (algebraMap E (Ad E)) *
      (L * e).map (algebraMap E (Ad E)) = rm e := by
    rw [← Matrix.map_mul, basisMat_mul_idem hLM]
    rfl
  have ht' : t.val * ((basisMat (LinearMap.range (Matrix.toLin' e))).map (algebraMap E (Ad E)) *
      (L * e).map (algebraMap E (Ad E))) = ((basisMat (LinearMap.range (Matrix.toLin' e))).map (algebraMap E (Ad E)) *
      (L * e).map (algebraMap E (Ad E))) * t.val := by
    rw [hAB]
    exact ht
  have h := hA E n _ x t (compress _ _ hBA t ht') _ hM (mul_frame _ _ hBA t ht')
  have hd := det_compress _ _ hBA t ht'
  rw [hAB] at hd
  unfold deg lam chi
  rw [← hd]
  exact h

end GlobalTheory.CompanionTheory.TorusCh.DegLam

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCentralContract
section
noncomputable section

namespace GlobalTheory.CompanionTheory.MoyPrasad

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.IwahoriInj GlobalTheory.DepthZeroJac ValuativeRel Matrix _root_.Topology

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isEmbedding_val_GL (n : ℕ) :
    IsEmbedding (Units.val : GL (Fin n) k → Matrix (Fin n) (Fin n) k) := by
  refine Units.isEmbedding_val_mk' (f := fun A => A⁻¹) (fun A hA => ?_) fun u => by simp
  have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
  exact (continuousAt_matrix_inv _
    (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hd)).continuousWithinAt

theorem exists_entry_nhds {n : ℕ} {V : Set (Matrix (Fin n) (Fin n) k)}
    (hV : V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) k)) :
    ∃ W ∈ 𝓝 (0 : k), ∀ A : Matrix (Fin n) (Fin n) k, (∀ i j, (A - 1) i j ∈ W) → A ∈ V := by
  have hS : (fun A : Matrix (Fin n) (Fin n) k => A + 1) ⁻¹' V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) k) :=
    (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds (by simpa using hV)
  have e : 𝓝 (0 : Matrix (Fin n) (Fin n) k) =
      Filter.pi fun _ : Fin n => Filter.pi fun _ : Fin n => 𝓝 (0 : k) := by
    show 𝓝 (0 : Fin n → Fin n → k) = _
    rw [nhds_pi]
    congr 1
    funext i
    rw [nhds_pi]
    rfl
  rw [e] at hS
  obtain ⟨I, t, ht, hsub⟩ := Filter.mem_pi'.1 hS
  have ht' : ∀ i, ∃ (I' : Finset (Fin n)) (t' : Fin n → Set k), (∀ j, t' j ∈ 𝓝 (0 : k)) ∧
      (I' : Set (Fin n)).pi t' ⊆ t i := fun i => Filter.mem_pi'.1 (ht i)
  choose I' t' h1 h2 using ht'
  refine ⟨⋂ i, ⋂ j, t' i j, Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => h1 i j,
    fun A hA => ?_⟩
  have h3 : A - 1 ∈ (fun A : Matrix (Fin n) (Fin n) k => A + 1) ⁻¹' V :=
    hsub fun i _ => h2 i fun j _ => by
      have := hA i j
      simp only [Set.mem_iInter] at this
      exact this i j
  simpa using h3

variable {s : ℕ} {d : Fin s → ℕ}

def blockScalar {c : k} (hc : c ≠ 0) (C : Fin s → ℕ) : Levi k (fun a => Fin (d a)) := fun a =>
  ⟨(c ^ C a) • (1 : Matrix (Fin (d a)) (Fin (d a)) k), (c ^ C a)⁻¹ • (1 : Matrix (Fin (d a)) (Fin (d a)) k),
    by rw [smul_mul_smul_comm, mul_inv_cancel₀ (pow_ne_zero _ hc), one_smul, one_mul],
    by rw [smul_mul_smul_comm, inv_mul_cancel₀ (pow_ne_zero _ hc), one_smul, one_mul]⟩

theorem blockScalar_central {c : k} (hc : c ≠ 0) (C : Fin s → ℕ) (m : Levi k (fun a => Fin (d a))) :
    blockScalar hc C * m = m * blockScalar hc C := by
  funext a
  refine Units.ext ?_
  show ((c ^ C a) • (1 : Matrix (Fin (d a)) (Fin (d a)) k)) * (m a).val =
    (m a).val * ((c ^ C a) • (1 : Matrix (Fin (d a)) (Fin (d a)) k))
  simp

theorem leviEmb_blockScalar {n : ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {c : k} (hc : c ≠ 0)
    (C : Fin s → ℕ) : leviEmb k e (blockScalar hc C) = dia e hc C := by
  refine Units.ext ?_
  rw [dia_val]
  ext i j
  obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
  by_cases h : a = b
  · subst h
    rw [leviEmb_apply_same]
    show ((c ^ C a) • (1 : Matrix (Fin (d a)) (Fin (d a)) k)) i' j' = _
    by_cases h2 : i' = j'
    · subst h2
      simp
    · rw [Matrix.smul_apply, one_apply_ne h2, smul_zero, diagonal_apply_ne]
      simpa using h2
  · rw [leviEmb_apply_ne k e _ h, diagonal_apply_ne]
    exact fun h' => h (congrArg Sigma.fst (e.injective h'))

theorem valuation_conj_le {c x : k} (hc : c ≠ 0) (hv : valuation k c ≤ 1) (hx : valuation k x ≤ 1)
    {A B N : ℕ} (h : A + N ≤ B) : valuation k ((c ^ A)⁻¹ * x * c ^ B) ≤ valuation k c ^ N := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  have e1 : (c ^ A)⁻¹ * x * c ^ (A + N + r) = c ^ N * (x * c ^ r) := by
    rw [pow_add, pow_add]
    field_simp
  rw [e1, map_mul, map_mul, map_pow, map_pow]
  exact mul_le_of_le_one_right' (mul_le_one' hx (pow_le_one' hv r))

theorem expo_gap {s : ℕ} (N : ℕ) {a b : Fin s} (h : b < a) : expo s N a + N ≤ expo s N b := by
  have h1 : (b : ℕ) < a := h
  have h2 : (a : ℕ) < s := a.2
  simp only [expo]
  calc (N + 1) * (s - 1 - (a : ℕ)) + N ≤ (N + 1) * (s - 1 - (a : ℕ)) + (N + 1) := by omega
    _ = (N + 1) * (s - 1 - (a : ℕ) + 1) := by ring
    _ ≤ (N + 1) * (s - 1 - (b : ℕ)) := Nat.mul_le_mul_left _ (by omega)

end GlobalTheory.CompanionTheory.MoyPrasad
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedInjSmooth
section
namespace GlobalTheory.CompanionTheory.DepthZeroJac

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead _root_.Topology
open GlobalTheory.DepthZeroJac GlobalTheory.StepData GlobalTheory.IwahoriInj

theorem fixed_inj_smooth (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hπ : IsSmooth π) :
    ∀ v ∈ fixed π (Gx k e),
      (Submodule.Quotient.mk v : Jacquet π (unipRad k e)) = 0 → v = 0 := by
  intro v hv h0
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_deep (k := k) 1
  have h1 : v ∈ twKer π (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 h0
  obtain ⟨M, hM⟩ := (eventually_mem_twKer (hc := hc0) hc1 hc2 h1).exists
  exact claim_of_antitone hc1 hc2 hπ _ _ rfl (antitone_expo M) v hv hM

end GlobalTheory.CompanionTheory.DepthZeroJac
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedPiecesGeneratedByIdealGeneratorsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_pieces_generated_by_ideal_generators : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules}, P.IsQuasicoherent → ∀ (S : ℕ → Subobject P) (hS : ClosedSys I P S) {k : ℕ} (g : Fin k → A), Ideal.span (Set.range g) = I → ∀ (hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i))) (e : ℕ) (U : X.affineOpens), Submodule.span Γ(X, U) (⋃ i, Set.range ((grT (anti hS) (hr i) e).app U)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.span_grT_eq_top | exact GlobalTheory.CompanionTheory.GE.Step.span_grT_eq_top | (intros; apply GlobalTheory.CompanionTheory.GE.Step.span_grT_eq_top <;> assumption)
end

