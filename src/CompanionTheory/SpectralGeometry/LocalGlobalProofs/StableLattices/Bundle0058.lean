module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0013
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
public import Mathlib
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRTWNeAlg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0040

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharSub
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgTransport

open _root_.CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL

variable {n : ℕ}

def actML {M : Type} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M where
  toFun := actM E
  map_add' X Y := by simp only [actM, Matrix.add_apply, add_smul, sum_add_distrib]
  map_smul' c X := by simp only [actM, Matrix.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_sum]

theorem actM_single {M : Type} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    actM E (Matrix.single a b 1) = E a b := by
  classical
  simp [actM, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_smul]

theorem glRel_Eb (X : GMod n) {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) : GlRel (Eb X B) := by
  have h := GlobalTheory.CapelliLowest.glRel_conj n (actML X.E) ⟨B.U, B.Ui, B.hU, B.hUi⟩ (by
    have : (fun i j => actML X.E (Matrix.single i j 1)) = X.E := by
      funext i j; exact actM_single X.E i j
    rw [this]; exact X.gl)
  exact h

def ebMod (X : GMod n) {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) : GMod n := ⟨X.V, Eb X B, glRel_Eb X B⟩

def trMod (Y : GMod n) : GMod n where
  V := Module.Dual ℂ Y.V
  E := fun a b => (Y.E b a).dualMap
  gl := fun a b c d => by
    refine LinearMap.ext fun φ => LinearMap.ext fun x => ?_
    have h := comm_apply Y d c b a x
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.dualMap_apply, h, map_add (f := _), map_sub]
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · subst h1; subst h2; simp; ring
    · subst h1; simp [h2, Ne.symm h2]
    · subst h2; simp [h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

def quoMod (Y : GMod n) (S : Submodule ℂ Y.V) (h : ∀ a b, ∀ x ∈ S, Y.E a b x ∈ S) : GMod n where
  V := Y.V ⧸ S
  E := fun a b => S.mapQ S (Y.E a b) (fun x hx => h a b x hx)
  gl := fun a b c d => by
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective S q
    have h' := comm_apply Y a b c d x
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, h']
    by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2, Submodule.Quotient.mk_add, Submodule.Quotient.mk_sub] <;> abel

def bops (Q : GMod n) {c : ℕ} (d : Fin c → ℕ) (h : ∑ i, d i = n) (i : Fin c) : Fin (d i) → Fin (d i) → Module.End ℂ Q.V :=
  fun p q => Q.E (stdBlocks d h ⟨i, p⟩) (stdBlocks d h ⟨i, q⟩)

def Qd (Q : GMod n) {c : ℕ} (d : Fin c → ℕ) (h : ∑ i, d i = n) (i : Fin c) (Y : ℂ) : Module.End ℂ Q.V :=
  qdet (bops Q d h i) (Y + ((d i : ℂ) - 1) / 2 - (modExp (fun i => Fin (d i)) i : ℂ) / 2)

def leviSub (P : GMod n) (d : Fin 3 → ℕ) (h : ∑ i, d i = n) (χ : Fin n → ℂ) (L : Fin n → Fin 3) : Submodule ℂ P.V where
  carrier := {x | (∀ a b, blk (stdBlocks d h) b < blk (stdBlocks d h) a → P.E a b x = 0) ∧
    ∀ i Y, Qd P d h i Y x = plab χ L i Y • x}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨fun a b hab => by rw [map_add (f := _), hx a b hab, hy a b hab, add_zero],
      fun i Y => by rw [map_add (f := _), hx', hy', smul_add]⟩
  zero_mem' := ⟨fun _ _ _ => map_zero _, fun _ _ => by simp⟩
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    exact ⟨fun a b hab => by rw [map_smul, hx a b hab, smul_zero],
      fun i Y => by rw [map_smul, hx', smul_comm]⟩

theorem ofFn_lin {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (f : V →ₗ[ℂ] V') :
    ∀ {t : ℕ} (g : Fin t → Module.End ℂ V) (g' : Fin t → Module.End ℂ V'), (∀ k x, f (g k x) = g' k (f x)) → ∀ x,
      f ((List.ofFn g).prod x) = (List.ofFn g').prod (f x)
  | 0, _, _, _, x => by simp
  | t + 1, g, g', h, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply, h,
      ofFn_lin f (fun k => g k.succ) (fun k => g' k.succ) (fun k x => h k.succ x)]

theorem qdet_lin {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (f : V →ₗ[ℂ] V') {m : ℕ}
    (E : Fin m → Fin m → Module.End ℂ V) (E' : Fin m → Fin m → Module.End ℂ V')
    (h : ∀ a b x, f (E a b x) = E' a b (f x)) (u : ℂ) (x : V) : f (qdet E u x) = qdet E' u (f x) := by
  have hT : ∀ (v : ℂ) (a b : Fin m) (y : V), f (Tm E v a b y) = Tm E' v a b (f y) := by
    intro v a b y
    unfold Tm
    by_cases hab : a = b <;> simp [hab, h]
  unfold qdet qminor
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Module.End.mul_apply, Module.End.intCast_apply, map_zsmul]
  rw [ofFn_lin f _ _ (fun k y => hT _ _ _ y)]

theorem pow_lin {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (f : V →ₗ[ℂ] V')
    (T : Module.End ℂ V) (T' : Module.End ℂ V') (h : ∀ x, f (T x) = T' (f x)) (k : ℕ) (x : V) :
    f ((T ^ k) x) = (T' ^ k) (f x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

theorem shift_lin {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (f : V →ₗ[ℂ] V')
    (T : Module.End ℂ V) (T' : Module.End ℂ V') (h : ∀ x, f (T x) = T' (f x)) (c : ℂ) (x : V) :
    f ((T - c • (1 : Module.End ℂ V)) x) = (T' - c • (1 : Module.End ℂ V')) (f x) := by
  simp [h]

theorem hasChar_sub (Y : GMod n) (S : Submodule ℂ Y.V) (h : ∀ a b, ∀ x ∈ S, Y.E a b x ∈ S) {χ : Fin n → ℂ}
    (hY : HasChar Y χ) : HasChar (Y.sub S h) χ := by
  obtain ⟨k, hk⟩ := hY
  refine ⟨k, fun c => LinearMap.ext fun x => ?_⟩
  have e := pow_lin (V := S) S.subtype _ _
    (shift_lin (V := S) S.subtype (qdet (Y.sub S h).E (c + ((n : ℂ) - 1) / 2)) (qdet Y.E (c + ((n : ℂ) - 1) / 2))
      (fun y => qdet_lin (V := S) S.subtype (Y.sub S h).E Y.E (fun a b x => rfl) _ y) (Formalism.QuantumDeterminants.capP χ c)) k x
  rw [hk c] at e
  exact S.injective_subtype (e.trans (by simp; rfl))

theorem hasChar_quo (Y : GMod n) (S : Submodule ℂ Y.V) (h : ∀ a b, ∀ x ∈ S, Y.E a b x ∈ S) {χ : Fin n → ℂ}
    (hY : HasChar Y χ) : HasChar (quoMod Y S h) χ := by
  obtain ⟨k, hk⟩ := hY
  refine ⟨k, fun c => LinearMap.ext fun q => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective S q
  have e := pow_lin (V' := Y.V ⧸ S) S.mkQ _ _
    (shift_lin (V' := Y.V ⧸ S) S.mkQ (qdet Y.E (c + ((n : ℂ) - 1) / 2)) (qdet (quoMod Y S h).E (c + ((n : ℂ) - 1) / 2))
      (fun y => qdet_lin (V' := Y.V ⧸ S) S.mkQ Y.E (quoMod Y S h).E (fun a b x => rfl) _ y) (Formalism.QuantumDeterminants.capP χ c)) k x
  rw [hk c] at e
  exact e.symm.trans (by simp; rfl)

end GlobalTheory.CompanionTheory.RgTransport
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ScalarOfSeparatingSmoothL2Maps
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.AdjointSignNormality

open _root_.CompanionTheory.RgExh CompanionTheory.RgExh.Fin ReciprocityTheory.ChartRestriction.DS
open Formalism.REAL (GlRel qdet)

variable {n : ℕ} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem exists_adj_sum {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E)
    (l : List (ℂ × List (Fin n × Fin n))) :
    ∃ B : Module.End ℂ M, ∀ x y : M,
      inner ℂ ((l.map fun c => c.1 • (c.2.map fun p => E p.1 p.2).prod).sum x) y = inner ℂ x (B y) := by
  induction l with
  | nil => exact ⟨0, fun x y => by simp⟩
  | cons c l ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨((starRingEnd ℂ) c.1 * (c.2.map fun p => adjSign ε p.1 p.2).prod) •
      ((c.2.reverse.map Prod.swap).map fun p => E p.1 p.2).prod + B, fun x y => ?_⟩
    simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, LinearMap.smul_apply, inner_add_left,
      inner_add_right, inner_smul_left, inner_smul_right, hB, eword_adjoint hU]
    ring

theorem exists_adj_qdet {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E) (u : ℂ) :
    ∃ B : Module.End ℂ M, ∀ x y : M, inner ℂ (qdet E u x) y = inner ℂ x (B y) := by
  obtain ⟨l, hl⟩ := qdet_eq_sum_words E u
  rw [hl]
  exact exists_adj_sum hU l

theorem adjSign_mul_self (ε : Fin n → Bool) (a b : Fin n) : adjSign ε a b * adjSign ε a b = 1 := by
  unfold adjSign
  split_ifs <;> simp

theorem commute_adj {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E)
    {A B : Module.End ℂ M} (hA : ∀ a b, Commute A (E a b)) (hB : ∀ x y : M, inner ℂ (A x) y = inner ℂ x (B y))
    (c d : Fin n) : Commute B (E c d) := by
  have key : ∀ x y : M, inner ℂ x (B (E c d y)) = inner ℂ x (E c d (B y)) := by
    intro x y
    have h1 : inner ℂ (E d c (A x)) y = adjSign ε d c * inner ℂ (A x) (E c d y) := hU d c _ _
    have h2 : inner ℂ (E d c x) (B y) = adjSign ε d c * inner ℂ x (E c d (B y)) := hU d c _ _
    have h3 : E d c (A x) = A (E d c x) := LinearMap.congr_fun (hA d c).symm.eq x
    rw [h3, hB, h2] at h1
    have hs : adjSign ε d c ≠ 0 := left_ne_zero_of_mul_eq_one (adjSign_mul_self ε d c)
    rw [← hB]
    exact (mul_left_cancel₀ hs h1).symm
  refine LinearMap.ext fun y => ?_
  have h := key (B (E c d y) - E c d (B y)) y
  have h0 : inner ℂ (B (E c d y) - E c d (B y)) (B (E c d y) - E c d (B y)) = (0 : ℂ) := by
    rw [inner_sub_right, h, sub_self]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

theorem normal_sq {A B : Module.End ℂ M} (hB : ∀ x y : M, inner ℂ (A x) y = inner ℂ x (B y)) (hc : Commute A B)
    (y : M) (h : A (A y) = 0) : A y = 0 := by
  have hn : ∀ z : M, inner ℂ (B z) (B z) = inner ℂ (A z) (A z) := by
    intro z
    have h1 : inner ℂ (A (B z)) z = inner ℂ (B z) (B z) := hB _ _
    have h2 : inner ℂ (A z) (A z) = inner ℂ z (B (A z)) := hB _ _
    have h3 : A (B z) = B (A z) := LinearMap.congr_fun hc.eq z
    rw [← h1, h3, ← inner_conj_symm, ← h2, inner_self_conj]
  have h0 : B (A y) = 0 := by
    have := hn (A y)
    rw [h, inner_zero_left] at this
    exact inner_self_eq_zero.1 this
  have h1 : inner ℂ (A y) (A y) = (0 : ℂ) := by rw [hB, h0, inner_zero_right]
  exact inner_self_eq_zero.1 h1

theorem normal_pow {A B : Module.End ℂ M} (hB : ∀ x y : M, inner ℂ (A x) y = inner ℂ x (B y)) (hc : Commute A B)
    (k : ℕ) (y : M) (h : (A ^ k) y = 0) : A y = 0 := by
  induction k generalizing y with
  | zero =>
    have : y = 0 := by simpa using h
    simp [this]
  | succ k ih =>
    refine normal_sq hB hc y (ih (A y) ?_)
    rw [pow_succ] at h
    exact h

theorem qdet_shift_pow {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E)
    (hU : IsInfUnitary ε E) (w s : ℂ) (k : ℕ) (y : M)
    (h : ((qdet E w - s • (1 : Module.End ℂ M)) ^ k) y = 0) : (qdet E w - s • (1 : Module.End ℂ M)) y = 0 := by
  obtain ⟨B, hB⟩ := exists_adj_qdet hU w
  have hA : ∀ a b, Commute (qdet E w) (E a b) := fun a b =>
    (Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW.qdet_comm hE w a b)
  have hBE := commute_adj hU hA hB
  have hQ : Commute B (qdet E w) := by
    have hm : qdet E w ∈ Subalgebra.centralizer ℂ {B} := by
      unfold qdet Formalism.REAL.qminor
      refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) ?_
      refine Subalgebra.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
      unfold Formalism.REAL.Tm
      refine Subalgebra.add_mem _ ?_ ?_
      · split_ifs
        · exact Subalgebra.algebraMap_mem _ _
        · exact Subalgebra.zero_mem _
      · exact (Subalgebra.mem_centralizer_iff ℂ).2 fun _ hg => by rw [hg]; exact hBE _ _
    exact (Subalgebra.mem_centralizer_iff ℂ).1 hm B rfl
  have hadj : ∀ x y : M, inner ℂ ((qdet E w - s • (1 : Module.End ℂ M)) x) y =
      inner ℂ x ((B - (starRingEnd ℂ) s • (1 : Module.End ℂ M)) y) := by
    intro x y
    simp [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hB, mul_comm]
  have hc : Commute (qdet E w - s • (1 : Module.End ℂ M)) (B - (starRingEnd ℂ) s • (1 : Module.End ℂ M)) := by
    refine Commute.sub_left (Commute.sub_right hQ.symm ?_) (Commute.sub_right ?_ ?_)
    · exact (Commute.one_right _).smul_right _
    · exact (Commute.one_left _).smul_left _
    · exact ((Commute.one_left _).smul_left _).smul_right _
  exact normal_pow hadj hc k y h

theorem scalar_of_separating_smooth_l2_maps : ScalarCharacterOfL2Embedding := by
  rintro n ε X χ hL ⟨k, hk⟩ Y
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hE : GlRel (smE ε (rreg ε)) := hD.glRep
  refine sub_eq_zero.1 (LinearMap.ext fun u => ?_)
  by_contra hne
  obtain ⟨c, hc, hcu⟩ := hL _ hne
  apply hcu
  set w : ℂ := Y + ((n : ℂ) - 1) / 2
  set s : ℂ := Formalism.QuantumDeterminants.capP χ Y
  have hint : ∀ x, c ((qdet X.E w - s • (1 : Module.End ℂ X.V)) x) =
      (qdet (smE ε (rreg ε)) w - s • (1 : Module.End ℂ (smD ε (rreg ε)))) (c x) := by
    intro x
    simp [Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.qdet_int c hc]
  have hpow : ∀ (j : ℕ) x, c (((qdet X.E w - s • (1 : Module.End ℂ X.V)) ^ j) x) =
      ((qdet (smE ε (rreg ε)) w - s • (1 : Module.End ℂ (smD ε (rreg ε)))) ^ j) (c x) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hint]
  have h0 := hpow k u
  rw [hk Y, LinearMap.zero_apply, map_zero] at h0
  rw [hint]
  exact qdet_shift_pow hE hU w s k _ h0.symm

end GlobalTheory.CompanionTheory.AdjointSignNormality
end
end

