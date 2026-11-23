module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0058
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0060
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0059

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantBlockEigenvalue
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgTransport

open _root_.CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL

theorem glRel_comp_inj {A : Type*} [Ring A] {m n : ℕ} {E : Fin n → Fin n → A} (hE : GlRel E)
    (e : Fin m → Fin n) (he : Function.Injective e) : GlRel (fun a b => E (e a) (e b)) := by
  intro a b c d
  have := hE (e a) (e b) (e c) (e d)
  simpa only [he.eq_iff] using this

theorem glRel_op_transpose {A : Type*} [Ring A] {n : ℕ} {E : Fin n → Fin n → A} (hE : GlRel E) :
    GlRel (fun a b => MulOpposite.op (E b a)) := by
  intro a b c d
  have h := congrArg MulOpposite.op (hE d c b a)
  simp only [MulOpposite.op_sub, MulOpposite.op_mul] at h
  rw [h]
  simp only [eq_comm (a := c) (b := b), eq_comm (a := a) (b := d)]
  by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2]

theorem qdet_eigen_of_killed {n : ℕ} (Q : GMod n) (d : Fin 3 → ℕ) (h : ∑ i, d i = n) (w : Q.V)
    (hw : ∀ a b, blk (stdBlocks d h) b < blk (stdBlocks d h) a → Q.E a b w = 0)
    (c : Fin 3 → ℂ → ℂ) (hc : ∀ i Y, Qd Q d h i Y w = c i Y • w) (Y : ℂ) :
    qdet Q.E (Y + ((n : ℂ) - 1) / 2) w = (∏ i, c i Y) • w := by
  let f : Module.End ℂ Q.V →ₗ[ℂ] (Module.End ℂ Q.V)ᵐᵒᵖ := (MulOpposite.opLinearEquiv ℂ).toLinearMap
  have f1 : f 1 = 1 := rfl
  have fm : ∀ x y, f (x * y) = f y * f x := fun _ _ => rfl
  let X : Fin n → Fin n → (Module.End ℂ Q.V)ᵐᵒᵖ := fun p q => MulOpposite.op (Q.E q p)
  have hX : GlRel X := glRel_op_transpose Q.gl
  have hq : ∀ u, qdet X u = f (qdet Q.E u) := fun u => GlobalTheory.T.quantum_determinant_anti_homomorphism f f1 fm Q.E Q.gl u
  have hb : ∀ i u, qdet (fun p q : Fin (d i) => X (stdBlocks d h ⟨i, p⟩) (stdBlocks d h ⟨i, q⟩)) u =
      f (qdet (bops Q d h i) u) := fun i u =>
    GlobalTheory.T.quantum_determinant_anti_homomorphism f f1 fm (bops Q d h i)
      (glRel_comp_inj Q.gl (fun p => stdBlocks d h ⟨i, p⟩)
        (fun p q e => by simpa using (stdBlocks d h).injective e)) u
  have hspan := _root_.GlobalTheory.CapHC.qdet_blocks_congr (Module.End ℂ Q.V)ᵐᵒᵖ d h X hX Y
  let L : (Module.End ℂ Q.V)ᵐᵒᵖ →ₗ[ℂ] Q.V :=
    { toFun := fun a => a.unop w
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL : ∀ y ∈ Submodule.span ℂ {y : (Module.End ℂ Q.V)ᵐᵒᵖ | ∃ (p q : Fin n) (v : (Module.End ℂ Q.V)ᵐᵒᵖ),
      blk (stdBlocks d h) p < blk (stdBlocks d h) q ∧ y = X p q * v}, L y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, q, v, hpq, rfl⟩ := hy
      show (v.unop * Q.E q p) w = 0
      rw [Module.End.mul_apply, hw q p hpq, map_zero]
    | zero => exact map_zero L
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
    | smul a x _ hx => rw [map_smul, hx, smul_zero]
  have h0 := hL _ hspan
  rw [map_sub, sub_eq_zero] at h0
  have hl3 : ∀ g : Fin 3 → (Module.End ℂ Q.V)ᵐᵒᵖ, (List.ofFn g).prod = g 0 * g 1 * g 2 := by
    intro g
    simp [List.ofFn_succ, mul_assoc]
  rw [hl3] at h0
  simp only [hb, hq] at h0
  have e1 : qdet Q.E (Y + ((n : ℂ) - 1) / 2) w = Qd Q d h 2 Y (Qd Q d h 1 Y (Qd Q d h 0 Y w)) := h0
  simp only [e1, hc, map_smul, smul_smul, Fin.prod_univ_three]

end GlobalTheory.CompanionTheory.RgTransport
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TensorQuotientQuantumDeterminantEigen
section
noncomputable section

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport

namespace GlobalTheory.CompanionTheory.RgTransport.Raise

theorem exists_capelliPoly_eq_sum {m : ℕ} (χ : Fin m → ℂ) :
    ∃ a : ℕ → ℂ, ∀ Y : ℂ, Formalism.QuantumDeterminants.capP χ Y = ∑ j ∈ Finset.range (m + 1), Y ^ j * a j := by
  let p : Polynomial ℂ := ∏ s : Fin m, (Polynomial.X + Polynomial.C (χ s))
  have hd : p.natDegree ≤ m := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc _ ≤ ∑ _s : Fin m, 1 := Finset.sum_le_sum fun s _ => (Polynomial.natDegree_X_add_C _).le
      _ = m := by simp
  refine ⟨p.coeff, fun Y => ?_⟩
  have e : Formalism.QuantumDeterminants.capP χ Y = p.eval Y := by
    simp [p, Formalism.QuantumDeterminants.capP, Polynomial.eval_prod]
  rw [e, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd)]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exists_raised : StepChar → TensDecomp → ∀ {m : ℕ} (M : GMod m) (χ : Fin m → ℂ), HasChar M χ →
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin m → Fin m → Module.End ℂ V), GlRel E →
    ∀ Φ : (Fin m → M.V) →ₗ[ℂ] V, (∀ a b u, Φ (tensE M a b u) = E a b (Φ u)) → Φ ≠ 0 →
    ∃ r, ∃ w ∈ LinearMap.range Φ, w ≠ 0 ∧ ∀ Y : ℂ,
      qdet E (Y + ((m : ℂ) - 1) / 2) w = Formalism.QuantumDeterminants.capP (χ + Pi.single r 1) Y • w := by
  intro hS hT m M χ hM V _ _ E hE Φ hΦ hne
  have hsup := hT m M χ hM
  obtain ⟨r, hr⟩ : ∃ r, ¬ stepSub M (χ r) ≤ LinearMap.ker Φ := by
    by_contra h
    push Not at h
    have h' : (⊤ : Submodule ℂ (Fin m → M.V)) ≤ LinearMap.ker Φ := hsup ▸ iSup_le h
    exact hne (LinearMap.ker_eq_top.1 (top_le_iff.1 h'))
  obtain ⟨N, hN⟩ := hS m M χ r hM
  let f : (step M (χ r)).V →ₗ[ℂ] V := Φ ∘ₗ (stepSub M (χ r)).subtype
  have hf : ∀ a b x, f ((step M (χ r)).E a b x) = E a b (f x) := fun a b x => hΦ a b x.1
  let D : ℂ → Module.End ℂ V := fun Y =>
    qdet E (Y + ((m : ℂ) - 1) / 2) - Formalism.QuantumDeterminants.capP (χ + Pi.single r 1) Y • (1 : Module.End ℂ V)
  have hI : LinearMap.range f ≠ ⊥ := by
    intro h0
    refine hr fun x hx => ?_
    have : f ⟨x, hx⟩ ∈ LinearMap.range f := ⟨_, rfl⟩
    rw [h0] at this
    exact (Submodule.mem_bot ℂ).1 this
  have hsh : ∀ Y x, f ((qdet (step M (χ r)).E (Y + ((m : ℂ) - 1) / 2) -
      Formalism.QuantumDeterminants.capP (χ + Pi.single r 1) Y • (1 : Module.End ℂ (step M (χ r)).V)) x) = D Y (f x) := fun Y x =>
    shift_lin f _ _ (fun y => qdet_lin f (step M (χ r)).E E hf _ y) _ x
  have hcomm : ∀ Y Y', Commute (D Y) (D Y') := by
    intro Y Y'
    have h0 : Commute (qdet E (Y + ((m : ℂ) - 1) / 2)) (qdet E (Y' + ((m : ℂ) - 1) / 2)) :=
      by
        unfold qdet qminor
        refine Commute.sum_right _ _ _ fun σ _ => ?_
        refine Commute.mul_right (Int.cast_commute _ _).symm ?_
        refine Commute.list_prod_right _ _ fun x hx => ?_
        rw [List.mem_ofFn] at hx
        obtain ⟨k, rfl⟩ := hx
        unfold Tm
        refine Commute.add_right ?_ (qDetCentral _ m E hE _ _ _)
        split_ifs
        · exact Algebra.commute_algebraMap_right _ _
        · exact Commute.zero_right _
    refine Commute.sub_left (Commute.sub_right h0 ((Commute.one_right _).smul_right _)) ?_
    exact ((Commute.one_left _).smul_left _).sub_right ((Commute.one_left _).smul_left _ |>.smul_right _)
  have hst : ∀ Y, ∀ x ∈ LinearMap.range f, D Y x ∈ LinearMap.range f := by
    rintro Y _ ⟨x, rfl⟩
    exact ⟨_, hsh Y x⟩
  have hnil : ∀ Y, ∀ x ∈ LinearMap.range f, ∃ k : ℕ, (D Y ^ k) x = 0 := by
    rintro Y _ ⟨x, rfl⟩
    refine ⟨N, ?_⟩
    have e := pow_lin f _ (D Y) (hsh Y) N x
    rw [hN Y] at e
    simpa using e.symm
  let t : ℕ → Fin m → Fin m → Polynomial (Module.End ℂ V) := fun k a b =>
    (if a = b then Polynomial.X + Polynomial.C (algebraMap ℂ (Module.End ℂ V) (((m : ℂ) - 1) / 2 - k)) else 0) + Polynomial.C (E a b)
  let p : Polynomial (Module.End ℂ V) := ∑ σ : Equiv.Perm (Fin m), Polynomial.C ((Equiv.Perm.sign σ : ℤ) : Module.End ℂ V) * (List.ofFn fun k : Fin m => t k (σ k) k).prod
  have ht : ∀ k a b, (t k a b).natDegree ≤ 1 := by
    intro k a b
    dsimp [t]
    split_ifs
    · exact (Polynomial.natDegree_add_le _ _).trans (max_le ((Polynomial.natDegree_add_le _ _).trans (max_le Polynomial.natDegree_X_le (by rw [Polynomial.natDegree_C]; omega))) (by simp))
    · simp
  have hp : p.natDegree ≤ m := by
    dsimp [p]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (Polynomial.natDegree_list_prod_le _).trans ?_
    rw [List.map_ofFn, List.sum_ofFn]
    calc _ ≤ ∑ _k : Fin m, 1 := Finset.sum_le_sum fun k _ => ht _ _ _
      _ = m := by simp
  let ev (Y : ℂ) : Polynomial (Module.End ℂ V) →+* Module.End ℂ V :=
    Polynomial.eval₂RingHom' (RingHom.id _) (algebraMap ℂ _ Y) (fun a => (Algebra.commutes Y a).symm)
  have hc : ∀ Y, qdet E (Y + ((m : ℂ) - 1) / 2) = ∑ j ∈ Finset.range (m + 1), Y ^ j • p.coeff j := by
    intro Y
    have he : ev Y p = qdet E (Y + ((m : ℂ) - 1) / 2) := by
      dsimp [p]
      unfold qdet qminor
      rw [map_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [map_mul, map_list_prod, List.map_ofFn]
      congr 1
      · simp [ev]
      · congr 1
        congr 1
        funext k
        simp only [Function.comp_apply]
        dsimp [t, Tm]
        split_ifs <;> change Polynomial.eval₂ (RingHom.id _) (algebraMap ℂ _ Y) _ = _ <;>
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [← he]
    change Polynomial.eval₂ (RingHom.id _) (algebraMap ℂ _ Y) p = _
    rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hp)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [RingHom.id_apply, ← map_pow]
    rw [Algebra.smul_def]
    exact (Algebra.commutes _ _).symm
  let c := p.coeff
  obtain ⟨a, ha⟩ := exists_capelliPoly_eq_sum (χ + Pi.single r 1)
  have hD : ∀ Y, D Y = ∑ j ∈ Finset.range (m + 1), Y ^ j • (c j - a j • (1 : Module.End ℂ V)) := by
    intro Y
    have h1 := hc Y
    simp only [D, h1, ha Y, c, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul, mul_smul]
  obtain ⟨w, hw, hw0, hwD⟩ := _root_.GlobalTheory.CompanionTheory.RgTransport.exists_joint_kernel_polynomial_family _ hI D hcomm hst hnil (m + 1) _ hD
  obtain ⟨x, rfl⟩ := hw
  refine ⟨r, f x, ⟨_, rfl⟩, hw0, fun Y => ?_⟩
  have h2 := hwD Y
  simpa [D, sub_eq_zero] using h2

end GlobalTheory.CompanionTheory.RgTransport.Raise
end
end

