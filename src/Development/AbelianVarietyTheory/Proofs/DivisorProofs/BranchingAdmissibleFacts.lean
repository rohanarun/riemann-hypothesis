module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0651
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0041
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0790
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0812
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

noncomputable section

namespace GlobalTheory.BrCompare

section Core

variable {K : Type} [Field K] [CharZero K] {n : ℕ}

theorem hw_raise (ν : Fin n → ℕ) (l j : Fin n) (h : l < j) : rowE K n n l j (hw K le_rfl ν) = 0 := by
  rw [(rowE_eq_rowDiv K n n l j _).1]
  exact hwRaise K n n le_rfl ν l j 1 h le_rfl

theorem hw_weight {ν : Fin n → ℕ} (hν : Antitone ν) (s : Fin n) :
    rowE K n n s s (hw K le_rfl ν) = (ν s : K) • hw K le_rfl ν := by
  have h := (rowWeight_iff _ _).1 (hwRowWeight K n n le_rfl ν hν) s
  simpa [rowNu] using h

theorem capDet_dualWeyl {μ : Fin n → ℕ} (hμ : Antitone μ) (u : ℤ) {f : MvPolynomial (Fin n × Fin n) K}
    (hf : f ∈ dualWeyl K n n μ) :
    capDet (fun i j => rowE K n n i j) u f = ((∏ j : Fin n, (u + ((j : ℕ) : ℤ) - (μ j : ℤ)) : ℤ) : K) • f := by
  have h := _root_.GlobalTheory.BrCompare.dualWeyl_le_of_rowE_stable K n μ hμ (Module.End.eigenspace (capDet (fun i j => rowE K n n i j) u)
    ((∏ j : Fin n, (u + ((j : ℕ) : ℤ) - (μ j : ℤ)) : ℤ) : K)) ?_ ?_ hf
  · exact Module.End.mem_eigenspace_iff.1 h
  · exact Module.End.mem_eigenspace_iff.2 (capDet_eigen _ u _ (fun j => (μ j : ℤ)) (hw_raise μ)
      (fun s => by simpa using hw_weight hμ s))
  · intro a b g hg
    rw [Module.End.mem_eigenspace_iff] at hg ⊢
    have hc := capDet_central (fun i j => rowE K n n i j) u (fun i j k l => by
      simpa only [eq_comm (a := l)] using glRel_rowE K n n i j k l) end_two a b
    rw [← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply, hg, map_smul]

theorem branchingAdmissible_facts {lam : Fin n → ℕ} {d : ℕ} {β : Fin n → ℤ} (h : bmAdm lam d β) :
    ∃ b : Fin n → ℕ, β = (fun s => (b s : ℤ)) ∧ (∀ s, b s ≤ lam s) ∧ Antitone fun s => lam s - b s := by
  lift β to Fin n → ℕ using h.1 with b
  have h2 := h.2.2
  have hb : ∀ s, b s ≤ lam s := fun s => by
    have h3 := (h2 s).2
    rw [bmH_lamZ_succ] at h3
    simp only [Function.comp] at h3
    omega
  refine ⟨b, rfl, hb, bmK_antitone lam (fun s => lam s - b s) (bm_IL_of lam _ ?_)⟩
  simpa only [Nat.cast_sub (hb _)] using h2

theorem rCap_top {lam : Fin n → ℕ} {d : ℕ} (G : BP K n) (hG : G ∈ bmW K n lam d) (β : Fin n → ℤ)
    (hβ : zcomp K n β G ≠ 0) (hmax : ∀ β', zcomp K n β' G ≠ 0 → omg β' ≤ omg β) :
    bmAdm lam d β ∧ ∀ u, rCap K n n u (zcomp K n β G) = ((bmChi lam β u : ℤ) : K) • zcomp K n β G := by
  have hA := (bm_eig lam d G (bmK_mem_alt.1 hG).1 (bmK_mem_alt.1 hG).2 β hβ hmax).1
  refine ⟨hA, fun u => ?_⟩
  obtain ⟨b, rfl, hb, ha⟩ := branchingAdmissible_facts hA
  obtain ⟨f, hf, e⟩ := GlobalTheory.T.lastRow_top_component_dualWeyl_eq_monomial_mul K n lam G (bmK_mem_alt.1 hG).1 b hb hmax
  rw [e, rCap_lead, capDet_dualWeyl ha u hf, map_smul, mul_smul_comm, bmChi]
  simp only [Nat.cast_sub (hb _)]

theorem rCap_kill {lam sg : Fin n → ℕ} (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) (ℓ : List ℤ)
    (hℓ : ∀ u ∈ bmList lam sg, u ∈ ℓ) (G : BP K n) (hG : G ∈ bmW K n lam (∑ s, (lam s - sg s)))
    (h0 : zcomp K n (fun s => ((lam s - sg s : ℕ) : ℤ)) G = 0) : (ℓ.map (rCap K n n)).prod G = 0 :=
  bm_kill (zW n) omg (rCap K n n) (bmW K n lam (∑ s, (lam s - sg s))) (bmChi lam)
    (bmAdm lam (∑ s, (lam s - sg s))) (rCap_comm n n) (fun u β => zcomp_comm_rCap n β u) (fun u _ h => capelliDeterminantFirstRows_mem_bmW u h)
    (fun G hG β h1 h2 => rCap_top G hG β h1 h2) (bm_sep lam _) ℓ _
    (fun β h1 h2 => by
      obtain ⟨u, hu, e⟩ := bm_list_kills lam sg hI β h1 h2
      exact ⟨u, hℓ u hu, e⟩) G hG h0

theorem dual_tri {M : Type} [AddCommGroup M] [Module K M] (ψ : M →ₗ[K] K) : ∀ {m : ℕ} (g : Fin m → Module.End K M)
    (c : Fin m → K) (F : Fin m → Prop), (∀ k, F k → ∀ x, ψ (g k x) = c k * ψ x) →
    (∀ k, ¬ F k → (∀ j, j < k → F j) → ∀ x, ψ (g k x) = 0) → ∀ x,
    ((∀ k, F k) → ψ ((List.ofFn g).prod x) = (∏ k, c k) * ψ x) ∧ ((¬ ∀ k, F k) → ψ ((List.ofFn g).prod x) = 0) := by
  intro m
  induction m with
  | zero =>
    intro g c F _ _ x
    exact ⟨fun _ => by simp, fun h => absurd (fun k : Fin 0 => k.elim0) h⟩
  | succ m ih =>
    intro g c F h1 h2 x
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, Fin.prod_univ_succ]
    by_cases h0 : F 0
    · obtain ⟨ih1, ih2⟩ := ih (fun i : Fin m => g i.succ) (fun i => c i.succ) (fun i => F i.succ)
        (fun k hk => h1 _ hk) (fun k hk hj => h2 _ hk (fun j hkj => by
          induction j using Fin.cases with
          | zero => exact h0
          | succ j => exact hj j (Fin.succ_lt_succ_iff.1 hkj))) x
      rw [h1 0 h0]
      refine ⟨fun h => by rw [ih1 fun k => h _, mul_assoc], fun h => ?_⟩
      rw [ih2 fun h' => h fun k => Fin.cases h0 h' k, mul_zero]
    · exact ⟨fun h => absurd (h 0) h0, fun _ => h2 0 h0 (fun j hj => absurd hj (Fin.not_lt_zero j)) _⟩

theorem capDet_dual {M : Type} [AddCommGroup M] [Module K M] (E : Fin n → Fin n → Module.End K M) (u : ℤ)
    (ψ : M →ₗ[K] K) (μ : Fin n → ℤ) (hr : ∀ l j, l < j → ∀ x, ψ (E j l x) = 0)
    (hw : ∀ s x, ψ (E s s x) = ((μ s : ℤ) : K) * ψ x) (x : M) :
    ψ (capDet E u x) = ((∏ j : Fin n, (u + ((j : ℕ) : ℤ) - μ j) : ℤ) : K) * ψ x := by
  have key := fun α : Equiv.Perm (Fin n) => dual_tri ψ (fun k => bmF E u k (α k) k)
    (fun j => ((u + ((j : ℕ) : ℤ) - μ j : ℤ) : K)) (fun k => α k = k)
    (fun k hk x => by
      simp only [bmF, hk, if_true, LinearMap.sub_apply, Module.End.intCast_apply, map_sub, map_zsmul, hw, zsmul_eq_mul]
      push_cast; ring)
    (fun k hk hj x => by
      have hlt : k < α k := by
        rcases lt_trichotomy k (α k) with h | h | h
        · exact h
        · exact absurd h.symm hk
        · exact absurd (α.injective (hj _ h)) hk
      simp [bmF, hk, hr k _ hlt]) x
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [capDet, bmPi, bmM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul, id]
  rw [Finset.sum_eq_single 1]
  · rw [(key 1).1 fun _ => rfl]; simp
  · intro α _ hα
    rw [(key α).2 fun h => hα (Equiv.ext h), smul_zero]
  · simp

theorem rowGen_initMinor {r m s : ℕ} (a b : Fin r) (I : Fin s → Fin r) (hs : s ≤ m) (hI : Function.Injective I)
    (h : ∀ p, I p = b → ∃ p', p ≠ p' ∧ I p' = a) :
    rowGen K a b (initMinor K I hs) = Polynomial.C (initMinor K I hs) := by
  unfold initMinor
  rw [AlgHom.map_det, RingHom.map_det]
  by_cases hb : ∃ p, I p = b
  · obtain ⟨i, hi⟩ := hb
    obtain ⟨j, hij, hj⟩ := h i hi
    rw [← Matrix.det_updateRow_add_smul_self (Polynomial.C.mapMatrix _) hij Polynomial.X]
    congr 1
    ext1 p q
    by_cases hp : p = i
    · subst hp
      simp [rowGen_X, hi, hj]
    · have e1 : I p ≠ b := fun h' => hp (hI (h'.trans hi.symm))
      simp [Matrix.updateRow_apply, rowGen_X, hp, e1]
  · congr 1
    ext1 p q
    have e1 : I p ≠ b := fun h' => hb ⟨p, h'⟩
    simp [rowGen_X, e1]

theorem xi_raise (lam sg : Fin n → ℕ) (l j : Fin n) (h : l < j) : rE K n n l j (xiB K lam sg) = 0 := by
  have h' : l.val < j.val := h
  have key : rowGen K l.castSucc j.castSucc (xiB K lam sg) = Polynomial.C (xiB K lam sg) := by
    unfold xiB
    rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, rowGen_initMinor, rowGen_initMinor]
    · intro p q e
      have := p.2; have := q.2; have := i.2
      simp only [rowsB, Fin.ext_iff] at e ⊢
      split_ifs at e <;> simp at e <;> omega
    · intro p e
      have := p.2; have := i.2; have := j.2
      have hp : p.val = j.val ∧ p.val < i.val := by
        simp only [rowsB, Fin.ext_iff] at e
        split_ifs at e <;> simp at e <;> omega
      refine ⟨⟨l.val, by omega⟩, fun e' => ?_, ?_⟩
      · have := congrArg Fin.val e'
        simp at this; omega
      · simp only [rowsB]
        rw [if_pos (by omega)]; rfl
    · intro p q e
      simpa [rowsA, Fin.ext_iff] using e
    · intro p e
      have := p.2
      have hp : p.val = j.val := by simpa [rowsA, Fin.ext_iff] using e
      refine ⟨⟨l.val, by omega⟩, fun e' => ?_, rfl⟩
      have := congrArg Fin.val e'
      simp at this; omega
  rw [rE, (rowE_eq_rowDiv K _ _ _ _ _).1, rowDiv, key, Polynomial.coeff_C, if_neg one_ne_zero]

theorem zcomp_lift {lam b : Fin n → ℕ} {f : MvPolynomial (Fin n × Fin n) K} {G : BP K n} (h : bmLift K n lam b f G) :
    zcomp K n (fun s => (b s : ℤ)) G = zmon K n b * emb K n f := by
  have h1 := (bm_isLow_iff _ _).1 h.2.2 _ le_rfl
  rw [map_sub, sub_eq_zero] at h1
  rw [h1]
  exact (bmF_lead_WH K n b f).weightedHomogeneousComponent_same

theorem coeff_zcomp (β : Fin n → ℤ) (G : BP K n) (μ : Fin (n + 1) × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (zcomp K n β G) μ = if Finsupp.weight (zW n) μ = β then AddMonoidAlgebra.coeff G μ else 0 := by
  classical
  unfold zcomp
  rw [coeff_weightedHomogeneousComponent]

theorem fockB_zcomp (β : Fin n → ℤ) (G A : BP K n) (hA : IsWeightedHomogeneous (zW n) A β) :
    fockB G A = fockB (zcomp K n β G) A := by
  rw [← sub_eq_zero, ← fockBL_apply, ← fockBL_apply, ← LinearMap.sub_apply, ← map_sub]
  refine fockB_eq_zero _ _ fun μ hμ => ?_
  by_contra h0
  rw [coeff_sub, coeff_zcomp, if_pos (hA h0), sub_self] at hμ
  exact hμ rfl

theorem lead_inj (b : Fin n → ℕ) {f g : MvPolynomial (Fin n × Fin n) K}
    (h : zmon K n b * emb K n f = zmon K n b * emb K n g) : f = g := by
  have h0 : zmon K n b ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => pow_ne_zero _ (X_ne_zero _)
  exact rename_injective _ (fun v w e => Prod.ext (Fin.castSucc_injective n (Prod.mk.inj e).1) (Prod.mk.inj e).2)
    (mul_left_cancel₀ h0 h)

theorem chi_eq {lam sg : Fin n → ℕ} (hIL : bmIL lam sg) (u : ℤ) :
    bmChi lam (fun s => ((lam s - sg s : ℕ) : ℤ)) u = ∏ j : Fin n, (u + ((j : ℕ) : ℤ) - (sg j : ℤ)) := by
  refine Finset.prod_congr rfl fun j _ => ?_
  beta_reduce
  rw [Nat.cast_sub (hIL j).1]
  ring

theorem list_dual {M : Type} [AddCommGroup M] [Module K M] (C : ℤ → Module.End K M) (χ : ℤ → ℤ) (ψ : M →ₗ[K] K)
    (h : ∀ u x, ψ (C u x) = (χ u : K) * ψ x) (ℓ : List ℤ) (x : M) :
    ψ ((ℓ.map C).prod x) = (((ℓ.map χ).prod : ℤ) : K) * ψ x := by
  induction ℓ with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, h, ih, Int.cast_mul, mul_assoc]

theorem psi_eq_zero {lam sg : Fin n → ℕ} (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) (ψ : BP K n →ₗ[K] K)
    (hr : ∀ l j, l < j → ∀ x, ψ (rE K n n j l x) = 0)
    (hwt : ∀ a x, ψ (rowE K (n + 1) n a a x) = (bmRho lam sg a : K) * ψ x) (hxi : ψ (xiB K lam sg) = 0)
    (x : BP K n) (hx : x ∈ dualWeyl K (n + 1) n lam) : ψ x = 0 := by
  classical
  have hIL := bm_IL_of lam sg hI
  have hρ : ∀ s : Fin n, bmRho lam sg s.castSucc = sg s := fun s => by simp [bmRho]
  have hC : ∀ u x, ψ (rCap K n n u x) = ((bmChi lam (fun s => ((lam s - sg s : ℕ) : ℤ)) u : ℤ) : K) * ψ x := fun u x => by
    rw [chi_eq hIL]
    exact capDet_dual _ u ψ (fun s => (sg s : ℤ)) hr (fun s x => by rw [rE, hwt, hρ]; simp) x
  have hAdm : bmAdm lam (∑ s, (lam s - sg s)) fun s => ((lam s - sg s : ℕ) : ℤ) := by
    refine ⟨fun s => Int.natCast_nonneg _, by simp, ?_⟩
    simpa only [Nat.cast_sub (hIL _).1, sub_sub_cancel] using hI
  have key : ∀ (k : ℕ) (y : BP K n), y ∈ bmW K n lam (∑ s, (lam s - sg s)) →
      (∀ s, rE K n n s s y = (sg s : K) • y) → ∀ S : Finset (Fin n → ℤ), S.card ≤ k →
      (∀ β, zcomp K n β y ≠ 0 → β ∈ S) → ψ y = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro y hy hs S hS hsub
    by_cases h0 : y = 0
    · rw [h0, map_zero]
    obtain ⟨μ, hμ⟩ := ne_zero_iff.1 h0
    have hne : (S.filter fun β => zcomp K n β y ≠ 0).Nonempty := by
      have : zcomp K n (Finsupp.weight (zW n) μ) y ≠ 0 := ne_zero_iff.2 ⟨μ, by rw [coeff_zcomp, if_pos rfl]; exact hμ⟩
      exact ⟨_, Finset.mem_filter.2 ⟨hsub _ this, this⟩⟩
    obtain ⟨β, hβ, hmax⟩ := Finset.exists_max_image _ omg hne
    obtain ⟨hβS, hβ⟩ := Finset.mem_filter.1 hβ
    have hmax' : ∀ β', zcomp K n β' y ≠ 0 → omg β' ≤ omg β := fun β' h => hmax β' (Finset.mem_filter.2 ⟨hsub _ h, h⟩)
    by_cases hb : β = fun s => ((lam s - sg s : ℕ) : ℤ)
    · subst hb
      obtain ⟨f, hf, e⟩ := GlobalTheory.T.lastRow_top_component_dualWeyl_eq_monomial_mul K n lam y (bmK_mem_alt.1 hy).1 (fun s => lam s - sg s) (fun s => Nat.sub_le _ _) hmax'
      simp only [Nat.sub_sub_self (hIL _).1] at hf
      have hfw : IsWeightedHomogeneous (rowW n n) f sg := (rowWeight_iff _ _).2 fun s => by
        refine lead_inj (fun s => lam s - sg s) ?_
        rw [← rE_lead, map_smul, mul_smul_comm, ← e, ← Module.End.mul_apply, ← (zcomp_comm_rE n _ s s).eq,
          Module.End.mul_apply, hs, map_smul]
      obtain ⟨a, ha⟩ : ∃ a : K, f = a • hw K le_rfl sg :=
        ⟨_, GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight K n sg (bmK_antitone lam sg hIL) f hf hfw⟩
      have hl := bmLift_xi (R := K) lam sg hIL
      have hk := rCap_kill hI (bmList lam sg) (fun _ h => h) (y - a • xiB K lam sg)
        (Submodule.sub_mem _ hy (Submodule.smul_mem _ _ (bmK_liftW hl)))
        (by rw [map_sub, map_smul, e, zcomp_lift hl, ha, map_smul, mul_smul_comm, sub_self])
      have h1 := list_dual _ _ ψ hC (bmList lam sg) (y - a • xiB K lam sg)
      rw [hk, map_zero, bm_list_prod lam sg hI, map_sub, map_smul, hxi, smul_zero, sub_zero] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left (Int.cast_ne_zero.2 (capConst n _ _ hI).1)
    · obtain ⟨hA, hE⟩ := rCap_top y hy β hβ hmax'
      obtain ⟨u, hu⟩ := bm_sep lam _ _ _ hA hAdm hb
      have hcard := Finset.card_erase_lt_of_mem hβS
      have h1 := ih (S.erase β).card (by omega) (rCap K n n u y - ((bmChi lam β u : ℤ) : K) • y)
        (Submodule.sub_mem _ (capelliDeterminantFirstRows_mem_bmW u hy) (Submodule.smul_mem _ _ hy))
        (fun s => by
          rw [map_sub, map_smul, ← Module.End.mul_apply, (rE_comm_rCap n n u s s).eq, Module.End.mul_apply, hs, map_smul,
            smul_sub, smul_comm])
        (S.erase β) le_rfl (fun β' h => by
          rw [map_sub, map_smul, ← Module.End.mul_apply, (zcomp_comm_rCap n β' u).eq, Module.End.mul_apply] at h
          refine Finset.mem_erase.2 ⟨fun e => h ?_, hsub _ fun e => h ?_⟩
          · rw [e, hE, sub_self]
          · rw [e, map_zero, smul_zero, sub_zero])
      rw [map_sub, map_smul, hC, smul_eq_mul, ← sub_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 fun e => hu (Int.cast_injective e).symm)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sum_weightedHomogeneousComponent (rowW (n + 1) n) x,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp (w := rowW (n + 1) n) x), map_sum]
  refine Finset.sum_eq_zero fun ρ _ => ?_
  have hy := (rowWeight_iff ρ _).1 (weightedHomogeneousComponent_isWeightedHomogeneous (w := rowW (n + 1) n) ρ x)
  have hm := dualWeylRowGraded K (n + 1) n lam ρ x hx
  by_cases hρ' : ρ = bmRho lam sg
  · subst hρ'
    refine key _ _ (bmK_mem_alt.2 ⟨hm, fun μ hμ => ?_⟩) (fun s => by rw [rE, hy, hρ])
      ((weightedHomogeneousComponent (rowW (n + 1) n) (bmRho lam sg) x).support.image (Finsupp.weight (zW n))) le_rfl
      fun β h => ?_
    · rw [bm_weight_lastW, ← bm_weight_rowW,
        weightedHomogeneousComponent_isWeightedHomogeneous (w := rowW (n + 1) n) _ x hμ]
      simp [bmRho]
    · obtain ⟨μ, hμ⟩ := ne_zero_iff.1 h
      rw [coeff_zcomp] at hμ
      split_ifs at hμ with e
      · exact Finset.mem_image.2 ⟨μ, mem_support_iff.2 hμ, e⟩
      · exact absurd rfl hμ
  · obtain ⟨a, ha⟩ := Function.ne_iff.1 hρ'
    have h1 := hwt a (weightedHomogeneousComponent (rowW (n + 1) n) ρ x)
    rw [hy, map_smul, smul_eq_mul, ← sub_eq_zero, ← sub_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 fun e => ha (Nat.cast_injective e))

theorem fock_xi {lam sg : Fin n → ℕ} (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) (x : BP K n)
    (hx : x ∈ dualWeyl K (n + 1) n lam) :
    fockB x (xiB K lam sg) * (fockB (hw K le_rfl sg) (hw K le_rfl sg) * (bfact fun s => lam s - sg s : K)) =
      fockB (xiB K lam sg) (xiB K lam sg) * fockB x (zmon K n (fun s => lam s - sg s) * emb K n (hw K le_rfl sg)) := by
  have hIL := bm_IL_of lam sg hI
  have hl := bmLift_xi (R := K) lam sg hIL
  have hw1 := bm_xi_row (R := K) lam sg hIL
  have hw2 : IsWeightedHomogeneous (rowW (n + 1) n) (zmon K n (fun s => lam s - sg s) * emb K n (hw K le_rfl sg))
      (bmRho lam sg) := fun μ hμ => by
    rw [← zcomp_lift hl, coeff_zcomp] at hμ
    split_ifs at hμ
    · exact hw1 hμ
    · exact absurd rfl hμ
  have h := psi_eq_zero hI
    ((fockB (hw K le_rfl sg) (hw K le_rfl sg) * (bfact fun s => lam s - sg s : K)) • fockBL.flip (xiB K lam sg) -
      fockB (xiB K lam sg) (xiB K lam sg) • fockBL.flip (zmon K n (fun s => lam s - sg s) * emb K n (hw K le_rfl sg)))
    (fun l j hlj x => by
      have h1 := xi_raise (K := K) lam sg l j hlj
      have h2 := rE_lead n l j (fun s => lam s - sg s) (hw K le_rfl sg)
      rw [hw_raise sg l j hlj, map_zero, mul_zero] at h2
      simp only [rE] at h1 h2
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.flip_apply, fockBL_apply, rE, fockB_rowE, h1, h2]
      simp [← fockBL_apply])
    (fun a x => by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.flip_apply, fockBL_apply, fockB_rowE,
        (rowWeight_iff _ _).1 hw1 a, (rowWeight_iff _ _).1 hw2 a]
      simp only [← fockBL_apply, map_smul, smul_eq_mul]
      ring)
    (by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.flip_apply, fockBL_apply, smul_eq_mul]
      rw [fockB_zcomp _ _ _ (bmF_lead_WH K n _ _), zcomp_lift hl, (_root_.GlobalTheory.BrCoefFock.fockB_zmon_emb K n _).2]
      ring) x hx
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.flip_apply, fockBL_apply, smul_eq_mul] at h
  linear_combination h

end Core

section One

open GlobalTheory.IndefiniteRowSideFullHecke _root_.Formalism.L2.Col

variable {K : Type} [Field K] {n : ℕ}

theorem detShift_succ (lam : DomWeight (n + 1)) : lam.detShift = lam.w (Fin.last n) := by
  unfold DomWeight.detShift
  rw [dite_eq_left (Nat.succ_pos n)]
  rfl

end One

section Tensor

open GlobalTheory.IndefiniteRowSideFullHecke _root_.Formalism.L2.Col Formalism.L2.Col.Br GlobalTheory.BranchFormula
open scoped Pointwise

theorem coeff_prod_rename {A ι : Type} [CommRing A] [Fintype ι] {n : ℕ} (b : ι → Fin n → ℕ)
    (P : ι → MvPolynomial (Unit × Fin n) A) :
    AddMonoidAlgebra.coeff (∏ τ, rename (fun p : Unit × Fin n => (τ, p.2)) (P τ)) (expOf b) =
      ∏ τ, AddMonoidAlgebra.coeff (P τ) (expOf fun _ : Unit => b τ) := by
  classical
  have hinj : ∀ τ : ι, Function.Injective (fun p : Unit × Fin n => (τ, p.2)) :=
    fun τ p q h => Prod.ext rfl (Prod.mk.inj h).2
  have h1 : ∀ τ, rename (fun p : Unit × Fin n => (τ, p.2)) (P τ) =
      ∑ m ∈ (P τ).support, monomial (m.mapDomain fun p : Unit × Fin n => (τ, p.2)) (AddMonoidAlgebra.coeff (P τ) m) := by
    intro τ
    conv_lhs => rw [(P τ).as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, rename_monomial]
  have h2 : ∀ τ, AddMonoidAlgebra.coeff (P τ) (expOf fun _ : Unit => b τ) =
      ∑ m ∈ (P τ).support, if m = expOf (fun _ : Unit => b τ) then AddMonoidAlgebra.coeff (P τ) m else 0 := by
    intro τ
    conv_lhs => rw [(P τ).as_sum]
    simp only [coeff_sum, coeff_monomial]
  simp only [h1]
  rw [Finset.prod_congr rfl fun τ _ => h2 τ, Finset.prod_univ_sum, Finset.prod_univ_sum, coeff_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← monomial_sum_prod, coeff_monomial, Finset.prod_ite_zero]
  have h3 : ∀ τ s, (∑ τ', (p τ').mapDomain fun q : Unit × Fin n => (τ', q.2)) (τ, s) = p τ ((), s) := by
    intro τ s
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single τ]
    · exact Finsupp.mapDomain_apply_of_injective (hinj τ) (p τ) ((), s)
    · intro τ' _ h
      refine Finsupp.mapDomain_of_notMem_range _ _ ?_
      rintro ⟨q, hq⟩
      exact h (Prod.mk.inj hq).1
    · simp
  congr 1
  apply propext
  constructor
  · intro h τ _
    ext q
    rw [← h3 τ q.2, h]
    rfl
  · intro h
    ext q
    rw [h3 q.1 q.2, h q.1 (Finset.mem_univ _)]
    rfl

theorem splitLast_blockEmb {K ι : Type} [Field K] {N n : ℕ} (hN : N = n + 1) (τ : ι) (f : MvPolynomial (Fin N × Fin N) K) :
    splitLast K ι hN (Formalism.GradedWeylDivisibility.blockEmb K τ f) =
      rename (fun p : Unit × Fin n => (τ, p.2))
        (map (rename (R := K) (fun v : Unit × Fin n × Fin n => (τ, v.2))).toRingHom
          (splitLast K Unit hN (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N)) f))) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp only [Formalism.GradedWeylDivisibility.blockEmb, rename_C, splitLast_C, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    have : splitLast K ι hN (Formalism.GradedWeylDivisibility.blockEmb K τ (X v)) =
      rename (fun p : Unit × Fin n => (τ, p.2))
        (map (rename (R := K) (fun v : Unit × Fin n × Fin n => (τ, v.2))).toRingHom
          (splitLast K Unit hN (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N)) (X v)))) := by
      obtain ⟨a, s⟩ := v
      rw [fk_blockEmb_X, rename_X]
      rcases cases_idx hN s with rfl | ⟨s, rfl⟩
      · simp only [splitLast_X_lastCol, map_zero]
      · rcases cases_idx hN a with rfl | ⟨a, rfl⟩
        · simp only [splitLast_X_lastRow, map_X, rename_X]
        · simp only [splitLast_X_up, map_C, rename_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X]
    rw [map_mul, map_mul, hp, this, map_mul, map_mul, map_mul, map_mul]

theorem coefLast_ten {K ι : Type} [Field K] [Fintype ι] {N n : ℕ} (hN : N = n + 1) (b : ι → Fin n → ℕ)
    (f : ι → MvPolynomial (Fin N × Fin N) K) :
    coefLast hN b (ten f) = ten fun τ => rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n)
      (coefLast hN (fun _ : Unit => b τ) (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N)) (f τ))) := by
  rw [coefLast_eq_coeff, ten, ten, map_prod]
  simp only [splitLast_blockEmb]
  rw [coeff_prod_rename]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [coeff_map, coefLast_eq_coeff, Formalism.GradedWeylDivisibility.blockEmb, rename_rename]
  rfl

theorem fockB_ten {K ι : Type} [Field K] [Fintype ι] {n : ℕ} (f g : ι → MvPolynomial (Fin n × Fin n) K) :
    fockB (ten f) (ten g) = ∏ τ, fockB (f τ) (g τ) :=
  @fockSymTensor_holds K _ starRingOfComm ι _ n f g

variable {K : Type} [Field K] [CharZero K] {n : ℕ} {ι : Type} [Fintype ι]
  {lam : ι → DomWeight (n + 1)} {sg : ι → DomWeight n}

theorem fock_extremal_ne (w : DomWeight n) : fockB (extremal K n w) (extremal K n w) ≠ 0 := by
  simpa [extNormB] using pb_extNormB_ne K (fun _ : Unit => w)

end Tensor

section Compare

open GlobalTheory.IndefiniteRowSideFullHecke _root_.Formalism.L2.Col Formalism.L2.Col.Br GlobalTheory.BranchFormula NumberField IsDedekindDomain

theorem interlace_iff {n : ℕ} (lam : DomWeight (n + 1)) (sg : DomWeight n) :
    Br.Interlace rfl lam sg ↔ InterlacingNumerators.Interlace lam sg := by
  refine forall_congr' fun i => ?_
  change 0 ≤ sg.w i - lam.w i.succ ∧ 0 ≤ lam.w i.castSucc - sg.w i ↔ _
  omega

theorem sameShift_iff {n : ℕ} (lam : DomWeight (n + 1)) (sg : DomWeight n) :
    SameShift lam sg ↔ InterlacingNumerators.EqualLast lam sg ∧ (n = 0 → lam.w (Fin.last n) = 0) := by
  unfold SameShift InterlacingNumerators.EqualLast
  rw [detShift_succ]
  unfold DomWeight.detShift
  split_ifs with h
  · refine ⟨fun e => ⟨fun i hi => ?_, by omega⟩, fun e => e.1 _ (by simp only; omega)⟩
    rw [← e]
    congr 1
    exact Fin.ext (by simp only; omega)
  · exact ⟨fun e => ⟨fun i _ => absurd i.pos h, fun _ => e.symm⟩, fun e => (e.2 (by omega)).symm⟩

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

omit [NumberField K] in
theorem exists_block (B : GL (Fin n) K) {t : K} (ht : t ≠ 0) : ∃ B' : GL (Fin (n + 1)) K,
    IsBlock rfl (B' : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (B : Matrix (Fin n) (Fin n) K) t := by
  have h : IsBlock rfl (Matrix.of fun a b : Fin (n + 1) => if h : a.val < n ∧ b.val < n then
      (B : Matrix (Fin n) (Fin n) K) ⟨a.val, h.1⟩ ⟨b.val, h.2⟩ else if a = b then t else 0)
      (B : Matrix (Fin n) (Fin n) K) t := by
    refine ⟨fun a b => by simp [iC], fun a => ⟨?_, ?_⟩, by simp [iL]⟩
    · have := a.2
      simp [iC, iL, Fin.ext_iff]; omega
    · have := a.2
      simp [iC, iL, Fin.ext_iff]; omega
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (by
    rw [h.det]; exact mul_ne_zero (Matrix.GeneralLinearGroup.det B).ne_zero ht), h⟩


end Compare

end GlobalTheory.BrCompare
