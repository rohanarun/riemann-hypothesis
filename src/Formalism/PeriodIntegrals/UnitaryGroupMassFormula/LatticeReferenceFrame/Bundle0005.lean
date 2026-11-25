module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.HGZeroRight
section
noncomputable section

open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk

namespace PI.ScRefExists.WB

variable (I : Formalism.MainNotions.S.AutInst)

theorem hG_def (x y : Fin I.n → I.E) : hG I x y = ∑ i, ∑ j, star (x i) * I.J i j * y j := rfl

theorem hG_add_right (x y z : Fin I.n → I.E) : hG I x (y + z) = hG I x y + hG I x z := by
  simp only [hG_def, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hG_smul_right (c : I.E) (x y : Fin I.n → I.E) : hG I x (c • y) = c * hG I x y := by
  simp only [hG_def, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hG_zero_right (x : Fin I.n → I.E) : hG I x 0 = 0 := by simp [hG_def]

theorem J_entry (i j : Fin I.n) : star (I.J j i) = I.J i j := by
  have h := congrFun (congrFun I.J_herm i) j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, starRingEnd_apply] at h
  exact h

theorem hG_symm (x y : Fin I.n → I.E) : hG I y x = star (hG I x y) := by
  simp only [hG_def, star_sum, star_mul', star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [J_entry]
  ring

variable {I}

end PI.ScRefExists.WB
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.MemLAOfNsmul
section
noncomputable section

open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk

namespace PI.ScRefExists.WF

variable {I : Formalism.MainNotions.S.AutInst} {p : ℕ}

theorem ap_smul (a : Ap I p) (v : Fin I.n → I.E) : a • v = (a : I.E) • v := rfl

theorem osmul (o : 𝓞 I.E) (v : Fin I.n → I.E) : o • v = (o : I.E) • v :=
  (algebraMap_smul I.E o v).symm

theorem hG_L {x y : Fin I.n → I.E} (hx : x ∈ I.L) (hy : y ∈ I.L) :
    hG I x y ∈ (algebraMap (𝓞 I.E) I.E).range := by
  unfold hG
  exact (I.L_dual y).mp hy x hx

theorem natsmul_mem_L {s : ℕ} {x : Fin I.n → I.E} (hx : x ∈ I.L) : (s : I.E) • x ∈ I.L := by
  have h1 : ((s : 𝓞 I.E) : I.E) = (s : I.E) := by simp
  rw [← h1, ← osmul]
  exact I.L.smul_mem _ hx

theorem mem_LA_iff (hp : p.Prime) {x : Fin I.n → I.E} :
    x ∈ LA I p ↔ ∃ s : ℕ, Nat.Coprime s p ∧ (s : I.E) • x ∈ I.L := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, Nat.coprime_one_left p, by simpa using hx⟩
    | zero => exact ⟨1, Nat.coprime_one_left p, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨t, ht, hty⟩ := hy
      refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
      have : ((s * t : ℕ) : I.E) • (x + y) = (t : I.E) • ((s : I.E) • x) + (s : I.E) • ((t : I.E) • y) := by
        push_cast; module
      rw [this]
      exact I.L.add_mem (natsmul_mem_L hsx) (natsmul_mem_L hty)
    | smul a x _ hx =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨s0, hs0, a0, ha0⟩ := a.2
      refine ⟨s0 * s, Nat.Coprime.mul_left hs0 hs, ?_⟩
      have : ((s0 * s : ℕ) : I.E) • (a • x) = a0 • ((s : I.E) • x) := by
        rw [ap_smul, osmul, ← ha0]; push_cast; module
      rw [this]
      exact I.L.smul_mem _ hsx
  · rintro ⟨s, hs, hsx⟩
    have hsA : ((s : I.E))⁻¹ ∈ Ap I p := inv_mem_Ap hp hs
    have hs0 : (s : I.E) ≠ 0 := by
      have : s ≠ 0 := by
        rintro rfl
        exact hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp hs)
      exact_mod_cast this
    have : x = (⟨_, hsA⟩ : Ap I p) • ((s : I.E) • x) := by
      rw [ap_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)

theorem L_le_LA {x : Fin I.n → I.E} (hx : x ∈ I.L) : x ∈ LA I p := Submodule.subset_span hx

theorem hG_LA (hp : p.Prime) {x y : Fin I.n → I.E} (hx : x ∈ LA I p) (hy : y ∈ LA I p) :
    hG I x y ∈ Ap I p := by
  obtain ⟨s, hs, hsx⟩ := (mem_LA_iff hp).1 hx
  obtain ⟨t, ht, hty⟩ := (mem_LA_iff hp).1 hy
  obtain ⟨o, ho⟩ := hG_L hsx hty
  refine ⟨s * t, Nat.Coprime.mul_left hs ht, o, ?_⟩
  rw [hG_smul_left, hG_smul_right, star_natCast] at ho
  rw [show ((o : 𝓞 I.E) : I.E) = algebraMap (𝓞 I.E) I.E o from rfl, ho]; push_cast; ring

theorem dual_LA (hp : p.Prime) {x : Fin I.n → I.E} (hx : ∀ y ∈ I.L, hG I y x ∈ Ap I p) : x ∈ LA I p := by
  classical
  obtain ⟨T, hT⟩ := I.L_fg
  have hden : ∀ t ∈ T, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * hG I t x = (a : I.E) := by
    intro t ht
    exact hx t (hT ▸ Submodule.subset_span ht)
  choose! s hs a ha using hden
  let S : ℕ := ∏ t ∈ T, s t
  have hS : Nat.Coprime S p := Nat.Coprime.prod_left fun t ht => hs t ht
  have key : ∀ y ∈ I.L, hG I y ((S : I.E) • x) ∈ (algebraMap (𝓞 I.E) I.E).range := by
    intro y hy
    rw [← hT] at hy
    induction hy using Submodule.span_induction with
    | mem t ht =>
      have hdvd : s t ∣ S := Finset.dvd_prod_of_mem s ht
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨(c : 𝓞 I.E) * a t, ?_⟩
      rw [hG_smul_right, hc]; push_cast
      rw [mul_comm ((s t : ℕ) : I.E), mul_assoc, ha t ht]
    | zero => exact ⟨0, by simp [hG_zero_left]⟩
    | add y z _ _ hy hz =>
      obtain ⟨o1, h1⟩ := hy; obtain ⟨o2, h2⟩ := hz
      exact ⟨o1 + o2, by rw [hG_add_left, ← h1, ← h2]; simp⟩
    | smul o y _ hy =>
      obtain ⟨o1, h1⟩ := hy
      refine ⟨PI.ScRefExists.TH.sg I o * o1, ?_⟩
      rw [osmul, hG_smul_left, ← h1]; simp [PI.ScRefExists.TH.sg_coe]
  have hSx : (S : I.E) • x ∈ I.L := (I.L_dual _).2 key
  exact (mem_LA_iff hp).2 ⟨S, hS, hSx⟩

theorem mem_LA_of_nsmul (hp : p.Prime) {M : ℕ} (hM : Nat.Coprime M p) {x : Fin I.n → I.E}
    (hx : M • x ∈ I.L) : x ∈ LA I p := by
  refine (mem_LA_iff hp).2 ⟨M, hM, ?_⟩
  rwa [← Nat.cast_smul_eq_nsmul I.E] at hx

def proj {r : ℕ} (e f : Fin r → Fin I.n → I.E) (y : Fin I.n → I.E) : Fin I.n → I.E :=
  ∑ a, (hG I (f a) y • e a + hG I (e a) y • f a)

theorem hG_e_proj {r : ℕ} {e f : Fin r → Fin I.n → I.E} (he : ∀ a b, hG I (e a) (e b) = 0)
    (hef : ∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) (b : Fin r) (y : Fin I.n → I.E) :
    hG I (e b) (proj e f y) = hG I (e b) y := by
  have hr : ∀ (x : Fin I.n → I.E) (c : Fin r → I.E) (w : Fin r → Fin I.n → I.E),
      hG I x (∑ a, c a • w a) = ∑ a, c a * hG I x (w a) := by
    intro x c w
    unfold hG Formalism.UG.hform
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  have hadd2 : ∀ x u w : Fin I.n → I.E, hG I x (u + w) = hG I x u + hG I x w := by
    intro x u w
    unfold hG Formalism.UG.hform
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  unfold proj
  rw [Finset.sum_add_distrib, hadd2, hr, hr]
  simp only [he, hef]
  simp

theorem hG_f_proj {r : ℕ} {e f : Fin r → Fin I.n → I.E} (hf : ∀ a b, hG I (f a) (f b) = 0)
    (hef : ∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) (b : Fin r) (y : Fin I.n → I.E) :
    hG I (f b) (proj e f y) = hG I (f b) y := by
  have hr : ∀ (x : Fin I.n → I.E) (c : Fin r → I.E) (w : Fin r → Fin I.n → I.E),
      hG I x (∑ a, c a • w a) = ∑ a, c a * hG I x (w a) := by
    intro x c w
    unfold hG Formalism.UG.hform
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  have hadd2 : ∀ x u w : Fin I.n → I.E, hG I x (u + w) = hG I x u + hG I x w := by
    intro x u w
    unfold hG Formalism.UG.hform
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hJ : ∀ i j, starRingEnd I.E (I.J i j) = I.J j i := by
    intro i j
    have := congrFun (congrFun I.J_herm j) i
    simpa [Formalism.UG.cT] using this
  have hsym : ∀ x y, hG I y x = starRingEnd I.E (hG I x y) := by
    intro x y
    unfold hG Formalism.UG.hform
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, starRingEnd_self_apply, hJ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have h1 : ∀ a, hG I (f b) (e a) = if a = b then 1 else 0 := by
    intro a
    rw [hsym (e a) (f b), hef]
    split_ifs <;> simp
  unfold proj
  rw [Finset.sum_add_distrib, hadd2, hr, hr]
  simp only [hf, h1]
  simp

theorem proj_mem (hp : p.Prime) {r : ℕ} {e f : Fin r → Fin I.n → I.E}
    (heA : ∀ a, e a ∈ LA I p) (hfA : ∀ a, f a ∈ LA I p) {y : Fin I.n → I.E} (hy : y ∈ LA I p) :
    proj e f y ∈ LA I p := by
  unfold proj
  refine Submodule.sum_mem _ fun a _ => Submodule.add_mem _ ?_ ?_
  · have h1 := Submodule.smul_mem (LA I p) (⟨hG I (f a) y, hG_LA hp (hfA a) hy⟩ : Ap I p) (heA a)
    rwa [ap_smul] at h1
  · have h1 := Submodule.smul_mem (LA I p) (⟨hG I (e a) y, hG_LA hp (heA a) hy⟩ : Ap I p) (hfA a)
    rwa [ap_smul] at h1

theorem proj_span {r : ℕ} (e f : Fin r → Fin I.n → I.E) (hp : p.Prime)
    (heA : ∀ a, e a ∈ LA I p) (hfA : ∀ a, f a ∈ LA I p) {y : Fin I.n → I.E} (hy : y ∈ LA I p)
    (S : Set (Fin I.n → I.E)) (hS : Set.range e ∪ Set.range f ⊆ S) :
    proj e f y ∈ Submodule.span (Ap I p) S := by
  unfold proj
  refine Submodule.sum_mem _ fun a _ => Submodule.add_mem _ ?_ ?_
  · have h1 := Submodule.smul_mem (Submodule.span (Ap I p) S)
      (⟨hG I (f a) y, hG_LA hp (hfA a) hy⟩ : Ap I p)
      (Submodule.subset_span (hS (Or.inl ⟨a, rfl⟩)))
    rwa [ap_smul] at h1
  · have h1 := Submodule.smul_mem (Submodule.span (Ap I p) S)
      (⟨hG I (e a) y, hG_LA hp (heA a) hy⟩ : Ap I p)
      (Submodule.subset_span (hS (Or.inr ⟨a, rfl⟩)))
    rwa [ap_smul] at h1

end PI.ScRefExists.WF
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.SpanSmulInto
section
noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain

namespace PI.ScRefExists.PPA

open PI.ScRefExists.Sk

variable (I : Formalism.MainNotions.S.AutInst)

theorem GE_star (g : ℕ) {x : I.E} (h : GE I g x) : GE I g (star x) := by
  obtain ⟨t, ht⟩ := h
  have hint : IsIntegral ℤ (starRingEnd I.E (t : I.E)) := by
    first
    | exact (RingOfIntegers.isIntegral_coe t).map (starRingEnd I.E).toIntAlgHom
    | exact (t.2).map (starRingEnd I.E).toIntAlgHom
  refine ⟨⟨starRingEnd I.E (t : I.E), hint⟩, ?_⟩
  rw [ht]
  first
  | (rw [star_mul', star_natCast]; rfl)
  | simp [star_mul']

theorem span_part (p m r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M T : ℕ)
    (w wd : Fin (k + 1) → Fin I.n → I.E)
    (hM : Nat.Coprime M p) (hM0 : (M : I.E) ≠ 0) (hT : Nat.Coprime T p) (hT0 : (T : I.E) ≠ 0)
    (hθ1 : GE I (p ^ m) ((θ : I.E) * θ - θ)) (hθ2 : GE I (p ^ m) ((θ : I.E) * star (θ : I.E)))
    (hθ3 : GE I (p ^ m) (1 - (θ : I.E) - star (θ : I.E)))
    (hw : ∀ i, w i ∈ LA I p ∧ wd i ∈ LA I p)
    (hspan : ∀ y ∈ I.L, y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) ∧
        y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd))
    (Sset : Set (Fin I.n → I.E))
    (hSe : ∀ a, M • e a ∈ Sset) (hSf : ∀ a, M • f a ∈ Sset)
    (hSz : (T : I.E) • ((θ : I.E) • w (Fin.last k) - star (θ : I.E) • wd (Fin.last k)) ∈ Sset)
    (hSb : ∀ i : Fin k, (θ : I.E) • ((T : I.E) • w i.castSucc) ∈ Sset)
    (hSbd : ∀ i : Fin k, star (θ : I.E) • ((T : I.E) • wd i.castSucc) ∈ Sset) :
    ∀ y ∈ I.L, y ∈ Submodule.span (𝓞 I.E) Sset ⊔ gL I (p ^ m) := by
  classical
  set N : Submodule (𝓞 I.E) (Fin I.n → I.E) := Submodule.span (𝓞 I.E) Sset ⊔ gL I (p ^ m) with hN
  have hsm : ∀ (c : 𝓞 I.E) (v : Fin I.n → I.E), c • v = (c : I.E) • v := fun c v => rfl
  have hS : ∀ v ∈ Sset, v ∈ N := fun v hv => Submodule.mem_sup_left (Submodule.subset_span hv)
  have hE : ∀ (c : 𝓞 I.E) (v : Fin I.n → I.E), v ∈ N → (c : I.E) • v ∈ N := fun c v hv => by
    rw [← hsm]
    exact N.smul_mem c hv
  have hnat : ∀ (s : ℕ) (v : Fin I.n → I.E), v ∈ N → (s : I.E) • v ∈ N := fun s v hv => by
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hv s
  have hgl : ∀ x ∈ I.L, ∀ t : 𝓞 I.E, (((p ^ m : ℕ) : I.E) * (t : I.E)) • x ∈ N := by
    intro x hx t
    have h1 : ((p ^ m : ℕ) : I.E) • x ∈ N :=
      Submodule.mem_sup_right (Submodule.subset_span ⟨x, hx, rfl⟩)
    rw [mul_comm, mul_smul]
    exact hE t _ h1
  have hbez : ∀ z ∈ I.L, ∀ s : ℕ, Nat.Coprime s p → (s : I.E) • z ∈ N → z ∈ N := by
    intro z hz s hs hsz
    have hcop : IsCoprime (s : ℤ) ((p ^ m : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_right m hs)
    obtain ⟨u, v, huv⟩ := hcop
    have hpz : ((p ^ m : ℕ) : I.E) • z ∈ N :=
      Submodule.mem_sup_right (Submodule.subset_span ⟨z, hz, rfl⟩)
    have hc : (u : I.E) * (s : I.E) + (v : I.E) * ((p ^ m : ℕ) : I.E) = 1 := by
      have h := congrArg (Int.cast : ℤ → I.E) huv
      push_cast at h ⊢
      linear_combination h
    have e : z = u • ((s : I.E) • z) + v • (((p ^ m : ℕ) : I.E) • z) := by
      rw [← Int.cast_smul_eq_zsmul I.E u, ← Int.cast_smul_eq_zsmul I.E v, smul_smul, smul_smul,
        ← add_smul, hc, one_smul]
    rw [e]
    exact N.add_mem (zsmul_mem hsz u) (zsmul_mem hpz v)
  have hclr : ∀ v ∈ LA I p, ∃ s : ℕ, Nat.Coprime s p ∧ (s : I.E) • v ∈ I.L := by
    intro v hv
    obtain ⟨s, hs, h⟩ := span_clear I p (I.L : Set (Fin I.n → I.E)) hv
    exact ⟨s, hs, by rwa [Submodule.span_eq] at h⟩
  have gen : ∀ (φ φ' : 𝓞 I.E) (u u' : Fin (k + 1) → Fin I.n → I.E),
      (∀ i, u i ∈ LA I p) → (∀ i, u' i ∈ LA I p) →
      (∀ i : Fin k, (φ : I.E) • ((T : I.E) • u i.castSucc) ∈ Sset) →
      (T : I.E) • ((φ : I.E) • u (Fin.last k) - (φ' : I.E) • u' (Fin.last k)) ∈ N →
      GE I (p ^ m) ((φ : I.E) * φ - φ) → GE I (p ^ m) ((φ : I.E) * φ') →
      ∀ y ∈ I.L, y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range u) →
        (φ : I.E) • y ∈ N := by
    intro φ φ' u u' hu hu' hSu hz h1 h2 y hy hyA
    obtain ⟨s2, hs2, hs2L⟩ := hclr _ (hu (Fin.last k))
    obtain ⟨s3, hs3, hs3L⟩ := hclr _ (hu' (Fin.last k))
    obtain ⟨t1, ht1⟩ := h1
    obtain ⟨t2, ht2⟩ := h2
    obtain ⟨s1, hs1, hs1y⟩ := span_clear I p _ hyA
    have key : ∀ v ∈ Submodule.span (𝓞 I.E) (Set.range e ∪ Set.range f ∪ Set.range u),
        ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • v) ∈ N := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        rcases hv with (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨i, rfl⟩
        · have h := hS _ (hSe a)
          rw [← Nat.cast_smul_eq_nsmul I.E] at h
          have e1 : ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • e a) =
              ((T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • ((M : I.E) • e a)) := by
            simp only [smul_smul]
            congr 1
            push_cast
            ring
          rw [e1]
          exact hnat _ _ (hE φ _ h)
        · have h := hS _ (hSf a)
          rw [← Nat.cast_smul_eq_nsmul I.E] at h
          have e1 : ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • f a) =
              ((T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • ((M : I.E) • f a)) := by
            simp only [smul_smul]
            congr 1
            push_cast
            ring
          rw [e1]
          exact hnat _ _ (hE φ _ h)
        · cases i using Fin.lastCases with
          | last =>
            have hA : ((M * s2 * s3 : ℕ) : I.E) •
                ((φ : I.E) • ((T : I.E) • ((φ : I.E) • u (Fin.last k) - (φ' : I.E) • u' (Fin.last k)))) ∈ N :=
              hnat _ _ (hE φ _ hz)
            have hB : ((M * s3 * T : ℕ) : I.E) • ((((p ^ m : ℕ) : I.E) * (t1 : I.E)) •
                ((s2 : I.E) • u (Fin.last k))) ∈ N := hnat _ _ (hgl _ hs2L t1)
            have hC : ((M * s2 * T : ℕ) : I.E) • ((((p ^ m : ℕ) : I.E) * (t2 : I.E)) •
                ((s3 : I.E) • u' (Fin.last k))) ∈ N := hnat _ _ (hgl _ hs3L t2)
            have e1 : ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • u (Fin.last k)) =
                ((M * s2 * s3 : ℕ) : I.E) •
                  ((φ : I.E) • ((T : I.E) • ((φ : I.E) • u (Fin.last k) - (φ' : I.E) • u' (Fin.last k)))) -
                ((M * s3 * T : ℕ) : I.E) • ((((p ^ m : ℕ) : I.E) * (t1 : I.E)) •
                  ((s2 : I.E) • u (Fin.last k))) +
                ((M * s2 * T : ℕ) : I.E) • ((((p ^ m : ℕ) : I.E) * (t2 : I.E)) •
                  ((s3 : I.E) • u' (Fin.last k))) := by
              rw [← ht1, ← ht2]
              funext i
              simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
              push_cast
              ring
            rw [e1]
            exact N.add_mem (N.sub_mem hA hB) hC
          | cast j =>
            have h := hS _ (hSu j)
            have e1 : ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • u j.castSucc) =
                ((M * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • ((T : I.E) • u j.castSucc)) := by
              simp only [smul_smul]
              congr 1
              push_cast
              ring
            rw [e1]
            exact hnat _ _ h
      | zero => simp
      | add v w _ _ hv hw =>
        rw [smul_add, smul_add]
        exact N.add_mem hv hw
      | smul c v _ hv =>
        rw [hsm, smul_comm (φ : I.E) (c : I.E) v, smul_comm ((M * T * s2 * s3 : ℕ) : I.E) (c : I.E)]
        exact hE c _ hv
    have hk := key _ hs1y
    have hφy : (φ : I.E) • y ∈ I.L := by
      rw [← hsm]
      exact I.L.smul_mem φ hy
    refine hbez _ hφy (M * T * s2 * s3 * s1)
      (Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.mul_left hM hT) hs2) hs3) hs1) ?_
    have e2 : ((M * T * s2 * s3 * s1 : ℕ) : I.E) • ((φ : I.E) • y) =
        ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • ((s1 : I.E) • y)) := by
      simp only [smul_smul]
      congr 1
      push_cast
      ring
    rw [e2]
    exact hk
  obtain ⟨θb, hθb⟩ : ∃ θb : 𝓞 I.E, (θb : I.E) = star (θ : I.E) := by
    have hint : IsIntegral ℤ (starRingEnd I.E (θ : I.E)) := by
      first
      | exact (RingOfIntegers.isIntegral_coe θ).map (starRingEnd I.E).toIntAlgHom
      | exact (θ.2).map (starRingEnd I.E).toIntAlgHom
    exact ⟨⟨starRingEnd I.E (θ : I.E), hint⟩, rfl⟩
  intro y hy
  have hyN1 : (θ : I.E) • y ∈ N :=
    gen θ θb w wd (fun i => (hw i).1) (fun i => (hw i).2) hSb (by rw [hθb]; exact hS _ hSz) hθ1
      (by rw [hθb]; exact hθ2) y hy (hspan y hy).1
  have hz2 : (T : I.E) • ((θb : I.E) • wd (Fin.last k) - (θ : I.E) • w (Fin.last k)) ∈ N := by
    have e : (T : I.E) • ((θb : I.E) • wd (Fin.last k) - (θ : I.E) • w (Fin.last k)) =
        -((T : I.E) • ((θ : I.E) • w (Fin.last k) - star (θ : I.E) • wd (Fin.last k))) := by
      rw [hθb, ← smul_neg, neg_sub]
    rw [e]
    exact N.neg_mem (hS _ hSz)
  have h1' : GE I (p ^ m) ((θb : I.E) * θb - θb) := by
    have h := GE_star I (p ^ m) hθ1
    rwa [star_sub, star_mul', ← hθb] at h
  have h2' : GE I (p ^ m) ((θb : I.E) * θ) := by
    rw [hθb, mul_comm]
    exact hθ2
  have hyN2 : (θb : I.E) • y ∈ N :=
    gen θb θ wd w (fun i => (hw i).2) (fun i => (hw i).1) (fun i => by rw [hθb]; exact hSbd i) hz2 h1' h2'
      y hy (hspan y hy).2
  obtain ⟨t3, ht3⟩ := hθ3
  have h3 : ((1 : I.E) - θ - star (θ : I.E)) • y ∈ N := by
    rw [ht3]
    exact hgl y hy t3
  have e : y = (θ : I.E) • y + (θb : I.E) • y + ((1 : I.E) - θ - star (θ : I.E)) • y := by
    rw [hθb, ← add_smul, ← add_smul,
      show (θ : I.E) + star (θ : I.E) + (1 - θ - star (θ : I.E)) = 1 by ring, one_smul]
  rw [e]
  exact N.add_mem (N.add_mem hyN1 hyN2) h3

end PI.ScRefExists.PPA
end
end

