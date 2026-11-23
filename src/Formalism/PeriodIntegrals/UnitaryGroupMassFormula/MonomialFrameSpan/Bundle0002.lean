module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.SatFin
section
noncomputable section

open scoped BigOperators
open Classical

namespace GenFrameSpan

open CutKW

theorem stepSat_of (hP : ProjZ) : StepSat := by
  intro hadm Lt _ _ l _ N0 nu P B hPmem hPc
  obtain ⟨T, hTmem, hTfix⟩ := hP hadm Lt N0 nu
  have ha : ∀ m, ∃ a : ColChoice N0 nu →₀ ℤ,
      (a.sum fun J k => k • nablaX N0 nu J) = T (MvPolynomial.monomial m 1) :=
    fun m => Finsupp.mem_span_range_iff_exists_finsupp.mp (hTmem _)
  choose a ha using ha
  let S : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
    (MvPolynomial.basisMonomials _ ℂ_[l]).constr ℂ_[l]
      fun m => MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1))
  have hS1 : ∀ m, S (MvPolynomial.monomial m 1) =
      MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1)) := by
    intro m
    have h := (MvPolynomial.basisMonomials _ ℂ_[l]).constr_basis ℂ_[l]
      (fun m => MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1))) m
    simpa [MvPolynomial.coe_basisMonomials] using h
  have hSφ : ∀ Q : MvPolynomial (Lt × ℕ × Fin N0) ℤ,
      S (MvPolynomial.map (Int.castRingHom ℂ_[l]) Q) =
        MvPolynomial.map (Int.castRingHom ℂ_[l]) (T Q) := by
    intro Q
    induction Q using MvPolynomial.induction_on' with
    | monomial m k =>
      have hk : MvPolynomial.monomial m k = k • MvPolynomial.monomial m (1 : ℤ) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [hk]
      simp only [map_zsmul]
      rw [MvPolynomial.map_monomial, map_one, hS1]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
  have hle : Submodule.span ℂ_[l] (Set.range fun J : ColChoice N0 nu =>
      MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J)) ≤ LinearMap.eqLocus S LinearMap.id := by
    rw [Submodule.span_le]
    rintro _ ⟨J, rfl⟩
    exact (LinearMap.mem_eqLocus).mpr (by rw [hSφ, hTfix]; rfl)
  have hSP : S P = P := (LinearMap.mem_eqLocus).mp (hle hPmem)
  have hSexp : S P = ∑ m ∈ P.support, AddMonoidAlgebra.coeff P m •
      MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1)) := by
    conv_lhs => rw [MvPolynomial.as_sum P]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← hS1, ← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  let c : ColChoice N0 nu →₀ ℂ_[l] := ∑ m ∈ P.support,
    AddMonoidAlgebra.coeff P m • Finsupp.mapRange (Int.cast : ℤ → ℂ_[l]) Int.cast_zero (a m)
  have hc : ∀ J, c J = ∑ m ∈ P.support, AddMonoidAlgebra.coeff P m * (a m J : ℂ_[l]) := by
    intro J
    simp [c, Finsupp.finsetSum_apply]
  refine ⟨c, fun J => ?_, ?_⟩
  · rw [hc]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg l) _) fun m _ => ?_
    rw [norm_mul]
    calc ‖AddMonoidAlgebra.coeff P m‖ * ‖(a m J : ℂ_[l])‖ ≤ ‖AddMonoidAlgebra.coeff P m‖ * 1 :=
          mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_intCast_le_one _ _) (norm_nonneg _)
      _ ≤ (l : ℝ) ^ (-B) := by rw [mul_one]; exact hPc m
  · rw [← Finsupp.linearCombination_apply]
    have hΦ : ∀ m, Finsupp.linearCombination ℂ_[l]
        (fun J => MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J))
        (Finsupp.mapRange (Int.cast : ℤ → ℂ_[l]) Int.cast_zero (a m)) =
        MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1)) := by
      intro m
      rw [← ha, Finsupp.linearCombination_apply, map_finsuppSum]
      rw [Finsupp.sum_mapRange_index (by intro; exact zero_smul _ _)]
      refine Finsupp.sum_congr fun J _ => ?_
      rw [map_zsmul, Int.cast_smul_eq_zsmul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [c, map_sum, map_smul, hΦ]
    rw [← hSexp, hSP]

end GenFrameSpan
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.SatProj
section
noncomputable section

open scoped BigOperators
open Classical

namespace GenFrameSpan

open CutKW MvPolynomial

namespace SatP

section Proj

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 : ℕ}

def emb (s : Lt) : ℕ × Fin N0 → Lt × ℕ × Fin N0 := fun p => (s, p.1, p.2)

theorem emb_inj (s : Lt) : Function.Injective (emb (N0 := N0) s) := by
  intro a b h
  simp only [emb, Prod.mk.injEq] at h
  exact Prod.ext h.2.1 h.2.2

def res (s : Lt) (m : Lt × ℕ × Fin N0 →₀ ℕ) : ℕ × Fin N0 →₀ ℕ :=
  m.comapDomain (emb s) (emb_inj s).injOn

theorem res_apply (s : Lt) (m : Lt × ℕ × Fin N0 →₀ ℕ) (p : ℕ × Fin N0) :
    res s m p = m (emb s p) :=
  Finsupp.comapDomain_apply _ _ _ _

theorem res_sum (n : Lt → (ℕ × Fin N0 →₀ ℕ)) (t : Lt) :
    res t (∑ s, (n s).mapDomain (emb s)) = n t := by
  ext p
  rw [res_apply, Finsupp.finsetSum_apply, Finset.sum_eq_single t]
  · exact Finsupp.mapDomain_apply_of_injective (emb_inj t) _ _
  · intro s _ hst
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨q, hq⟩
    simp only [emb, Prod.mk.injEq] at hq
    exact hst hq.1
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem prod_rename_monomial (n : Lt → (ℕ × Fin N0 →₀ ℕ)) :
    ∏ s, rename (emb s) (monomial (n s) (1 : ℤ)) =
      monomial (∑ s, (n s).mapDomain (emb s)) 1 := by
  simp only [rename_monomial]
  rw [monomial_sum_one]

theorem nablaX_eq (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) :
    nablaX N0 nu J = ∏ s, rename (emb s) (∏ c : Fin ((nu s).rowLen 0), minorX ℤ N0 ((nu s).colLen c) (J s c)) := by
  unfold nablaX minorX
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [AlgHom.map_det]
  congr 1
  ext i k
  simp [emb]

def Tmap (π : Lt → (MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (ℕ × Fin N0) ℤ)) :
    MvPolynomial (Lt × ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  (basisMonomials (Lt × ℕ × Fin N0) ℤ).constr ℤ fun m =>
    ∏ s, rename (emb s) (π s (monomial (res s m) 1))

theorem Tmap_monomial (π : Lt → (MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (ℕ × Fin N0) ℤ))
    (m : Lt × ℕ × Fin N0 →₀ ℕ) :
    Tmap π (monomial m 1) = ∏ s, rename (emb s) (π s (monomial (res s m) 1)) := by
  have : (monomial m (1 : ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℤ) =
      basisMonomials (Lt × ℕ × Fin N0) ℤ m := by
    rw [coe_basisMonomials]
  rw [this, Tmap, Module.Basis.constr_basis]

theorem Tmap_prod (π : Lt → (MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (ℕ × Fin N0) ℤ))
    (h : Lt → MvPolynomial (ℕ × Fin N0) ℤ) :
    Tmap π (∏ s, rename (emb s) (h s)) = ∏ s, rename (emb s) (π s (h s)) := by
  suffices H : ∀ F : Finset Lt, ∀ h : Lt → MvPolynomial (ℕ × Fin N0) ℤ,
      (∀ s ∉ F, ∃ n, h s = monomial n 1) →
      Tmap π (∏ s, rename (emb s) (h s)) = ∏ s, rename (emb s) (π s (h s)) from
    H Finset.univ h (fun s hs => absurd (Finset.mem_univ s) hs)
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro h hh
    choose n hn using fun s => hh s (by simp)
    have : h = fun s => monomial (n s) 1 := funext hn
    subst this
    rw [prod_rename_monomial, Tmap_monomial]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [res_sum]
  | insert a F haF ih =>
    intro h hh
    have key : ∀ g : MvPolynomial (ℕ × Fin N0) ℤ,
        Tmap π (rename (emb a) g * ∏ s ∈ Finset.univ.erase a, rename (emb s) (h s)) =
          rename (emb a) (π a g) * ∏ s ∈ Finset.univ.erase a, rename (emb s) (π s (h s)) := by
      let A : MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
        Tmap π ∘ₗ LinearMap.mulRight ℤ (∏ s ∈ Finset.univ.erase a, rename (emb s) (h s)) ∘ₗ
          (rename (emb a)).toLinearMap
      let B : MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
        LinearMap.mulRight ℤ (∏ s ∈ Finset.univ.erase a, rename (emb s) (π s (h s))) ∘ₗ
          (rename (emb a)).toLinearMap ∘ₗ π a
      have hAB : A = B := by
        refine (basisMonomials (ℕ × Fin N0) ℤ).ext fun u => ?_
        rw [coe_basisMonomials]
        simp only [A, B, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
          AlgHom.toLinearMap_apply]
        have h1 := ih (Function.update h a (monomial u 1)) (by
          intro s hs
          by_cases hsa : s = a
          · subst hsa
            exact ⟨u, by simp⟩
          · rw [Function.update_of_ne hsa]
            exact hh s (by simp [hsa, hs]))
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a),
          ← Finset.mul_prod_erase _ (fun s => rename (emb s) (π s (Function.update h a (monomial u 1) s)))
            (Finset.mem_univ a)] at h1
        simp only [Function.update_self] at h1
        have e1 : ∏ s ∈ Finset.univ.erase a, rename (emb s) (Function.update h a (monomial u 1) s) =
            ∏ s ∈ Finset.univ.erase a, rename (emb s) (h s) :=
          Finset.prod_congr rfl fun s hs => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
        have e2 : ∏ s ∈ Finset.univ.erase a,
            rename (emb s) (π s (Function.update h a (monomial u 1) s)) =
            ∏ s ∈ Finset.univ.erase a, rename (emb s) (π s (h s)) :=
          Finset.prod_congr rfl fun s hs => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
        rw [e1, e2] at h1
        exact h1
      intro g
      exact LinearMap.congr_fun hAB g
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a),
      ← Finset.mul_prod_erase _ (fun s => rename (emb s) (π s (h s))) (Finset.mem_univ a)]
    exact key (h a)

theorem prod_mem_span (nu : Lt → YoungDiagram) (g : Lt → MvPolynomial (ℕ × Fin N0) ℤ)
    (hg : ∀ s, g s ∈ nablaSpan ℤ N0 (nu s)) :
    ∏ s, rename (emb s) (g s) ∈ Submodule.span ℤ (Set.range (nablaX N0 nu)) := by
  by_cases hne : Nonempty (ColChoice N0 nu)
  · obtain ⟨J0⟩ := hne
    suffices H : ∀ F : Finset Lt, ∏ s ∈ F, rename (emb s) (g s) ∈ Submodule.span ℤ
        (Set.range fun J : ColChoice N0 nu =>
          ∏ s ∈ F, rename (emb s) (∏ c : Fin ((nu s).rowLen 0), minorX ℤ N0 ((nu s).colLen c) (J s c))) by
      have H1 := H Finset.univ
      have hf : (fun J : ColChoice N0 nu =>
          ∏ s, rename (emb s) (∏ c : Fin ((nu s).rowLen 0), minorX ℤ N0 ((nu s).colLen c) (J s c))) = nablaX N0 nu :=
        funext fun J => (_root_.GenFrameSpan.SatP.nablaX_eq nu J).symm
      rw [hf] at H1
      exact H1
    intro F
    induction F using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact Submodule.subset_span ⟨J0, rfl⟩
    | insert a F haF ih =>
      rw [Finset.prod_insert haF]
      have ha : rename (emb a) (g a) ∈ Submodule.span ℤ (Set.range fun
          j : (∀ c : Fin ((nu a).rowLen 0), Fin ((nu a).colLen c) ↪o Fin N0) =>
            rename (emb a) (∏ c : Fin ((nu a).rowLen 0), minorX ℤ N0 ((nu a).colLen c) (j c))) := by
        have := Submodule.mem_map_of_mem (f := (rename (emb a)).toLinearMap) (hg a)
        rw [nablaSpan, Submodule.map_span, ← Set.range_comp] at this
        exact this
      have hm := Submodule.mul_mem_mul ha ih
      rw [Submodule.span_mul_span] at hm
      refine Submodule.span_mono ?_ hm
      rintro _ ⟨_, ⟨j, rfl⟩, _, ⟨J, rfl⟩, rfl⟩
      change (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N0) at J
      refine ⟨Function.update J a j, ?_⟩
      show ∏ s ∈ insert a F, rename (emb s) (∏ c : Fin ((nu s).rowLen 0),
          minorX ℤ N0 ((nu s).colLen c) (Function.update J a j s c)) =
        rename (emb a) (∏ c : Fin ((nu a).rowLen 0), minorX ℤ N0 ((nu a).colLen c) (j c)) *
          ∏ s ∈ F, rename (emb s) (∏ c : Fin ((nu s).rowLen 0),
            minorX ℤ N0 ((nu s).colLen c) (J s c))
      rw [Finset.prod_insert haF, Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun s hs => ?_
      have hsa : s ≠ a := fun h => haF (h ▸ hs)
      rw [Function.update_of_ne hsa]
  · have hex : ∃ s, IsEmpty (∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N0) := by
      by_contra hcon
      push Not at hcon
      exact hne ⟨fun s => (hcon s).some⟩
    obtain ⟨s, hs⟩ := hex
    have h0 : g s = 0 := by
      have := hg s
      rw [nablaSpan, Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at this
      exact this
    rw [Finset.prod_eq_zero (Finset.mem_univ s) (by rw [h0, map_zero])]
    exact Submodule.zero_mem _

end Proj

end SatP

open SatP in
theorem projZ : ProjZ := by
  intro hSB Lt _ _ N0 nu
  choose Cm hCm using fun s => hSB ℤ N0 (nu s)
  let π : Lt → (MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (ℕ × Fin N0) ℤ) := fun s =>
    (nablaSpan ℤ N0 (nu s)).subtype ∘ₗ Submodule.projectionOnto _ _ (hCm s)
  have hπmem : ∀ s x, π s x ∈ nablaSpan ℤ N0 (nu s) := fun s x =>
    (Submodule.projectionOnto _ _ (hCm s) x).2
  have hπfix : ∀ s x, x ∈ nablaSpan ℤ N0 (nu s) → π s x = x := fun s x hx => by
    simp only [π, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [Submodule.projectionOnto_apply_left (hCm s) ⟨x, hx⟩]
  refine ⟨Tmap π, fun P => ?_, fun J => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [MvPolynomial.as_sum P, map_sum]
      refine Submodule.sum_mem _ fun m _ => ?_
      have : monomial m (AddMonoidAlgebra.coeff P m) = AddMonoidAlgebra.coeff P m • monomial m (1 : ℤ) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [this, LinearMap.map_smul, Tmap_monomial]
      exact Submodule.smul_mem _ _ (prod_mem_span nu _ fun s => hπmem s _)
  · rw [SatP.nablaX_eq, Tmap_prod π (fun s => ∏ c : Fin ((nu s).rowLen 0), minorX ℤ N0 ((nu s).colLen c) (J s c))]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [hπfix]
    exact Submodule.subset_span ⟨J s, rfl⟩

end GenFrameSpan
end
end

