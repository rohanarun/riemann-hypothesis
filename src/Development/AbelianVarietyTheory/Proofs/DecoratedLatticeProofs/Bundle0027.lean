module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiesOnRamOfInvariant
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0019

@[expose] public section
set_option synthInstance.maxHeartbeats 200000

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmulGluedLatticeFirstPositionCases
section
open GlobalTheory.LatPair ValuativeRel
open scoped Pointwise
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)

noncomputable section
namespace GlobalTheory.GluedOrbit
open GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration (interX)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}

theorem eq_gluedS_of_mem (q : Unif k) {M : Submodule 𝒪[k] (n ⊕ Fin 1 → k)}
    (hq : ∀ x ∈ M, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k]) {m : n ⊕ Fin 1 → k} (hm : m ∈ M)
    (hm1 : m (Sum.inr 0) = q.inv) : M = gluedS q 1 (interX M) (m ∘ Sum.inl) := by
  have hqi : (q.1 : k) * q.inv = 1 := mul_inv_cancel₀ q.ne_zero
  ext y
  rw [GlobalTheory.LevelUnfold.mem_gluedS]
  constructor
  · intro hy
    refine ⟨⟨_, hq y hy⟩, ?_, fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    · have e : inX k n 1 (y ∘ Sum.inl - (⟨_, hq y hy⟩ : 𝒪[k]) • (m ∘ Sum.inl)) =
          y - (⟨_, hq y hy⟩ : 𝒪[k]) • m := by
        ext (j | j)
        · rfl
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change (0 : k) = y (Sum.inr 0) - (q.1 : k) * y (Sum.inr 0) * m (Sum.inr 0)
          rw [hm1, mul_right_comm, hqi, one_mul, sub_self]
      change inX k n 1 _ ∈ M
      rw [e]
      exact sub_mem hy (M.smul_mem _ hm)
    · have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      change y (Sum.inr 0) = q.inv * ((q.1 : k) * y (Sum.inr 0))
      rw [← mul_assoc, mul_comm q.inv, hqi, one_mul]
  · rintro ⟨s, hs, h⟩
    have e : y = inX k n 1 (y ∘ Sum.inl - s • (m ∘ Sum.inl)) + s • m := by
      ext (j | j)
      · change y (Sum.inl j) = (y (Sum.inl j) - (s : k) * m (Sum.inl j)) + (s : k) * m (Sum.inl j)
        ring
      · have hj : j = 0 := Subsingleton.elim _ _
        subst hj
        change y (Sum.inr 0) = 0 + (s : k) * m (Sum.inr 0)
        rw [(h 0).1 rfl, hm1, zero_add, mul_comm]
    rw [e]
    exact add_mem hs (M.smul_mem _ hm)

theorem gluedS_zero_eq_lastPair_lat [Fintype n] (q : Unif k) (L : Submodule 𝒪[k] (n → k))
    [L.IsFullLattice k] :
    gluedS q 1 L 0 = (lastPair q L).lat := by
  change _ = (glue (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.isGlue_last q L)).lat
  rw [glue_lat]
  refine le_antisymm (GlobalTheory.LevelUnfold.gluedS_le_iff.2 ⟨fun y hy => ?_, ?_, fun i hi => absurd hi (by omega)⟩)
    (sup_le (fun y hy => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_))
  · refine Submodule.mem_sup_left (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨by simpa [inX] using hy, ?_⟩)
    simp [inX]
  · rw [map_zero, add_zero]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · obtain ⟨h1, h2⟩ := GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 hy
    refine GlobalTheory.LevelUnfold.mem_gluedS.2 ⟨⟨(q.1 : k) * y (Sum.inr 0), mul_mem q.1.2 h2⟩, by simpa using h1,
      fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    change y (Sum.inr 0) = q.inv * ((q.1 : k) * y (Sum.inr 0))
    rw [← mul_assoc, mul_comm q.inv, GlobalTheory.LevelUnfold.mul_inv_q, one_mul]
  · have := GlobalTheory.LevelUnfold.glue_mem_gluedS (q := q) (c := 1) L (0 : n → k)
    rwa [map_zero, add_zero] at this

theorem smul_gluedS_cases : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (P : Pair k n) (h : GL (n ⊕ Fin 1) k),
    (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∈ h • gluedS q 1 P.ker P.vec →
    (∀ x ∈ h • gluedS q 1 P.ker P.vec, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k]) →
    (∃ (Λ : Submodule 𝒪[k] (n → k)) (_ : Λ.IsFullLattice k), h • gluedS q 1 P.ker P.vec = lastKer Λ ∨
      h • gluedS q 1 P.ker P.vec = (lastPair q Λ).lat) ∨
    ∃ g : GL n k, h • gluedS q 1 P.ker P.vec = embX 1 g • gluedS q 1 P.ker P.vec := by
  intro k _ _ _ _ n _ _ q P h hz hq
  have hML : (h • gluedS q 1 P.ker P.vec).IsFullLattice k := inferInstance
  generalize h • gluedS q 1 P.ker P.vec = M at hz hq hML ⊢
  have : (interX M).IsFullLattice k := by
    refine { toIsLattice := Submodule.IsLattice.of_fg k ?_, span_eq_top := ?_ }
    · exact Submodule.fg_of_fg_map_injective (inX k n 1)
        (fun x y e => funext fun i => congrFun e (Sum.inl i))
        (hML.fg.of_le (Submodule.map_comap_le _ _))
    · refine eq_top_iff.2 fun x _ => ?_
      have hx : inX k n 1 x ∈ Submodule.span k (M : Set (n ⊕ Fin 1 → k)) :=
        hML.span_eq_top ▸ Submodule.mem_top
      obtain ⟨y, hy, d, hd⟩ := (IsLocalization.mem_span_iff (M := nonZeroDivisors 𝒪[k])).1 hx
      have hdx : (d : 𝒪[k]) • x ∈ interX M := by
        change inX k n 1 ((d : 𝒪[k]) • x) ∈ M
        rw [map_smul, hd, ← IsScalarTower.algebraMap_smul k (d : 𝒪[k]), smul_smul,
          IsLocalization.mk'_spec', map_one, one_smul]
        simpa only [Submodule.span_eq] using hy
      have h := (Submodule.span k (interX M : Set (n → k))).smul_mem
        (IsLocalization.mk' k 1 d) (Submodule.subset_span hdx)
      rwa [← IsScalarTower.algebraMap_smul k (d : 𝒪[k]), smul_smul,
        IsLocalization.mk'_spec, map_one, one_smul] at h
  have hqi : (q.1 : k) * q.inv = 1 := mul_inv_cancel₀ q.ne_zero
  by_cases hO : ∀ x ∈ M, x (Sum.inr 0) ∈ 𝒪[k]
  · refine Or.inl ⟨interX M, inferInstance, Or.inl ?_⟩
    ext y
    rw [GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer]
    constructor
    · intro hy
      refine ⟨?_, hO y hy⟩
      have e : inX k n 1 (y ∘ Sum.inl) = y - (⟨_, hO y hy⟩ : 𝒪[k]) • (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) := by
        ext (j | j)
        · simp [inX]
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change (0 : k) = y (Sum.inr 0) - y (Sum.inr 0) * (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inr 0)
          simp
      change inX k n 1 _ ∈ M
      rw [e]
      exact sub_mem hy (M.smul_mem _ hz)
    · rintro ⟨h1, h2⟩
      have e : y = inX k n 1 (y ∘ Sum.inl) + (⟨_, h2⟩ : 𝒪[k]) • (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) := by
        ext (j | j)
        · simp [inX]
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change y (Sum.inr 0) = 0 + y (Sum.inr 0) * (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inr 0)
          simp
      rw [e]
      exact add_mem h1 (M.smul_mem _ hz)
  · push Not at hO
    obtain ⟨m₀, hm₀, hm₀'⟩ := hO
    have ht : IsUnit (⟨_, hq m₀ hm₀⟩ : 𝒪[k]) := by
      by_contra ht
      obtain ⟨s, hs⟩ := q.mem_max_iff.1 ht
      apply hm₀'
      have h' : (q.1 : k) * m₀ (Sum.inr 0) = (q.1 : k) * s := congrArg Subtype.val hs
      rw [mul_left_cancel₀ q.ne_zero h']
      exact s.2
    obtain ⟨u, hu⟩ := ht
    have hu' : ((u : 𝒪[k]) : k) = (q.1 : k) * m₀ (Sum.inr 0) := congrArg Subtype.val hu
    have hinv : ((((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])) : k) * ((u : 𝒪[k]) : k) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      exact this
    set m : n ⊕ Fin 1 → k := ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) • m₀
    have hm : m ∈ M := M.smul_mem _ hm₀
    have hm1 : m (Sum.inr 0) = q.inv := by
      change ((((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])) : k) * m₀ (Sum.inr 0) = (q.1 : k)⁻¹
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← hinv, hu']
      ring
    have hMeq := eq_gluedS_of_mem q hq hm hm1
    have hqf : q.1 • (m ∘ Sum.inl) ∈ interX M := by
      have e : inX k n 1 (q.1 • (m ∘ Sum.inl)) = q.1 • m - (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) := by
        ext (j | j)
        · change (q.1 : k) * m (Sum.inl j) = (q.1 : k) * m (Sum.inl j) - (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inl j)
          simp
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change (0 : k) = (q.1 : k) * m (Sum.inr 0) - (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inr 0)
          rw [hm1, hqi]
          simp
      change inX k n 1 _ ∈ M
      rw [e]
      exact sub_mem (M.smul_mem _ hm) hz
    by_cases hf : m ∘ Sum.inl ∈ interX M
    · refine Or.inl ⟨interX M, inferInstance, Or.inr ?_⟩
      calc M = gluedS q 1 (interX M) (m ∘ Sum.inl) := hMeq
        _ = gluedS q 1 (interX M) 0 := GlobalTheory.LevelUnfold.gluedS_congr (by simpa using hf)
        _ = (lastPair q (interX M)).lat := gluedS_zero_eq_lastPair_lat q _
    · refine Or.inr ?_
      have hG : IsGlue (interX M) (m ∘ Sum.inl) := (isGlue_iff q).2 ⟨inferInstance, hf, hqf⟩
      obtain ⟨g, hg1, hg2⟩ := (GlobalTheory.LevelUnfold.oneOrbit (k := k) (n := n) (c := 1) (q := q)).1 P.ker (interX M)
        P.vec (m ∘ Sum.inl) (Pair.isGlue P.hasVal_vec) hG
      refine ⟨g, ?_⟩
      rw [GlobalTheory.LevelUnfold.embX_smul_gluedS, hg1, GlobalTheory.LevelUnfold.gluedS_congr hg2]
      exact hMeq

end GlobalTheory.GluedOrbit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainOneIndexAtOfClassSupport
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem oneIndexAt_of_classAt_supportAt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.ClassAt t ν → S.SupportAt t → S.OneIndexAt t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hC hS j c H p hp1 hpc h hE
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨r, hr, u, hu, rfl⟩ := hC j c H p hp1 hpc h hE
  obtain ⟨γ, g, hg, rfl⟩ := Radical.exists_of_mem_R hr
  have hmul : ∀ (a b : GL (XIx (Fin κ) t (j + 1) ⊕ Fin c) k) (Ψ : type_of% ((S.T t).Phi j c H)),
      om (S.μ (j + 1)) 1 (a * b) Ψ = om (S.μ (j + 1)) 1 a (om (S.μ (j + 1)) 1 b Ψ) :=
    fun a b Ψ => by rw [← om_mul, one_mul]
  have hne : opE S.ψ ν p (om (S.μ (j + 1)) 1 u ((S.T t).Phi j c H)) ≠ 0 := by
    intro h0
    apply hE
    rw [mul_assoc, hmul, (opE_om_embX k _ _ c p hp1 hpc S.ψ ν _ _).1, hmul,
      opE_om_target_unipotent k _ _ c p hp1 hpc S.ψ ν _ _ g hg, h0]
    funext y
    simp [om]
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, opE S.ψ ν p (om (S.μ (j + 1)) 1 u ((S.T t).Phi j c H)) x₀ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  classical
  obtain ⟨e, he⟩ : ∃ e, om (S.μ (j + 1)) 1 u ((S.T t).Phi j c H) (affPt p x₀ e) ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hx₀
    simp [opE, hc]
  have hΦ : (S.T t).Phi j c H ((u⁻¹).val * affPt p x₀ e) ≠ 0 := by
    intro h0
    apply he
    simp only [om, Units.val_one, Matrix.mul_one, h0, mul_zero]
  obtain ⟨r', hr', u', hu', rfl⟩ := hS j c H p hp1 hpc u hu x₀ e hΦ
  exact ⟨embX c γ * g * r', mul_mem hr hr', u', hu', by group⟩

end GlobalTheory.SymChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPatternIterated
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain.IterPattern

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem intM_submatrix_iff {a b : Type*} (e : a ≃ b) (M : Matrix b b k) :
    IntM (M.submatrix e e) ↔ IntM M := by
  constructor
  · intro h i j
    simpa using h (e.symm i) (e.symm j)
  · intro h i j
    exact h (e i) (e j)

theorem symm_mem_KO_iff {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b)
    (g : GL b k) : (reGL e).symm g ∈ KO k a ↔ g ∈ KO k b := by
  rw [mem_KO, mem_KO, ← map_inv (reGL e).symm g, reGL_symm_val, reGL_symm_val,
    intM_submatrix_iff, intM_submatrix_iff]

theorem mem_reindex_J {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (P : GlobalTheory.StepData.TypeDatum k a)
    (e : a ≃ b) (g : GL b k) : g ∈ (P.reindex e).J ↔ (reGL e).symm g ∈ P.J := Iff.rfl

variable {ρ κ l j : ℕ} {t : Type}

theorem free_ll (x y : Ix (Fin κ ⊕ Fin l) t j) :
    FreeIx ρ (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inl y)) ↔ FreeIx ρ x y := by
  rcases x with a | ⟨i, s⟩ <;> rcases y with b | ⟨i', s'⟩ <;> simp [ixSucc, FreeIx]

theorem free_lr (x : Ix (Fin κ ⊕ Fin l) t j) (s : t) :
    FreeIx ρ (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inr s)) := by
  rcases x with a | ⟨i, s'⟩ <;> simp [ixSucc, FreeIx, (Fin.castSucc_lt_last _).le]

theorem not_free_rl (s : t) (y : Ix (Fin κ ⊕ Fin l) t j) :
    ¬ FreeIx ρ (ixSucc _ t j (.inr s)) (ixSucc _ t j (.inl y)) := by
  rcases y with b | ⟨i, s'⟩
  · simp [ixSucc, FreeIx]
  · simp [ixSucc, FreeIx]

theorem free_rr (s s' : t) : FreeIx ρ (ixSucc (Fin κ ⊕ Fin l) t j (.inr s)) (ixSucc _ t j (.inr s')) := by
  simp [ixSucc, FreeIx]

variable [Fintype t] [DecidableEq t]

theorem base_iff (P : GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l))
    (hP : ∀ g : GL (Fin κ ⊕ Fin l) k, g ∈ P.J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1)
    (g : GL (Ix (Fin κ ⊕ Fin l) t 0) k) :
    g ∈ (P.reindex (ixZero _ t)).J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  have hz : ∀ a b : Fin κ ⊕ Fin l, FreeIx ρ (ixZero _ t a) (ixZero _ t b) ↔ FreeTop ρ a b := fun _ _ => Iff.rfl
  rw [mem_reindex_J, hP, symm_mem_KO_iff]
  simp only [reGL_symm_val]
  refine and_congr_right fun _ => ⟨fun h a b hab => ?_, fun h a b hab => ?_⟩
  · obtain ⟨a, rfl⟩ := (ixZero _ t).surjective a
    obtain ⟨b, rfl⟩ := (ixZero _ t).surjective b
    have := h a b (fun hf => hab ((hz a b).2 hf))
    simpa [Matrix.one_apply] using this
  · have := h _ _ (fun hf => hab ((hz a b).1 hf))
    simpa [Matrix.one_apply] using this

theorem step_iff (Q : GlobalTheory.StepData.TypeDatum k (Ix (Fin κ ⊕ Fin l) t j))
    (μ : kˣ →* ℂˣ) (hμ : IsTame μ)
    (hQ : ∀ g : GL (Ix (Fin κ ⊕ Fin l) t j) k, g ∈ Q.J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1)
    (g : GL (Ix (Fin κ ⊕ Fin l) t (j + 1)) k) :
    g ∈ ((Q.step t μ hμ).reindex (ixSucc _ t j)).J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  rw [mem_reindex_J, TypeDatum.step_J, TypeDatum.mem_stepJ_iff, symm_mem_KO_iff]
  constructor
  · rintro ⟨hK, ⟨g', hg', hval⟩, hC⟩
    refine ⟨hK, fun a b hab => ?_⟩
    obtain ⟨a, rfl⟩ := (ixSucc _ t j).surjective a
    obtain ⟨b, rfl⟩ := (ixSucc _ t j).surjective b
    rcases a with x | s <;> rcases b with y | s'
    ·
      have hxy : ¬ FreeIx ρ x y := fun h => hab ((free_ll x y).2 h)
      have hold := ((hQ g').1 hg').2 x y hxy
      have hentry : g'.val x y = g.val (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inl y)) := by
        rw [hval, reGL_symm_val]; rfl
      rw [hentry] at hold
      simpa [Matrix.one_apply] using hold
    · exact absurd (free_lr x s') hab
    ·
      have hlow := hC s y
      simpa [Matrix.one_apply, reGL_symm_val, Matrix.toBlocks₂₁] using hlow
    · exact absurd (free_rr s s') hab
  · rintro ⟨hK, hfree⟩
    have hK' : (reGL (ixSucc _ t j)).symm g ∈ KO k _ := (symm_mem_KO_iff _ g).2 hK
    have hC : MaxM ((reGL (ixSucc _ t j)).symm g).val.toBlocks₂₁ := by
      intro s y
      have hnf := hfree _ _ (not_free_rl s y)
      simpa [Matrix.one_apply, reGL_symm_val, Matrix.toBlocks₂₁] using hnf
    refine ⟨hK, ?_, hC⟩
    obtain ⟨⟨g', hg'K, hg'val⟩, -⟩ := exists_diag_blocks hK' hC
    refine ⟨g', (hQ g').2 ⟨hg'K, fun x y hxy => ?_⟩, hg'val⟩
    have hnf := hfree _ _ (fun h => hxy ((free_ll x y).1 h))
    have hentry : g'.val x y = g.val (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inl y)) := by
      rw [hg'val, reGL_symm_val]; rfl
    rw [hentry]
    simpa [Matrix.one_apply] using hnf

theorem iter_iff (P : GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l))
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (hP : ∀ g : GL (Fin κ ⊕ Fin l) k, g ∈ P.J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1)
    (j : ℕ) (g : GL (Ix (Fin κ ⊕ Fin l) t j) k) :
    g ∈ (P.iter t μ hμ j).J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  induction j with
  | zero =>
    rw [TypeDatum.iter_zero]
    exact base_iff P hP g
  | succ j ih =>
    rw [TypeDatum.iter_succ]
    exact step_iff _ (μ (j + 1)) (hμ _) ih g

end GlobalTheory.SymChain.IterPattern

theorem GlobalTheory.SymChain.pattern_iter (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ)
    (t : Type) [Fintype t] [DecidableEq t] :
    S.Pattern t := by
  intro j g
  have hP : ∀ x : GL (Fin κ ⊕ Fin (s + 1)) k, x ∈ S.P.J ↔
      x ∈ KO k _ ∧ ∀ a b, ¬ FreeTop S.ρ a b →
        valuation k (x.val a b - (1 : Matrix _ _ k) a b) < 1 := by
    intro x
    rw [S.sym.1 x]
    constructor
    · rintro ⟨u, hu, γ, hγ, x₀, hx₀, hxb⟩
      refine ⟨⟨x₀, hx₀⟩, fun a b hab => ?_⟩
      rw [← hx₀, GlobalTheory.SymPattern.entry_lt_iff, hxb]
      exact GlobalTheory.SymPattern.pat_of_mul S.ρ u ((Radical.mem_N_iff u).mp hu) γ hγ a b hab
    · rintro ⟨⟨x₀, hx₀⟩, hpat⟩
      obtain ⟨u, hu, γ, hγ, he⟩ := GlobalTheory.SymPattern.exists_of_pat S.ρ
        (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) x₀) (fun a b hab => by
          rw [← GlobalTheory.SymPattern.entry_lt_iff, hx₀]
          exact hpat a b hab)
      exact ⟨u, (Radical.mem_N_iff u).mpr hu, γ, hγ, x₀, hx₀, he⟩
  exact IterPattern.iter_iff S.P S.μ S.tame hP j g
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPhiSupportPeriodic
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChainSupport

theorem phi_support_periodic :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ)
      (t : Type) [Fintype t] [DecidableEq t] (j c : ℕ) (H : j + c = s)
      (x z : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k),
      ((S.T t).Phi j c H x ≠ 0 →
        IntM (((embA (XIx (Fin κ) t (j + 1))
          (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)))⁻¹.val :
            Matrix _ _ k) * x * (embA (XIx (Fin κ) t j)
          (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1))).val)) ∧
      (MaxM (((embA (XIx (Fin κ) t (j + 1))
          (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)))⁻¹.val :
            Matrix _ _ k) * z * (embA (XIx (Fin κ) t j)
          (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1))).val) →
        (S.T t).Phi j c H (x + z) = (S.T t).Phi j c H x) := by
  intro k _ _ _ _ s κ S t _ _ j c H x z
  set o := stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)
  set o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega)
  set F := typeFrame (k := k) S.ϖ o
  set F' := typeFrame (k := k) S.ϖ o'
  have hPhi : ∀ y, (S.T t).Phi j c H y = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      ((F.coords F' y).submatrix (ixSucc _ t j) id) := fun y => rfl
  constructor
  · intro hx i l
    rw [hPhi] at hx
    have := TypeDatum.intM_of_Phi_ne_zero _ _ hx ((ixSucc _ t j).symm (o.symm i)) (o'.symm l)
    simpa [LatFrame.coords, F, F', typeFrame] using this
  · intro hz
    rw [hPhi, hPhi]
    have e : F.coords F' (x + z) = F.coords F' x + F.coords F' z := by
      unfold LatFrame.coords; rw [Matrix.mul_add, Matrix.add_mul]; rfl
    rw [e]
    exact TypeDatum.Phi_add _ (S.tame _) _ (y := (F.coords F' z).submatrix (ixSucc _ t j) id) fun _ _ => hz _ _

end GlobalTheory.SymChainSupport
end

