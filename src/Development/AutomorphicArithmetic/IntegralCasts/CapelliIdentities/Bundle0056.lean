module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SmoothOnGroupSum
section
namespace UpperTheory.Reformulated.B.Qh27

open scoped ContDiff Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable def Jm : {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
  fun {_} ε ↦ Matrix.diagonal fun a ↦ if ε a then 1 else -1

noncomputable def inUJ : {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
  fun {_} ε g ↦ gᴴ * Jm ε * g = Jm ε

noncomputable def SmoothOnG :
    {n : ℕ} → (Fin n → Bool) → (Matrix (Fin n) (Fin n) ℂ → ℂ) → Prop :=
  fun {n} ε f ↦
    ∀ g₀ : Matrix (Fin n) (Fin n) ℂ, inUJ ε g₀ →
      ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ),
        IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, inUJ ε g → f g = F g

theorem smooth_on_group_sum.{u_1} :
    ∀ {n : ℕ} {ε : Fin n → Bool} {ι : Type u_1} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) ℂ → ℂ),
      (∀ i ∈ s, SmoothOnG ε (f i)) → SmoothOnG ε (fun x ↦ ∑ i ∈ s, f i x) := by
  intro n ε ι s f h g₀ hg₀
  choose! U F hU hmem hF heq using fun i hi ↦ h i hi g₀ hg₀
  refine ⟨⋂ i ∈ s, U i, fun x ↦ ∑ i ∈ s, F i x, isOpen_biInter_finset hU,
    Set.mem_iInter₂.2 hmem, ?_, ?_⟩
  · exact ContDiffOn.sum fun i hi ↦ (hF i hi).mono (Set.biInter_subset_of_mem (Finset.mem_coe.2 hi))
  · intro g hg hgu
    exact Finset.sum_congr rfl fun i hi ↦ heq i hi g (Set.mem_iInter₂.1 hg i hi) hgu

end UpperTheory.Reformulated.B.Qh27
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SmoothTensorFactor
section
noncomputable def UpperTheory.Reformulated.B.SmoothTensorFactor.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}

noncomputable def UpperTheory.Reformulated.B.SmoothTensorFactor.piTensor :
    {F : Type} →
      [inst : Field F] →
        {α : Type} →
          {Γ X : α → Type} →
            [inst_1 : (a : α) → Group (Γ a)] →
              [inst_2 : (a : α) → AddCommGroup (X a)] →
                [inst_3 : (a : α) → _root_.Module F (X a)] →
                  ((a : α) → Representation F (Γ a) (X a)) →
                    Representation F ((a : α) → Γ a) (PiTensorProduct F fun (a : α) ↦ X a) :=
    fun {F : Type} [Field F] {α : Type} {Γ X : α → Type} [(a : α) → Group (Γ a)] [(a : α) → AddCommGroup (X a)]
        [(a : α) → _root_.Module F (X a)] (ρ : (a : α) → Representation F (Γ a) (X a)) ↦
      PiTensorProduct.mapMonoidHom.comp (MonoidHom.pi fun (a : α) ↦ MonoidHom.comp (ρ a) (Pi.evalMonoidHom Γ a))

noncomputable def UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one :
    {s : ℕ} →
      {G V : Fin s → Type} →
        [inst : (a : Fin s) → Group (G a)] →
          [inst_1 : (a : Fin s) → AddCommGroup (V a)] →
            [inst_2 : (a : Fin s) → _root_.Module ℂ (V a)] →
              ((a : Fin s) → Representation ℂ (G a) (V a)) → (a : Fin s) → Representation ℂ (G a) (PiTensorProduct ℂ V) :=
    fun {s : ℕ} {G V : Fin s → Type} [(a : Fin s) → Group (G a)] [(a : Fin s) → AddCommGroup (V a)]
        [(a : Fin s) → _root_.Module ℂ (V a)] (σ : (a : Fin s) → Representation ℂ (G a) (V a)) (a : Fin s) ↦
      MonoidHom.comp (UpperTheory.Reformulated.B.SmoothTensorFactor.piTensor σ) (MonoidHom.mulSingle G a)

private lemma UpperTheory.Reformulated.B.SmoothTensorFactor.position_tprod {s : ℕ} {G V : Fin s → Type} [(a : Fin s) → Group (G a)]
    [(a : Fin s) → AddCommGroup (V a)] [(a : Fin s) → _root_.Module ℂ (V a)]
    (σ : (a : Fin s) → Representation ℂ (G a) (V a)) (a : Fin s) (g : G a) (f : (i : Fin s) → V i) :
    UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g (PiTensorProduct.tprod ℂ f) =
      PiTensorProduct.tprod ℂ (fun i => σ i ((Pi.mulSingle a g : (i : Fin s) → G i) i) (f i)) := by
  change PiTensorProduct.map _ (PiTensorProduct.tprod ℂ f) = _
  rw [PiTensorProduct.map_tprod]
  rfl

private lemma UpperTheory.Reformulated.B.SmoothTensorFactor.stab_mem_nhds {s : ℕ} {G V : Fin s → Type} [(a : Fin s) → Group (G a)]
    [(a : Fin s) → AddCommGroup (V a)] [(a : Fin s) → _root_.Module ℂ (V a)]
    [(a : Fin s) → TopologicalSpace (G a)]
    (σ : (a : Fin s) → Representation ℂ (G a) (V a))
    (h : ∀ a, UpperTheory.Reformulated.B.SmoothTensorFactor.IsSmooth (σ a)) (a : Fin s) (v : PiTensorProduct ℂ V) :
    {g : G a | UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g v = v} ∈ nhds (1 : G a) := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have hopen : {g : G a | σ a g (f a) = f a} ∈ nhds (1 : G a) :=
      (h a (f a)).mem_nhds (by simp)
    refine Filter.mem_of_superset hopen ?_
    intro g hg
    have hg' : σ a g (f a) = f a := hg
    have key : (fun i => σ i ((Pi.mulSingle a g : (i : Fin s) → G i) i) (f i)) = f := by
      funext i
      by_cases hi : i = a
      · subst hi
        simpa using hg'
      · simp [Pi.mulSingle_eq_of_ne hi]
    change UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g (r • PiTensorProduct.tprod ℂ f) = _
    rw [map_smul, UpperTheory.Reformulated.B.SmoothTensorFactor.position_tprod, key]
  | add x y hx hy =>
    refine Filter.mem_of_superset (Filter.inter_mem hx hy) ?_
    rintro g ⟨h1, h2⟩
    have h1' : UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g x = x := h1
    have h2' : UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g y = y := h2
    change UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g (x + y) = x + y
    rw [map_add (f := _), h1', h2']

theorem UpperTheory.Reformulated.B.SmoothTensorFactor.position_smooth :
    ∀ {s : ℕ} {G V : Fin s → Type} [inst : (a : Fin s) → Group (G a)] [inst_1 : (a : Fin s) → AddCommGroup (V a)]
      [inst_2 : (a : Fin s) → _root_.Module ℂ (V a)] [inst_3 : (a : Fin s) → TopologicalSpace (G a)]
      [∀ (a : Fin s), IsTopologicalGroup (G a)] (σ : (a : Fin s) → Representation ℂ (G a) (V a)),
      (∀ (a : Fin s), UpperTheory.Reformulated.B.SmoothTensorFactor.IsSmooth (σ a)) →
        ∀ (a : Fin s), UpperTheory.Reformulated.B.SmoothTensorFactor.IsSmooth (UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a) := by
  intro s G V _ _ _ _ _ σ h a v
  let H : Subgroup (G a) :=
    { carrier := {g | UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g v = v}
      mul_mem' := by
        intro x y hx hy
        have hx' : UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a x v = v := hx
        have hy' : UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a y v = v := hy
        change UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a (x * y) v = v
        rw [map_mul, Module.End.mul_apply, hy', hx']
      one_mem' := by
        change UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a 1 v = v
        rw [map_one, Module.End.one_apply]
      inv_mem' := by
        intro x hx
        have hx' : UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a x v = v := hx
        change UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a x⁻¹ v = v
        conv_lhs => rw [← hx']
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  exact Subgroup.isOpen_of_mem_nhds H (g := 1) (UpperTheory.Reformulated.B.SmoothTensorFactor.stab_mem_nhds σ h a v)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SmulMemOfSpanEqTop
section
theorem UpperTheory.Reformulated.B.SmulMemOfSpanEqTop.exists_ne_zero_smul_mem_of_span_eq_top :
    ∀ {A : Type} [inst : CommRing A] [IsDomain A]
    {K : Type} [inst_2 : Field K] [inst_3 : Algebra A K] [IsFractionRing A K] {V : Type} [inst_5 : AddCommGroup V]
    [inst_6 : _root_.Module K V] [inst_7 : _root_.Module A V] [IsScalarTower A K V] (M : Submodule A V),
    Submodule.span K (↑M : Set V) = ⊤ → ∀ (v : V), ∃ (d : A), d ≠ (0 : A) ∧ d • v ∈ M := by
  intro A _ _ K _ _ _ V _ _ _ _ M hM v
  have hv : v ∈ Submodule.span K (↑M : Set V) := hM ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨a, ha, hax⟩ := ihx
    obtain ⟨b, hb, hby⟩ := ihy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact M.smul_mem b hax
    · rw [mul_smul]
      exact M.smul_mem a hby
  | smul k x _ ih =>
    obtain ⟨a, ha, hax⟩ := ih
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := A) k
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqK : algebraMap A K q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hq0
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have key : (a * q) • ((algebraMap A K p / algebraMap A K q) • x) = p • (a • x) := by
      rw [← algebraMap_smul K (a * q), ← algebraMap_smul K a, ← algebraMap_smul K p,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [key]
    exact M.smul_mem p hax
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SmulNn
section
namespace MulEquivHaarCharEqOfProjection
open MeasureTheory

private lemma smul_nn {α : Type*} [MeasurableSpace α] (c : NNReal) (μ : Measure α) (s : Set α) :
    (c • μ) s = (c : ENNReal) * μ s := Measure.coe_nnreal_smul_apply c μ s

end MulEquivHaarCharEqOfProjection

open MeasureTheory MeasureTheory.Measure in
theorem UpperTheory.Reformulated.B.Yhb4.main :
    ∀ {H N : Type} [inst : Group H] [inst_1 : TopologicalSpace H] [inst_2 : IsTopologicalGroup H]
      [inst_3 : LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [inst_6 : MeasurableSpace H]
      [inst_7 : BorelSpace H] [inst_8 : Group N] [inst_9 : TopologicalSpace N] [inst_10 : IsTopologicalGroup N]
      [inst_11 : LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [inst_14 : MeasurableSpace N]
      [inst_15 : BorelSpace N] (ι : N →* H),
      Continuous (⇑ι : N → H) →
        ∀ (π : H → N),
          Continuous π →
            (∀ (x : N) (p : H), π ((ι : N → H) x * p) = x * π p) →
              ∀ (φ : H ≃ₜ* H) (ψ : N ≃ₜ* N),
                (∀ (p : H), π ((φ : H → H) p) = (ψ : N → N) (π p)) →
                  (∀ (p : H), ((ι : N → H) (π ((φ : H → H) p)))⁻¹ * (φ : H → H) p = ((ι : N → H) (π p))⁻¹ * p) →
                    MeasureTheory.mulEquivHaarChar φ = MeasureTheory.mulEquivHaarChar ψ := by
  intro H N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι hι π hπ hπι φ ψ hφψ hσ
  classical
  let σ : H → H := fun p => (ι (π p))⁻¹ * p
  have hσc : Continuous σ := ((hι.comp hπ).inv).mul continuous_id
  have hsplit : ∀ p, ι (π p) * σ p = p := by intro p; simp [σ]
  have hσmul : ∀ x p, σ (ι x * p) = σ p := by
    intro x p; simp [σ, hπι, mul_assoc]
  have hσφ : ∀ p, σ (φ p) = σ p := fun p => hσ p
  obtain ⟨C, hCc, hCn⟩ := exists_compact_mem_nhds (σ 1)
  let μH : Measure H := Measure.haar
  let μN : Measure N := Measure.haar
  let m : Measure N := Measure.map π (μH.restrict (σ ⁻¹' C))
  have hσC : MeasurableSet (σ ⁻¹' C) := (hCc.isClosed.preimage hσc).measurableSet
  have hmA : ∀ A, MeasurableSet A → m A = μH (π ⁻¹' A ∩ σ ⁻¹' C) := by
    intro A hA
    rw [Measure.map_apply hπ.measurable hA, Measure.restrict_apply (hπ.measurable hA)]
  have hinv : m.IsMulLeftInvariant := by
    refine ⟨fun x => ?_⟩
    ext A hA
    rw [Measure.map_apply (measurable_const_mul x) hA, hmA _ hA, hmA _ ((measurable_const_mul x) hA)]
    have : π ⁻¹' ((fun y => x * y) ⁻¹' A) ∩ σ ⁻¹' C
        = (fun p => ι x * p) ⁻¹' (π ⁻¹' A ∩ σ ⁻¹' C) := by
      ext p; simp [hπι, hσmul]
    rw [this, measure_preimage_mul]
  have hfin : IsFiniteMeasureOnCompacts m := by
    refine ⟨fun K hK => ?_⟩
    rw [hmA _ hK.isClosed.measurableSet]
    have hcomp : IsCompact ((fun q : N × H => ι q.1 * q.2) '' (K ×ˢ C)) :=
      (hK.prod hCc).image ((hι.comp continuous_fst).mul continuous_snd)
    refine lt_of_le_of_lt (measure_mono ?_) hcomp.measure_lt_top
    rintro p ⟨hp1, hp2⟩
    exact ⟨(π p, σ p), ⟨hp1, hp2⟩, hsplit p⟩
  have hc : m = haarScalarFactor m μN • μN := isMulLeftInvariant_eq_smul m μN
  set c := haarScalarFactor m μN with hcdef
  have hmuniv : 0 < m Set.univ := by
    rw [hmA _ MeasurableSet.univ, Set.preimage_univ, Set.univ_inter]
    have h1 : σ ⁻¹' C ∈ nhds (1 : H) := hσc.continuousAt.preimage_mem_nhds hCn
    exact measure_pos_of_nonempty_interior μH ⟨1, mem_interior_iff_mem_nhds.2 h1⟩
  have hc0 : (c : ENNReal) ≠ 0 := by
    intro h0
    rw [hc, MulEquivHaarCharEqOfProjection.smul_nn, h0, zero_mul] at hmuniv
    exact lt_irrefl _ hmuniv
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds (1 : N)
  let A : Set N := ψ.symm ⁻¹' K
  have hAm : MeasurableSet A := (hKc.isClosed.preimage ψ.symm.continuous).measurableSet
  have hApre : ψ ⁻¹' A = K := by ext x; simp [A]
  have hK0 : μN K ≠ 0 :=
    (measure_pos_of_nonempty_interior μN ⟨1, mem_interior_iff_mem_nhds.2 hKn⟩).ne'
  have hKt : μN K ≠ ⊤ := hKc.measure_lt_top.ne

  have e1 := mulEquivHaarChar_smul_preimage μH (X := π ⁻¹' A ∩ σ ⁻¹' C) φ
  have hpre : ⇑φ ⁻¹' (π ⁻¹' A ∩ σ ⁻¹' C) = π ⁻¹' K ∩ σ ⁻¹' C := by
    ext p; simp [A, hφψ, hσφ]
  rw [hpre, ← hmA _ hKc.isClosed.measurableSet, ← hmA _ hAm, hc, ENNReal.smul_def,
    MulEquivHaarCharEqOfProjection.smul_nn, MulEquivHaarCharEqOfProjection.smul_nn] at e1
  have e2 := mulEquivHaarChar_smul_preimage μN (X := A) ψ
  rw [hApre] at e2
  simp only [ENNReal.smul_def, smul_eq_mul] at e1 e2
  have key : ((c : ENNReal) * μN K) * (mulEquivHaarChar φ : ENNReal)
      = ((c : ENNReal) * μN K) * (mulEquivHaarChar ψ : ENNReal) := by
    calc ((c : ENNReal) * μN K) * (mulEquivHaarChar φ : ENNReal)
        = (mulEquivHaarChar φ : ENNReal) * ((c : ENNReal) * μN K) := by ring
      _ = (c : ENNReal) * μN A := e1
      _ = (c : ENNReal) * ((mulEquivHaarChar ψ : ENNReal) * μN K) := by rw [e2]
      _ = ((c : ENNReal) * μN K) * (mulEquivHaarChar ψ : ENNReal) := by ring
  rw [ENNReal.mul_right_inj (mul_ne_zero hc0 hK0) (ENNReal.mul_ne_top ENNReal.coe_ne_top hKt)] at key
  exact_mod_cast key
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanImageDenominators
section
theorem UpperTheory.Reformulated.B.SpanImageDenominators.exists_ne_zero_smul_mem_span_image :
    ∀ {A F M N : Type} [inst : CommRing A]
    [IsDomain A] [inst_2 : Field F] [inst_3 : Algebra A F] [IsFractionRing A F] [inst_5 : AddCommGroup M]
    [inst_6 : _root_.Module A M] [inst_7 : AddCommGroup N] [inst_8 : _root_.Module A N] [inst_9 : _root_.Module F N]
    [IsScalarTower A F N] (φ : M →ₗ[A] N) (T : Set M),
    ∀ y ∈ Submodule.span F ((⇑φ : M → N) '' T),
      ∃ (d : A), d ≠ (0 : A) ∧ ∃ w ∈ Submodule.span A T, d • y = (φ : M → N) w := by
  intro A F M N _ _ _ _ _ _ _ _ _ _ _ φ T y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨1, one_ne_zero, m, Submodule.subset_span hm, one_smul _ _⟩
  | zero => exact ⟨1, one_ne_zero, 0, Submodule.zero_mem _, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨d, hd, w, hw, e⟩ := hx
    obtain ⟨d', hd', w', hw', e'⟩ := hz
    refine ⟨d * d', mul_ne_zero hd hd', d' • w + d • w',
      Submodule.add_mem _ (Submodule.smul_mem _ _ hw) (Submodule.smul_mem _ _ hw'), ?_⟩
    rw [map_add (f := _), map_smul, map_smul, ← e, ← e', smul_add, smul_smul, smul_smul, mul_comm d' d]
  | smul c x _ hx =>
    obtain ⟨d, hd, w, hw, e⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) c
    refine ⟨b * d, mul_ne_zero (nonZeroDivisors.ne_zero b.2) hd, a • w,
      Submodule.smul_mem _ _ hw, ?_⟩
    have hab' : c * algebraMap A F b = algebraMap A F a := hab
    rw [map_smul, ← e, ← algebraMap_smul F ((b : A) * d), ← algebraMap_smul F a,
      ← algebraMap_smul F d, smul_smul, smul_smul, ← hab', map_mul]
    congr 1
    ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanLinearIndependentBase
section
theorem UpperTheory.span_linear_independent_base :
    ∀ {A Ω C E V I : Type} [CommRing A] [Field Ω] [Field C] [AddCommGroup E] [Module Ω E] [AddCommGroup V]
          [Module C V] [Fintype I] {n : ℕ} (φ : A →+* Ω) (ψ : A →+* C) (κ : E ≃ₗ[Ω] (Fin n → Ω)) (κ' : V ≃ₗ[C] (Fin n → C))
          (F : I → E), Function.Injective φ → LinearIndependent Ω F →
          Submodule.span (↥φ.range) {e : E | ∃ a : Fin n → A, κ e = fun i => φ (a i)} =
            Submodule.span (↥φ.range) (Set.range F) →
          ∃ y : Module.Basis I C V, ∀ j, ∃ a : Fin n → A, (κ (F j) = fun i => φ (a i)) ∧ κ' (y j) = fun i => ψ (a i) := by
  intro A Ω C E V I _ _ _ _ _ _ _ _ n φ ψ κ κ' F hφ hF hspan
  classical
  have hlat : ∀ e ∈ Submodule.span (↥φ.range) {e : E | ∃ a : Fin n → A, κ e = fun i => φ (a i)},
      ∃ a : Fin n → A, κ e = fun i => φ (a i) := by
    intro e he
    induction he using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, by ext i; simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by ext i; simp [ha, hb]⟩
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨c, r, rfl⟩ := c
      refine ⟨r • a, ?_⟩
      change κ (φ r • x) = _
      ext i
      simp [ha]
  have ha : ∀ j, ∃ a : Fin n → A, κ (F j) = fun i => φ (a i) := fun j =>
    hlat _ (hspan ▸ Submodule.subset_span ⟨j, rfl⟩)
  choose a ha using ha
  have hb : ∀ k : Fin n, ∃ b : I → A, ∀ i, ∑ j, a j i * b j = (1 : Matrix (Fin n) (Fin n) A) i k := by
    intro k
    have hk : κ.symm (fun i => φ ((1 : Matrix (Fin n) (Fin n) A) i k)) ∈
        Submodule.span (↥φ.range) (Set.range F) := by
      rw [← hspan]
      exact Submodule.subset_span ⟨fun i => (1 : Matrix (Fin n) (Fin n) A) i k, by simp⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hk
    choose b hb using fun j => (c j).2
    refine ⟨b, fun i => hφ ?_⟩
    have h1 : ∑ j, φ (b j) • F j = κ.symm (fun i => φ ((1 : Matrix (Fin n) (Fin n) A) i k)) := by
      rw [← hc]
      exact Finset.sum_congr rfl fun j _ => by rw [hb j]; rfl
    have h2 := congrFun (congrArg κ h1) i
    rw [LinearEquiv.apply_symm_apply] at h2
    rw [← h2]
    simp [ha, mul_comm]
  choose b hb using hb
  set P : Matrix (Fin n) I A := Matrix.of fun i j => a j i with hP
  set Q : Matrix I (Fin n) A := Matrix.of fun j k => b k j with hQ
  have hPQ : P * Q = 1 := by
    ext i k
    simpa [Matrix.mul_apply, hP, hQ] using hb k i
  have hQP : Q * P = 1 := by
    have hD : P * (Q * P - 1) = 0 := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hPQ, Matrix.one_mul, Matrix.mul_one, sub_self]
    rw [← sub_eq_zero]
    generalize Q * P - 1 = D at hD
    ext l j
    have h0 : ∑ l, φ (D l j) • F l = 0 := by
      apply κ.injective
      ext i
      have h3 := congrArg φ (congrFun (congrFun hD i) j)
      simpa [Matrix.mul_apply, hP, ha, mul_comm] using h3
    apply hφ
    simpa using Fintype.linearIndependent_iff.1 hF _ h0 l
  have h1 : Q.map ψ * P.map ψ = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  have h2 : P.map ψ * Q.map ψ = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  refine ⟨(Pi.basisFun C I).map ((Matrix.toLin'OfInv h1 h2).trans κ'.symm), fun j => ⟨a j, ha j, ?_⟩⟩
  ext i
  simp [Matrix.toLin'OfInv, hP]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanSInduction
section
noncomputable def UpperTheory.Reformulated.B.Qe24.spanS.{u_1, u_2} :
    {K : Type u_1} →
      {V : Type u_2} →
        [inst : Field K] →
          [inst_1 : AddCommGroup V] →
            [inst_2 : _root_.Module K V] → (S : Subring K) → {n : ℕ} → (Fin n → V) → Submodule (↥S) V :=
    fun {K : Type u_1} {V : Type u_2} [Field K] [AddCommGroup V] [_root_.Module K V] (S : Subring K) {n : ℕ}
        (x : Fin n → V) ↦
      Submodule.span (↥S) (Set.range x)

theorem UpperTheory.Reformulated.B.Qe24.spanS_induction.{u_1, u_2} :
    ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [StarRing K] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module K V]
      {S : Subring K} {n : ℕ} {x : Fin n → V} {p : V → Prop},
      p (0 : V) →
        (∀ (a b : V), p a → p b → p (a + b)) →
          (∀ c ∈ S, ∀ (a : V), p a → p (c • a)) → (∀ (i : Fin n), p (x i)) → ∀ v ∈ UpperTheory.Reformulated.B.Qe24.spanS S x, p v := by
  intro K V _ _ _ _ S n x p h0 hadd hsmul hx v hv
  unfold UpperTheory.Reformulated.B.Qe24.spanS at hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact hx i
  | zero => exact h0
  | add a b _ _ ha hb => exact hadd a b ha hb
  | smul c a _ ha => exact hsmul c.1 c.2 a ha
end

