module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StrictlyUpperRank
section
noncomputable def UpperTheory.Reformulated.B.StrictlyUpperRank.IsStrictUpper.{u_1, u_2} :
    {𝕜 : Type u_1} → [RCLike 𝕜] → {n : Type u_2} → [LinearOrder n] → Matrix n n 𝕜 → Prop :=
  fun {𝕜} [RCLike 𝕜] {n} [LinearOrder n] X ↦
    ∀ (i j : n), j ≤ i → X i j = 0

noncomputable def UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow.{u_2} :
    {n : Type u_2} → [Fintype n] → [LinearOrder n] → n → ℕ :=
  fun {n} [Fintype n] [LinearOrder n] i ↦
    ({x : n | x < i} : Finset n).card

theorem UpperTheory.Reformulated.B.StrictlyUpperRank.rank_add_le_of_pow_ne_zero.{u_1, u_2} :
    ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {n : Type u_2} [inst_1 : Fintype n] [inst_2 : LinearOrder n] {X : Matrix n n 𝕜},
      @UpperTheory.Reformulated.B.StrictlyUpperRank.IsStrictUpper 𝕜 inst n inst_2 X →
        ∀ (k : Nat) (i j : n),
          @Ne 𝕜
              (@HPow.hPow (Matrix n n 𝕜) Nat (Matrix n n 𝕜)
                (@instHPow (Matrix n n 𝕜) Nat
                  (@NPow.toPow (Matrix n n 𝕜)
                    (@Monoid.toNPow (Matrix n n 𝕜)
                      (@Semiring.toMonoid (Matrix n n 𝕜)
                        (@Matrix.semiring n 𝕜
                          (@DivisionSemiring.toSemiring 𝕜
                            (@Semifield.toDivisionSemiring 𝕜
                              (@Field.toSemifield 𝕜
                                (@NormedField.toField 𝕜
                                  (@DenselyNormedField.toNormedField 𝕜 (@RCLike.toDenselyNormedField 𝕜 inst))))))
                          inst_1 fun (a b : n) ↦ @LinearOrder.toDecidableEq n inst_2 a b)))))
                X k i j)
              (@OfNat.ofNat 𝕜 (nat_lit 0)
                (@Zero.toOfNat0 𝕜
                  (@MulZeroClass.toZero 𝕜
                    (@instMulZeroClassOfSemiring 𝕜
                      (@DivisionSemiring.toSemiring 𝕜
                        (@Semifield.toDivisionSemiring 𝕜
                          (@Field.toSemifield 𝕜
                            (@NormedField.toField 𝕜
                              (@DenselyNormedField.toNormedField 𝕜 (@RCLike.toDenselyNormedField 𝕜 inst)))))))))) →
            @LE.le Nat instLENat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow n inst_1 inst_2 i) k)
              (@UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow n inst_1 inst_2 j) := by
  intro 𝕜 _ n _ _ X hX k
  induction k with
  | zero =>
    intro i j h
    have hij : i = j := by
      by_contra hne
      exact h (by rw [pow_zero]; exact Matrix.one_apply_ne hne)
    subst hij
    exact le_rfl
  | succ k ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 := ih i l (left_ne_zero_of_mul hl)
    have hlj : l < j := by
      by_contra hle
      exact right_ne_zero_of_mul hl (hX l j (not_lt.mp hle))
    have h2 : UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow l < UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow j := by
      unfold UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow
      apply Finset.card_lt_card
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx.trans hlj
      · have hm := @hsub l (by simpa using hlj)
        simp at hm
    omega
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StronglyIrreducible
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.StronglyIrreducible.gm :
    {G R : Type} → [inst : Group G] → [inst_1 : CommRing R] → {n : ℕ} → (G →* GL (Fin n) R) → G → Matrix (Fin n) (Fin n) R :=
    fun {G R : Type} [Group G] [CommRing R] {n : ℕ} (r : G →* GL (Fin n) R) (g : G) ↦
      (↑((r : G → GL (Fin n) R) g) : Matrix (Fin n) (Fin n) R)

noncomputable def UpperTheory.Reformulated.B.StronglyIrreducible.StrongIrr :
    {G κ : Type} → [inst : Group G] → [inst_1 : Field κ] → {n : ℕ} → (G →* GL (Fin n) κ) → Prop :=
    fun {G κ : Type} [Group G] [Field κ] {n : ℕ} (r : G →* GL (Fin n) κ) ↦
      ∀ (W : Submodule κ (Fin n → κ)) (S : Subgroup G),
        S.FiniteIndex → (∀ (g : G), g ∈ S ↔ ∀ v ∈ W, (UpperTheory.Reformulated.B.StronglyIrreducible.gm r g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤

theorem UpperTheory.Reformulated.B.StronglyIrreducible.strongIrr_conj :
    ∀ {G κ : Type} [inst : Group G] [inst_1 : Field κ] {n : ℕ} (r : G →* GL (Fin n) κ),
      UpperTheory.Reformulated.B.StronglyIrreducible.StrongIrr r →
        ∀ (P : GL (Fin n) κ),
          UpperTheory.Reformulated.B.StronglyIrreducible.StrongIrr
            ((MulEquiv.toMonoidHom ((MulAut.conj : GL (Fin n) κ → MulAut (GL (Fin n) κ)) P⁻¹)).comp r) := by
  intro G κ _ _ n r h P W S hS hW
  have h1 : ∀ v : Fin n → κ, ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVec
      ((P : Matrix (Fin n) (Fin n) κ).mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have h2 : ∀ v : Fin n → κ, (P : Matrix (Fin n) (Fin n) κ).mulVec
      (((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have h3 : ∀ (g : G) (v : Fin n → κ),
      (UpperTheory.Reformulated.B.StronglyIrreducible.gm ((MulEquiv.toMonoidHom
        ((MulAut.conj : GL (Fin n) κ → MulAut (GL (Fin n) κ)) P⁻¹)).comp r) g).mulVec v
      = ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVec
        ((UpperTheory.Reformulated.B.StronglyIrreducible.gm r g).mulVec ((P : Matrix (Fin n) (Fin n) κ).mulVec v)) := by
    intro g v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    change (((P⁻¹ * r g * P⁻¹⁻¹ : GL (Fin n) κ)) : Matrix (Fin n) (Fin n) κ).mulVec v = _
    rw [inv_inv, Units.val_mul, Units.val_mul]
  have hmem : ∀ v : Fin n → κ,
      v ∈ W.comap (Matrix.mulVecLin ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ)) ↔
        ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVec v ∈ W := fun v => Iff.rfl
  have key := h (W.comap (Matrix.mulVecLin ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ)))
    S hS (by
      intro g
      rw [hW g]
      constructor
      · intro hg v hv
        have := hg _ ((hmem v).1 hv)
        rw [h3, h2] at this
        exact (hmem _).2 this
      · intro hg v hv
        rw [h3]
        apply (hmem _).1
        apply hg
        rw [hmem, h1]
        exact hv)
  rcases key with key | key
  · left
    rw [eq_bot_iff]
    intro v hv
    have hv' : (P : Matrix (Fin n) (Fin n) κ).mulVec v ∈
        W.comap (Matrix.mulVecLin ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ)) := by
      rw [hmem, h1]
      exact hv
    rw [key, Submodule.mem_bot] at hv'
    rw [Submodule.mem_bot, ← h1 v, hv', Matrix.mulVec_zero]
  · right
    rw [eq_top_iff]
    intro v _
    rw [← h1 v]
    apply (hmem _).1
    rw [key]
    exact Submodule.mem_top
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SubalgebraEqTop
section
noncomputable def UpperTheory.Reformulated.B.Qe26.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.Qe26.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.Qe26.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.Qe26.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.Qe26.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.Qe26.IsIrrSub r ⊤

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe26.tr :
    {k : Type} → [inst : Field k] → {n : ℕ} → GL (Fin n) k → k :=
    fun {k : Type} [Field k] {n : ℕ} (g : GL (Fin n) k) ↦ (↑g : Matrix (Fin n) (Fin n) k).trace

private theorem UpperTheory.Reformulated.B.Qe26.subalgebra_eq_top {k V : Type} [Field k] [IsAlgClosed k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (S : Subalgebra k (Module.End k V))
    (h : ∀ W : Submodule k V, (∀ s ∈ S, ∀ v ∈ W, s v ∈ W) → W = ⊥ ∨ W = ⊤) :
    S = ⊤ := by
  have hsimple : IsSimpleModule S V := by
    rw [isSimpleModule_iff]
    refine ⟨fun p ↦ ?_⟩
    rcases h (p.restrictScalars k) (fun s hs v hv ↦ p.smul_mem ⟨s, hs⟩ hv) with h1 | h1
    · left
      simpa using h1
    · right
      simpa using h1
  have hb := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := S) (V := V) k
  have hfin : Module.Finite (Module.End S V) V :=
    Module.Finite.of_restrictScalars_finite k _ _
  rw [eq_top_iff]
  intro T _
  let T' : Module.End (Module.End S V) V :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun c v ↦ by
        obtain ⟨a, rfl⟩ := hb.2 c
        simp }
  obtain ⟨s, hs⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := S) (M := V) T'
  have : T = s.1 := by
    ext v
    exact (LinearMap.congr_fun hs v).symm
  rw [this]
  exact s.2

private theorem UpperTheory.Reformulated.B.Qe26.lift_surjective {k : Type} [Field k] [IsAlgClosed k] {H : Type}
    [Group H] {n : ℕ} (R : H →* GL (Fin n) k) (hR : UpperTheory.Reformulated.B.Qe26.IsIrr R) :
    Function.Surjective (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H
      ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R)) := by
  obtain ⟨h0, -, h1⟩ := hR
  set L := MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H
      ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R) with hL
  have hnt : Nontrivial (Fin n → k) := (Submodule.nontrivial_iff k).1 ⟨⟨_, _, h0⟩⟩
  have htop := UpperTheory.Reformulated.B.Qe26.subalgebra_eq_top
    (((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp L).range) (by
      intro W hW
      refine h1 W le_top (fun g v hv ↦ ?_)
      have := hW _ ⟨MonoidAlgebra.single g 1, rfl⟩ v hv
      simpa [hL] using this)
  intro M
  have hM : Matrix.toLinAlgEquiv' M ∈
      ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp L).range := by
    rw [htop]; trivial
  obtain ⟨x, hx⟩ := hM
  exact ⟨x, (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).injective hx⟩

theorem UpperTheory.Reformulated.B.Qe26.kerLe :
    ∀ (k : Type) [inst : Field k] [IsAlgClosed k] (H : Type) [inst_2 : Group H] (n : ℕ) (R : H →* GL (Fin n) k),
      UpperTheory.Reformulated.B.Qe26.IsIrr R →
        ∀ (x₀ : GL (Fin n) k) (B : Type) [inst_3 : Ring B] [inst_4 : Algebra k B] [Module.Finite k B] (φ : H →* B)
          (f : B →ₗ[k] k),
          (∀ (h : H), UpperTheory.Reformulated.B.Qe26.tr (x₀ * (R : H → GL (Fin n) k) h) = (f : B → k) ((φ : H → B) h)) →
            n ^ (2 : ℕ) ≤ Module.finrank k ↥(Algebra.adjoin k (Set.range (⇑φ : H → B))) ∧
              ∀ (x : MonoidAlgebra k H),
                ((MonoidAlgebra.lift k B H : (H →* B) → MonoidAlgebra k H →ₐ[k] B) φ : MonoidAlgebra k H → B) x = (0 : B) →
                  ((MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H :
                            (H →* Matrix (Fin n) (Fin n) k) → MonoidAlgebra k H →ₐ[k] Matrix (Fin n) (Fin n) k)
                          ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R) :
                        MonoidAlgebra k H → Matrix (Fin n) (Fin n) k)
                      x =
                    (0 : Matrix (Fin n) (Fin n) k) := by
  intro k _ _ H _ n R hR x₀ B _ _ _ φ f hf
  have hsurj := UpperTheory.Reformulated.B.Qe26.lift_surjective R hR
  set L := MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H
      ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R) with hL
  set Φ := MonoidAlgebra.lift k B H φ with hΦ
  have htr : ∀ y, ((x₀ : Matrix (Fin n) (Fin n) k) * L y).trace = f (Φ y) := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp [mul_add, ha, hb]
    | single g c =>
      have := hf g
      simp only [UpperTheory.Reformulated.B.Qe26.tr, Units.val_mul] at this
      simp [hL, hΦ, ← this]
  have hker : ∀ x, Φ x = 0 → L x = 0 := by
    intro x hx
    rw [Matrix.ext_iff_trace_mul_left]
    intro M
    obtain ⟨y, hy⟩ := hsurj ((↑x₀⁻¹ : Matrix (Fin n) (Fin n) k) * M)
    have := htr (y * x)
    rw [map_mul, map_mul, hx, hy, mul_zero, map_zero, ← mul_assoc, Units.mul_inv_cancel_left] at this
    simpa using this
  refine ⟨?_, hker⟩
  have hle : LinearMap.ker Φ.toLinearMap ≤ LinearMap.ker L.toLinearMap := fun x hx ↦ hker x hx
  have hrange : LinearMap.range Φ.toLinearMap ≤
      Subalgebra.toSubmodule (Algebra.adjoin k (Set.range φ)) := by
    rintro _ ⟨y, rfl⟩
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add]; exact add_mem ha hb
    | single g c =>
      have : Φ.toLinearMap (MonoidAlgebra.single g c) = c • φ g := by simp [hΦ]
      rw [this]
      exact Submodule.smul_mem _ _ (Algebra.subset_adjoin ⟨g, rfl⟩)
  let ψ : LinearMap.range Φ.toLinearMap →ₗ[k] Matrix (Fin n) (Fin n) k :=
    ((LinearMap.ker Φ.toLinearMap).liftQ L.toLinearMap hle).comp
      Φ.toLinearMap.quotKerEquivRange.symm.toLinearMap
  have hψ : Function.Surjective ψ := by
    intro M
    obtain ⟨y, rfl⟩ := hsurj M
    exact ⟨Φ.toLinearMap.quotKerEquivRange (Submodule.Quotient.mk y), by simp [ψ]⟩
  calc n ^ 2 = Module.finrank k (Matrix (Fin n) (Fin n) k) := by
        simp [Module.finrank_matrix, sq]
    _ ≤ Module.finrank k (LinearMap.range Φ.toLinearMap) :=
        LinearMap.finrank_le_finrank_of_surjective hψ
    _ ≤ Module.finrank k (Subalgebra.toSubmodule (Algebra.adjoin k (Set.range φ))) :=
        Submodule.finrank_mono hrange
    _ = _ := rfl
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SubgroupFixed
section
noncomputable def UpperTheory.Reformulated.B.SubgroupFixed.HasFixed :
    {Γ V : Type} →
      [inst : Group Γ] → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ Γ V → Subgroup Γ → Prop :=
    fun {Γ V : Type} [Group Γ] [AddCommGroup V] [_root_.Module ℂ V] (ρ : Representation ℂ Γ V) (U : Subgroup Γ) ↦
      ∃ (v : V), v ≠ (0 : V) ∧ ∀ u ∈ U, ((ρ : Γ → V →ₗ[ℂ] V) u : V → V) v = v

private lemma UpperTheory.Reformulated.B.SubgroupFixed.core {R M N : Type*} [Ring R] [AddCommGroup M] [_root_.Module R M]
    [AddCommGroup N] [_root_.Module R N] [IsSimpleModule R M]
    (hsup : ∀ S : Submodule R N, (∀ f : M →ₗ[R] N, LinearMap.range f ≤ S) → S = ⊤)
    (W : Submodule R N) (hW : W ≠ ⊥) :
    ∃ g : M →ₗ[R] N, Function.Injective g ∧ LinearMap.range g ≤ W := by
  have hss : IsSemisimpleModule R N := by
    refine isSemisimpleModule_of_isSemisimpleModule_submodule'
      (p := fun f : M →ₗ[R] N => LinearMap.range f) (fun f => IsSemisimpleModule.range f) ?_
    exact hsup _ (fun f => le_iSup (fun f : M →ₗ[R] N => LinearMap.range f) f)
  obtain ⟨C, hC⟩ := exists_isCompl W
  let p : N →ₗ[R] W := W.linearProjOfIsCompl C hC
  have hex : ∃ f : M →ₗ[R] N, p ∘ₗ f ≠ 0 := by
    by_contra hno
    push Not at hno
    have htop : LinearMap.ker p = ⊤ := hsup _ (fun f => by
      rintro _ ⟨x, rfl⟩
      exact LinearMap.congr_fun (hno f) x)
    apply hW
    rw [eq_bot_iff]
    intro w hw
    have h1 : p w = 0 := by
      have : w ∈ LinearMap.ker p := htop ▸ Submodule.mem_top
      exact this
    have h2 : p w = ⟨w, hw⟩ := Submodule.linearProjOfIsCompl_apply_left hC ⟨w, hw⟩
    have h3 : (⟨w, hw⟩ : W) = 0 := h2.symm.trans h1
    simpa using congrArg Subtype.val h3
  obtain ⟨f, hf⟩ := hex
  have hinj := (LinearMap.injective_or_eq_zero (p ∘ₗ f)).resolve_right hf
  refine ⟨W.subtype ∘ₗ p ∘ₗ f, W.injective_subtype.comp hinj, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (p (f x)).2

theorem UpperTheory.Reformulated.B.SubgroupFixed.sub_fixed :
    ∀ {Γ X V : Type} [inst : Group Γ] [inst_1 : AddCommGroup X] [inst_2 : _root_.Module ℂ X] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (σ : Representation ℂ Γ X),
      σ.IsIrreducible →
        ∀ (τ : Representation ℂ Γ V),
          ⨆ (f :
                { f : X →ₗ[ℂ] V //
                  ∀ (g : Γ) (v : X),
                    (f : X → V) (((σ : Γ → X →ₗ[ℂ] X) g : X → X) v) = ((τ : Γ → V →ₗ[ℂ] V) g : V → V) ((f : X → V) v) }),
                (↑f : X →ₗ[ℂ] V).range =
              ⊤ →
            ∀ (W : Submodule ℂ V),
              (∀ (g : Γ), ∀ v ∈ W, ((τ : Γ → V →ₗ[ℂ] V) g : V → V) v ∈ W) →
                W ≠ ⊥ →
                  ∀ (K : Subgroup Γ),
                    UpperTheory.Reformulated.B.SubgroupFixed.HasFixed σ K → ∃ v ∈ W, v ≠ (0 : V) ∧ ∀ u ∈ K, ((τ : Γ → V →ₗ[ℂ] V) u : V → V) v = v := by
  intro Γ X V _ _ _ _ _ σ hσ τ h W hWinv hW K hK
  obtain ⟨x0, hx0, hfix⟩ := hK
  haveI : IsSimpleModule (MonoidAlgebra ℂ Γ) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp hσ
  let W' : Submodule (MonoidAlgebra ℂ Γ) τ.asModule :=
    { carrier := {x | τ.asModuleEquiv x ∈ W}
      add_mem' := fun {a b} ha hb => by
        show τ.asModuleEquiv (a + b) ∈ W
        rw [map_add (f := _)]
        exact W.add_mem ha hb
      zero_mem' := by
        show τ.asModuleEquiv 0 ∈ W
        rw [map_zero]
        exact W.zero_mem
      smul_mem' := fun r x hx => by
        show τ.asModuleEquiv (r • x) ∈ W
        rw [Representation.asModuleEquiv_map_smul]
        exact τ.asAlgebraHom_mem_of_forall_mem W hWinv _ hx r }
  have hW' : W' ≠ ⊥ := by
    intro hbot
    apply hW
    rw [eq_bot_iff]
    intro w hw
    have hmem : τ.asModuleEquiv.symm w ∈ W' := by
      show τ.asModuleEquiv (τ.asModuleEquiv.symm w) ∈ W
      simpa using hw
    rw [hbot, Submodule.mem_bot] at hmem
    simpa using hmem
  have hsup : ∀ S : Submodule (MonoidAlgebra ℂ Γ) τ.asModule,
      (∀ f : σ.asModule →ₗ[MonoidAlgebra ℂ Γ] τ.asModule, LinearMap.range f ≤ S) → S = ⊤ := by
    intro S hS
    let S0 : Submodule ℂ V :=
      (S.restrictScalars ℂ).comap (τ.asModuleEquiv.symm : V →ₗ[ℂ] τ.asModule)
    have hS0 : S0 = ⊤ := by
      rw [eq_top_iff, ← h]
      refine iSup_le fun f => ?_
      rintro _ ⟨x, rfl⟩
      let F : Representation.IntertwiningMap σ τ :=
        f.1.intertwiningMap_of_isIntertwiningMap σ τ f.2
      exact hS (Representation.IntertwiningMap.equivLinearMapAsModule σ τ F)
        ⟨σ.asModuleEquiv.symm x, rfl⟩
    rw [eq_top_iff]
    intro y _
    have hy : τ.asModuleEquiv y ∈ S0 := hS0 ▸ Submodule.mem_top
    simpa [S0] using hy
  obtain ⟨g, hg, hgW⟩ := UpperTheory.Reformulated.B.SubgroupFixed.core hsup W' hW'
  refine ⟨τ.asModuleEquiv (g (σ.asModuleEquiv.symm x0)), hgW ⟨_, rfl⟩, ?_, ?_⟩
  · intro h0
    have h1 : g (σ.asModuleEquiv.symm x0) = 0 := by simpa using h0
    have h2 : σ.asModuleEquiv.symm x0 = 0 := hg (h1.trans (map_zero g).symm)
    exact hx0 (by simpa using h2)
  · intro u hu
    apply τ.asModuleEquiv.symm.injective
    rw [Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply, ← map_smul,
      ← Representation.asModuleEquiv_symm_map_rho, hfix u hu]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumOverPlacesFibre
section
open scoped Classical

theorem UpperTheory.Reformulated.B.SumOverPlacesFibre.sum_fibre_place :
    ∀ (F : Type) [inst : Field F]
    [inst_1 : NumberField F] [NumberField.IsTotallyComplex F] (x : F) (v : NumberField.InfinitePlace F),
    ∑ φ : F →+* ℂ with NumberField.InfinitePlace.mk φ = v, (φ : F → ℂ) x =
      (↑((2 : ℝ) * ((v.embedding : F → ℂ) x).re) : ℂ) := by
  intro F _ _ _ x v
  have hc : v.IsComplex := NumberField.IsTotallyComplex.isComplex v
  have hne : v.embedding ≠ NumberField.ComplexEmbedding.conjugate v.embedding := by
    intro h
    exact (NumberField.InfinitePlace.isComplex_iff.mp hc)
      (NumberField.ComplexEmbedding.isReal_iff.mpr h.symm)
  have hset : (Finset.univ.filter fun φ : F →+* ℂ => NumberField.InfinitePlace.mk φ = v) =
      {v.embedding, NumberField.ComplexEmbedding.conjugate v.embedding} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      have h' : NumberField.InfinitePlace.mk v.embedding = NumberField.InfinitePlace.mk φ := by
        rw [NumberField.InfinitePlace.mk_embedding, h]
      rcases NumberField.InfinitePlace.mk_eq_iff.mp h' with h1 | h1
      · exact Or.inl h1.symm
      · exact Or.inr h1.symm
    · rintro (h | h)
      · rw [h, NumberField.InfinitePlace.mk_embedding]
      · rw [h, NumberField.InfinitePlace.mk_conjugate_eq, NumberField.InfinitePlace.mk_embedding]
  rw [hset, Finset.sum_pair hne, NumberField.ComplexEmbedding.conjugate_coe_eq,
    Complex.add_conj]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TensorHomExt
section
theorem UpperTheory.Reformulated.B.Qk54.tensor_hom_ext :
    ∀ {A A' C Ω : Type}
    [inst : CommRing A] [inst_1 : CommRing A'] [inst_2 : CommRing C] [inst_3 : Algebra A A'] [inst_4 : Algebra A C]
    [inst_5 : CommRing Ω] {u v : TensorProduct A C A' →+* Ω},
    (∀ (c : C), (u : TensorProduct A C A' → Ω) (c ⊗ₜ[A] (1 : A')) = (v : TensorProduct A C A' → Ω) (c ⊗ₜ[A] (1 : A'))) →
      (∀ (b : A'), (u : TensorProduct A C A' → Ω) ((1 : C) ⊗ₜ[A] b) = (v : TensorProduct A C A' → Ω) ((1 : C) ⊗ₜ[A] b)) →
        u = v := by
  intro A A' C Ω _ _ _ _ _ _ u v h₁ h₂
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c b =>
    have e : c ⊗ₜ[A] b = (c ⊗ₜ[A] (1 : A')) * ((1 : C) ⊗ₜ[A] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, h₁, h₂]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
end

