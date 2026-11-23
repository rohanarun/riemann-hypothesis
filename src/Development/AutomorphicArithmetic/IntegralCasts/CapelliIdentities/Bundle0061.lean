module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TendstoCut
section
open scoped Classical

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi11.Af :
    (F : Type) → [inst : Field F] → [NumberField F] → Type :=
    fun (F : Type) [Field F] [NumberField F] ↦ IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F

theorem UpperTheory.Reformulated.B.Qi11.aux2 :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      (a : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v),
      ∀ᶠ (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) in Filter.cofinite,
        Pi.single v a x ∈
          (↑(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F x) :
            Set (IsDedekindDomain.HeightOneSpectrum.adicCompletion F x)) := by
  intro F _ _ v a
  refine (Set.finite_singleton v).subset fun x hx => ?_
  by_contra h
  apply hx
  have hne : x ≠ v := h
  simp only [Set.mem_setOf_eq, Pi.single_eq_of_ne hne]
  exact zero_mem _

noncomputable def UpperTheory.Reformulated.B.Qi11.sglV :
    {F : Type} →
      [inst : Field F] →
        [inst_1 : NumberField F] →
          (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
            IsDedekindDomain.HeightOneSpectrum.adicCompletion F v → UpperTheory.Reformulated.B.Qi11.Af F :=
    fun {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
        (a : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v) ↦
      (⟨Pi.single v a, UpperTheory.Reformulated.B.Qi11.aux2 v a⟩ :
        { x :
          (i : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
            (fun (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
                IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)
              i //
          ∀ᶠ (i : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) in Filter.cofinite,
            x i ∈
              (fun (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
                  (↑(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v) :
                    Set (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)))
                i })

noncomputable def UpperTheory.Reformulated.B.Qi11.sglS :
    {F : Type} →
      [inst : Field F] →
        [inst_1 : NumberField F] →
          Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) → UpperTheory.Reformulated.B.Qi11.Af F :=
    fun {F : Type} [Field F] [NumberField F]
        (A : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) ↦
      ∑ v ∈ A, UpperTheory.Reformulated.B.Qi11.sglV v (1 : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)

private theorem UpperTheory.Reformulated.B.Qi11.tendsto_cut {ι : Type*} {R : ι → Type*} [∀ i, Zero (R i)]
    [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)} (h0 : ∀ i, (0 : R i) ∈ A i)
    (y z : RestrictedProduct R A Filter.cofinite) (hz : ∀ i, z i = 0)
    (f : Finset ι → RestrictedProduct R A Filter.cofinite)
    (hf : ∀ B i, f B i = if i ∈ B then 0 else y i) :
    Filter.Tendsto f Filter.atTop (nhds z) := by
  have hS : Filter.cofinite ≤ Filter.principal {i | y i ∈ A i} := Filter.le_principal_iff.2 y.2
  let g : Finset ι → RestrictedProduct R A (Filter.principal {i | y i ∈ A i}) := fun B =>
    ⟨fun i => if i ∈ B then 0 else y i, fun i hi => by
      show (if i ∈ B then 0 else y i) ∈ A i
      split_ifs
      · exact h0 i
      · exact hi⟩
  let o : RestrictedProduct R A (Filter.principal {i | y i ∈ A i}) := ⟨fun _ => 0, fun i _ => h0 i⟩
  have hg : Filter.Tendsto g Filter.atTop (nhds o) := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro i
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({i} : Finset ι)] with B hB
    have hi : i ∈ B := hB (Finset.mem_singleton_self i)
    show (0 : R i) = if i ∈ B then 0 else y i
    rw [if_pos hi]
  have h1 : f = RestrictedProduct.inclusion R A hS ∘ g :=
    funext fun B => RestrictedProduct.ext _ _ fun i => hf B i
  have h2 : z = RestrictedProduct.inclusion R A hS o := RestrictedProduct.ext _ _ fun i => hz i
  rw [h1, h2]
  exact ((RestrictedProduct.continuous_inclusion hS).tendsto o).comp hg

private theorem UpperTheory.Reformulated.B.Qi11.sglS_apply {F : Type} [Field F] [NumberField F]
    (A : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    UpperTheory.Reformulated.B.Qi11.sglS A w = if w ∈ A then 1 else 0 := by
  induction A using Finset.induction_on with
  | empty => rfl
  | insert v A hv ih =>
    have h : UpperTheory.Reformulated.B.Qi11.sglS (insert v A) =
        UpperTheory.Reformulated.B.Qi11.sglV v 1 + UpperTheory.Reformulated.B.Qi11.sglS A := Finset.sum_insert hv
    have h' : UpperTheory.Reformulated.B.Qi11.sglS (insert v A) w =
        (Pi.single v 1 : ∀ u, IsDedekindDomain.HeightOneSpectrum.adicCompletion F u) w +
          UpperTheory.Reformulated.B.Qi11.sglS A w := by
      rw [h]
      rfl
    rw [h', ih]
    by_cases hw : w = v
    · subst hw
      simp [hv]
    · simp [hw]

theorem UpperTheory.Reformulated.B.Qi11.tendsto_fin :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] (y : UpperTheory.Reformulated.B.Qi11.Af F),
      Filter.Tendsto
        (fun (A : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) ↦
          ((1 : UpperTheory.Reformulated.B.Qi11.Af F) - UpperTheory.Reformulated.B.Qi11.sglS A) * y)
        Filter.atTop (nhds (0 : UpperTheory.Reformulated.B.Qi11.Af F)) := by
  intro F _ _ y
  have key := UpperTheory.Reformulated.B.Qi11.tendsto_cut
    (R := fun v => IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)
    (A := fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) =>
      SetLike.coe (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v))
    (fun v => zero_mem _)
  refine key y (0 : UpperTheory.Reformulated.B.Qi11.Af F) (fun w => ?_)
    (fun B => ((1 - UpperTheory.Reformulated.B.Qi11.sglS B) * y : UpperTheory.Reformulated.B.Qi11.Af F)) fun B w => ?_
  · rfl
  · show (1 - UpperTheory.Reformulated.B.Qi11.sglS B w) * y w = if w ∈ B then 0 else y w
    rw [UpperTheory.Reformulated.B.Qi11.sglS_apply]
    split_ifs <;> simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ThetaInvolution
section
universe u_1 u_3

namespace UpperTheory.Reformulated.B.ThetaInvolution

noncomputable def Jmat (R : Type u_1) [CommRing R] (m : ℕ) : Matrix (Fin m) (Fin m) R :=
  fun i j ↦ if j = i.rev then (1 : R) else (0 : R)

theorem aux2 {R : Type u_1} [CommRing R] (m : ℕ) :
    Jmat R m * Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · simp only [Jmat, Matrix.one_apply, if_true, one_mul, Fin.rev_rev]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (fun e => h e.symm), if_neg h]
  · intro k _ hk
    simp [Jmat, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

noncomputable def Jgl (R : Type u_1) [CommRing R] (m : ℕ) : GL (Fin m) R :=
  { val := Jmat R m, inv := Jmat R m, val_inv := aux2 m, inv_val := aux2 m :
    (Matrix (Fin m) (Fin m) R)ˣ }

theorem aux4 {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) :
    (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]

theorem aux5 {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) :
    (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]

noncomputable def trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R]
    (g : GL n R) : GL n R :=
  { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose,
    val_inv := aux4 g, inv_val := aux5 g : (Matrix n n R)ˣ }

noncomputable def theta {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) : GL (Fin m) R :=
  Jgl R m * trInv g * Jgl R m

private theorem Jgl_mul_self (R : Type u_1) [CommRing R] (m : ℕ) : Jgl R m * Jgl R m = 1 :=
  Units.ext (aux2 m)

private theorem trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R]
    (g h : GL n R) : trInv (g * h) = trInv g * trInv h := by
  apply Units.ext
  change (((g * h)⁻¹ : GL n R) : Matrix n n R).transpose =
    ((g⁻¹ : GL n R) : Matrix n n R).transpose * ((h⁻¹ : GL n R) : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R]
    (g : GL n R) : trInv (trInv g) = g := by
  apply Units.ext
  change (g : Matrix n n R).transpose.transpose = (g : Matrix n n R)
  exact Matrix.transpose_transpose _

private theorem trInv_Jgl (R : Type u_1) [CommRing R] (m : ℕ) : trInv (Jgl R m) = Jgl R m := by
  apply Units.ext
  change (Jmat R m).transpose = Jmat R m
  ext i j
  simp only [Matrix.transpose_apply, Jmat]
  by_cases h : j = i.rev
  · rw [if_pos h, if_pos (by rw [h, Fin.rev_rev])]
  · rw [if_neg h, if_neg (fun e => h (by rw [e, Fin.rev_rev]))]

theorem aux8 {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) : theta (theta g) = g := by
  have hJ := Jgl_mul_self R m
  simp only [theta, trInv_mul, trInv_trInv, trInv_Jgl]
  calc _ = (Jgl R m * Jgl R m) * g * (Jgl R m * Jgl R m) := by simp only [mul_assoc]
    _ = g := by rw [hJ, one_mul, mul_one]

theorem aux9 {m : ℕ} {R : Type u_1} [CommRing R] (g h : GL (Fin m) R) :
    theta (g * h) = theta g * theta h := by
  have hJ := Jgl_mul_self R m
  simp only [theta, trInv_mul]
  calc _ = Jgl R m * trInv g * 1 * trInv h * Jgl R m := by rw [mul_one]; simp only [mul_assoc]
    _ = _ := by rw [← hJ]; simp only [mul_assoc]

noncomputable def thetaAut (m : ℕ) (R : Type u_1) [CommRing R] : MulAut (GL (Fin m) R) :=
  { toFun := theta, invFun := theta, left_inv := aux8, right_inv := aux8, map_mul' := aux9 :
    GL (Fin m) R ≃* GL (Fin m) R }

theorem aux11 (m : ℕ) (R : Type u_1) [CommRing R] :
    (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R) =
      (1 : MulAut (GL (Fin m) R)) :=
  if_pos rfl

private theorem thetaAut_mul_self (m : ℕ) (R : Type u_1) [CommRing R] :
    thetaAut m R * thetaAut m R = 1 :=
  MulEquiv.ext (fun g => aux8 g)

theorem aux12 (m : ℕ) (R : Type u_1) [CommRing R] (s t : ℤˣ) :
    (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R) =
      (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R) *
        if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R := by
  have hn : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · simp
  · simp [hn]
  · simp [hn]
  · simp [hn, thetaAut_mul_self]

noncomputable def sgnAct (m : ℕ) (R : Type u_1) [CommRing R] : ℤˣ →* MulAut (GL (Fin m) R) :=
  { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R,
    map_one' := aux11 m R, map_mul' := aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def GG (m : ℕ) (R : Type u_1) [CommRing R] : Type u_1 :=
  GL (Fin m) R ⋊[sgnAct m R] ℤˣ

@[reducible] noncomputable def ofGL {m : ℕ} {R : Type u_1} [CommRing R] : GL (Fin m) R →* GG m R :=
  SemidirectProduct.inl

noncomputable def conjBy {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G]
    (h : GL (Fin m) R) (r : G →* GG m R) : G →* GG m R :=
  (MulAut.conj (ofGL h : GG m R)).toMonoidHom.comp r

theorem conjBy_conjBy {C D : Type} [CommRing C] [Group D] (h h' : GL (Fin (3 : ℕ)) C)
    (r : D →* GG (3 : ℕ) C) : conjBy (h * h')⁻¹ (conjBy h r) = conjBy h'⁻¹ r := by
  ext1 x
  have e1 : (ofGL (h * h')⁻¹ : GG 3 C) = (ofGL h * ofGL h')⁻¹ := by rw [map_inv, map_mul]
  have e2 : (ofGL h'⁻¹ : GG 3 C) = (ofGL h')⁻¹ := map_inv _ _
  change MulAut.conj (ofGL (h * h')⁻¹) (MulAut.conj (ofGL h) (r x)) = MulAut.conj (ofGL h'⁻¹) (r x)
  rw [e1, e2]
  generalize (ofGL h : GG 3 C) = a
  generalize (ofGL h' : GG 3 C) = b
  generalize r x = y
  simp only [MulAut.conj_apply]
  group

end UpperTheory.Reformulated.B.ThetaInvolution
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TmASmSum
section
namespace UpperTheory.Reformulated.B.Qf26

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

theorem tmA_sm_sum.{u_1} :
    ∀ {n : ℕ} {ε : Fin n → Bool} {ι : Type u_1} (s : Finset ι) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ),
      (∀ i ∈ s, SmoothOnG ε (F i)) → SmoothOnG ε (fun x ↦ ∑ i ∈ s, F i x) := by
  intro n ε ι s F h g₀ hg
  classical
  choose! U G hUo hUm hG hE using fun i hi => h i hi g₀ hg
  refine ⟨⋂ i ∈ s, U i, fun x => ∑ i ∈ s, G i x, isOpen_biInter_finset hUo, ?_, ?_, ?_⟩
  · exact Set.mem_iInter₂.2 hUm
  · exact ContDiffOn.sum fun i hi => (hG i hi).mono (Set.biInter_subset_of_mem hi)
  · intro g hgU hgJ
    exact Finset.sum_congr rfl fun i hi => hE i hi g (Set.mem_iInter₂.1 hgU i hi) hgJ

end UpperTheory.Reformulated.B.Qf26
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TorsSatMult
section
theorem UpperTheory.Reformulated.B.Qi35.torsSat_mult :
    ∀ {M : Type} [inst : AddCommGroup M] (L : Set M)
    (N : Submodule ℤ M),
    (∀ x ∈ L, ∃ (n : ℤ), n ≠ (0 : ℤ) ∧ n • x ∈ N) → ∀ x ∈ Submodule.span ℤ L, ∃ (n : ℤ), n ≠ (0 : ℤ) ∧ n • x ∈ N := by
  intro M _ L N h x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact N.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact N.smul_mem b hay
    · rw [mul_smul]
      exact N.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    refine ⟨a, ha, ?_⟩
    rw [smul_comm]
    exact N.smul_mem c hay
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TorsStep
section
noncomputable def UpperTheory.Reformulated.B.Qf15.CardLe :
    Type → ℕ → Prop :=
    fun (M : Type) (B : ℕ) ↦ Finite M ∧ Nat.card M ≤ B

noncomputable def UpperTheory.Reformulated.B.Qf15.TorsLe :
    (M : Type) → [AddCommGroup M] → ℕ → Prop :=
    fun (M : Type) [AddCommGroup M] (B : ℕ) ↦ Finite ↥(AddCommGroup.torsion M) ∧ Nat.card ↥(AddCommGroup.torsion M) ≤ B

theorem UpperTheory.Reformulated.B.Qf15.torsStep :
    ∀ (A B C : Type) [inst : AddCommGroup A] [inst_1 : AddCommGroup B] [inst_2 : AddCommGroup C] (f : A →+ B) (g : B →+ C)
      (a c : ℕ),
      Function.Exact (⇑f : A → B) (⇑g : B → C) →
        UpperTheory.Reformulated.B.Qf15.CardLe A a → UpperTheory.Reformulated.B.Qf15.TorsLe C c → UpperTheory.Reformulated.B.Qf15.TorsLe B (a * c) := by
  intro A B C _ _ _ f g a c hfg hA hC
  obtain ⟨hAf, hAc⟩ := hA
  obtain ⟨hCf, hCc⟩ := hC
  let φ : AddCommGroup.torsion B →+ AddCommGroup.torsion C :=
    (g.comp (AddCommGroup.torsion B).subtype).codRestrict _
      (fun x => g.isOfFinAddOrder x.2)
  have hk : ∀ x : φ.ker, ∃ y : A, f y = ((x : AddCommGroup.torsion B) : B) := by
    intro x
    have hx : φ x = 0 := x.2
    exact (hfg _).1 (congrArg Subtype.val hx)
  choose s hs using hk
  have hsi : Function.Injective s := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    rw [← hs x, ← hs y, h]
  haveI : Finite φ.ker := Finite.of_injective s hsi
  have e := (QuotientAddGroup.quotientKerEquivRange φ).toEquiv
  haveI : Finite (AddCommGroup.torsion B ⧸ φ.ker) := Finite.of_equiv _ e.symm
  have h1 : Nat.card φ.ker ≤ a := (Nat.card_le_card_of_injective s hsi).trans hAc
  have h2 : Nat.card (AddCommGroup.torsion B ⧸ φ.ker) ≤ c := by
    rw [Nat.card_congr e]
    exact (Nat.card_le_card_of_injective _ Subtype.val_injective).trans hCc
  refine ⟨Finite.of_equiv _ (AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := φ.ker)).symm, ?_⟩
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker, mul_comm]
  exact Nat.mul_le_mul h1 h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TotalDegreeLinear
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.TotalDegreeLinear.PV :
    Type → Type → Type → Type :=
    fun (ι A B : Type) ↦ MvPolynomial (ι × A ⊕ ι × B) ℂ

noncomputable def UpperTheory.Reformulated.B.TotalDegreeLinear.sub :
    {ι A B : Type} → [Fintype ι] → Matrix ι ι ℂ → Matrix ι ι ℂ → UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B →ₐ[ℂ] UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B :=
    fun {ι A B : Type} [Fintype ι] (g h : Matrix ι ι ℂ) ↦
      MvPolynomial.aeval
        (Sum.elim
          (fun (x : ι × A) ↦
            ∑ j : ι, (MvPolynomial.C : ℂ → MvPolynomial (ι × A ⊕ ι × B) ℂ) (g x.1 j) * MvPolynomial.X (Sum.inl (j, x.2)))
          fun (y : ι × B) ↦
          ∑ j : ι, (MvPolynomial.C : ℂ → MvPolynomial (ι × A ⊕ ι × B) ℂ) (h y.1 j) * MvPolynomial.X (Sum.inr (j, y.2)))

private lemma UpperTheory.Reformulated.B.TotalDegreeLinear.totalDegree_aeval_le {σ τ : Type}
    (f : σ → MvPolynomial τ ℂ) (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ ℂ) :
    (MvPolynomial.aeval f p).totalDegree ≤ p.totalDegree := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ d.support, (f i ^ d i).totalDegree
      ≤ ∑ i ∈ d.support, d i := Finset.sum_le_sum fun i _ =>
        (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hf i))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

private lemma UpperTheory.Reformulated.B.TotalDegreeLinear.totalDegree_linear_le {ι τ : Type} [Fintype ι]
    (c : ι → ℂ) (v : ι → τ) :
    (∑ j : ι, (MvPolynomial.C (c j) : MvPolynomial τ ℂ) * MvPolynomial.X (v j)).totalDegree ≤ 1 := by
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_X _).le

theorem UpperTheory.Reformulated.B.TotalDegreeLinear.main :
    ∀ {ι A B : Type} [inst : Fintype ι] (g h : Matrix ι ι ℂ) (p : UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B),
      MvPolynomial.totalDegree ((UpperTheory.Reformulated.B.TotalDegreeLinear.sub g h : UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B → UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B) p) ≤
        MvPolynomial.totalDegree p := by
  intro ι A B _ g h p
  refine UpperTheory.Reformulated.B.TotalDegreeLinear.totalDegree_aeval_le _ ?_ p
  rintro (x | y)
  · exact UpperTheory.Reformulated.B.TotalDegreeLinear.totalDegree_linear_le _ _
  · exact UpperTheory.Reformulated.B.TotalDegreeLinear.totalDegree_linear_le _ _
end

