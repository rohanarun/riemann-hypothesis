module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0149
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0223
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Formalism.LocalToGlobal.IndefiniteReal.CongNatCastEqOneTmul
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0595

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLatticeIdempotentPositionInvolutionStable
section
noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial

theorem exists_isIntegral_pow_smul : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ x : B.A,
    ∃ k : ℕ, IsIntegral K.O ((al K a ^ k) • x) := GlobalTheory.T.exists_isIntegral_smallElement_pow_smul

theorem isIntegral_or_of_fieldFactor : ∀ (K : UQ) (B : InvAlg K) (f y z : B.A), IsIdempotentElem f →
    (∀ w, f * w ≠ 0 → ∃ v, f * w * v = f) → f * y * z = f →
    IsIntegral K.O (f * y) ∨ IsIntegral K.O (f * z) := _root_.GlobalTheory.UnitLemma.Desc.isIntegral_or_isIntegral_of_fieldFactor

theorem exists_pow_smul_mem_adjoin_g : ∀ (K : UQ) (B : InvAlg K) (a : K.O), B.P.Separable → K.Small a →
    ∃ N : ℕ, ∀ r : B.A, IsIntegral K.O r → (al K a ^ N) • r ∈ Algebra.adjoin K.O {B.g} := _root_.GlobalTheory.UnitLemma.Desc.pow_smul_mem_adjoin_gen

variable {K : UQ} (B : InvAlg K)

theorem al_ne (a : K.O) (ha : K.Small a) : al K a ≠ 0 := by
  intro h
  exact ha.1 ((IsFractionRing.injective K.O K.E) (by simpa using h))

theorem sigma_smul (c : K.E) (x : B.A) : B.σ (c • x) = K.c c • B.σ x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, B.σ_alg]

theorem isIntegral_idem {f : B.A} (hf : IsIdempotentElem f) : IsIntegral K.O f :=
  ⟨X ^ 2 - X, by
    have : (X ^ 2 - X : K.O[X]) = X ^ 2 - C 1 * X ^ 1 := by simp
    rw [this]; exact monic_X_pow_sub (by simp), by simp [sq, hf.eq]⟩

theorem isIntegral_pow_smul (a : K.O) (n : ℕ) {x : B.A} (hx : IsIntegral K.O x) :
    IsIntegral K.O ((al K a ^ n) • x) := by
  have : (al K a ^ n) • x = algebraMap K.O B.A (a ^ n) * x := by
    simp only [al, Algebra.smul_def, IsScalarTower.algebraMap_apply K.O K.E B.A, map_pow]
  rw [this]; exact isIntegral_algebraMap.mul hx

theorem not_isIntegral_inv_smul (a : K.O) (ha : K.Small a) {f : B.A} (hf : IsIdempotentElem f)
    (hf0 : f ≠ 0) : ¬ IsIntegral K.O ((al K a ^ (-1 : ℤ)) • f) := by
  intro h
  let I : Ideal B.A := Ideal.span {1 - f}
  have hI : I ≠ ⊤ := by
    intro hT
    have : (1 : B.A) ∈ I := hT ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 this
    apply hf0
    calc f = f * (c * (1 - f)) := by rw [hc, mul_one]
      _ = c * (f - f * f) := by ring
      _ = 0 := by rw [hf.eq, sub_self, mul_zero]
  haveI : Nontrivial (B.A ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  have hmk : Ideal.Quotient.mk I f = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), eq_comm, Ideal.Quotient.eq]
    exact Ideal.subset_span rfl
  have h2 : IsIntegral K.O (algebraMap K.E (B.A ⧸ I) (al K a ^ (-1 : ℤ))) := by
    have := h.map (Ideal.Quotient.mkₐ K.O I)
    rwa [Ideal.Quotient.mkₐ_eq_mk, Algebra.smul_def, map_mul, hmk, mul_one,
      Ideal.Quotient.mk_algebraMap] at this
  have h3 : IsIntegral K.O (al K a ^ (-1 : ℤ)) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom K.O K.E (B.A ⧸ I))
      (algebraMap K.E (B.A ⧸ I)).injective).1 h2
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  have hne := al_ne a ha
  have h4 : algebraMap K.O K.E (a * t) = algebraMap K.O K.E 1 := by
    rw [map_mul, ht, map_one, zpow_neg_one]; exact mul_inv_cancel₀ hne
  have h5 : a * t = 1 := IsFractionRing.injective K.O K.E h4
  exact (IsLocalRing.mem_maximalIdeal a).1 ha.2.1 (⟨⟨a, t, h5, by rw [mul_comm]; exact h5⟩, rfl⟩)

theorem smul_mem_of_adjoin (M : Submodule K.O B.A) (hM : ∀ y ∈ M, B.g * y ∈ M) {s : B.A}
    (hs : s ∈ Algebra.adjoin K.O {B.g}) : ∀ m ∈ M, s * m ∈ M := by
  let T : Subalgebra K.O B.A :=
    { carrier := {s | ∀ m ∈ M, s * m ∈ M}
      mul_mem' := fun {x y} hx hy m hm => by rw [mul_assoc]; exact hx _ (hy m hm)
      one_mem' := fun m hm => by rw [one_mul]; exact hm
      add_mem' := fun {x y} hx hy m hm => by rw [add_mul]; exact M.add_mem (hx m hm) (hy m hm)
      zero_mem' := fun m hm => by rw [zero_mul]; exact M.zero_mem
      algebraMap_mem' := fun c m hm => by rw [← Algebra.smul_def]; exact M.smul_mem c hm }
  have : Algebra.adjoin K.O {B.g} ≤ T := Algebra.adjoin_le (by
    intro x hx; rw [Set.mem_singleton_iff.1 hx]; exact hM)
  exact this hs

theorem exists_pos : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι)
    (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S →
    ∃ N : ℕ, ∀ M ∈ B.Lin, ∃ p : ι → ℤ, Pos B a e N M p := by
  intro K B ι _ e π S a hP ha hF
  obtain ⟨N0, hN0⟩ := exists_pow_smul_mem_adjoin_g K B a hP ha
  refine ⟨N0 + 1, fun M hM => ?_⟩
  set t := al K a with ht_def
  have ht : t ≠ 0 := al_ne a ha
  have hct : K.c t = t := ha.2.2
  have hRM : ∀ r : B.A, IsIntegral K.O r → ∀ m ∈ M, (t ^ N0) • (r * m) ∈ M := fun r hr m hm => by
    rw [← smul_mul_assoc]; exact smul_mem_of_adjoin B M hM.2.1 (hN0 r hr) m hm
  have core : ∀ f : B.A, IsIdempotentElem f → (∀ w, f * w ≠ 0 → ∃ v, f * w * v = f) →
      ∀ (q : ℤ) (m : B.A), m ∈ M → ¬ IsIntegral K.O ((t ^ (-q)) • (f * m)) →
      ∀ r : B.A, IsIntegral K.O r → (t ^ (q + N0)) • (f * r) ∈ M := by
    intro f hf hfld q m hm hni r hr
    have hy0 : f * ((t ^ (-q)) • m) ≠ 0 := by
      intro h0; apply hni; rw [← mul_smul_comm, h0]; exact isIntegral_zero
    obtain ⟨z, hz⟩ := hfld _ hy0
    have hfz : IsIntegral K.O (f * z) := by
      rcases isIntegral_or_of_fieldFactor K B f ((t ^ (-q)) • m) z hf hfld hz with h | h
      · exact (hni (by rwa [mul_smul_comm] at h)).elim
      · exact h
    have key : (t ^ (q + N0)) • (f * r) = (t ^ N0) • ((r * (f * z)) * m) := by
      have e1 : f * r = (t ^ (-q)) • ((r * (f * z)) * m) := by
        calc f * r = r * (f * ((t ^ (-q)) • m) * z) := by rw [hz]; ring
          _ = _ := by simp only [Algebra.smul_def]; ring
      rw [e1, smul_smul, ← zpow_add₀ ht, show q + N0 + -q = (N0 : ℤ) by ring, zpow_natCast]
    rw [key]; exact hRM _ (hr.mul hfz) m hm
  have hpos : ∀ i, ∃ pi : ℤ, (∀ r : B.A, IsIntegral K.O r → (t ^ (pi + ↑(N0 + 1))) • (e i * r) ∈ M) ∧
      ∀ m ∈ M, IsIntegral K.O ((t ^ (-pi)) • (e i * m)) := by
    intro i
    obtain ⟨f, hf, hf0, hfld, hS, hnS⟩ := hF.1.2 i
    have hfe : f * e i = f := by
      by_cases hi : i ∈ S
      · rw [(hS hi).1, hf.eq]
      · rw [(hnS hi).2, mul_add, hf.eq, (hnS hi).1, add_zero]
    let P : Set ℤ := {p | ∀ m ∈ M, IsIntegral K.O ((t ^ (-p)) • (e i * m))}
    have hne : P.Nonempty := by
      obtain ⟨s, hs⟩ := hM.1.1
      choose k hk using fun x : B.A => exists_isIntegral_pow_smul K B a ha (e i * x)
      refine ⟨-((s.sup k : ℕ) : ℤ), fun m hm => ?_⟩
      rw [neg_neg, zpow_natCast]
      rw [← hs] at hm
      induction hm using Submodule.span_induction with
      | mem x hx =>
        have hle : k x ≤ s.sup k := Finset.le_sup hx
        rw [← Nat.sub_add_cancel hle, pow_add, ← smul_smul]
        exact isIntegral_pow_smul B a _ (hk x)
      | zero => rw [mul_zero, smul_zero]; exact isIntegral_zero
      | add x y _ _ hx hy => rw [mul_add, smul_add]; exact hx.add hy
      | smul c x _ hx =>
        rw [Algebra.smul_def c x, ← mul_assoc, mul_comm (e i), mul_assoc, ← mul_smul_comm]
        exact isIntegral_algebraMap.mul hx
    have hbdd : BddAbove P := by
      have hm0 : ∃ m ∈ M, f * m ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        have hle : Submodule.span K.E (M : Set B.A) ≤ LinearMap.ker (LinearMap.mulLeft K.E f) := by
          rw [Submodule.span_le]; intro m hm; exact hcon m hm
        rw [hM.1.2] at hle
        have := hle (Submodule.mem_top : (1 : B.A) ∈ ⊤)
        simp at this; exact hf0 this
      obtain ⟨m0, hm0, hfm0⟩ := hm0
      obtain ⟨z, hz⟩ := hfld m0 hfm0
      obtain ⟨k, hk⟩ := exists_isIntegral_pow_smul K B a ha (f * z)
      refine ⟨k, fun p hp => ?_⟩
      by_contra hlt
      push_neg at hlt
      have h1 : IsIntegral K.O ((t ^ (-p)) • (e i * m0)) := hp m0 hm0
      have h2 : IsIntegral K.O ((t ^ (-p)) • (e i * m0) * (t ^ k • (f * z)) * f) :=
        (h1.mul hk).mul (isIntegral_idem B hf)
      have hq : e i * m0 * (f * z) * f = f := by
        calc e i * m0 * (f * z) * f = (f * e i) * m0 * z * f := by ring
          _ = f := by rw [hfe, hz, hf.eq]
      have h3 : (t ^ (-p)) • (e i * m0) * (t ^ k • (f * z)) * f = (t ^ ((k : ℤ) - p)) • f := by
        rw [sub_eq_add_neg, zpow_add₀ ht, zpow_natCast]
        simp only [Algebra.smul_def, map_mul]
        linear_combination (algebraMap K.E B.A (t ^ (-p)) * algebraMap K.E B.A (t ^ k)) * hq
      have h4 : (t ^ (-1 : ℤ)) • f = (t ^ ((p - k - 1 : ℤ).toNat)) • ((t ^ ((k : ℤ) - p)) • f) := by
        rw [smul_smul, ← zpow_natCast, ← zpow_add₀ ht, Int.toNat_of_nonneg (by omega),
          show (p - k - 1 : ℤ) + (k - p) = -1 by ring]
      exact not_isIntegral_inv_smul B a ha hf hf0 (h4 ▸ isIntegral_pow_smul B a _ (h3 ▸ h2))
    obtain ⟨pi, hmem, hnot⟩ : ∃ pi, pi ∈ P ∧ pi + 1 ∉ P :=
      ⟨sSup P, Int.csSup_mem hne hbdd, fun h => by have := le_csSup hbdd h; omega⟩
    refine ⟨pi, fun r hr => ?_, hmem⟩
    have hnot' : ¬ ∀ m ∈ M, IsIntegral K.O ((t ^ (-(pi + 1))) • (e i * m)) := hnot
    push_neg at hnot'
    obtain ⟨m, hm, hni⟩ := hnot'
    have hexp : pi + ↑(N0 + 1) = (pi + 1) + N0 := by push_cast; ring
    rw [hexp]
    by_cases hi : i ∈ S
    · rw [(hS hi).1] at hni ⊢
      exact core f hf hfld (pi + 1) m hm hni r hr
    · obtain ⟨hff, hei⟩ := hnS hi
      have Hf : ∀ r : B.A, IsIntegral K.O r → (t ^ (pi + 1 + N0)) • (f * r) ∈ M := by
        by_cases h1 : IsIntegral K.O ((t ^ (-(pi + 1))) • (f * m))
        · have h2 : ¬ IsIntegral K.O ((t ^ (-(pi + 1))) • (B.σ f * m)) := by
            intro h2; apply hni; rw [hei, add_mul, smul_add]; exact h1.add h2
          have h3 : ¬ IsIntegral K.O ((t ^ (-(pi + 1))) • (f * B.σ m)) := by
            intro h3; apply h2
            have := isIntegral_sigma _ B _ h3
            rwa [sigma_smul, map_mul, B.σ_σ, map_zpow₀, hct] at this
          exact core f hf hfld (pi + 1) (B.σ m) (hM.2.2 m hm) h3
        · exact core f hf hfld (pi + 1) m hm h1
      rw [hei, add_mul, smul_add]
      refine M.add_mem (Hf r hr) ?_
      have := hM.2.2 _ (Hf (B.σ r) (isIntegral_sigma _ B _ hr))
      rwa [sigma_smul, map_mul, B.σ_σ, map_zpow₀, hct] at this
  choose p hp using hpos
  exact ⟨p, hp⟩

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmulOfDvdRepr
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.GamModX

theorem full_of_std {L M : Type} [Field L] [AddCommGroup M] [Module L M] {D : Submodule L M}
    {Λ : Submodule L (ℤ → M)} (h : Std D Λ) : Full D Λ :=
  ⟨0, fun f h1 h2 => (h f).2 ⟨h1, by simpa using h2⟩⟩

theorem shift_mem {L M : Type} [Field L] [AddCommGroup M] [Module L M] {D : Submodule L M}
    {Λ : Submodule L (ℤ → M)} (h : Std D Λ) (e y : ℤ → M) (he : e ∈ Λ) (u : L)
    (hy : ∀ k : ℤ, y k = u ^ k • e k - e k) :
    ∃ f ∈ Λ, ∀ j : ℤ, y j = f (j - ((1 : ℕ) : ℤ)) := by
  obtain ⟨h1, h2⟩ := (h e).1 he
  refine ⟨fun k => y (k + 1), (h _).2 ⟨fun k => ?_, fun k hk => ?_⟩, fun j => by simp⟩
  · rw [hy]; exact D.sub_mem (D.smul_mem _ (h1 _)) (h1 _)
  · rw [hy]
    rcases (show k + 1 < 0 ∨ k + 1 = 0 by omega) with h3 | h3
    · simp [h2 _ h3]
    · simp [h3]

theorem conv_one {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : ℤ → M) :
    conv (1 : PowerSeries L) f = f := by
  funext k
  unfold conv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

theorem exists_smul_of_dvd_repr {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M]
    [Fintype ι] (N : Submodule A M) (nb : Module.Basis ι A ↥N) (a : A) (z : ↥N)
    (hz : ∀ j, a ^ 1 ∣ nb.repr z j) : ∃ y ∈ N, (z : M) = a • y := by
  choose c hc using hz
  refine ⟨((∑ j, c j • nb j : ↥N) : M), Subtype.property _, ?_⟩
  have key : z = a • ∑ j, c j • nb j := by
    conv_lhs => rw [← nb.sum_repr z]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc j, pow_one, mul_smul]
  exact congrArg Subtype.val key


set_option maxHeartbeats 1000000 in
theorem ex_of_val {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P}
    {F : LocFon l P AI H} (C : LocCmpT l P AI H F) {K : FinExt l} {s : ℕ} {LL : FinExt l}
    (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) (i : Let K) (ζ : ↥LL.1) (m : ℕ)
    (hζ : ζ ^ (l ^ m) = 1) (g : (H.W K s LL h).Gam)
    (hg : (m : WithTop ℚ) ≤
      P.v LL (algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ g : ↥(OL LL)) - 1))
    (x : ↥((H.W K s LL h).N T)) (k : ℤ) :
    ex C h T i ζ ⟨_, (H.W K s LL h).N_Γ T g x x.2⟩ k =
      (algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ g : ↥(OL LL))) ^ k • ex C h T i ζ x k := by
  obtain ⟨j, hj, hord⟩ := (Nat.dvd_prime_pow (Fact.out : l.Prime)).1 (orderOf_dvd_of_pow_eq_one hζ)
  have hjs : (j : WithTop ℚ) ≤ (m : WithTop ℚ) := by exact_mod_cast hj
  exact (C.C K s LL h).tie.levB_Γ T hT g i ζ ζ j 1
    (by rw [P.PD_p, ← hord]; exact IsPrimitiveRoot.orderOf ζ)
    (by rw [Nat.cast_one]; exact hjs.trans hg) (pow_one ζ).symm x
    ((H.W K s LL h).N_Γ T g x x.2) k


set_option maxHeartbeats 1000000 in
theorem sub_mem_X_of_val : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (_ : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL), let W := (HW l).W K s LL h;
    ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ g : W.Gam,
      ((s - 1 : ℕ) : WithTop ℚ) ≤
        (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL)) - 1) →
      ∀ x ∈ W.N T, ∃ y ∈ W.N T, W.γD T g x - x = W.X • y := by
  intro D HW F Cm l _ K s LL h W T hT g hg x hx
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  let x' : ↥(W.N T) := ⟨x, hx⟩
  let g' : ↥(W.N T) := ⟨_, W.N_Γ T g x hx⟩
  refine exists_smul_of_dvd_repr (W.N T) nb W.X (g' - x') fun j => ?_
  refine (GlobalTheory.T.wachWeierstrass_test_and_density D HW l K s LL h).2.1 1 _ fun i ζ hζ => ?_
  have hS := GlobalTheory.T.wachLattice_expansions_std_below_level D HW F Cm l K s LL h T hT i ζ hζ
  have hprim : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := by
    obtain ⟨j, -, hord⟩ :=
      (Nat.dvd_prime_pow (Fact.out : l.Prime)).1 (orderOf_dvd_of_pow_eq_one hζ)
    exact ⟨j, hord ▸ IsPrimitiveRoot.orderOf ζ⟩
  have hI := (GlobalTheory.T.wachExpansion_basis_divisibility D HW F Cm l K s LL h T hT i ζ hprim (full_of_std hS)).2 _ nb
  refine (hI.2.2 (g' - x') 1).1 ?_ j
  refine shift_mem hS (ex (Cm l) h T i ζ x') _ ?_
    (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL))) fun k => ?_
  · exact Submodule.subset_span ⟨1, x', (conv_one _).symm⟩
  · rw [← ex_of_val (Cm l) h T hT i ζ (s - 1) hζ g hg x' k]
    unfold ex
    rw [map_sub]
    rfl


set_option maxHeartbeats 1000000 in
theorem gam_mod_π_mod_X : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (_ : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL), let W := (HW l).W K s LL h;
    ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ →
      (∀ g : W.Gam, ∀ x ∈ W.N T, W.γD T g x ∈ W.N T) ∧
      (∀ g : W.Gam, ∀ x ∈ W.N T, ∃ y ∈ W.N T, W.γD T g x - x = (letπ : AA K LL) • y) ∧
      ∀ x ∈ W.N T, ∃ y ∈ W.N T, W.γD T W.gam x - x = W.X • y := by
  intro D HW F Cm l _ K s LL h W T hT
  refine ⟨W.N_Γ T, W.N_π T, sub_mem_X_of_val D HW F Cm l K s LL h T hT W.gam ?_⟩
  have hg := W.gam_gen
  rw [(HW l).W_s] at hg
  have hs : ((s - 1 : ℕ) : WithTop ℚ) ≤ (s : WithTop ℚ) := by exact_mod_cast Nat.sub_le s 1
  exact hs.trans hg.ge

end GlobalTheory.NL.GamModX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRationalConjMemBoundedCompact
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

open scoped TensorProduct

namespace GlobalTheory.StabFin

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem norm_entry_le_one {g : GL (Fin n) L} (hg : g ∈ GQ0 L n) (φ : L →+* ℂ) (i j : Fin n) :
    ‖φ ((g : Matrix (Fin n) (Fin n) L) i j)‖ ≤ 1 := by
  have h0 : (g : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) g = 1 := hg
  have h1 := congrFun (congrFun h0 i) i
  simp only [Matrix.mul_apply, conjT, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply_eq] at h1
  have h2 := congrArg φ h1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_one] at h2
  have h3 : ∑ k, ((‖φ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := IsCMField.complexEmbedding_complexConj L φ ((g : Matrix (Fin n) (Fin n) L) i k)
    rw [show ((IsCMField.complexConj L : L →+* L) ((g : Matrix (Fin n) (Fin n) L) i k)) =
      IsCMField.complexConj L ((g : Matrix (Fin n) (Fin n) L) i k) from rfl, this, Complex.mul_conj', Complex.ofReal_pow]
  have h4 : ∑ k, ‖φ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2 = 1 := by exact_mod_cast h3
  have h5 : ‖φ ((g : Matrix (Fin n) (Fin n) L) i j)‖ ^ 2 ≤ 1 := by
    rw [← h4]
    exact Finset.single_le_sum (f := fun k => ‖φ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  nlinarith [norm_nonneg (φ ((g : Matrix (Fin n) (Fin n) L) i j))]

theorem exists_common_denom {ι : Type} [Fintype ι] (x : ι → AL L) :
    ∃ D : ℕ, 0 < D ∧ ∀ a, (D : AL L) * x a ∈ ALint L := by
  classical
  choose d hd0 hd using fun a => Formalism.IndefR.principalLevelFrame.cong_nat_denom (x a)
  refine ⟨∏ a, d a, Finset.prod_pos fun a _ => hd0 a, fun a => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), Nat.cast_mul, mul_comm ((d a : ℕ) : AL L), mul_assoc]
  exact Subring.mul_mem _ (natCast_mem _ _) (hd a)

theorem exists_rat (γ : GQ L n) : ∃ g : GL (Fin n) L, g ∈ GQ0 L n ∧
    ∀ i j, (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j =
      ((g : Matrix (Fin n) (Fin n) L) i j) ⊗ₜ[NumberField.maximalRealSubfield L] (1 : AFplus L) := by
  have h : ((γ : GAf L n) : GL (Fin n) (AL L)) ∈ (GQ0 L n).map (Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L)) := Subgroup.mem_subgroupOf.1 γ.2
  obtain ⟨g, hg, he⟩ := Subgroup.mem_map.1 h
  refine ⟨g, hg, fun i j => ?_⟩
  rw [← he]
  rfl

theorem isIntegral_of_mem (z : L) (hz : z ⊗ₜ[NumberField.maximalRealSubfield L] (1 : AFplus L) ∈ ALint L) :
    IsIntegral ℤ z := by
  have hle : ALint L ≤ Formalism.MainNotions.S.IntAf (NumberField.maximalRealSubfield L) L := by
    rw [ReciprocityTheory.Aut.ALint, Subring.closure_le]
    rintro x (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨⟨(y : L), y, rfl⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  exact Formalism.UG.P.csGlob_int (F := NumberField.maximalRealSubfield L) z (hle hz)

end GlobalTheory.StabFin

open scoped TensorProduct

namespace GlobalTheory.StabFin

theorem finite_conj_mem : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J : Subgroup (GAf L n)),
    IsBounded J → ∀ t : GAf L n, Finite {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ J} := by
  intro L _ _ _ n J hJ t
  classical
  obtain ⟨F, hF⟩ := hJ
  let M : GAf L n → Matrix (Fin n) (Fin n) (AL L) := fun a => ((a : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))
  obtain ⟨D, hD0, hD⟩ := exists_common_denom (L := L) (ι := (F × Fin n × Fin n) ⊕ (Fin n × Fin n))
    (fun a => match a with
      | .inl ⟨f, i, k⟩ => M (t * f) i k
      | .inr ⟨l, j⟩ => M t⁻¹ l j)
  have key : ∀ γ : GQ L n, t⁻¹ * (γ : GAf L n) * t ∈ J → ∀ i j, ((D : AL L) * D) * M γ i j ∈ ALint L := by
    intro γ hγ i j
    obtain ⟨f, hf, hu⟩ := hF _ hγ
    have hu' : ∀ a b, M (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) a b ∈ ALint L := hu
    have e : (γ : GAf L n) = (t * f) * (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) * t⁻¹ := by group
    have eM : M γ = M (t * f) * M (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) * M t⁻¹ := by
      conv_lhs => rw [e]
      simp only [M, Subgroup.coe_mul, Units.val_mul]
    rw [eM, Matrix.mul_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have e2 : ((D : AL L) * D) * (M (t * f) i k * M (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) k l * M t⁻¹ l j) =
        ((D : AL L) * M (t * f) i k) * M (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) k l * ((D : AL L) * M t⁻¹ l j) := by ring
    rw [e2]
    exact Subring.mul_mem _ (Subring.mul_mem _ (hD (.inl ⟨⟨f, hf⟩, i, k⟩)) (hu' k l)) (hD (.inr ⟨l, j⟩))
  set T : Set L := {z : L | IsIntegral ℤ z ∧ ∀ φ : L →+* ℂ, ‖φ z‖ ≤ ((D * D : ℕ) : ℝ)} with hT
  have hTfin : T.Finite := NumberField.Embeddings.finite_of_norm_le L ℂ _
  have : Finite T := hTfin.to_subtype
  choose gs hgs0 hgs using exists_rat (L := L) (n := n)
  have hmem : ∀ x : {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ J}, ∀ i j,
      ((D * D : ℕ) : L) * (gs x.1 : Matrix (Fin n) (Fin n) L) i j ∈ T := by
    intro x i j
    refine ⟨isIntegral_of_mem _ ?_, fun φ => ?_⟩
    · have e : (((D * D : ℕ) : L) * (gs x.1 : Matrix (Fin n) (Fin n) L) i j) ⊗ₜ[NumberField.maximalRealSubfield L] (1 : AFplus L) =
          ((D : AL L) * D) * M x.1 i j := by
        simp only [M]
        rw [hgs, ← Algebra.TensorProduct.includeLeftRingHom_apply, ← Algebra.TensorProduct.includeLeftRingHom_apply,
          map_mul, map_natCast]
        push_cast; ring
      rw [e]
      exact key x.1 x.2 i j
    · rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) (norm_entry_le_one (hgs0 x.1) φ i j)
  refine Finite.of_injective (fun x => fun i j => (⟨_, hmem x i j⟩ : T)) ?_
  intro x y hxy
  have hD' : ((D * D : ℕ) : L) ≠ 0 := by exact_mod_cast (Nat.mul_pos hD0 hD0).ne'
  have hg : ∀ i j, (gs x.1 : Matrix (Fin n) (Fin n) L) i j = (gs y.1 : Matrix (Fin n) (Fin n) L) i j := by
    intro i j
    have := congrArg Subtype.val (congrFun (congrFun hxy i) j)
    exact mul_left_cancel₀ hD' this
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [hgs x.1 i j, hgs y.1 i j, hg i j]

end GlobalTheory.StabFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlaces
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineAdmissible

theorem fontaineProperties_all_places : ∀ D : D7, Formalism.MainNotions.PairedCharacterCondition.FontaineAtPlacesOverL (D := D) := by
  intro D l _ K LL
  exact GlobalTheory.FontaineAll.fontaineAt_all D l K LL

end GlobalTheory.FontaineAdmissible
end

