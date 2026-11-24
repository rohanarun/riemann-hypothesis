module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0120
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0050
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMulHeightMinpolyCoeffLeRelativeHeight
section
open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal

namespace GlobalTheory.RatCount.CoefHt

theorem mult_le_two (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) : w.mult ≤ 2 := by
  unfold InfinitePlace.mult; split_ifs <;> norm_num


open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
open Classical in
theorem exists_mulHeight_coeff_minpoly_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (c : ℝ) (a : ℕ),
    ∀ (x : E) (j : ℕ), Height.mulHeight₁ ((minpoly F x).coeff j) ≤ c * (GlobalTheory.RatCount.htE F x : ℝ) ^ a := by
  intro F E _ _ _ _ _
  refine ⟨4 ^ (Module.finrank F E * Fintype.card (InfinitePlace F)), 2 * Module.finrank F E, fun x j => ?_⟩
  set m := Module.finrank F E with hm
  set c := (minpoly F x).coeff j with hc
  let A : InfinitePlace F → ℝ := fun w =>
    ((max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) : ℝ≥0) : ℝ)
  let B0 : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => max 1 (absFin F v ((1 : v.adicCompletion F) ⊗ₜ[F] x))
  let B : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (B0 v : ℝ)
  have hA : ∀ w, 1 ≤ A w := fun w => by simp only [A]; exact_mod_cast le_max_left _ _
  have hB : ∀ v, 1 ≤ B v := fun v => by simp only [B, B0]; exact_mod_cast le_max_left _ _
  have hB0fin : Function.HasFiniteMulSupport B0 := by
    have h := eventually_absFin_le_one (E := E) F ((1 : AF F) ⊗ₜ[F] x)
    refine (Filter.eventually_cofinite.1 h).subset fun v hv hv' => hv ?_
    have e : compFin F E v ((1 : AF F) ⊗ₜ[F] x) = (1 : v.adicCompletion F) ⊗ₜ[F] x := by
      simp [compFin, map_one]
    rw [e] at hv'
    exact max_eq_left hv'
  have hBfin : Function.HasFiniteMulSupport B := by
    refine hB0fin.subset fun v hv hv' => hv ?_
    simp only [B, hv', NNReal.coe_one]
  have hht : (htE F x : ℝ) = (∏ w, A w) * ∏ᶠ v, B v := by
    rw [htE, NNReal.coe_mul, NNReal.coe_prod]
    congr 1
    exact (MonoidHom.map_finprod NNReal.toRealHom.toMonoidHom hB0fin)
  have hB1 : ∀ v, 1 ≤ B v ^ m := fun v => one_le_pow₀ (hB v)

  have hinf : (∏ w : InfinitePlace F, max (w c) 1 ^ w.mult) ≤
      4 ^ (m * Fintype.card (InfinitePlace F)) * (∏ w, A w) ^ (2 * m) := by
    have h1 : ∀ w : InfinitePlace F, max (w c) 1 ^ w.mult ≤ 4 ^ m * A w ^ (2 * m) := fun w => by
      have hb : 1 ≤ 2 ^ m * A w ^ m := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (hA w))
      have h2 : max (w c) 1 ≤ 2 ^ m * A w ^ m := max_le (_root_.GlobalTheory.minpoly_coeff_le_inf F E x w j) hb
      calc max (w c) 1 ^ w.mult ≤ (2 ^ m * A w ^ m) ^ w.mult :=
            pow_le_pow_left₀ (le_trans zero_le_one (le_max_right _ _)) h2 _
        _ ≤ (2 ^ m * A w ^ m) ^ 2 := pow_le_pow_right₀ hb (mult_le_two F w)
        _ = 4 ^ m * A w ^ (2 * m) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm m 2, pow_mul, mul_comm 2 m, pow_mul]; norm_num
    calc (∏ w : InfinitePlace F, max (w c) 1 ^ w.mult) ≤ ∏ w : InfinitePlace F, (4 ^ m * A w ^ (2 * m)) :=
          Finset.prod_le_prod₀ (fun w _ => pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _) fun w _ => h1 w
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul, Finset.prod_pow]

  have hfin : (∏ᶠ v : FinitePlace F, max (v c) 1) ≤ (∏ᶠ v, B v) ^ (2 * m) := by
    have e : (∏ᶠ v : FinitePlace F, max (v c) 1) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 F), max (FinitePlace.mk v c) 1 := by
      rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
      rfl
    have hle : ∀ v : HeightOneSpectrum (𝓞 F), max (FinitePlace.mk v c) 1 ≤ B v ^ m := fun v => by
      refine max_le ?_ (hB1 v)
      rw [FinitePlace.mk_apply]
      have := _root_.GlobalTheory.CoefHeight.nnnorm_coeff_minpoly_le F E x v j
      simp only [B, B0]
      exact_mod_cast this
    have hBm : Function.HasFiniteMulSupport fun v => B v ^ m := by
      refine hBfin.subset fun v hv hv' => hv ?_
      simp only [hv', one_pow]
    have hf : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => max (FinitePlace.mk v c) 1 := by
      refine hBfin.subset fun v hv hv' => hv ?_
      exact le_antisymm ((hle v).trans (by rw [hv', one_pow])) (le_max_right _ _)
    rw [e]
    calc (∏ᶠ v : HeightOneSpectrum (𝓞 F), max (FinitePlace.mk v c) 1) ≤ ∏ᶠ v, B v ^ m :=
          finprod_le_finprod₀ hf (fun v => le_trans zero_le_one (le_max_right _ _)) hBm hle
      _ = (∏ᶠ v, B v) ^ m := (finprod_pow hBfin m).symm
      _ ≤ (∏ᶠ v, B v) ^ (2 * m) := pow_le_pow_right₀ (one_le_finprod fun v => hB v) (by omega)
  rw [NumberField.mulHeight₁_eq, hht, mul_pow, ← mul_assoc]
  exact mul_le_mul hinf hfin (finprod_nonneg fun v => le_trans zero_le_one (le_max_right _ _))
    (mul_nonneg (by positivity) (pow_nonneg (Finset.prod_nonneg fun w _ => le_trans zero_le_one (hA w)) _))

end GlobalTheory.RatCount.CoefHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianStdIsometryOfRationalIsometry
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

variable {D : D7}

def sumMap (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) {a ρ : ℕ} (z : Fin a → Y.V) (e f : Fin ρ → Y.V) :
    (X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) →ₗ[D.host.E] Y.V :=
  ι.coprod ((Fintype.linearCombination D.host.E z).coprod
    ((Fintype.linearCombination D.host.E e).coprod (Fintype.linearCombination D.host.E f)))

theorem sumMap_apply (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) {a ρ : ℕ} (z : Fin a → Y.V) (e f : Fin ρ → Y.V)
    (p : X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) :
    sumMap Y X ι z e f p = ι p.1 + (∑ i, p.2.1 i • z i + (∑ i, p.2.2.1 i • e i + ∑ i, p.2.2.2 i • f i)) := by
  simp [sumMap, Fintype.linearCombination_apply]

theorem hT_swap (Y : HSp D) (x y : Y.V) : Y.hT x y = star (Y.hT y x) := (Y.herm.eq y x).symm

theorem form_sumMap {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f)
    (p q : X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) :
    Y.hT (sumMap Y X ι z e f p) (sumMap Y X ι z e f q) =
      X.hT p.1 q.1 + (∑ i, star (p.2.1 i) * q.2.1 i * c +
        (∑ i, star (p.2.2.1 i) * q.2.2.2 i + ∑ i, star (p.2.2.2 i) * q.2.2.1 i)) := by
  have hsub : Subsingleton (Fin a) := by
    have := h.a_le
    exact ⟨fun i j => Fin.ext (by omega)⟩
  have zz : ∀ i j, Y.hT (z i) (z j) = if i = j then c else 0 := fun i j => by
    obtain rfl := Subsingleton.elim i j
    rw [if_pos rfl]; exact h.z_norm i
  have zx : ∀ i x, Y.hT (z i) (ι x) = 0 := fun i x => h.z_X i x
  have xz : ∀ i x, Y.hT (ι x) (z i) = 0 := fun i x => by rw [hT_swap, zx, star_zero]
  have ex : ∀ i x, Y.hT (e i) (ι x) = 0 := fun i x => (h.hyp_X i x).1
  have xe : ∀ i x, Y.hT (ι x) (e i) = 0 := fun i x => by rw [hT_swap, ex, star_zero]
  have fx : ∀ i x, Y.hT (f i) (ι x) = 0 := fun i x => (h.hyp_X i x).2
  have xf : ∀ i x, Y.hT (ι x) (f i) = 0 := fun i x => by rw [hT_swap, fx, star_zero]
  have ez : ∀ i j, Y.hT (e i) (z j) = 0 := fun i x => (h.hyperbolicDecomp_hyp_orthogonal_line i x).1
  have ze : ∀ i j, Y.hT (z j) (e i) = 0 := fun i x => by rw [hT_swap, ez, star_zero]
  have fz : ∀ i j, Y.hT (f i) (z j) = 0 := fun i x => (h.hyperbolicDecomp_hyp_orthogonal_line i x).2
  have zf : ∀ i j, Y.hT (z j) (f i) = 0 := fun i x => by rw [hT_swap, fz, star_zero]
  have ee : ∀ i j, Y.hT (e i) (e j) = 0 := fun i j => h.ee j i
  have ff : ∀ i j, Y.hT (f i) (f j) = 0 := fun i j => h.ff j i
  have fe : ∀ i j, Y.hT (f i) (e j) = if j = i then 1 else 0 := fun i j => h.ef j i
  have ef : ∀ i j, Y.hT (e i) (f j) = if i = j then 1 else 0 := fun i j => by
    rw [hT_swap, fe]; split_ifs <;> simp
  have xx : ∀ x y, Y.hT (ι x) (ι y) = X.hT x y := h.isom
  rw [sumMap_apply, sumMap_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, zz, zx, xz, ex, xe, fx, xf, ez, ze, fz, zf, ee, ff, fe, ef, xx, smul_eq_mul, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, mul_one, RingHom.id_apply, starRingEnd_apply]
  rw [add_comm (∑ i, star (p.2.2.1 i) * q.2.2.2 i)]
  congr 1
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

theorem sumMap_injective {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f) (hc : c ≠ 0) : Function.Injective (sumMap Y X ι z e f) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  rintro ⟨x, α, β, γ⟩ hp
  have H := fun q => form_sumMap h (x, α, β, γ) q
  simp only [hp, map_zero, LinearMap.zero_apply] at H
  have h1 : x = 0 := X.nondeg.1 x fun y => by simpa using (H (y, 0, 0, 0)).symm
  have h2 : α = 0 := funext fun i => by
    simpa [Pi.single_apply, hc] using (H (0, Pi.single i 1, 0, 0)).symm
  have h3 : β = 0 := funext fun i => by
    simpa [Pi.single_apply] using (H (0, 0, 0, Pi.single i 1)).symm
  have h4 : γ = 0 := funext fun i => by
    simpa [Pi.single_apply] using (H (0, 0, Pi.single i 1, 0)).symm
  simp [h1, h2, h3, h4]

def sumEquiv {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f) (hc : c ≠ 0) :
    (X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) ≃ₗ[D.host.E] Y.V :=
  LinearEquiv.ofInjectiveOfFinrankEq (sumMap Y X ι z e f) (sumMap_injective h hc) (by
    simp only [Module.finrank_prod, Module.finrank_fin_fun, X.rank_eq, Y.rank_eq, h.rank]
    ring)

theorem sumEquiv_apply {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f) (hc : c ≠ 0) (p) :
    sumEquiv h hc p = sumMap Y X ι z e f p := rfl

theorem exists_isom {Y Y' X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {ι' : X.V →ₗ[D.host.E] Y'.V} {a ρ : ℕ}
    {z : Fin a → Y.V} {z' : Fin a → Y'.V} {c : D.host.E} {e f : Fin ρ → Y.V} {e' f' : Fin ρ → Y'.V}
    (h : IsDec Y X ι z c e f) (h' : IsDec Y' X ι' z' c e' f') (hc : c ≠ 0) :
    ∃ io : Y.V ≃ₗ[D.host.E] Y'.V, HSpace.IsIsomEmb Y Y' io.toLinearMap ∧
      (∀ x, io (ι x) = ι' x) ∧ (∀ i, io (z i) = z' i) ∧ ∀ i, io (e i) = e' i ∧ io (f i) = f' i := by
  have key : ∀ p, ((sumEquiv h hc).symm.trans (sumEquiv h' hc)) (sumMap Y X ι z e f p) =
      sumMap Y' X ι' z' e' f' p := fun p => by
    rw [← sumEquiv_apply h hc, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, sumEquiv_apply]
  refine ⟨(sumEquiv h hc).symm.trans (sumEquiv h' hc), fun x y => ?_, fun x => ?_, fun i => ?_, fun i => ⟨?_, ?_⟩⟩
  · obtain ⟨p, rfl⟩ := (sumEquiv h hc).surjective x
    obtain ⟨q, rfl⟩ := (sumEquiv h hc).surjective y
    rw [sumEquiv_apply, sumEquiv_apply, LinearEquiv.coe_coe, key, key, form_sumMap h, form_sumMap h']
  · simpa [sumMap_apply] using key (x, 0, 0, 0)
  · simpa [sumMap_apply, Pi.single_apply] using key (0, Pi.single i 1, 0, 0)
  · simpa [sumMap_apply, Pi.single_apply] using key (0, 0, Pi.single i 1, 0)
  · simpa [sumMap_apply, Pi.single_apply] using key (0, 0, 0, Pi.single i 1)

theorem isDec_rescale {Y X X' : HSp D} {ι : X'.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X' ι z c e f) (φ : X.V →ₗ[D.host.E] X'.V) (hφ : HSpace.IsIsomEmb X X' φ)
    (hr : X.rank = X'.rank) (π : D.host.E) :
    IsDec Y X (ι ∘ₗ φ) (fun i => π • z i) (c * (π * star π)) e f := by
  refine
    { isom := fun x y => (h.isom _ _).trans (hφ x y)
      a_le := h.a_le
      rank := ?_
      z_norm := ?_
      z_X := ?_
      ee := h.ee
      ff := h.ff
      ef := h.ef
      hyp_X := fun i x => h.hyp_X i (φ x)
      hyperbolicDecomp_hyp_orthogonal_line := ?_ }
  · rw [hr, h.rank]
  · intro i
    have := h.z_norm i
    simp only [HSpace.hD, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      starRingEnd_apply] at this ⊢
    rw [this]
    ring
  · intro i x
    have := h.z_X i (φ x)
    simp only [HSpace.hD, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply] at this ⊢
    rw [this, mul_zero]
  · intro i j
    have := h.hyperbolicDecomp_hyp_orthogonal_line i j
    simp only [HSpace.hD, LinearMap.map_smulₛₗ, smul_eq_mul] at this ⊢
    rw [this.1, this.2, mul_zero]
    exact ⟨rfl, rfl⟩

theorem stdIsomSt_of_rationalSt : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D → GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.StdIsomSt D := by
  intro D hR u
  refine ⟨?_, ?_⟩
  · obtain ⟨π, h1, h2, -⟩ := D.T_norm u
    exact ⟨π, h1, by rw [bridge_star_holds D.R D.host]; exact h2⟩
  intro π hπ s a ρ Y X ι z e f Y' X' ι' z' e' f' h h' hX hX' hp hp' hr
  obtain ⟨φ, hφ⟩ := hR X X' hX hX' hr fun τ => by rw [hp τ, hp' τ, hr]
  have h2 := isDec_rescale h' φ.toLinearMap hφ hr (π : D.host.E)
  rw [hπ.2] at h2
  have hc : ((s : ℤ) : D.host.E) * Tu D u ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr s.ne_zero) (Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero)
  obtain ⟨io, a1, a2, a3, a4⟩ := exists_isom h h2 hc
  exact ⟨φ, io, hφ, a1, a2, a3, a4⟩

end GlobalTheory.StdIsom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicStdCharHalfSymplecticRealPartZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PsiFinAlgebraic

theorem exists_pow_psi_fin_eq_one {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ)
    (y : Af F) : ∃ M : ℕ, 0 < M ∧ ψ (pairA F 0 y) ^ M = 1 := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F {c | ψ (pairA F 0 c) = 1}
    (GlobalTheory.FinTranslate.eventually_fin_eq_one hψ)
  obtain ⟨m, hm, hy⟩ := GlobalTheory.UnRep.SmallMat.exists_nsmul_integral y
  refine ⟨N * m, Nat.mul_pos hN (Nat.pos_of_ne_zero hm), ?_⟩
  have h1 : ψ (pairA F 0 (N • m • y)) = 1 := h _ hy
  have e : pairA F 0 (N • m • y) = (N * m) • pairA F 0 y :=
    Prod.ext (smul_zero (N * m)).symm (mul_smul N m y).symm
  rwa [e, AddChar.map_nsmul_eq_pow] at h1

theorem isAlgebraic_psi_fin {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ)
    (y : Af F) : IsAlgebraic ℚ (ψ (pairA F 0 y)) := by
  obtain ⟨M, hM, h⟩ := exists_pow_psi_fin_eq_one hψ y
  refine IsAlgebraic.of_pow hM ?_
  rw [h]
  exact isAlgebraic_one

theorem isAlgebraic_psi_symplOH : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ}, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (u v : WO S T),
    u.map (infPart D) = 0 → v.map (infPart D) = 0 → IsAlgebraic ℚ (ψ (symplOH S T u v)) := by
  intro D ψ hψ S T u v hu _
  have e : pairA D.host.F 0 (sndA D.host.F (symplOH S T u v)) = symplOH S T u v :=
    Prod.ext (GlobalTheory.WeilVacMove.fst_symplOH S T u v (Or.inl hu)).symm rfl
  rw [← e]
  exact isAlgebraic_psi_fin hψ.1 _

end GlobalTheory.PsiFinAlgebraic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMultMapRightTranslateFiniteAdelicNormalizer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

private lemma atTau_mem_GinfC_twisted_operators {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact (GinfC V).one_mem

theorem isMultMap_rightTranslate_finite : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (κ : GA D V), κ ∈ GfC V → (∀ k ∈ J, κ⁻¹ * k * κ ∈ J ∧ χ (κ⁻¹ * k * κ) = χ k) → ∀ T : MMap M, IsMultMap θ M J χ T → ∃ T' : MMap M, IsMultMap θ M J χ T' ∧ ∀ v, T' v = rTr V κ (T v) := by
  intro D V S θ M J χ κ hκ hJ T hT
  refine ⟨(LinearMap.funLeft ℂ ℂ (fun g : GA D V => g * κ)).compMultilinearMap T,
    ⟨fun v => ?_, fun v => ?_, fun v k hk g => ?_, fun τ g hg v w hw => ?_, fun τ v x => ?_⟩, fun v => rfl⟩
  ·
    exact GlobalTheory.T.isSmoothAutomorphic_rightTranslate_finite θ V κ hκ (T v) (hT.aut v)
  ·
    intro r C hC μ 𝓕 hμ h𝓕 g
    have h := hT.cusp v r C hC μ 𝓕 hμ h𝓕 (g * κ)
    simpa only [LinearMap.compMultilinearMap_apply, LinearMap.funLeft_apply, Function.comp, mul_assoc] using h
  ·
    obtain ⟨hk1, hk2⟩ := hJ k hk
    show T v (g * k * κ) = χ k * T v (g * κ)
    have h := hT.lev v _ hk1 (g * κ)
    rw [hk2] at h
    rw [← h]
    congr 1
    group
  ·
    rw [LinearMap.compMultilinearMap_apply, hT.equiv τ g hg v w hw]
    funext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.funLeft_apply, rTr]
    rw [mul_assoc, mul_assoc, _root_.GlobalTheory.FinRealComm.finite_real_points_commute V κ _ hκ (atTau_mem_GinfC_twisted_operators θ V τ g)]
  ·
    obtain ⟨ℓ, hℓ, hℓw⟩ := hT.cont τ v (x * κ)
    exact ⟨ℓ, hℓ, fun w => hℓw w⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityInnerProductUnitTwistedRightTranslat
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isMultiplicityInner_of_unit_twist_shift : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ J χ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (κ : GA D V) (a : ℂ), ‖a‖ = 1 → Measure.map (fun g => g * κ) μ = μ → ∀ T ∈ Mult θ M J χ, ∀ T' ∈ Mult θ M J χ, ∀ U U' : MMap M, (∀ v g, U v g = a * T v (g * κ)) → (∀ v g, U' v g = a * T' v (g * κ)) → ∀ c, IsMultIP M μ 𝓕 T T' c → IsMultIP M μ 𝓕 U U' c := by
  intro D V S θ M J χ μ 𝓕 hμ h𝓕 κ a ha hκ T hT T' hT' U U' hU hU' c hc
  obtain ⟨hLC, hSC, hB, hC⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  unfold IsMultIP at hc ⊢
  intro v v'
  have haa : star a * a = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ha]
    norm_num
  have hfun : (fun g => star (U v g) * U' v' g) = fun g => star (T v (g * κ)) * T' v' (g * κ) := by
    funext g
    rw [hU, hU', star_mul']
    calc star a * star (T v (g * κ)) * (a * T' v' (g * κ))
        = (star a * a) * (star (T v (g * κ)) * T' v' (g * κ)) := by ring
      _ = star (T v (g * κ)) * T' v' (g * κ) := by rw [haa, one_mul]
  have hinv : ∀ γ ∈ GQ V, ∀ g, star (T v (γ * g)) * T' v' (γ * g) = star (T v g) * T' v' g := by
    intro γ hγ g
    rw [(GlobalTheory.mult_value_left_cont_level θ M J χ T hT v).1 γ hγ g,
      (GlobalTheory.mult_value_left_cont_level θ M J χ T' hT' v').1 γ hγ g]
  have key := GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ V) μ 𝓕 h𝓕 κ hκ
    (fun g => star (T v g) * T' v' g) hinv (hc v v').1
  rw [hfun]
  exact ⟨key.1, key.2.trans (hc v v').2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLineDecompositionsOfBaseSpaceProof
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof

open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  have := D.host.der.cm
  obtain ⟨ψ⟩ := (inferInstance : Nonempty (D.host.E →+* ℂ))
  have hc : ∀ y, ψ (D.host.conj y) = starRingEnd ℂ (ψ y) :=
    (D.host.der.conj_iff ψ D.host.conj).2 (MulEquiv.apply_symm_apply _ _)
  apply ψ.injective
  rw [hc]
  exact NumberField.IsCMField.complexEmbedding_complexConj _ ψ x

theorem hT_zero_symm {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {x y : S.V}
    (h : S.hT x y = 0) : S.hT y x = 0 := by
  rw [← S.herm.eq x y, h, map_zero]

theorem isDec_smul (D : D7) (t : D.host.E) :
    IsDec (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0) (fun _ : Fin 1 => t • D.sp.zm)
      (-(t * star t * ((D.mem D.u₀).A.T : D.host.E))) D.sp.hypE D.sp.hypF := by
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hsym : ∀ a b : (D.sp.Y 0).V, (D.sp.Y 0).hT a b = 0 → (D.sp.Y 0).hT b a = 0 :=
    fun a b h => hT_zero_symm (D.sp.Y 0) h
  refine
    { isom := D.sp.iXY_isom 0 hm
      a_le := le_rfl
      rank := ?_
      z_norm := ?_
      z_X := ?_
      ee := ?_
      ff := ?_
      ef := ?_
      hyp_X := ?_
      hyperbolicDecomp_hyp_orthogonal_line := ?_ }
  · rw [D.sp.Y_rank 0 (Nat.zero_le _), D.sp.X_rank 0 (Nat.zero_le _)]
    obtain ⟨j, hj⟩ := D.R.m_even
    simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.N, Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
    omega
  · intro i
    simp only [HSpace.hD, LinearMap.map_smulₛₗ₂, map_smul, D.sp.zm_norm, starRingEnd_apply, smul_eq_mul,
      D.sp_T]
    ring
  · intro i x
    simp only [HSpace.hD, LinearMap.map_smulₛₗ₂, hsym _ _ (D.sp.zm_orth x), smul_zero]
  · intro i j
    exact D.sp.hyp_ee j i
  · intro i j
    exact D.sp.hyp_ff j i
  · intro i j
    simp only [HSpace.hD]
    rw [← (D.sp.Y 0).herm.eq (D.sp.hypE i) (D.sp.hypF j), D.sp.hyp_ef]
    split_ifs <;> simp
  · intro i x
    exact ⟨hsym _ _ (D.sp.hyp_orthX i x).1, hsym _ _ (D.sp.hyp_orthX i x).2⟩
  · intro i j
    simp only [HSpace.hD, map_smul, hsym _ _ (D.sp.hyp_orthz i).1, hsym _ _ (D.sp.hyp_orthz i).2, smul_zero,
      and_self]

theorem recordDec (D : D7) : RecordDecSt D := by
  refine ⟨fun u => ?_, ?_⟩
  · have hc0 := D.cOf_ne u
    have hc1 : D.host.conj (D.cOf u) ≠ 0 := (map_ne_zero _).2 hc0
    have h := isDec_smul D (D.cOf u)⁻¹
    have hs : -((D.cOf u)⁻¹ * star (D.cOf u)⁻¹ * ((D.mem D.u₀).A.T : D.host.E)) = -Tu D u := by
      rw [star_inv₀, star_eq_conj, ← D.cOf_eq u]
      field_simp
    rw [hs] at h
    exact h
  · obtain ⟨π, -, hπ, -⟩ := D.T_norm D.u₀
    have hT : ((D.mem D.u₀).A.T : D.host.E) ≠ 0 := by
      rw [← D.sp_T]
      exact_mod_cast D.sp.T_prime.ne_zero
    have hπ0 : (π : D.host.E) ≠ 0 := by
      rintro h0
      rw [h0, zero_mul] at hπ
      exact hT hπ.symm
    have hπ1 : D.host.conj (π : D.host.E) ≠ 0 := (map_ne_zero _).2 hπ0
    refine ⟨(π : D.host.E)⁻¹ • D.sp.zm, ?_⟩
    have h := isDec_smul D (π : D.host.E)⁻¹
    have hs : -((π : D.host.E)⁻¹ * star (π : D.host.E)⁻¹ * ((D.mem D.u₀).A.T : D.host.E)) = -1 := by
      rw [star_inv₀, star_eq_conj, ← hπ]
      field_simp
    rw [hs] at h
    exact h

end GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof
end

