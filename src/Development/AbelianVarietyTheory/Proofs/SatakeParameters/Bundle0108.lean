module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Formalism.LocalRingCardinality.DataKerI
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormResFormPullFormPull
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCompletedLatticeBasisAtPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatLocBasis

noncomputable abbrev locRing {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Subalgebra (𝓞 E) E :=
  Localization.subalgebra.ofField E P.asIdeal.primeCompl P.asIdeal.primeCompl_le_nonZeroDivisors

theorem exists_gens {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ b : Fin n → Fin n → E, (∀ i, b i ∈ Submodule.span (locRing P) (L : Set (Fin n → E))) ∧
      ∀ x ∈ L, ∃ c : Fin n → locRing P, ∀ a, x a = ∑ i, (c i : E) * b i a := by
  have : IsLocalization.AtPrime (locRing P) P.asIdeal :=
    Localization.subalgebra.isLocalization_ofField E _ _
  have : IsDiscreteValuationRing (locRing P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) P.ne_bot _
  have : IsFractionRing (locRing P) E := Localization.subalgebra.isFractionRing_ofField E _ _
  let M := Submodule.span (locRing P) (L : Set (Fin n → E))
  have hM : Submodule.IsLattice E M := Submodule.IsLattice.of_fg E (by
    obtain ⟨s, rfl⟩ := hfg
    exact ⟨s, (Submodule.span_span_of_tower (𝓞 E) (locRing P) _).symm⟩)
  have : Submodule.IsFullLattice E M :=
    { hM with span_eq_top := by rw [Submodule.span_span_of_tower, hsp] }
  have : Module.Finite (locRing P) M := Submodule.IsLattice.finite E M
  have : Module.Free (locRing P) M := Submodule.IsLattice.free E M
  have hr : Module.finrank (locRing P) M = n := by
    simpa using ((Submodule.IsFullLattice.finrank_eq E M).trans (Module.finrank_fintype_fun_eq_card E))
  let b := Module.finBasisOfFinrankEq (locRing P) M hr
  refine ⟨fun i => b i, fun i => (b i).2, fun x hx => ?_⟩
  refine ⟨b.repr ⟨x, Submodule.subset_span hx⟩, fun a => ?_⟩
  have h := congrArg (fun v : M => (v : Fin n → E) a) (b.sum_repr ⟨x, Submodule.subset_span hx⟩)
  simp only [Submodule.coe_sum, Finset.sum_apply] at h
  exact h.symm

theorem mul_mem_int (D : D7) {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem idem_mul_loc_mem {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (h : IsIdemAt e P) {t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F} (ht : t ∈ intAf D.host.F) (c : locRing P) :
    finPart D e * (t ⊗ₜ[D.host.F] (c : D.host.E)) ∈ intAE D := by
  obtain ⟨a, s, hs, hc⟩ := c.2
  have hs0 : s ≠ 0 := fun h0 => hs (h0 ▸ P.asIdeal.zero_mem)
  have h1 : finPart D (e * incA D ((s : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra hn
    exact hs ((h.2 s hs0).2 hn)
  have h2 : (t ⊗ₜ[D.host.F] (a : D.host.E)) ∈ intAE D := AddSubgroup.subset_closure ⟨t, ht, a, rfl⟩
  have h3 := mul_mem_int D h1 h2
  have h4 : finPart D (incA D ((s : D.host.E)⁻¹)) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((s : D.host.E)⁻¹) := rfl
  rw [RingHom.map_mul, h4, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm _ (a : D.host.E)] at h3
  rw [hc]
  exact h3

theorem one_mem_intAf (F : Type) [Field F] [NumberField F] : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ∈ intAf F :=
  fun v => by rw [map_one]; exact one_mem _

theorem idem_mul_span_mem {D : D7} (V : HSp D) {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (h : IsIdemAt e P) {x : Fin V.rank → D.host.E}
    (hx : x ∈ Submodule.span (locRing P) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))) :
    (fun a => finPart D e * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x a)) ∈ LamHat V := by
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, h.1.1]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    have h1 : finPart D e ∈ intAE D := by
      have := idem_mul_loc_mem h (one_mem_intAf _) 1
      rwa [OneMemClass.coe_one, ← Algebra.TensorProduct.one_def, mul_one] at this
    refine GlobalTheory.LatDual.smul_mem_lamHat V _ h1 _ ?_
    rw [GlobalTheory.LatDual.lamHat_eq_hat]
    exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩
  | zero =>
    simp only [Pi.zero_apply, TensorProduct.tmul_zero, mul_zero]
    exact zero_mem _
  | add u w _ _ hu hw =>
    simp only [Pi.add_apply, TensorProduct.tmul_add, mul_add]
    exact add_mem hu hw
  | smul c u _ hu =>
    have := GlobalTheory.LatDual.smul_mem_lamHat V _ (idem_mul_loc_mem h (one_mem_intAf _) c) _ hu
    convert this using 2 with a
    rw [mul_mul_mul_comm, hee, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl


set_option maxHeartbeats 1000000 in
theorem exists_loc_basis : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D), IsIdemAt e P → ∃ B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), (∀ z, IntVec z → (fun a => finPart D e * B.mulVec z a) ∈ LamHat V) ∧ ∀ y ∈ LamHat V, ∃ z, IntVec z ∧ (fun a => finPart D e * y a) = fun a => finPart D e * B.mulVec z a := by
  intro D V P e h
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, h.1.1]
  obtain ⟨-, -, hfg, hspan, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨b, hb, hc⟩ := exists_gens P (GlobalTheory.Member.latC V) hfg hspan
  have h1 : finPart D e ∈ intAE D := by
    have := idem_mul_loc_mem h (one_mem_intAf _) 1
    rwa [OneMemClass.coe_one, ← Algebra.TensorProduct.one_def, mul_one] at this
  refine ⟨Matrix.of fun a i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] b i a, fun z hz => ?_, fun y hy => ?_⟩
  · have := sum_mem (S := LamHat V) (t := Finset.univ) fun i _ =>
      GlobalTheory.LatDual.smul_mem_lamHat V _ (hz i) _ (idem_mul_span_mem V h (hb i))
    convert this using 1
    funext a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [GlobalTheory.LatDual.lamHat_eq_hat] at hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hy
      obtain ⟨c, hc⟩ := hc x hx
      refine ⟨fun i => finPart D e * (t ⊗ₜ[D.host.F] (c i : D.host.E)), fun i => idem_mul_loc_mem h ht _, ?_⟩
      funext a
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
      rw [hc a, TensorProduct.tmul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_left_comm _ (finPart D e), ← mul_assoc, hee, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        mul_comm (b i a)]
    | zero => exact ⟨0, fun _ => zero_mem _, by rw [Matrix.mulVec_zero]⟩
    | add u w _ _ hu hw =>
      obtain ⟨z, hz, hu⟩ := hu
      obtain ⟨z', hz', hw⟩ := hw
      refine ⟨z + z', fun i => add_mem (hz i) (hz' i), funext fun a => ?_⟩
      rw [Matrix.mulVec_add, Pi.add_apply, Pi.add_apply, mul_add, mul_add, congrFun hu a, congrFun hw a]
    | neg u _ hu =>
      obtain ⟨z, hz, hu⟩ := hu
      refine ⟨-z, fun i => neg_mem (hz i), funext fun a => ?_⟩
      rw [Matrix.mulVec_neg, Pi.neg_apply, Pi.neg_apply, mul_neg, mul_neg, congrFun hu a]

end GlobalTheory.LatLocBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRationalFrame
section
noncomputable section

namespace GlobalTheory.UnUnitCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts

section Units

variable {l : ℕ} [Fact l.Prime] {lam : (algebraicClosure ℚ ℂ) →+* ℂ_[l]}

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem emb_mem {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (x : K) : φ x ∈ algebraicClosure ℚ ℂ :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom)

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) (φ : H.E →+* ℂ) {N : ℕ} (g : GL (Fin N) (Ad H))

end Units

section Rescale

variable {D : D7} {Dx : DivX D} {Tw : TwForms D}

end Rescale

section Ties

variable {D : D7} {Dx : DivX D} {Tw : TwForms D} {C : CharFrame D} {nch : NChoice D}

variable (E : KerEnt D Dx Tw) (Tp : TupTied D C nch) (g : ∀ u μ, Reps D u μ) (fr : ∀ u μ, Frames D u μ)

end Ties

end GlobalTheory.UnUnitCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinTypInvariantFormOfIsotIn
section
open Formalism.BasicNotions Formalism.L2 Formalism.L2.NG Formalism.AUTREP Formalism.IndefR.principalLevelFrame

namespace GlobalTheory

theorem finTyp_invariant_form_of_isotIn : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (B : A → A → ℂ), (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z) → (∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)) → (∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) → (∀ h, ∀ x ∈ C, ρ h x ∈ C) → (∀ h, ∀ x ∈ C, ∀ y ∈ C, B (ρ h x) (ρ h y) = B x y) → ∀ π : FinTyp D.host.E n, isotIn (D := D) ρ C π ≠ ⊥ → ∃ B' : π.S → π.S → ℂ, (∀ x y z (c : ℂ), B' x (y + c • z) = B' x y + c * B' x z) ∧ (∀ x y, B' x y = starRingEnd ℂ (B' y x)) ∧ (∀ x, x ≠ 0 → 0 < (B' x x).re) ∧ ∀ h (x y x' y' : π.S), (x' : GAf D.host.E n → ℂ) = rt D.host.E n h x → (y' : GAf D.host.E n → ℂ) = rt D.host.E n h y → B' x' y' = B' x y := by
  intro D n A _ _ ρ C B hlin hherm hpos _hstab hinv π hne

  obtain ⟨Φ, ⟨hΦe, hΦC⟩, hΦne⟩ : ∃ Φ : π.S →ₗ[ℂ] A, (IsEqvA ρ π Φ ∧ LinearMap.range Φ ≤ C) ∧ LinearMap.range Φ ≠ ⊥ := by
    by_contra hcon
    push_neg at hcon
    apply hne
    unfold isotIn
    refine iSup_eq_bot.2 fun Φ => iSup_eq_bot.2 fun hΦ => hcon Φ hΦ
  have hmemC : ∀ x : π.S, Φ x ∈ C := fun x => hΦC (LinearMap.mem_range_self Φ x)

  let S' : Submodule ℂ (GAf D.host.E n → ℂ) := (LinearMap.ker Φ).map π.S.subtype
  have hS'le : S' ≤ π.S := by
    rintro f ⟨k, _, rfl⟩
    exact k.2
  have hS'st : ∀ h, ∀ f ∈ S', rt D.host.E n h f ∈ S' := by
    rintro h f ⟨k, hk, rfl⟩
    refine ⟨⟨rt D.host.E n h k, π.stable h k k.2⟩, ?_, rfl⟩
    have hk' : Φ k = 0 := hk
    show Φ _ = 0
    rw [hΦe h k, hk', map_zero]
  have hinj : ∀ x : π.S, Φ x = 0 → x = 0 := by
    intro x hx
    rcases π.irr S' hS'le hS'st with h0 | hall
    · have : (x : GAf D.host.E n → ℂ) ∈ S' := ⟨x, hx, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact Subtype.ext this
    · exfalso
      apply hΦne
      rw [eq_bot_iff]
      rintro a ⟨y, rfl⟩
      have : (y : GAf D.host.E n → ℂ) ∈ S' := by rw [hall]; exact y.2
      obtain ⟨k, hk, hky⟩ := this
      have : k = y := Subtype.ext hky
      subst this
      have hk' : Φ k = 0 := hk
      exact (Submodule.mem_bot ℂ).2 hk'
  refine ⟨fun x y => B (Φ x) (Φ y), ?_, ?_, ?_, ?_⟩
  · intro x y z c
    simp only [map_add (f := _), map_smul]
    exact hlin _ (hmemC x) _ (hmemC y) _ (hmemC z) c
  · intro x y
    exact hherm _ (hmemC x) _ (hmemC y)
  · intro x hx
    exact hpos _ (hmemC x) (fun h0 => hx (hinj x h0))
  · intro h x y x' y' hx hy
    have ex : x' = ⟨rt D.host.E n h x, π.stable h x x.2⟩ := Subtype.ext hx
    have ey : y' = ⟨rt D.host.E n h y, π.stable h y y.2⟩ := Subtype.ext hy
    simp only
    rw [ex, ey, hΦe h x, hΦe h y]
    exact hinv h _ (hmemC x) _ (hmemC y)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharFiniteOrderUnitIdele
section
noncomputable section

namespace GlobalTheory.HeckeFin

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

variable {L : Type} [Field L] [NumberField L]

theorem circle_pow (ψ : Ideles L →* Circle) (hψ : Continuous ψ) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : Ideles L, IsFinIdele u → u ∈ unitIdl L → ψ u ^ m = 1 := by
  obtain ⟨-, -, -, m, hm, h⟩ := GlobalTheory.CharFin.finite_order_of_small (R := AdeleRing (𝓞 L) L)
    (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) (RingHom.snd _ _) id continuous_id (fun _ => rfl)
    (GlobalTheory.UnUnitCmp.Val.intFin L) (fun W hW => GlobalTheory.AdLat.OpenLat.exists_nsmul_adele L W hW)
    GlobalTheory.UnUnitCmp.Val.finite_quot ψ hψ
  exact ⟨m, hm, fun u h1 h2 => h u ⟨funext h1, fun v => (h2 v).le, fun v => ((unitIdl L).inv_mem h2 v).le⟩⟩

theorem norm_ne (χ : HChar L) (x : Ideles L) : ‖((χ.1 x : ℂˣ) : ℂ)‖ ≠ 0 :=
  norm_ne_zero_iff.2 (Units.ne_zero _)

theorem continuous_norm_val (χ : HChar L) : Continuous fun x : Ideles L => ‖((χ.1 x : ℂˣ) : ℂ)‖ :=
  (Units.continuous_val.comp χ.2.1).norm

def twist (χ : HChar L) (c : ℝ) : Ideles L →* Circle where
  toFun x := Circle.exp (c * Real.log ‖((χ.1 x : ℂˣ) : ℂ)‖)
  map_one' := by simp
  map_mul' x y := by
    rw [χ.1.map_mul, Units.val_mul, norm_mul, Real.log_mul (norm_ne χ x) (norm_ne χ y), mul_add, Circle.exp_add]

theorem continuous_twist (χ : HChar L) (c : ℝ) : Continuous (twist χ c) :=
  Circle.exp.continuous.comp (continuous_const.mul ((continuous_norm_val χ).log (norm_ne χ)))

theorem norm_eq_one (χ : HChar L) (a : Ideles L) (h1 : IsFinIdele a) (h2 : a ∈ unitIdl L) :
    ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
  by_contra hne
  have ht : Real.log ‖((χ.1 a : ℂˣ) : ℂ)‖ ≠ 0 := by
    intro h0
    rcases Real.log_eq_zero.1 h0 with h | h | h
    · exact norm_ne χ a h
    · exact hne h
    · linarith [norm_nonneg ((χ.1 a : ℂˣ) : ℂ)]
  set t := Real.log ‖((χ.1 a : ℂˣ) : ℂ)‖ with htdef
  obtain ⟨m, hm, h⟩ := circle_pow (twist χ (2 * Real.pi * √2 / t)) (continuous_twist χ _)
  have e := h a h1 h2
  have e1 : twist χ (2 * Real.pi * √2 / t) a = Circle.exp (2 * Real.pi * √2) := by
    change Circle.exp (2 * Real.pi * √2 / t * Real.log ‖((χ.1 a : ℂˣ) : ℂ)‖) = _
    rw [← htdef, div_mul_cancel₀ _ ht]
  rw [e1, ← Circle.exp_nsmul] at e
  have e2 := congrArg (fun z : Circle => (z : ℂ)) e
  simp only [Circle.coe_exp, Circle.coe_one] at e2
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 e2
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e3 : (m : ℂ) * (√2 : ℝ) = n := by
    have : ((m : ℂ) * (√2 : ℝ)) * (2 * Real.pi * Complex.I) = n * (2 * Real.pi * Complex.I) := by
      rw [← hn]; push_cast; simp only [nsmul_eq_mul]; push_cast; ring
    exact mul_right_cancel₀ (by simp [hpi, Complex.I_ne_zero]) this
  have e4 : (m : ℝ) * √2 = n := by exact_mod_cast e3
  exact (irrational_sqrt_two.natCast_mul hm.ne').ne_int n e4

def unitPart (χ : HChar L) : Ideles L →* Circle where
  toFun x := ⟨((χ.1 x : ℂˣ) : ℂ) / ‖((χ.1 x : ℂˣ) : ℂ)‖, by
    simp [Submonoid.unitSphere, norm_ne χ x]⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    change ((χ.1 (x * y) : ℂˣ) : ℂ) / ‖((χ.1 (x * y) : ℂˣ) : ℂ)‖ =
      (((χ.1 x : ℂˣ) : ℂ) / ‖((χ.1 x : ℂˣ) : ℂ)‖) * (((χ.1 y : ℂˣ) : ℂ) / ‖((χ.1 y : ℂˣ) : ℂ)‖)
    rw [χ.1.map_mul, Units.val_mul, norm_mul]
    push_cast
    rw [mul_div_mul_comm]

theorem continuous_unitPart (χ : HChar L) : Continuous (unitPart χ) := by
  refine Continuous.subtype_mk ?_ _
  exact (Units.continuous_val.comp χ.2.1).div (Complex.continuous_ofReal.comp (continuous_norm_val χ))
    (fun x => by simpa using norm_ne χ x)

theorem finite_order : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (a : Ideles L), IsFinIdele a →
    (∀ v, Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1) → ∃ n : ℕ, 0 < n ∧ χ.1 a ^ n = 1 := by
  intro L _ _ χ a h1 h2
  have h2' : a ∈ unitIdl L := h2
  obtain ⟨m, hm, h⟩ := circle_pow (unitPart χ) (continuous_unitPart χ)
  refine ⟨m, hm, Units.ext ?_⟩
  have e := congrArg (fun z : Circle => (z : ℂ)) (h a h1 h2')
  have e1 : ((unitPart χ a : Circle) : ℂ) = ((χ.1 a : ℂˣ) : ℂ) := by
    change ((χ.1 a : ℂˣ) : ℂ) / ‖((χ.1 a : ℂˣ) : ℂ)‖ = _
    rw [norm_eq_one χ a h1 h2']; simp
  simpa [e1] using e

end GlobalTheory.HeckeFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgePullHodgeTraceHodgePull
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

set_option autoImplicit false

open Opposite TensorProduct _root_.CategoryTheory.Limits GlobalTheory.Points

noncomputable section
namespace GlobalTheory.GalTrace

theorem preimage_le {Z Y W : Scheme.{0}} {c : Y ⟶ Z} {π : W ⟶ Z} {σ : W ⟶ Y} (hσ : σ ≫ c = π)
    (U : Z.Opens) : π ⁻¹ᵁ U ≤ σ ⁻¹ᵁ (c ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, hσ]

section Forms

variable {k : Type} [CommRing k] {Z Y W : Scheme.{0}} {s : Z ⟶ Sp k} {s' : Y ⟶ Sp k}
  {sW : W ⟶ Sp k} {c : Y ⟶ Z} {π : W ⟶ Z}

def liftPull {σ : W ⟶ Y} (hσ : σ ≫ c = π) (hσs : σ ≫ s' = sW) (j : ℕ) :
    (Scheme.Modules.pushforward c).obj (Omega s' j) ⟶
      (Scheme.Modules.pushforward π).obj (Omega sW j) :=
  (Scheme.Modules.pushforward c).map (omegaPull hσs j) ≫
    (Scheme.Modules.pushforwardComp σ c).hom.app _ ≫
      (Scheme.Modules.pushforwardCongr hσ).hom.app _

theorem liftPull_app (hc : c ≫ s = s') (hπ : π ≫ s = sW) {σ : W ⟶ Y} (hσ : σ ≫ c = π)
    (hσs : σ ≫ s' = sW) (j : ℕ) (U : Z.Opens) (b : Sec s' (c ⁻¹ᵁ U)) (x : OmU s U j) :
    (liftPull hσ hσs j).app U (toOm s' j (c ⁻¹ᵁ U) (b • formPull hc U j x)) =
      toOm sW j (π ⁻¹ᵁ U) (Sec.res sW (preimage_le hσ U) (appSec s' sW σ (c ⁻¹ᵁ U) b) •
        formPull hπ U j x) := by
  change (Omega sW j).presheaf.map (homOfLE (preimage_le hσ U)).op
    ((omegaPull hσs j).val.app (op (c ⁻¹ᵁ U))
      ((toOmega s' j).app (op (c ⁻¹ᵁ U)) (b • formPull hc U j x))) = _
  rw [omegaPull_toOmega]
  refine (res_toOm sW j (preimage_le hσ U) (formPull hσs (c ⁻¹ᵁ U) j (b • formPull hc U j x))).trans
    (congrArg (toOm sW j (π ⁻¹ᵁ U)) ?_)
  have h : (σ ≫ c) ≫ s = sW := by rw [hσ, hπ]
  rw [formPull_smul hσs (c ⁻¹ᵁ U) b (formPull hc U j x), formRes_smul,
    formPull_formPull hc hσs h U j x]
  exact congrArg (_ • ·) (formRes_formPull_congr hσ h hπ U (preimage_le hσ U) j x)

theorem sum_app {F G : Z.Modules} {ι : Type} (R : Finset ι) (φ : ι → (F ⟶ G)) (U : Z.Opens)
    (y : Γ(F, U)) : (∑ r ∈ R, φ r).app U y = ∑ r ∈ R, (φ r).app U y := by
  classical
  induction R using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert a R ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Scheme.Modules.Hom.add_app]
    exact congrArg ((φ a).app U y + ·) ih

variable [IsFinite c] [Etale c] (hc : c ≫ s = s') (hπ : π ≫ s = sW) {ι : Type} (R : Finset ι)
  {σ : ι → (W ⟶ Y)} (hσ : ∀ r, σ r ≫ c = π) (hσs : ∀ r, σ r ≫ s' = sW)

theorem omegaTrace_omegaPull
    (hF : ∀ (U : Z.Opens) (hU : IsAffineOpen U) (b : Sec s' (c ⁻¹ᵁ U)),
      appSec s sW π U (secTrace s s' hU b) =
        ∑ r ∈ R, Sec.res sW (preimage_le (hσ r) U) (appSec s' sW (σ r) (c ⁻¹ᵁ U) b)) (j : ℕ) :
    omegaTrace hc j ≫ omegaPull hπ j = ∑ r ∈ R, liftPull (hσ r) (hσs r) j := by
  refine hom_ext_affine fun U hU y ↦ ?_
  obtain ⟨z, rfl⟩ := toOm_surjective (s := s') (j := j) (hU.preimage c) y
  refine formOm_induction (P := fun z ↦ (omegaTrace hc j ≫ omegaPull hπ j).app U
      (toOm s' j (c ⁻¹ᵁ U) z) = (∑ r ∈ R, liftPull (hσ r) (hσs r) j).app U
        (toOm s' j (c ⁻¹ᵁ U) z)) hc hU ?_ (fun y z hy hz ↦ ?_) (fun b x ↦ ?_) z
  · erw [map_zero, map_zero, map_zero]
  · erw [map_add, map_add, map_add]; exact congrArg₂ (· + ·) hy hz
  · refine Eq.trans ?_ (sum_app R _ U _).symm
    refine Eq.trans ?_ (Finset.sum_congr rfl fun r _ ↦
      liftPull_app hc hπ (hσ r) (hσs r) j U b x).symm
    rw [Scheme.Modules.Hom.comp_app]
    change (omegaPull hπ j).val.app (op U)
      ((omegaTrace hc j).app U (toOm s' j (c ⁻¹ᵁ U) (b • formPull hc U j x))) = _
    rw [omegaTrace_toOm_smul_formPull hc j hU, toOm_apply, omegaPull_toOmega, formPull_smul, hF,
      Finset.sum_smul]
    exact map_sum (toOm sW j (π ⁻¹ᵁ U)) _ _

theorem hodgePull_hodgeTrace (j : ℕ)
    (H : omegaTrace hc j ≫ omegaPull hπ j = ∑ r ∈ R, liftPull (hσ r) (hσs r) j) (q : ℕ)
    (x : hodgeH s' j q) :
    hodgePull hπ j q (hodgeTrace hc j q x) = ∑ r ∈ R, hodgePull (hσs r) j q x := by
  letI := algΓ s; letI := algΓ s'; letI := algΓ sW
  obtain ⟨y, rfl⟩ := (coh.pushforwardEquiv k (appTop_algebraMap hc) (Omega s' j) q).surjective x
  have e1 : hodgeTrace hc j q (coh.pushforwardEquiv k (appTop_algebraMap hc) (Omega s' j) q y) =
      cohOn.map k (omegaTrace hc j) ⊤ q y :=
    congrArg (cohOn.map k (omegaTrace hc j) ⊤ q)
      ((coh.pushforwardEquiv k (appTop_algebraMap hc) (Omega s' j) q).symm_apply_apply y)
  have e2 : ∀ φ : (Scheme.Modules.pushforward c).obj (Omega s' j) ⟶
      (Scheme.Modules.pushforward π).obj (Omega sW j),
      cohOn.pull (σ := RingHom.id k) (appTop_algebraMap hπ) (𝟙 _) (le_refl (π ⁻¹ᵁ ⊤)) q
        (cohOn.map k φ ⊤ q y) =
      cohOn.pull (σ := RingHom.id k) (appTop_algebraMap hπ) φ (le_refl (π ⁻¹ᵁ ⊤)) q y := fun φ ↦ by
    rw [cohOn.pull_map, Category.comp_id]
  have e4 := cohOn.pull_map (σ := RingHom.id k) (appTop_algebraMap hπ)
    (omegaPull hπ j) (omegaTrace hc j) (le_refl (π ⁻¹ᵁ ⊤)) (n := q) y
  have e5 : cohOn.map k (∑ r ∈ R, liftPull (hσ r) (hσs r) j) ⊤ q =
      ∑ r ∈ R, cohOn.map k (liftPull (hσ r) (hσs r) j) ⊤ q :=
    map_sum (cohOn.mapAddHom k _ _ ⊤ q) _ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [H, ← e2, e5, LinearMap.sum_apply, map_sum] at e4
  rw [e1]
  refine e4.trans (Finset.sum_congr rfl fun r _ ↦ (e2 _).trans ?_)
  have h : (σ r ≫ c) ≫ s = sW := by rw [hσ, hπ]
  have s2 := cohOn_pull_pull (appTop_algebraMap hc) (appTop_algebraMap (hσs r))
    (appTop_algebraMap h) (𝟙 _) (omegaPull (hσs r) j) (le_refl (c ⁻¹ᵁ ⊤)) (le_refl _) (le_refl _) q y
  have s3 := cohOn_pull_congr (hσ r) (appTop_algebraMap h) (appTop_algebraMap hπ)
    (G := Omega sW j) (𝟙 ((Scheme.Modules.pushforward c).obj (Omega s' j)) ≫
      (Scheme.Modules.pushforward c).map (omegaPull (hσs r) j) ≫
        (Scheme.Modules.pushforwardComp (σ r) c).hom.app _)
    (V := ⊤) (W := σ r ⁻¹ᵁ (c ⁻¹ᵁ ⊤)) (le_refl _) (fun _ _ ↦ trivial) q y
  have hm : liftPull (hσ r) (hσs r) j = (𝟙 ((Scheme.Modules.pushforward c).obj (Omega s' j)) ≫
      (Scheme.Modules.pushforward c).map (omegaPull (hσs r) j) ≫
        (Scheme.Modules.pushforwardComp (σ r) c).hom.app _) ≫
          (Scheme.Modules.pushforwardCongr (hσ r)).hom.app _ := by
    simp [liftPull]
  rw [hm]
  exact s3.symm.trans s2.symm

end Forms

end GlobalTheory.GalTrace
end
end

