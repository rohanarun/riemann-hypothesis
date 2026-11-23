module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsConjPrimeEqDualLabel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualSplitLabelOperatorMulScalarOperator
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0128

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeConjPlaceEqDualLabel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SphConj

variable {D : D7}

theorem cA_cA' (z : Formalism.L2.Theta.AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(cA D).map_zero, (cA D).map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a x => exact congrArg (fun t => a ⊗ₜ[D.host.F] t) (star_star x)

theorem cO_eq (x : 𝓞 D.host.E) : Formalism.DivisionValues.cO D.host.E x = GlobalTheory.IdemSupport.cO D x := RingOfIntegers.ext rfl

theorem conjPl_eq_cP (P : HeightOneSpectrum (𝓞 D.host.E)) : conjPl P = GlobalTheory.IdemSupport.cP P := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  rw [GlobalTheory.IdemSupport.mem_cP]
  change x ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) ↔ _
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [cO_eq, GlobalTheory.IdemSupport.cO_cO]; exact hy
  · intro h
    exact ⟨GlobalTheory.IdemSupport.cO D x, h, by rw [cO_eq, GlobalTheory.IdemSupport.cO_cO]⟩

theorem mem_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) (x : 𝓞 D.host.E) :
    x ∈ (conjPl P).asIdeal ↔ GlobalTheory.IdemSupport.cO D x ∈ P.asIdeal := by
  rw [conjPl_eq_cP]; exact GlobalTheory.IdemSupport.mem_cP P x

theorem conjPl_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) : conjPl (conjPl P) = P := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  rw [mem_conjPl, mem_conjPl, GlobalTheory.IdemSupport.cO_cO]

theorem isConjPl_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.IndefR.Lev.IsConjPl P (conjPl P) :=
  (GlobalTheory.IdemSupport.isConjPl_iff P _).2 (conjPl_eq_cP P)

theorem not_mem_sq (P : HeightOneSpectrum (𝓞 D.host.E)) (ϖ : 𝓞 D.host.E) (h : ϖ ∉ (conjPl P).asIdeal ^ 2) :
    GlobalTheory.IdemSupport.cO D ϖ ∉ P.asIdeal ^ 2 := by
  intro h'
  apply h
  have e1 : (conjPl P).asIdeal = P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) := rfl
  rw [e1, ← Ideal.map_pow]
  have := Ideal.mem_map_of_mem (Formalism.DivisionValues.cO D.host.E) h'
  convert this using 1
  rw [cO_eq, GlobalTheory.IdemSupport.cO_cO]

theorem conj_cases (V : HSp D) {Q : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D} (h : IsPrimeIdem Q e f) :
    (Formalism.L2.NTheta.IsIdemAt e Q ∧ IsPrimeIdem (conjPl Q) (cA D e) f) ∨ (conjPl Q = Q ∧ f = e) := by
  rcases h with ⟨hi, rfl⟩ | ⟨rfl, h2, h3⟩
  · have hc := (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.2 Q (conjPl Q) e hi
      (isConjPl_conjPl Q)
    exact Or.inl ⟨hi, Or.inl ⟨hc, by rw [cA_cA', add_comm]⟩⟩
  · have h' : IsPrimeIdem Q f f := Or.inr ⟨rfl, h2, h3⟩
    have hc := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 Q f f h').2.1
    have ht : GlobalTheory.IdemSupport.Comparison₂ (GlobalTheory.IdemSupport.cP Q) f := by
      have := GlobalTheory.IdemSupport.Comparison₂.conj (P := Q) (e := f) h3
      rwa [hc] at this
    refine Or.inr ⟨?_, rfl⟩
    rw [conjPl_eq_cP]
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · subst hx; simp only [Submodule.zero_mem]
    · exact (ht x hx).trans (h3 x hx).symm

theorem hyp_conj (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) : GlobalTheory.Hk3.hyp V (conjPl P) = GlobalTheory.Hk3.hyp V P := by
  obtain ⟨e, f, h⟩ := (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.1 P
  rcases conj_cases V h with ⟨-, h'⟩ | ⟨hc, -⟩
  · rw [GlobalTheory.SphLabelOps.hyp_eq h', GlobalTheory.SphLabelOps.hyp_eq h]
  · rw [hc]

theorem divAt_conj (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E)
    (d : List ℤ) (α : GA D V) (he : Formalism.L2.NTheta.IsIdemAt e P) (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2)
    (hd : DivAt V e (ϖ : D.host.E) d α) : DivAt V (cA D e) (star (ϖ : D.host.E)) (dualLab d) α :=
  _root_.GlobalTheory.DivConj.divAt_conj V P e ϖ d α he h1 h2 hd

theorem sphOp_conj (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (R : Finset (GA D V))
    (hR : SphOp V (conjPl P) d R) : SphOp V P (dualLab d) R := by
  obtain ⟨e, f, ϖ, α, -, hef, hϖ, hϖ2, hd, hJ, hχ, hα, hdiv, hR, hrep⟩ := hR
  have hS : OffS D ∅ P := fun v hv => absurd hv (Finset.notMem_empty v)
  rcases conj_cases V hef with ⟨hi, h'⟩ | ⟨hc, rfl⟩
  · rw [conjPl_conjPl] at h'
    have hD := divAt_conj V (conjPl P) e ϖ d α hi hϖ hϖ2 hdiv
    rw [← GlobalTheory.IdemSupport.cO_coe] at hD
    exact ⟨cA D e, f, GlobalTheory.IdemSupport.cO D ϖ, α, hS, h', (mem_conjPl P ϖ).1 hϖ, not_mem_sq P ϖ hϖ2,
      GlobalTheory.SphLabelOps.dualLab_pairwise hd, hJ, hχ, hα, hD, hR, hrep⟩
  · have hc' : conjPl P = P := hc.symm.trans (conjPl_conjPl P)
    rw [hc'] at hef hϖ hϖ2
    have he := (GlobalTheory.HeckeDual.idem_of_isPrimeIdem hef).1
    obtain ⟨a, b, ha, -, hb, -, hab⟩ :=
      (GlobalTheory.InertDoubleCoset.inert_double_cosets V P f hef (GlobalTheory.SphLabelOps.exists_real_unif D P) α hα).1
    have h0 := GlobalTheory.SphLabelOps.unif_ne_zero hϖ2
    have hinv := (GlobalTheory.DivDual.divAt_inv_and_mul V f _ d α he h0 hdiv).1
    have ha' : a⁻¹ ∈ KsphC V ∅ := (GlobalTheory.SphLabelOps.mem_stabG _).1 (inv_mem ((GlobalTheory.SphLabelOps.mem_stabG _).2 ha))
    have hb' : b⁻¹ ∈ KsphC V ∅ := (GlobalTheory.SphLabelOps.mem_stabG _).1 (inv_mem ((GlobalTheory.SphLabelOps.mem_stabG _).2 hb))
    have hD := (GlobalTheory.DivDual.divAt_inv_and_mul V f _ _ α⁻¹ he h0 hinv).2 _ ha' _ hb'
    have e1 : a⁻¹ * α⁻¹ * b⁻¹ = α := by rw [hab]; group
    rw [e1] at hD
    exact ⟨f, f, ϖ, α, hS, hef, hϖ, hϖ2, GlobalTheory.SphLabelOps.dualLab_pairwise hd, hJ, hχ, hα, hD, hR, hrep⟩

theorem isLab_conj (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) :
    IsLab V (conjPl P) d ↔ IsLab V P (dualLab d) := by
  constructor
  · rintro ⟨R, hR⟩; exact ⟨R, sphOp_conj V P d R hR⟩
  · rintro ⟨R, hR⟩
    rw [← conjPl_conjPl P] at hR
    have := sphOp_conj V (conjPl P) (dualLab d) R hR
    rw [GlobalTheory.SphLabelOps.dualLab_dualLab] at this
    exact ⟨R, this⟩

theorem sum_rep_conj (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) {M : Type} [AddCommGroup M] [Module ℂ M]
    (π : GA D V →* Module.End ℂ M) (u : M) (hu : ∀ k ∈ GlobalTheory.Hk3.hyp V P, π k u = u) (d : List ℤ) :
    ∑ γ ∈ rep V (conjPl P) d, π γ u = ∑ γ ∈ rep V P (dualLab d), π γ u := by
  by_cases hd : IsLab V (conjPl P) d
  · have h1 := sphOp_conj V P d _ (GlobalTheory.SphLabelOps.sphOp_rep hd)
    rw [((GlobalTheory.SphLabelOps.label_operators V P).1 _ _ h1).2 M π u hu, GlobalTheory.SphLabelOps.opOf_single]
  · have hd' : ¬ IsLab V P (dualLab d) := fun h => hd ((isLab_conj V P d).2 h)
    rw [Hk3.rep, dite_eq_right hd, Hk3.rep, dite_eq_right hd']

theorem sph_conj : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), GlobalTheory.Hk3.hyp V (conjPl P) = GlobalTheory.Hk3.hyp V P ∧ (∀ d, IsLab V (conjPl P) d ↔ IsLab V P (dualLab d)) ∧ ∀ c, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ GlobalTheory.Hk3.hyp V P, π k u = u) → opOf π (conjPl P) c u = opOf π P (dualC c) u := by
  intro D V P
  refine ⟨hyp_conj V P, isLab_conj V P, fun c M _ _ π u hu => ?_⟩
  rw [opOf, opOf, dualC, Finsupp.sum_mapDomain_index (h := fun d (z : ℂ) => z • ∑ γ ∈ rep V P d, π γ) (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun d _ => by rw [sum_rep_conj V P π u hu d]

end GlobalTheory.SphConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeScalarLabelCompEqShiftDownSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CentralShift

open Formalism.L2.NTheta GlobalTheory.SplitPlace GlobalTheory.DualSplitRel

variable {D : D7}

theorem split_of_primeIdem {P : Pl D.host.E} (hP : conjPl P ≠ P) {e f : AE D} (h : IsPrimeIdem P e f) :
    IsIdemAt e P ∧ f = e + cA D e := by
  rcases h with h | ⟨-, ⟨v, ε, -, rfl⟩, ht⟩
  · exact h
  · refine absurd (GlobalTheory.IdemSupport.eq_of_le (Ideal.map_le_iff_le_comap.2 fun x hx => ?_)) hP
    have h2 := GlobalTheory.IdemSupport.Comparison₂.conj (P := P) ht
    rw [GlobalTheory.IdemSupport.cA_algebraMap] at h2
    by_cases h0 : x = 0
    · rw [h0]; exact zero_mem _
    · exact (h2 x h0).2 ((ht x h0).1 hx)

theorem dual_shift (d : List ℤ) : dualLab ((dualLab (d.map fun x => x - 1)).map (· - 1)) = d := by
  simp [dualLab, List.map_reverse, List.map_map, Function.comp_def]

theorem shift {P : Pl D.host.E} (hP : conjPl P ≠ P) {V : HSp D} {d : List ℤ} {R : Finset (GA D V)} [DecidableEq (GA D V)]
    (hR : SphOp V P d R) : ∃ z : GA D V, (∀ γ ∈ R, γ * z = z * γ) ∧
      SphOp V P (splitLab V.rank V.rank) {z} ∧ SphOp V P (d.map fun x => x - 1) (R.image (· * z)) := by
  obtain ⟨e, f, ϖ, α, -, hpi, h1, h2, hd, -, -, hα, hD, hRs, hc⟩ := hR
  obtain ⟨he, rfl⟩ := split_of_primeIdem hP hpi
  have h0 : (ϖ : D.host.E) ≠ 0 := GlobalTheory.SphLabelOps.unif_ne_zero h2
  obtain ⟨z, hs, hzc, hz⟩ := exists_central he.1 V h0
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V P
  have hKl : locPart V (KsphC V ∅) e = (K : Set (GA D V)) := (hyp_eq_locPart he V).symm.trans hK
  have hKz : ∀ k ∈ locPart V (KsphC V ∅) e, k * z = z * k := fun k hk => hzc k hk.2
  have sh : ∀ {d : List ℤ} {g : GA D V} {R' : Finset (GA D V)}, SuppAt e V g → DivAt V e (ϖ : D.host.E) d g →
      (∀ γ ∈ R', SuppAt e V γ) → IsCosetRep V (locPart V (KsphC V ∅) e) g R' →
      (d.map (· - 1)).Pairwise (fun a b => b ≤ a) → SphOp V P (d.map (· - 1)) (R'.image (· * z)) := by
    intro d g R' sg dg sR hr hp
    obtain ⟨a, b⟩ := coset_mul hKz (fun γ hγ => (hr.1 γ hγ).2) hr.2
    have sup : ∀ γ ∈ R'.image (· * z), SuppAt e V γ := fun γ hγ => by
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ
      exact suppAt_mul (sR δ hδ) hs
    exact sphOp_of he h1 h2 hp (suppAt_mul sg hs) (divAt_mul h0 hz dg) sup
      ⟨fun γ hγ => ⟨mem_GfC he.1 (sup γ hγ), a γ hγ⟩, b⟩
  have one : IsCosetRep V (locPart V (KsphC V ∅) e) 1 {1} := by
    have := coset_one K
    rw [← hKl] at this
    refine ⟨fun γ hγ => ⟨?_, this.1 γ hγ⟩, this.2⟩
    rw [Finset.mem_singleton.1 hγ]
    exact one_mem _
  have S0 := sh (GlobalTheory.SplitHecke.suppAt_one V)
    (GlobalTheory.SphLabelOps.divAt_one V he.1.1 (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem (Or.inl ⟨he, rfl⟩)) (ϖ : D.host.E))
    (fun γ hγ => by rw [Finset.mem_singleton.1 hγ]; exact GlobalTheory.SplitHecke.suppAt_one V) one
    (by rw [label_shift_zero]; simp [splitLab, List.pairwise_append, List.pairwise_replicate])
  rw [label_shift_zero, Finset.image_singleton, one_mul] at S0
  refine ⟨z, fun γ hγ => hzc γ (hRs γ hγ), S0, sh hα hD hRs hc ?_⟩
  exact List.pairwise_map.2 (hd.imp fun h => by omega)

theorem isLab_of_shift {P : Pl D.host.E} (hP : conjPl P ≠ P) {V : HSp D} {d : List ℤ}
    (h : IsLab V P (d.map fun x => x - 1)) : IsLab V P d := by
  obtain ⟨R, e, f, ϖ, α, -, hpi, h1, h2, hd, -, -, hα, hD, -, -⟩ := h
  obtain ⟨he, rfl⟩ := split_of_primeIdem hP hpi
  have h0 : (ϖ : D.host.E) ≠ 0 := GlobalTheory.SphLabelOps.unif_ne_zero h2
  obtain ⟨z, hs, -, hz⟩ := exists_central he.1 V h0
  have D1 := (GlobalTheory.DivDual.divAt_inv_and_mul V e _ _ _ he.1.1 h0 hD).1
  have D2 := divAt_mul h0 hz D1
  have D3 := (GlobalTheory.DivDual.divAt_inv_and_mul V e _ _ _ he.1.1 h0 D2).1
  rw [dual_shift] at D3
  refine GlobalTheory.SphLabelOps.isLab_of_divAt hpi h1 h2 ?_ ?_ D3
  · exact (List.pairwise_map.1 hd).imp fun h => by omega
  · exact suppAt_inv (suppAt_mul (suppAt_inv hα) hs)

theorem central_shift : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), conjPl P ≠ P → ∀ (d : List ℤ) (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ GlobalTheory.Hk3.hyp V P, π k u = u) → opOf π P (Finsupp.single (splitLab V.rank V.rank) 1) (opOf π P (Finsupp.single d 1) u) = opOf π P (Finsupp.single (d.map fun x => x - 1) 1) u := by
  classical
  intro D V P hP d M _ _ π u hu
  have c1 := (GlobalTheory.SphLabelOps.label_operators V P).1
  by_cases hl : IsLab V P d
  · obtain ⟨z, hzR, S0, S1⟩ := shift hP (GlobalTheory.SphLabelOps.sphOp_rep hl)
    have fw := (GlobalTheory.SphLabelOps.label_operators V P).2.1 (Finsupp.single d 1) M π u hu
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← (c1 _ _ S0).2 M π _ fw, ← (c1 _ _ S1).2 M π u hu, Finset.sum_singleton, GlobalTheory.SphLabelOps.opOf_single,
      map_sum, Finset.sum_image (mul_left_injective z).injOn]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [hzR γ hγ, map_mul, Module.End.mul_apply]
  · have hl' : ¬ IsLab V P (d.map fun x => x - 1) := fun h => hl (isLab_of_shift hP h)
    have e0 : rep V P d = ∅ := by rw [Hk3.rep, dite_eq_right hl]
    have e1 : rep V P (d.map fun x => x - 1) = ∅ := by rw [Hk3.rep, dite_eq_right hl']
    rw [GlobalTheory.SphLabelOps.opOf_single π d, e0, Finset.sum_empty, map_zero, GlobalTheory.SphLabelOps.opOf_single, e1,
      Finset.sum_empty]

end GlobalTheory.CentralShift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodPrimes

theorem isConjPl_iff {D : D7} {P P' : Pl D.host.E} : Formalism.IndefR.Lev.IsConjPl P P' ↔ P' = Formalism.DivisionValues.conjPl P := by
  constructor
  · intro h
    apply HeightOneSpectrum.ext
    refine ((Formalism.DivisionValues.conjPl P).isMaximal.eq_of_le P'.isPrime.ne_top ?_).symm
    refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
    obtain ⟨c', h1, h2⟩ := h c hc
    have : Formalism.DivisionValues.cO _ c = c' := RingOfIntegers.ext h2.symm
    show Formalism.DivisionValues.cO _ c ∈ P'.asIdeal
    rwa [this]
  · rintro rfl
    exact fun c hc => ⟨Formalism.DivisionValues.cO _ c, Ideal.mem_map_of_mem _ hc, rfl⟩

theorem eq_or_conj_of_under_eq {D : D7} {P Q : Pl D.host.E} (h : Q.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) :
    Q = P ∨ Q = Formalism.DivisionValues.conjPl P := by
  have hsub : (Q.asIdeal : Set (𝓞 D.host.E)) ⊆ P.asIdeal ∪ (Formalism.DivisionValues.conjPl P).asIdeal := by
    intro x hx
    have hfix : star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E) := by
      rw [star_mul', star_star, mul_comm]
    obtain ⟨y, hy⟩ := (D.sp.cm.fixed ((x : D.host.E) * star (x : D.host.E))).1 hfix
    have hint : IsIntegral ℤ y := by
      rw [← isIntegral_algebraMap_iff (B := D.host.E)]
      have e : algebraMap D.host.F D.host.E y = ((x * Formalism.DivisionValues.cO _ x : 𝓞 D.host.E) : D.host.E) := hy
      rw [e]
      exact (x * Formalism.DivisionValues.cO _ x).isIntegral_coe
    have hn : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨y, hint⟩ = x * Formalism.DivisionValues.cO _ x := RingOfIntegers.ext hy
    have h1 : (⟨y, hint⟩ : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ Q.asIdeal
      rw [hn]
      exact Ideal.mul_mem_right _ _ hx
    rw [h] at h1
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨y, hint⟩ ∈ P.asIdeal := h1
    rw [hn] at h2
    refine (P.isPrime.mem_or_mem h2).imp id fun h3 => ?_
    have h4 : Formalism.DivisionValues.cO _ (Formalism.DivisionValues.cO _ x) ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ h3
    have e : Formalism.DivisionValues.cO _ (Formalism.DivisionValues.cO _ x) = x := RingOfIntegers.ext (star_star (x : D.host.E))
    rw [e] at h4
    exact h4
  exact (Ideal.subset_union.1 hsub).imp
    (fun h => HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h))
    (fun h => HeightOneSpectrum.ext (Q.isMaximal.eq_of_le (Formalism.DivisionValues.conjPl P).isPrime.ne_top h))

theorem offS_iff {D : D7} (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : Pl D.host.E) :
    OffS D S P ↔ P.under (𝓞 D.host.F) ∉ S := by
  constructor
  · intro h hP
    obtain ⟨x, hx, hy⟩ := h _ hP
    exact hy (algebraMap _ _ x) rfl hx
  · intro h v hv
    by_contra hc
    push Not at hc
    apply h
    have : v = P.under (𝓞 D.host.F) := by
      refine HeightOneSpectrum.ext (v.isMaximal.eq_of_le (P.under (𝓞 D.host.F)).isPrime.ne_top fun x hx => ?_)
      obtain ⟨y, h1, h2⟩ := hc x hx
      have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x = y := RingOfIntegers.ext h1.symm
      show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ P.asIdeal
      rwa [e]
    rwa [← this]

theorem good_primes : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.Q A.μ0 = ∅ ∧ (∀ t P, Good R t P → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ Good R t (Formalism.DivisionValues.conjPl P) ∧ Good R A.μ0 P) ∧ (∀ SF, IsSF R SF → ∀ P, OffS D SF P ↔ Good R A.μ0 P) ∧ (R.IsFam → ∀ t, ∀ P ∈ A.ok t, Good R t (R.pl P) ∧ Formalism.DivisionValues.conjPl (R.pl P) ≠ R.pl P ∧ A.q P = Ideal.absNorm (R.pl P).asIdeal) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL
  have hQ : R.Q A.μ0 = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP h => ?_
    refine (hL.Q_ram A.μ0 PP).2 (Or.inl h) ?_
    rw [hL.xi_base]
    exact fun x _ => rfl
  have hcc := fun w : Pl D.host.E => Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl w
  refine ⟨hQ, fun t P hP => ⟨fun hg => ?_, fun PP h => ?_, fun PP h => ?_⟩, fun SF hSF P => ?_, fun hF t P hP => ?_⟩
  · have hk : ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
      rw [Nat.cast_mul] at hg
      rcases P.isPrime.mem_or_mem hg with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    obtain ⟨k, hk⟩ := hk
    rcases GlobalTheory.ConjOverQuad.div_or_conj_div D R.C.P k P hk with h | ⟨w', h, hw⟩
    · exact (hP P (Or.inl ((hL.Pg P).2 ⟨k, h⟩))).1 rfl
    · refine (hP w' (Or.inl ((hL.Pg w').2 ⟨k, h⟩))).2 (isConjPl_iff.2 ?_)
      rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at hw
      rw [HeightOneSpectrum.ext hw, hcc]
  · obtain ⟨h1, h2⟩ := hP PP h
    rw [isConjPl_iff] at h2 ⊢
    refine ⟨fun e => h2 (by rw [e, hcc]), fun e => h1 ?_⟩
    rw [← hcc PP, ← e, hcc]
  · rw [hQ] at h
    exact hP PP (Or.inl (h.resolve_right (Finset.notMem_empty _)))
  · rw [offS_iff]
    constructor
    · intro h PP hPP
      rw [hQ] at hPP
      have hPP' := hPP.resolve_right (Finset.notMem_empty _)
      have key : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ P.under (𝓞 D.host.F) := fun e =>
        h ((hSF _).2 ⟨PP, hPP', by rw [← e]; rfl⟩)
      exact ⟨fun e => key (by rw [e]), fun e => key (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e)⟩
    · intro h hm
      obtain ⟨PP, hPP, e⟩ := (hSF _).1 hm
      obtain ⟨h1, h2⟩ := h PP (Or.inl hPP)
      have e' : P.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := HeightOneSpectrum.ext e.symm
      rcases eq_or_conj_of_under_eq e' with h3 | h3
      · exact h1 h3.symm
      · exact h2 (isConjPl_iff.2 h3)
  · obtain ⟨gramR, c0R, c0L, hT⟩ := hF.tie
    obtain ⟨h1, h2, h3⟩ := (hT.ok t P).1 hP
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at h1 h3
    refine ⟨fun PP h => ?_, fun e => h1 (by rw [e]), ?_⟩
    · have hm : PP ∈ (R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E)) :=
        h.imp (fun h => hF.Sb h) id
      refine ⟨fun e => h2 (e ▸ hm), fun hc => h3 PP hm ?_⟩
      rw [isConjPl_iff.1 hc, hcc]
    · rw [hT.q P, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end GlobalTheory.GoodPrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnipotentRadicalFlagStabilizer
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

namespace GlobalTheory.UnipFlag

open Matrix

variable {k : Type} [Field k] {a s : ℕ} {d : Fin s → ℕ}

def lowSpan (e : (Σ i, Fin (d i)) ≃ Fin a) (c : Fin s) : Submodule k (Fin a → k) :=
  GlobalTheory.LowerBlockFlag.f0 e c

theorem exists_sub (k : Type) [Field k] (a s : ℕ) (d : Fin s → ℕ) (e : (Σ i, Fin (d i)) ≃ Fin a)
    (hne : GlobalTheory.SmGL.unipRad k e ≠ ⊥) :
    ∃ W : Submodule k (Fin a → k), W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g : GL (Fin a) k,
      (∀ v, ((g : Matrix (Fin a) (Fin a) k) - 1).mulVec v ∈ W) →
      (∀ v ∈ W, ((g : Matrix (Fin a) (Fin a) k) - 1).mulVec v = 0) → g ∈ GlobalTheory.SmGL.unipRad k e := by
  have hex : ∃ u ∈ GlobalTheory.SmGL.unipRad k e, u ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne ((Subgroup.eq_bot_iff_forall _).2 h)
  obtain ⟨u, hu, hu1⟩ := hex
  have hij : ∃ i j, (u : Matrix (Fin a) (Fin a) k) i j ≠ (1 : Matrix (Fin a) (Fin a) k) i j := by
    by_contra h
    push_neg at h
    exact hu1 (Units.ext (Matrix.ext h))
  obtain ⟨i, j, hij⟩ := hij
  obtain ⟨hp, hd⟩ := GlobalTheory.SmGL.mem_unipRad.1 hu
  have hlt : GlobalTheory.SmGL.blk e i < GlobalTheory.SmGL.blk e j := by
    rcases lt_trichotomy (GlobalTheory.SmGL.blk e i) (GlobalTheory.SmGL.blk e j) with h | h | h
    · exact h
    · exfalso
      obtain ⟨⟨b, i'⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨b', j'⟩, rfl⟩ := e.surjective j
      simp only [GlobalTheory.SmGL.blk_apply] at h
      subst h
      apply hij
      rw [hd]
      simp [Matrix.one_apply]
    · exfalso
      apply hij
      rw [GlobalTheory.SmGL.mem_parab.1 hp i j h, one_apply_ne (by rintro rfl; exact lt_irrefl _ h)]
  refine ⟨lowSpan e (GlobalTheory.SmGL.blk e i), ?_, ?_, ?_⟩
  · intro hb
    have hm : Pi.single i (1 : k) ∈ lowSpan e (GlobalTheory.SmGL.blk e i) := fun p hp' =>
      Pi.single_eq_of_ne (by rintro rfl; exact lt_irrefl _ hp') _
    rw [hb] at hm
    simpa using congrFun ((Submodule.mem_bot k).1 hm) i
  · intro ht
    have hm : Pi.single j (1 : k) ∈ lowSpan e (GlobalTheory.SmGL.blk e i) := ht ▸ Submodule.mem_top
    have := hm j hlt
    simp at this
  · intro g h1 h2
    have key : ∀ p q, ¬ (GlobalTheory.SmGL.blk e p < GlobalTheory.SmGL.blk e q) →
        ((g : Matrix (Fin a) (Fin a) k) - 1) p q = 0 := by
      intro p q hpq
      have hcol : ((g : Matrix (Fin a) (Fin a) k) - 1) p q =
          (((g : Matrix (Fin a) (Fin a) k) - 1) *ᵥ Pi.single q 1) p := by
        simp [Matrix.mulVec_single_one]
      rw [hcol]
      by_cases hq : GlobalTheory.SmGL.blk e q ≤ GlobalTheory.SmGL.blk e i
      · rw [h2 _ (fun r hr => Pi.single_eq_of_ne (by rintro rfl; exact absurd hq (not_le.2 hr)) _)]
        rfl
      · exact h1 _ p (lt_of_lt_of_le (not_le.1 hq) (not_lt.1 hpq))
    have hg : ∀ p q, (g : Matrix (Fin a) (Fin a) k) p q =
        (1 : Matrix (Fin a) (Fin a) k) p q + ((g : Matrix (Fin a) (Fin a) k) - 1) p q := by
      intro p q
      simp
    refine GlobalTheory.SmGL.mem_unipRad.2 ⟨GlobalTheory.SmGL.mem_parab.2 fun p q hqp => ?_, fun b p q => ?_⟩
    · rw [hg, key p q (not_lt.2 hqp.le), one_apply_ne (by rintro rfl; exact lt_irrefl _ hqp), add_zero]
    · rw [hg, key _ _ (by simp), add_zero]
      simp [Matrix.one_apply]

end GlobalTheory.UnipFlag
end

