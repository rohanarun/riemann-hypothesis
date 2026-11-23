module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsMulMinusculeTopTerm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOneAddSkewHermitianMulLattice
section
open Matrix

noncomputable section

namespace GlobalTheory.SelfDualUnip

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem cT_add' (σ : L →+* L) {n : ℕ} (X Y : Matrix (Fin n) (Fin n) L) :
    Formalism.UG.cT σ (X + Y) = Formalism.UG.cT σ X + Formalism.UG.cT σ Y := by
  unfold Formalism.UG.cT; ext i j; simp

theorem det_cT (σ : L →+* L) {n : ℕ} (X : Matrix (Fin n) (Fin n) L) :
    (Formalism.UG.cT σ X).det = σ X.det := by
  unfold Formalism.UG.cT; rw [Matrix.det_transpose, RingHom.map_det]; rfl

theorem cT_int (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} {X : Matrix (Fin n) (Fin n) L}
    (hX : ∀ i j, X i j ∈ Formalism.UG.intL L) (i j : Fin n) : Formalism.UG.cT σ X i j ∈ Formalism.UG.intL L := by
  have h := hX j i
  rw [GlobalTheory.Hk3.mem_intL_iff] at h ⊢
  show Valued.v (σ (X j i)) ≤ 1
  rw [hσ]; exact h

theorem lift_int {n : ℕ} {X : Matrix (Fin n) (Fin n) L} (hX : ∀ i j, X i j ∈ Formalism.UG.intL L) :
    ∃ X' : Matrix (Fin n) (Fin n) (Formalism.UG.intL L), X'.map (Formalism.UG.intL L).subtype = X :=
  ⟨fun i j => ⟨X i j, hX i j⟩, by ext i j; rfl⟩

theorem v_det_eq_one {n : ℕ} {M N : Matrix (Fin n) (Fin n) L} (hM : ∀ i j, M i j ∈ Formalism.UG.intL L)
    (hN : ∀ i j, N i j ∈ Formalism.UG.intL L) (hMN : M * N = 1) : Valued.v M.det = 1 := by
  have hd : Valued.v M.det * Valued.v N.det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, hMN, Matrix.det_one, map_one]
  obtain ⟨M', rfl⟩ := lift_int hM
  obtain ⟨N', rfl⟩ := lift_int hN
  have hdM : (M'.map (Formalism.UG.intL L).subtype).det = (Formalism.UG.intL L).subtype M'.det :=
    (RingHom.map_det _ _).symm
  have hdN : (N'.map (Formalism.UG.intL L).subtype).det = (Formalism.UG.intL L).subtype N'.det :=
    (RingHom.map_det _ _).symm
  have hM1 : Valued.v (M'.map (Formalism.UG.intL L).subtype).det ≤ 1 := by
    rw [hdM]; exact (M'.det).2
  have hN1 : Valued.v (N'.map (Formalism.UG.intL L).subtype).det ≤ 1 := by
    rw [hdN]; exact (N'.det).2
  by_contra hne
  have hlt := lt_of_le_of_ne hM1 hne
  have := mul_lt_one_of_lt_of_le hlt hN1
  rw [hd] at this
  exact lt_irrefl _ this

theorem int_of_left_inv {n : ℕ} {G X : Matrix (Fin n) (Fin n) L} (hG : ∀ i j, G i j ∈ Formalism.UG.intL L)
    (hd : Valued.v G.det = 1) (hXG : X * G = 1) : ∀ i j, X i j ∈ Formalism.UG.intL L := by
  obtain ⟨G', rfl⟩ := lift_int hG
  have hdG : (G'.map (Formalism.UG.intL L).subtype).det = (Formalism.UG.intL L).subtype G'.det :=
    (RingHom.map_det _ _).symm
  have hne : (G'.map (Formalism.UG.intL L).subtype).det ≠ 0 := by
    intro h; rw [h, map_zero] at hd; exact zero_ne_one hd
  have hinv : ((G'.map (Formalism.UG.intL L).subtype).det)⁻¹ ∈ Formalism.UG.intL L := by
    rw [GlobalTheory.Hk3.mem_intL_iff, map_inv₀, hd, inv_one]
  have hu : IsUnit G'.det := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
    apply Subtype.ext
    show (Formalism.UG.intL L).subtype G'.det * ((G'.map (Formalism.UG.intL L).subtype).det)⁻¹ = 1
    rw [← hdG]; exact mul_inv_cancel₀ hne
  have hGY : G'.map (Formalism.UG.intL L).subtype * (G'⁻¹).map (Formalism.UG.intL L).subtype = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv G' hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hX : X = (G'⁻¹).map (Formalism.UG.intL L).subtype := by
    calc X = X * (G'.map (Formalism.UG.intL L).subtype * (G'⁻¹).map (Formalism.UG.intL L).subtype) := by
          rw [hGY, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hXG, Matrix.one_mul]
  intro i j
  rw [hX]; exact (G'⁻¹ i j).2

theorem selfDual_mul_of_skew : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L), (∀ x, Valued.v (σ x) = Valued.v x) →
  ∀ (n : ℕ) (JS a k : GL (Fin n) L) (E : Matrix (Fin n) (Fin n) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  Formalism.UG.cT σ E * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * E) → (∀ i j, E i j ∈ Formalism.UG.intL L) →
  (∀ i j, (E * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) → (k : Matrix (Fin n) (Fin n) L) = 1 + E →
  (∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.HoweG.SelfDual σ JS (k * a) := by
  intro L _ _ σ hσ n JS a k E hJ ha hE hEint hEa hk hki
  obtain ⟨hG0, hX0⟩ := ha

  have hKint : ∀ i j, (k : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
    intro i j
    rw [hk, Matrix.add_apply, Matrix.one_apply]
    refine (Formalism.UG.intL L).add_mem ?_ (hEint i j)
    split_ifs
    · exact (Formalism.UG.intL L).one_mem
    · exact (Formalism.UG.intL L).zero_mem
  have hE' : ∀ X : Matrix (Fin n) (Fin n) L, Formalism.UG.cT σ E * ((JS : Matrix (Fin n) (Fin n) L) * X) =
      -((JS : Matrix (Fin n) (Fin n) L) * (E * X)) := by
    intro X; rw [← Matrix.mul_assoc, hE, Matrix.neg_mul, Matrix.mul_assoc]

  have hGeq : Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
      (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) =
      Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L) +
      Formalism.UG.cT σ (E * (a : Matrix (Fin n) (Fin n) L)) * (JS : Matrix (Fin n) (Fin n) L) *
        (E * (a : Matrix (Fin n) (Fin n) L)) := by
    rw [hk, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_add', Formalism.UG.cT_one]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hE',
      Matrix.mul_neg]
    abel
  have hGint : ∀ i j, (Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
      (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L))) i j ∈
      Formalism.UG.intL L := by
    intro i j
    rw [hGeq, Matrix.add_apply]
    exact (Formalism.UG.intL L).add_mem (hG0 i j)
      (GlobalTheory.Hk3.matMul_int (GlobalTheory.Hk3.matMul_int (cT_int σ hσ hEa) hJ) hEa i j)

  have hK1 : Valued.v (k : Matrix (Fin n) (Fin n) L).det = 1 := v_det_eq_one hKint hki k.mul_inv
  have hX0G0 : Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L) *
      (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) = 1 := by
    have e3 : Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← Formalism.UG.cT_mul, a.inv_mul, Formalism.UG.cT_one]
    calc _ = Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * ((JS : Matrix (Fin n) (Fin n) L) *
          (((a : Matrix (Fin n) (Fin n) L) * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
          (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)))) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [a.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc (JS : Matrix (Fin n) (Fin n) L), JS.mul_inv,
          Matrix.one_mul, e3]
  have hG01 := v_det_eq_one hG0 hX0 hX0G0
  have hdet : Valued.v (Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
      (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L))).det = 1 := by
    have : (Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
        (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L))).det =
        σ (k : Matrix (Fin n) (Fin n) L).det * (k : Matrix (Fin n) (Fin n) L).det *
        (Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)).det := by
      simp only [Matrix.det_mul, det_cT, map_mul]; ring
    rw [this, map_mul, map_mul, hσ, hK1, hG01]; simp

  have hXG : (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Formalism.UG.cT σ (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
      (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L))) = 1 := by
    have hka : ((k * a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        (k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L) := Units.val_mul k a
    rw [← hka]
    have e3 : Formalism.UG.cT σ (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        Formalism.UG.cT σ ((k * a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← Formalism.UG.cT_mul, (k * a).mul_inv, Formalism.UG.cT_one]
    calc _ = (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          ((Formalism.UG.cT σ (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          Formalism.UG.cT σ ((k * a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
          ((JS : Matrix (Fin n) (Fin n) L) * ((k * a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)))) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e3, Matrix.one_mul, ← Matrix.mul_assoc ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L), JS.inv_mul, Matrix.one_mul, (k * a).inv_mul]
  refine ⟨?_, int_of_left_inv hGint hdet hXG⟩
  intro i j
  rw [Units.val_mul]
  exact hGint i j

end GlobalTheory.SelfDualUnip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeSplitTopDegreeRecursion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitTopStep

open Formalism.L2.NTheta

theorem opOf_sum_single {D : D7} {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M)
    (P : Pl D.host.E) {ι : Type} (s : Finset ι) (l : ι → List ℤ) (z : ι → ℂ) :
    opOf π P (∑ i ∈ s, Finsupp.single (l i) (z i)) = ∑ i ∈ s, z i • ∑ γ ∈ rep V P (l i), π γ := by
  classical
  unfold opOf
  rw [← Finsupp.sum_finsetSum_index (by simp) (by intros; simp [add_smul])]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.sum_single_index (by simp)]

theorem pos_iff_lt : ∀ {n : ℕ} (d : Fin n → ℤ), Antitone d →
    ∀ i : Fin n, 0 < d i ↔ (i : ℕ) < ((List.ofFn d).filter fun x => 0 < x).length
  | 0, _, _, i => i.elim0
  | n + 1, d, hd, i => by
    have ih := pos_iff_lt (fun j : Fin n => d j.succ) (fun a b h => hd (Fin.succ_le_succ_iff.2 h))
    rw [List.ofFn_succ, List.filter_cons]
    by_cases h0 : 0 < d 0
    · simp only [h0, decide_true, if_true, List.length_cons]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [h0]
      · simp [ih j]
    · have hnil : (List.ofFn fun j : Fin n => d j.succ).filter (fun x => 0 < x) = [] := by
        rw [List.filter_eq_nil_iff, List.forall_mem_ofFn_iff]
        intro j
        simpa only [decide_eq_true_eq] using
          (fun hj : 0 < d j.succ => h0 (lt_of_lt_of_le hj (hd (Fin.zero_le j.succ))))
      have hi : ¬ 0 < d i := fun hi => h0 (lt_of_lt_of_le hi (hd (Fin.zero_le i)))
      simp [h0, hnil, hi]

theorem dualLab_splitLab (n k : ℕ) (hk : k ≤ n) :
    dualLab (splitLab n k) = List.ofFn fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0 := by
  apply List.ext_getElem
  · simp [dualLab, splitLab]; omega
  · intro i h1 h2
    simp [dualLab, splitLab, List.getElem_reverse, List.getElem_append, List.getElem_replicate]

theorem top_step : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), conjPl P ≠ P → ∀ d : List ℤ, IsLab V P d → (∀ x ∈ d, 0 ≤ x) → (∃ x ∈ d, 0 < x) → ∃ m : ℕ, 0 < m ∧ ∃ c : List ℤ →₀ ℂ, (∀ d' ∈ c.support, (∀ x ∈ d', 0 ≤ x) ∧ d'.sum = d.sum ∧ (d'.map fun x => x ^ 2).sum < (d.map fun x => x ^ 2).sum) ∧ ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ GlobalTheory.Hk3.hyp V P, π k u = u) → opOf π P (Finsupp.single (d.map fun x => if 0 < x then x - 1 else x) 1) (opOf π P (Finsupp.single (dualLab (splitLab V.rank (d.filter fun x => 0 < x).length)) 1) u) = (m : ℂ) • opOf π P (Finsupp.single d 1) u + opOf π P c u := by
  classical
  intro D V P hP d hd hnn _
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V P
  obtain ⟨R0, e, f, ϖ, α0, -, hpi, h1, h2, hdp, -, -, -, hD0, -, -⟩ := hd
  obtain ⟨he, rfl⟩ := GlobalTheory.CentralShift.split_of_primeIdem hP hpi
  have hKl : ∀ k ∈ K, k ∈ KsphC V ∅ ∧ Formalism.L2.Theta.SuppAt e V k := fun k hk => by
    have : k ∈ GlobalTheory.Hk3.hyp V P := hK ▸ hk
    rw [GlobalTheory.DualSplitRel.hyp_eq_locPart he V] at this
    exact this
  obtain ⟨dF, rfl⟩ : ∃ dF : Fin V.rank → ℤ, d = List.ofFn dF :=
    ⟨fun i => d[i.1]'(by have := hD0.1; omega), by apply List.ext_getElem <;> simp [hD0.1]⟩
  have hanti : Antitone dF := fun i j hij => by
    rcases hij.lt_or_eq with h | h
    · exact List.pairwise_ofFn.1 hdp h
    · rw [h]
  have hnn' : ∀ i, 0 ≤ dF i := fun i => hnn _ (List.mem_ofFn.2 ⟨i, rfl⟩)
  set kk := ((List.ofFn dF).filter fun x => 0 < x).length with hkk
  have hk := pos_iff_lt dF hanti
  have hkn : kk ≤ V.rank := by
    have := List.length_filter_le (fun x => decide (0 < x)) (List.ofFn dF)
    simpa using this
  set d₁ : Fin V.rank → ℤ := fun i => if 0 < dF i then dF i - 1 else dF i with hd₁
  set aF : Fin V.rank → ℤ := fun i => if (i : ℕ) < kk then 1 else 0 with haF
  have e1 : (List.ofFn dF).map (fun x => if 0 < x then x - 1 else x) = List.ofFn d₁ := by
    rw [List.map_ofFn]; rfl
  rw [e1, dualLab_splitLab _ _ hkn]

  obtain ⟨ρ, hon, hint, hdiv⟩ := _root_.GlobalTheory.SplitPrimeChart.exists_chart V P e he ϖ h1 h2
  set ϖL := algebraMap D.host.E (P.adicCompletion D.host.E) (ϖ : D.host.E) with hϖL
  have hv : Formalism.UG.IsUnifV D.host.E P ϖL :=
    (P.valuedAdicCompletion_eq_valuation' (ϖ : D.host.E)).trans
      ((P.valuation_of_algebraMap ϖ).trans (GlobalTheory.LatIntFacts.intValuation_uniformiser P h1 h2))
  have hvO : ϖL ∈ Formalism.UG.Ov D.host.E P := (Formalism.UG.P.cartan_unif_lt_one D.host.E P _ hv).le
  have hϖ0 : ϖL ≠ 0 := by
    intro h0
    have := hv
    unfold Formalism.UG.IsUnifV at this
    rw [h0, map_zero] at this
    exact WithZero.zero_ne_coe this
  let mkD : (Fin V.rank → ℤ) → GL (Fin V.rank) (P.adicCompletion D.host.E) := fun a =>
    ⟨Formalism.UG.diagPow D.host.E P ϖL a, Formalism.UG.diagPow D.host.E P ϖL (-a),
      by simp only [Formalism.UG.diagPow, Matrix.diagonal_mul_diagonal, Pi.neg_apply, ← zpow_add₀ hϖ0, add_neg_cancel,
          zpow_zero, Matrix.diagonal_one],
      by simp only [Formalism.UG.diagPow, Matrix.diagonal_mul_diagonal, Pi.neg_apply, ← zpow_add₀ hϖ0, neg_add_cancel,
          zpow_zero, Matrix.diagonal_one]⟩
  have hmk : ∀ a, ((mkD a : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _) =
      Formalism.UG.diagPow D.host.E P ϖL a := fun a => rfl
  have hdiag : ∀ g a, ρ g = mkD a → DivAt V e (ϖ : D.host.E) (List.ofFn a) g := fun g a h =>
    hdiv g a 1 (one_mem _) 1 (one_mem _) (by rw [h, hmk]; simp)
  obtain ⟨g, hgS, hg⟩ := hon (mkD d₁)
  obtain ⟨h, hhS, hh⟩ := hon (mkD aF)
  have hgh : ρ (g * h) = mkD dF := by
    rw [map_mul, hg, hh]
    apply Units.ext
    simp only [Units.val_mul, hmk, Formalism.UG.diagPow, Matrix.diagonal_mul_diagonal]
    congr 1
    funext l
    rw [← zpow_add₀ hϖ0]
    congr 1
    have := hk l
    have := hnn' l
    simp only [d₁, aF]
    split_ifs <;> omega
  have hpi' : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have pw : ∀ a : Fin V.rank → ℤ, Antitone a → (List.ofFn a).Pairwise fun x y => y ≤ x :=
    fun a ha => List.pairwise_ofFn.2 fun i j hij => ha hij.le
  have hS : ∀ x, Formalism.L2.Theta.SuppAt e V x → ∀ a, Antitone a → DivAt V e (ϖ : D.host.E) (List.ofFn a) x →
      GlobalTheory.SphLabelOps.Reps K x (rep V P (List.ofFn a)) := fun x hx a ha hD =>
    GlobalTheory.SphLabelOps.reps_of_sphOp hK hpi' h1 h2 hx hD
      (GlobalTheory.SphLabelOps.sphOp_rep (GlobalTheory.SphLabelOps.isLab_of_divAt hpi' h1 h2 (pw a ha) hx hD))
  have a₁ : Antitone d₁ := fun i j hij => by
    have := hanti hij
    simp only [d₁]; split_ifs <;> omega
  have a₂ : Antitone aF := fun i j hij => by
    have : (i : ℕ) ≤ j := hij
    simp only [aF]; split_ifs <;> omega
  have r₁ := hS g hgS d₁ a₁ (hdiag g d₁ hg)
  have r₂ := hS h hhS aF a₂ (hdiag h aF hh)
  have hghS : Formalism.L2.Theta.SuppAt e V (g * h) := GlobalTheory.SplitHecke.suppAt_mul hgS hhS
  have r₀ := hS (g * h) hghS dF hanti (hdiag _ _ hgh)
  obtain ⟨T, m, hghT, hT, hTi, hsum⟩ := GlobalTheory.SphLabelOps.reps_mul_decomp K g h _ _ r₁ r₂

  have hx : ∀ x ∈ T, Formalism.L2.Theta.SuppAt e V x ∧ ∃ k₁ ∈ K, ∃ k₂ ∈ K, ∃ k₃ ∈ K, x = k₁ * g * k₂ * h * k₃ := by
    intro x hxT
    obtain ⟨-, γ, hγ, γ', hγ', k₁, hk₁, k₂, hk₂, rfl⟩ := hT x hxT
    obtain ⟨a, ha, b, hb, rfl⟩ := r₁.1 γ hγ
    obtain ⟨a', ha', b', hb', rfl⟩ := r₂.1 γ' hγ'
    have s : ∀ k ∈ K, Formalism.L2.Theta.SuppAt e V k := fun k hk => (hKl k hk).2
    have hxe : k₁ * (a * g * b * (a' * h * b')) * k₂ = k₁ * a * g * (b * a') * h * (b' * k₂) := by group
    rw [hxe]
    refine ⟨?_, k₁ * a, K.mul_mem hk₁ ha, b * a', K.mul_mem hb ha', b' * k₂, K.mul_mem hb' hk₂, rfl⟩
    have m := @GlobalTheory.SplitHecke.suppAt_mul
    exact m (m (m (m (m (s _ hk₁) (s _ ha)) hgS) (m (s _ hb) (s _ ha'))) hhS) (m (s _ hb') (s _ hk₂))

  have cart : ∀ x : GA D V, ∃ a : Fin V.rank → ℤ, Antitone a ∧
      ∃ k₁ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P), ∃ k₂ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P),
        ((ρ x : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _) =
          (k₁ : Matrix (Fin V.rank) (Fin V.rank) _) * Formalism.UG.diagPow D.host.E P ϖL a * (k₂ : Matrix (Fin V.rank) (Fin V.rank) _) :=
    fun x => Formalism.UG.Final.CartanDecomp D.host.E P V.rank ϖL hvO hv (ρ x)
  choose cx hcx k₁x hk₁x k₂x hk₂x hcxe using cart
  have hcxD : ∀ x, DivAt V e (ϖ : D.host.E) (List.ofFn (cx x)) x := fun x =>
    hdiv x (cx x) _ (hk₁x x) _ (hk₂x x) (hcxe x)

  have hineq : ∀ x ∈ T, x ≠ g * h → (∀ i, 0 ≤ cx x i) ∧
      (∑ i, cx x i = ∑ i, dF i ∧ ∑ i, cx x i ^ 2 < ∑ i, dF i ^ 2) := by
    intro x hxT hne
    obtain ⟨sx, k₁, hk₁, k₂, hk₂, k₃, hk₃, hxe⟩ := hx x hxT
    have key := _root_.GlobalTheory.Hk3.MinuscTopLocal.cartan_top_step D.host.E P V.rank ϖL hv dF kk hanti hnn' hk (ρ k₁) (hint _ (hKl _ hk₁).1)
      (ρ k₂) (hint _ (hKl _ hk₂).1) (ρ k₃) (hint _ (hKl _ hk₃).1) (cx x) (hcx x) _ (hk₁x x) _ (hk₂x x) (by
        rw [← hcxe x, hxe]
        simp only [map_mul, Units.val_mul, hg, hh, hmk] <;> rfl)
    refine ⟨key.1, key.2.resolve_left fun heq => hne ?_⟩
    have rx := hS x sx (cx x) (hcx x) (hcxD x)
    rw [heq] at rx
    obtain ⟨γ, ⟨hγ, hγx⟩, -⟩ := rx.2 x ⟨1, K.one_mem, 1, K.one_mem, by group⟩
    obtain ⟨a, ha, b, hb, hγe⟩ := r₀.1 γ hγ
    refine (hTi (g * h) hghT x hxT ⟨a, ha, b * (γ⁻¹ * x), K.mul_mem hb hγx, by rw [← mul_assoc, ← hγe]; group⟩).symm
  refine ⟨m (g * h), (hT _ hghT).1, ∑ x ∈ T.erase (g * h), Finsupp.single (List.ofFn (cx x)) (m x : ℂ), ?_, ?_⟩
  · intro d' hd'
    obtain ⟨x, hxT, hd'x⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hd')
    obtain ⟨hne, hxT⟩ := Finset.mem_erase.1 hxT
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hd'x)]
    obtain ⟨c1, c2, c3⟩ := hineq x hxT hne
    refine ⟨fun y hy => ?_, ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
      exact c1 i
    · rw [List.sum_ofFn, List.sum_ofFn]; exact c2
    · rw [List.map_ofFn, List.map_ofFn, List.sum_ofFn, List.sum_ofFn]; exact c3
  · intro M _ _ π u hu
    have hu' : ∀ k ∈ K, π k u = u := fun k hk => hu k (hK ▸ hk)
    rw [GlobalTheory.SphLabelOps.opOf_single, GlobalTheory.SphLabelOps.opOf_single, GlobalTheory.SphLabelOps.opOf_single, opOf_sum_single,
      LinearMap.sum_apply]
    have hsum' := hsum (fun x => if x = g * h then rep V P (List.ofFn dF) else rep V P (List.ofFn (cx x)))
      (fun x hxT => by
        by_cases hxe : x = g * h
        · rw [if_pos hxe, hxe]; exact r₀
        · rw [if_neg hxe]; exact hS x (hx x hxT).1 (cx x) (hcx x) (hcxD x)) M π u hu'
    have lhs : ∑ γ ∈ rep V P (List.ofFn d₁), π γ (∑ γ' ∈ rep V P (List.ofFn aF), π γ' u) =
        ∑ γ ∈ rep V P (List.ofFn d₁), ∑ γ' ∈ rep V P (List.ofFn aF), π (γ * γ') u := by
      refine Finset.sum_congr rfl fun γ _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun γ' _ => ?_
      rw [map_mul, Module.End.mul_apply]
    rw [lhs, hsum', ← Finset.add_sum_erase _ _ hghT, if_pos rfl]
    congr 1
    · rw [Nat.cast_smul_eq_nsmul]
    · refine Finset.sum_congr rfl fun x hxT => ?_
      rw [if_neg (Finset.mem_erase.1 hxT).1, LinearMap.smul_apply, LinearMap.sum_apply, Nat.cast_smul_eq_nsmul]

end GlobalTheory.SplitTopStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuaMatchingConjugatePrime
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.ConjMatch

variable {D : D7}

theorem conj_eq_cP (P : Pl D.host.E) : Formalism.DivisionValues.conjPl P = GlobalTheory.IdemSupport.cP P :=
  (GlobalTheory.IdemSupport.isConjPl_iff P _).1 (GlobalTheory.SplitHeckeAdj.isConjPl_conj P)

theorem conj_conj (P : Pl D.host.E) : Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl P) = P := by
  rw [conj_eq_cP, conj_eq_cP]
  apply HeightOneSpectrum.ext
  ext x
  rw [GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO]

theorem isPrimeIdem_conj {P : Pl D.host.E} {e f : AE D} (h : IsPrimeIdem P e f) :
    IsPrimeIdem (Formalism.DivisionValues.conjPl P) (cA D e) f := by
  rcases h with ⟨h, rfl⟩ | ⟨rfl, ⟨v, ε, hε, rfl⟩, ht⟩
  · have h1 : Formalism.L2.NTheta.IsIdemAt (cA D e) (Formalism.DivisionValues.conjPl P) := by
      rw [conj_eq_cP]
      obtain ⟨⟨h1, h2, v, ε, hε, h3⟩, ht⟩ := h
      exact ⟨⟨by rw [← RingHom.map_mul, h1], by rw [Formalism.L2.Theta.cA_cA, mul_comm, h2], v, ε, hε,
        by rw [Formalism.L2.Theta.cA_cA, add_comm, h3]⟩, GlobalTheory.IdemSupport.Comparison₂.conj ht⟩
    exact Or.inl ⟨h1, by rw [Formalism.L2.Theta.cA_cA, add_comm]⟩
  · have hc := GlobalTheory.IdemSupport.cA_algebraMap (D := D) ε
    have ht' := GlobalTheory.IdemSupport.Comparison₂.conj (P := P) ht
    rw [← conj_eq_cP] at ht'
    rw [hc] at ht' ⊢
    exact Or.inr ⟨rfl, ⟨v, ε, hε, rfl⟩, ht'⟩

theorem isVacAt_conj (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (P : Pl D.host.E) (f : WO S T → ℂ)
    (h : IsVacAt ψ S T P f) : IsVacAt ψ S T (Formalism.DivisionValues.conjPl P) f := by
  refine ⟨h.1, fun e f' hP u hu hh => h.2 (cA D e) f' ?_ u hu ?_⟩
  · have := isPrimeIdem_conj hP
    rwa [conj_conj] at this
  · rw [Formalism.L2.Theta.cA_cA]
    exact hh.symm

theorem one_mem_hyp (V : HSp D) (P : Pl D.host.E) : (1 : GA D V) ∈ hyp V P := by
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem (GlobalTheory.IdemSupport.exists_comp D).choose_spec P
  refine ⟨⟨one_mem _, fun y => ?_, fun v hv => absurd hv (Finset.notMem_empty v)⟩, e, f, h,
    (GlobalTheory.IdemSupport.suppGroup V f).one_mem⟩
  rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one, Matrix.one_mulVec]

theorem match_conj : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → (∀ f, IsVacAt ψ S T (conjPl P) f ↔ IsVacAt ψ S T P f) ∧ (VacFix ψ om P → VacFix ψ om (conjPl P) ∧ ∀ cS cT, Match ψ om (conjPl P) cS cT ↔ Match ψ om P (dualC cS) (dualC cT)) := by
  intro D ψ S T χS χT om P _
  have hv : ∀ f, IsVacAt ψ S T (conjPl P) f ↔ IsVacAt ψ S T P f := fun f =>
    ⟨fun h => by have := isVacAt_conj ψ S T _ f h; rwa [conj_conj] at this, isVacAt_conj ψ S T P f⟩
  refine ⟨hv, fun hF => ?_⟩
  have hS := _root_.GlobalTheory.SphConj.sph_conj S P
  have hT := _root_.GlobalTheory.SphConj.sph_conj T P
  refine ⟨fun f hf k hk k' hk' => hF f ((hv f).1 hf) k (hS.1 ▸ hk) k' (hT.1 ▸ hk'), fun cS cT => ?_⟩
  have eS : ∀ f, IsVacAt ψ S T P f → ∀ c, opOf (om.comp (MonoidHom.inl _ _)) (conjPl P) c f =
      opOf (om.comp (MonoidHom.inl _ _)) P (dualC c) f := fun f hf c =>
    hS.2.2 c _ (om.comp (MonoidHom.inl _ _)) f fun k hk => hF f hf k hk 1 (one_mem_hyp T P)
  have eT : ∀ f, IsVacAt ψ S T P f → ∀ c, opOf (om.comp (MonoidHom.inr _ _)) (conjPl P) c f =
      opOf (om.comp (MonoidHom.inr _ _)) P (dualC c) f := fun f hf c =>
    hT.2.2 c _ (om.comp (MonoidHom.inr _ _)) f fun k hk => hF f hf 1 (one_mem_hyp S P) k hk
  constructor
  · intro h f hf
    rw [← eS f hf, ← eT f hf]
    exact h f ((hv f).2 hf)
  · intro h f hf
    have hf' := (hv f).1 hf
    rw [eS f hf', eT f hf']
    exact h f hf'

end GlobalTheory.Hk3.ConjMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnipotentRadicalFlagStabilizerStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_flag_stabilizer : ∀ (k : Type) [Field k] (a s : ℕ) (d : Fin s → ℕ) (e : (Σ i, Fin (d i)) ≃ Fin a), GlobalTheory.SmGL.unipRad k e ≠ ⊥ → ∃ W : Submodule k (Fin a → k), W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g : GL (Fin a) k, (∀ v, ((g : Matrix (Fin a) (Fin a) k) - 1).mulVec v ∈ W) → (∀ v ∈ W, ((g : Matrix (Fin a) (Fin a) k) - 1).mulVec v = 0) → g ∈ GlobalTheory.SmGL.unipRad k e := by
  first | exact @GlobalTheory.UnipFlag.exists_sub | exact GlobalTheory.UnipFlag.exists_sub | (intros; apply GlobalTheory.UnipFlag.exists_sub; all_goals assumption)
end

