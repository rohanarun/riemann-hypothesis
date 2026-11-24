module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0010
public import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SumComplexEmbeddingsEqSumInfinitePlace
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LatticeSumBounds
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SchurAverage
public import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.Bundle0001
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0015
public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoveringRadius.CoverRad
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.FoldBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting

@[expose] public section

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
noncomputable section

namespace Formalism.L2.SG.Count

open MeasureTheory NumberField
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.L2.SG

section Lat

variable (I : AutInst)

def LatCount : Prop :=
  ∀ x y : I.GA, 0 < LitS.Size.tau1 I x → 0 < LitS.Size.tau1 I y →
    ∀ r : InfinitePlace I.F → ℝ, (∀ v, 0 ≤ r v) → ∀ S : Finset I.GFset,
      (∀ γ ∈ S, (x⁻¹ * (γ : I.GA) * y).2 ∈ I.Kset ∧ ∀ v, cartanDistance (I.ε v) ((x⁻¹ * (γ : I.GA) * y).1 v) ≤ r v) →
      (S.card : ℝ) ≤ (3 * Real.sqrt (I.n : ℝ) / (LitS.Size.tau1 I x * LitS.Size.tau1 I y)) ^ (2 * I.n ^ 2 * I.f) *
        Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, r v)

def Om (r : InfinitePlace I.F → ℝ) (K' : Set I.Gf) : Set I.GA :=
  {ω | (∀ v, cartanDistance (I.ε v) (ω.1 v) ≤ r v) ∧ ω.2 ∈ K'}

def COm (r : InfinitePlace I.F → ℝ) : ℝ :=
  (3 * Real.sqrt (I.n : ℝ)) ^ (2 * I.n ^ 2 * I.f) * Real.exp (4 * (I.n : ℝ) ^ 2 * ∑ v, r v)

def MultBound : Prop :=
  ∀ r : InfinitePlace I.F → ℝ, (∀ v, 0 ≤ r v) → ∀ K' : Subgroup I.Gf, (K' : Set I.Gf) ⊆ I.Kset →
    ∀ x : I.GA, 0 < LitS.Size.tau1 I x →
      FoldBound.mult (rr_GF I) (Om I r (K' : Set I.Gf)) x ≤
        ENNReal.ofReal (COm I r / LitS.Size.tau1 I x ^ (4 * I.n ^ 2 * I.f))

def FoldReady : Prop :=
  LocallyCompactSpace I.GA ∧ SecondCountableTopology I.GA ∧ T2Space I.GA ∧ BorelSpace I.GA ∧
    DiscreteTopology (rr_GF I)

end Lat

section DistInv

open Matrix

theorem dvi_hs_neg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.hs (-A) = Formalism.REAL.hs A := by
  simp [Formalism.REAL.hs, norm_neg]

theorem dvi_trace_hs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (Aᴴ * A).trace = ((Formalism.REAL.hs A : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Formalism.REAL.hs]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact RCLike.conj_mul _

theorem dvi_hs_conj {n : ℕ} (k X : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Formalism.REAL.hs (k * X * kᴴ) = Formalism.REAL.hs X := by
  have hk' : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
  apply Complex.ofReal_injective
  rw [← dvi_trace_hs, ← dvi_trace_hs, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  have e1 : k * (Xᴴ * kᴴ) * (k * X * kᴴ) = k * (Xᴴ * X) * kᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc kᴴ k, hk', Matrix.one_mul]
  rw [e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hk', Matrix.one_mul]

theorem dvi_sub {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) (t : ℝ)
    (ht : ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
      umat g = k * NormedSpace.exp X ∧ t = Real.sqrt (Formalism.REAL.hs X)) :
    ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
      umat g⁻¹ = k * NormedSpace.exp X ∧ t = Real.sqrt (Formalism.REAL.hs X) := by
  obtain ⟨k, X, hK, hX, hgm, ht⟩ := ht
  have hk1 : k ∈ Matrix.unitaryGroup (Fin n) ℂ := hK.1
  have hk : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk1
  have hk2 : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk1
  have hJk : k * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * k := hK.2
  have hX1 : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX.1
  have hX2 : X * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := hX.2
  have hY1 : (-X)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (-X) = 0 := by
    rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hX1, neg_zero]
  have hY2 : (-X) * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * (-X)) := by
    rw [Matrix.neg_mul, hX2, Matrix.mul_neg]
  have hφ : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (k * A * kᴴ) * (k * B * kᴴ) = k * (A * B) * kᴴ := by
    intro A B
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc kᴴ k, hk, Matrix.one_mul]
  have hJφ : k * Formalism.REAL.Jm ε * kᴴ = Formalism.REAL.Jm ε := by
    rw [hJk, Matrix.mul_assoc, hk2, Matrix.mul_one]
  have hct : (k * (-X) * kᴴ)ᴴ = k * (-X)ᴴ * kᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have hK' : kᴴ ∈ Formalism.REAL.Kset ε := by
    show kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ kᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * kᴴ
    refine ⟨Matrix.mem_unitaryGroup_iff.2 ?_, ?_⟩
    · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
      exact hk
    · calc kᴴ * Formalism.REAL.Jm ε = kᴴ * Formalism.REAL.Jm ε * (k * kᴴ) := by rw [hk2, Matrix.mul_one]
        _ = kᴴ * (Formalism.REAL.Jm ε * k) * kᴴ := by simp only [Matrix.mul_assoc]
        _ = kᴴ * (k * Formalism.REAL.Jm ε) * kᴴ := by rw [hJk]
        _ = Formalism.REAL.Jm ε * kᴴ := by rw [← Matrix.mul_assoc, hk, Matrix.one_mul]
  have hP' : Formalism.REAL.inP ε (k * (-X) * kᴴ) := by
    show ((k * (-X) * kᴴ)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (k * (-X) * kᴴ) = 0) ∧
      (k * (-X) * kᴴ) * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * (k * (-X) * kᴴ))
    constructor
    · rw [hct]
      calc (k * (-X)ᴴ * kᴴ) * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (k * (-X) * kᴴ)
          = (k * (-X)ᴴ * kᴴ) * (k * Formalism.REAL.Jm ε * kᴴ) + (k * Formalism.REAL.Jm ε * kᴴ) * (k * (-X) * kᴴ) := by
            rw [hJφ]
        _ = k * ((-X)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (-X)) * kᴴ := by
            rw [hφ, hφ, Matrix.mul_add, Matrix.add_mul]
        _ = 0 := by rw [hY1, Matrix.mul_zero, Matrix.zero_mul]
    · calc (k * (-X) * kᴴ) * Formalism.REAL.Jm ε = (k * (-X) * kᴴ) * (k * Formalism.REAL.Jm ε * kᴴ) := by rw [hJφ]
        _ = k * ((-X) * Formalism.REAL.Jm ε) * kᴴ := hφ _ _
        _ = k * (-(Formalism.REAL.Jm ε * (-X))) * kᴴ := by rw [hY2]
        _ = -((k * Formalism.REAL.Jm ε * kᴴ) * (k * (-X) * kᴴ)) := by rw [hφ, Matrix.mul_neg, Matrix.neg_mul]
        _ = -(Formalism.REAL.Jm ε * (k * (-X) * kᴴ)) := by rw [hJφ]
  have hE : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
    rw [← Matrix.exp_add_of_commute X (-X) (Commute.neg_right (Commute.refl X)), add_neg_cancel,
      NormedSpace.exp_zero]
  have hku : IsUnit k := ⟨⟨k, kᴴ, hk2, hk⟩, rfl⟩
  have hkinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hk
  have hconj : NormedSpace.exp (k * (-X) * kᴴ) = k * NormedSpace.exp (-X) * kᴴ := by
    rw [← hkinv]
    exact Matrix.exp_conj k (-X) hku
  have hinv : umat g⁻¹ * umat g = 1 := Units.inv_mul (g : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  have key : k * NormedSpace.exp X * (NormedSpace.exp (-X) * kᴴ) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (NormedSpace.exp X), hE, Matrix.one_mul, hk2]
  refine ⟨kᴴ, k * (-X) * kᴴ, hK', hP', ?_, ?_⟩
  · calc umat g⁻¹ = umat g⁻¹ * (umat g * (NormedSpace.exp (-X) * kᴴ)) := by
          rw [hgm, key, Matrix.mul_one]
      _ = NormedSpace.exp (-X) * kᴴ := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
      _ = kᴴ * NormedSpace.exp (k * (-X) * kᴴ) := by
          rw [hconj]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc kᴴ k, hk, Matrix.one_mul]
  · rw [ht, dvi_hs_conj k (-X) hk1, dvi_hs_neg]

theorem dV_inv {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) : cartanDistance ε g⁻¹ = cartanDistance ε g := by
  unfold cartanDistance
  congr 1
  ext t
  constructor
  · intro h
    have h2 := dvi_sub ε g⁻¹ t h
    rwa [inv_inv] at h2
  · exact dvi_sub ε g t

end DistInv

theorem encard_le_ofReal_of_finset {α : Type*} (T : Set α) (M : ℝ)
    (h : ∀ S : Finset α, (∀ a ∈ S, a ∈ T) → (S.card : ℝ) ≤ M) :
    ((T.encard : ℕ∞) : ENNReal) ≤ ENNReal.ofReal M := by
  rcases T.finite_or_infinite with hT | hT
  · have hS := h hT.toFinset (fun a ha => hT.mem_toFinset.1 ha)
    rw [hT.encard_eq_coe_toFinset_card]
    have e : (((hT.toFinset.card : ℕ∞)) : ENNReal) = ((hT.toFinset.card : ℕ) : ENNReal) := by simp
    rw [e, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hS
  · exfalso
    obtain ⟨S, hSsub, hcard⟩ := hT.exists_subset_card_eq (⌈M⌉₊ + 1)
    have h1 := h S (fun a ha => hSsub ha)
    rw [hcard] at h1
    push_cast at h1
    linarith [Nat.le_ceil M]

theorem multBound_of_latCount (I : AutInst) (hL : LatCount I) (hT : DistTri) : MultBound I := by
  intro r hr K' hK' x hx
  have hbound : (3 * Real.sqrt (I.n : ℝ) / (LitS.Size.tau1 I x * LitS.Size.tau1 I x)) ^ (2 * I.n ^ 2 * I.f) *
      Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, 2 * r v) = COm I r / LitS.Size.tau1 I x ^ (4 * I.n ^ 2 * I.f) := by
    have e1 : (LitS.Size.tau1 I x * LitS.Size.tau1 I x) ^ (2 * I.n ^ 2 * I.f) =
        LitS.Size.tau1 I x ^ (4 * I.n ^ 2 * I.f) := by
      rw [← pow_two, ← pow_mul]
      ring_nf
    have e2 : 2 * (I.n : ℝ) ^ 2 * ∑ v, 2 * r v = 4 * (I.n : ℝ) ^ 2 * ∑ v, r v := by
      rw [← Finset.mul_sum]
      ring
    rw [div_pow, e1, e2]
    unfold COm
    ring
  unfold FoldBound.mult
  refine iSup_le fun y => ?_
  apply encard_le_ofReal_of_finset
  intro S hS
  rcases S.eq_empty_or_nonempty with hS0 | ⟨γ0, hγ0S⟩
  · rw [hS0, Finset.card_empty, Nat.cast_zero]
    unfold COm
    have := hx
    positivity
  have hγ0 := hS γ0 hγ0S
  let F : rr_GF I → I.GFset := fun γ => ⟨((γ * γ0⁻¹ : rr_GF I) : I.GA), (γ * γ0⁻¹).2⟩
  have hFinj : Function.Injective F := by
    intro γ1 γ2 h
    have h2 : γ1 * γ0⁻¹ = γ2 * γ0⁻¹ := Subtype.ext (congrArg Subtype.val h)
    exact mul_right_cancel h2
  have hc := hL x x hx hx (fun v => 2 * r v) (fun v => by linarith [hr v]) (S.map ⟨F, hFinj⟩) ?_
  · rw [Finset.card_map] at hc
    rw [← hbound]
    exact hc
  · intro δ hδ
    obtain ⟨γ, hγS, hδeq⟩ := Finset.mem_map.1 hδ
    have h1 := hS γ hγS
    have hδv : (δ : I.GA) = (γ : I.GA) * (γ0 : I.GA)⁻¹ := by
      rw [← hδeq]
      rfl
    have e : x⁻¹ * ((γ : I.GA) * (γ0 : I.GA)⁻¹) * x =
        (x⁻¹ * ((γ : I.GA) * y)) * (x⁻¹ * ((γ0 : I.GA) * y))⁻¹ := by
      group
    rw [hδv, e]
    constructor
    · exact hK' (K'.mul_mem h1.2 (K'.inv_mem hγ0.2))
    · intro v
      refine le_trans (hT _ (I.ε v) ((x⁻¹ * ((γ : I.GA) * y)).1 v) ((x⁻¹ * ((γ0 : I.GA) * y)).1 v)⁻¹) ?_
      rw [dV_inv]
      linarith [h1.1 v, hγ0.1 v]

theorem muA_isHaar (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] :
    (I.muA μf).IsHaarMeasure := by
  haveI : ∀ v, (Formalism.REAL.muG (I.ε v)).IsHaarMeasure := fun v => by
    unfold Formalism.REAL.muG
    infer_instance
  haveI hpi : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsHaarMeasure := by
    infer_instance
  unfold AutInst.muA
  exact Measure.prod.instIsHaarMeasure _ _

theorem level_set_le_compact {D : Formalism.BasicNotions.D7} (X : HidaSetting.HidaSetting D) : X.K2 ⊆ X.B.I.Kset :=
  fun _ hx => hx.1

def levelSubgroupOfCharacter {D : Formalism.BasicNotions.D7} (X : HidaSetting.HidaSetting D) (hG : X.LevelSubgroupCharacter) : Subgroup X.B.I.Gf where
  carrier := X.K2
  one_mem' := hG.1
  mul_mem' := fun ha hb => hG.2.1 _ ha _ hb
  inv_mem' := fun ha => hG.2.2.1 _ ha

end Formalism.L2.SG.Count
