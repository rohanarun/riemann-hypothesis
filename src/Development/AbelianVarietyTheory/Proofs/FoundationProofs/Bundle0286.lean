module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicModelChordLawSumAndDifference
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaPar.Chord

theorem chord_change {K : Type*} [Field K] [CharZero K] (e r s t a b c d : K) (he : e ≠ 0)
    (hac : a - c ≠ 0) :
    e ^ 2 * ((((b - d) / (a - c)) ^ 2 / 4 - a - c) - r) =
      ((e ^ 3 * (b / 2 - s * (a - r) - t) - e ^ 3 * (d / 2 - s * (c - r) - t)) /
          (e ^ 2 * (a - r) - e ^ 2 * (c - r))) ^ 2 +
        (e * (2 * s)) * ((e ^ 3 * (b / 2 - s * (a - r) - t) - e ^ 3 * (d / 2 - s * (c - r) - t)) /
          (e ^ 2 * (a - r) - e ^ 2 * (c - r))) - e ^ 2 * (3 * r - s ^ 2) -
        e ^ 2 * (a - r) - e ^ 2 * (c - r) := by
  have hm : (e ^ 3 * (b / 2 - s * (a - r) - t) - e ^ 3 * (d / 2 - s * (c - r) - t)) /
      (e ^ 2 * (a - r) - e ^ 2 * (c - r)) = e * ((b - d) / (a - c) / 2 - s) := by
    rw [show e ^ 2 * (a - r) - e ^ 2 * (c - r) = e ^ 2 * (a - c) by ring]
    field_simp
    ring
  rw [hm]
  ring

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe' (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  unfold lamC
  rw [dite_eq_left x.2]

theorem W_a₁ (g : GL3Theta.G1 p) : g.W.a₁ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (2 * g.C.s) := by
  simp [GL3Theta.G1.W, wModel, WeierstrassCurve.variableChange_a₁]

theorem W_a₂ (g : GL3Theta.G1 p) :
    g.W.a₂ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (3 * g.C.r - g.C.s ^ 2) := by
  simp [GL3Theta.G1.W, wModel, WeierstrassCurve.variableChange_a₂]

theorem W_a₃ (g : GL3Theta.G1 p) :
    g.W.a₃ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3 * (2 * g.C.t) := by
  simp [GL3Theta.G1.W, wModel, WeierstrassCurve.variableChange_a₃]

theorem xAt_add (g : GL3Theta.G1 p) (P Q : ℂ) (h : GlobalTheory.EvenTheta.IsLat g.abelian₂) (hP : P ∉ g.abelian₂)
    (hQ : Q ∉ g.abelian₂) (h1 : P + Q ∉ g.abelian₂) (h2 : P - Q ∉ g.abelian₂) (a1 : wpF g.abelian₂ P ∈ Qbar)
    (a2 : wpD g.abelian₂ P ∈ Qbar) (a3 : wpF g.abelian₂ Q ∈ Qbar) (a4 : wpD g.abelian₂ Q ∈ Qbar) :
    GlobalTheory.EvenTheta.xAt g P ≠ GlobalTheory.EvenTheta.xAt g Q ∧ GlobalTheory.EvenTheta.xAt g (P + Q) =
      ((yAt g P - yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) ^ 2 +
        g.W.a₁ * ((yAt g P - yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) -
        g.W.a₂ - GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q := by
  have hne : wpF g.abelian₂ P ≠ wpF g.abelian₂ Q := fun e => by
    rcases (h.wp_eq_iff hP hQ).1 e.symm with h' | h'
    exacts [h1 h', h2 h']
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair g.abelian₂ h
  have hadd : wpF g.abelian₂ (P + Q) =
      ((wpD g.abelian₂ P - wpD g.abelian₂ Q) / (wpF g.abelian₂ P - wpF g.abelian₂ Q)) ^ 2 / 4 -
        wpF g.abelian₂ P - wpF g.abelian₂ Q := by
    simp only [GlobalTheory.LatticeInvariants.wpF_eq hL, GlobalTheory.LatticeInvariants.wpD_eq hL] at hne ⊢
    exact (GlobalTheory.weierstrassP_add L ((hL P).not.1 hP) ((hL Q).not.1 hQ) hne).1
  set A : Qbar := ⟨_, a1⟩
  set B : Qbar := ⟨_, a2⟩
  set C : Qbar := ⟨_, a3⟩
  set D : Qbar := ⟨_, a4⟩
  have eA : lamC g.lam (wpF g.abelian₂ P) = g.lam A := lamC_coe' g.lam A
  have eB : lamC g.lam (wpD g.abelian₂ P) = g.lam B := lamC_coe' g.lam B
  have eC : lamC g.lam (wpF g.abelian₂ Q) = g.lam C := lamC_coe' g.lam C
  have eD : lamC g.lam (wpD g.abelian₂ Q) = g.lam D := lamC_coe' g.lam D
  have eS : lamC g.lam (wpF g.abelian₂ (P + Q)) =
      ((g.lam B - g.lam D) / (g.lam A - g.lam C)) ^ 2 / 4 - g.lam A - g.lam C := by
    have : wpF g.abelian₂ (P + Q) = ((((B - D) / (A - C)) ^ 2 / 4 - A - C : Qbar) : ℂ) := by
      rw [hadd]; push_cast; rfl
    rw [this, lamC_coe']
    simp only [map_sub, map_div₀, map_pow, map_ofNat]
  have hAC : g.lam A - g.lam C ≠ 0 := fun e =>
    hne (congrArg Subtype.val (g.lam.injective (sub_eq_zero.1 e)))
  have he : ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ≠ 0 := Units.ne_zero _
  rw [W_a₁, W_a₂]
  simp only [GlobalTheory.EvenTheta.xAt, yAt, eA, eB, eC, eD, eS]
  refine ⟨fun e => hAC ?_, chord_change _ _ _ _ _ _ _ _ he hAC⟩
  have := mul_left_cancel₀ (pow_ne_zero 2 he) e
  linear_combination this

theorem wpF_neg' {Λ : AddSubgroup ℂ} (h : GlobalTheory.EvenTheta.IsLat Λ) (z : ℂ) :
    wpF Λ (-z) = wpF Λ z := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  simp only [GlobalTheory.LatticeInvariants.wpF_eq hL, PeriodPair.weierstrassP_neg]

theorem wpD_neg' {Λ : AddSubgroup ℂ} (h : GlobalTheory.EvenTheta.IsLat Λ) (z : ℂ) :
    wpD Λ (-z) = -wpD Λ z := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  simp only [GlobalTheory.LatticeInvariants.wpD_eq hL, PeriodPair.derivWeierstrassP_neg]

theorem xAt_neg (g : GL3Theta.G1 p) (h : GlobalTheory.EvenTheta.IsLat g.abelian₂) (Q : ℂ) :
    GlobalTheory.EvenTheta.xAt g (-Q) = GlobalTheory.EvenTheta.xAt g Q := by
  simp only [GlobalTheory.EvenTheta.xAt, wpF_neg' h]

theorem yAt_neg (g : GL3Theta.G1 p) (h : GlobalTheory.EvenTheta.IsLat g.abelian₂) (Q : ℂ)
    (a4 : wpD g.abelian₂ Q ∈ Qbar) :
    yAt g (-Q) = g.W.toAffine.negY (GlobalTheory.EvenTheta.xAt g Q) (yAt g Q) := by
  have e : lamC g.lam (-wpD g.abelian₂ Q) = -lamC g.lam (wpD g.abelian₂ Q) := by
    have e1 := lamC_coe' g.lam (-(⟨_, a4⟩ : Qbar))
    have e2 := lamC_coe' g.lam (⟨_, a4⟩ : Qbar)
    rw [map_neg, ← e2] at e1
    exact e1
  have e1 : g.W.toAffine.a₁ = _ := W_a₁ g
  have e3 : g.W.toAffine.a₃ = _ := W_a₃ g
  rw [WeierstrassCurve.Affine.negY, e1, e3]
  simp only [GlobalTheory.EvenTheta.xAt, yAt, wpF_neg' h, wpD_neg' h, e]
  ring

theorem model_chord : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (P Q : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → P ∉ g.abelian₂ → Q ∉ g.abelian₂ → P + Q ∉ g.abelian₂ → P - Q ∉ g.abelian₂ → wpF g.abelian₂ P ∈ Qbar → wpD g.abelian₂ P ∈ Qbar → wpF g.abelian₂ Q ∈ Qbar → wpD g.abelian₂ Q ∈ Qbar → GlobalTheory.EvenTheta.xAt g P ≠ GlobalTheory.EvenTheta.xAt g Q ∧ GlobalTheory.EvenTheta.xAt g (P + Q) = ((GlobalTheory.ThetaPar.yAt g P - GlobalTheory.ThetaPar.yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) ^ 2 + g.W.a₁ * ((GlobalTheory.ThetaPar.yAt g P - GlobalTheory.ThetaPar.yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) - g.W.a₂ - GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q ∧ GlobalTheory.EvenTheta.xAt g (P - Q) = ((GlobalTheory.ThetaPar.yAt g P - g.W.toAffine.negY (GlobalTheory.EvenTheta.xAt g Q) (GlobalTheory.ThetaPar.yAt g Q)) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) ^ 2 + g.W.a₁ * ((GlobalTheory.ThetaPar.yAt g P - g.W.toAffine.negY (GlobalTheory.EvenTheta.xAt g Q) (GlobalTheory.ThetaPar.yAt g Q)) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) - g.W.a₂ - GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q := by
  intro p _ g P Q h _ _ hP hQ h1 h2 a1 a2 a3 a4
  obtain ⟨n, e⟩ := xAt_add g P Q h hP hQ h1 h2 a1 a2 a3 a4
  refine ⟨n, e, ?_⟩
  have := (xAt_add g P (-Q) h hP (by simpa using hQ) (by rwa [← sub_eq_add_neg])
    (by rwa [sub_neg_eq_add]) a1 a2 (by rwa [wpF_neg' h])
    (by rw [wpD_neg' h]; exact neg_mem a4)).2
  rwa [← sub_eq_add_neg, xAt_neg g h, yAt_neg g h Q a4] at this

end GlobalTheory.ThetaPar.Chord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicModelEquationTangentAtLatticeParameter
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaPar.ModelPoint

theorem wpD_sq {Λ : AddSubgroup ℂ} (h : GlobalTheory.EvenTheta.IsLat Λ) {v : ℂ} (hv : v ∉ Λ) :
    wpD Λ v ^ 2 = 4 * wpF Λ v ^ 3 - g2 Λ * wpF Λ v - g3 Λ := by
  obtain ⟨w₁, w₂, hi, hΛ⟩ := h
  let L : PeriodPair := ⟨w₁, w₂, hi⟩
  have hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
    intro z
    rw [hΛ, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  rw [GlobalTheory.LatticeInvariants.wpD_eq hL, GlobalTheory.LatticeInvariants.wpF_eq hL,
    GlobalTheory.LatticeInvariants.g2_eq hL, GlobalTheory.LatticeInvariants.lattice_invariant_g3_eq hL]
  exact L.derivWeierstrassP_sq v fun h => hv ((hL v).2 h)

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := dif_pos x.2

theorem lamC_neg_div_four (lam : Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ Qbar) :
    lamC lam (-x / 4) = -lamC lam x / 4 := by
  lift x to Qbar using hx
  have e : (-(x : ℂ) / 4) = ((-x / 4 : Qbar) : ℂ) := by push_cast; rfl
  rw [e, lamC_coe, lamC_coe, map_div₀, map_neg, map_ofNat]

theorem lamC_eqn (lam : Qbar →+* ℂ_[p]) {x y a b : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar)
    (ha : a ∈ Qbar) (hb : b ∈ Qbar) (h : y ^ 2 = 4 * x ^ 3 - a * x - b) :
    lamC lam y ^ 2 = 4 * lamC lam x ^ 3 - lamC lam a * lamC lam x - lamC lam b := by
  lift x to Qbar using hx
  lift y to Qbar using hy
  lift a to Qbar using ha
  lift b to Qbar using hb
  have e : y ^ 2 = 4 * x ^ 3 - a * x - b := by
    apply Subtype.ext
    push_cast
    exact h
  have := congrArg lam e
  simpa only [lamC_coe, map_sub, map_mul, map_pow, map_ofNat] using this

theorem model_point : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (v : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → wpD g.abelian₂ v ∈ Qbar → g.W.toAffine.Equation (GlobalTheory.EvenTheta.xAt g v) (GlobalTheory.ThetaPar.yAt g v) ∧ 2 * GlobalTheory.ThetaPar.yAt g v + g.W.a₁ * GlobalTheory.EvenTheta.xAt g v + g.W.a₃ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3 * lamC g.lam (wpD g.abelian₂ v) := by
  intro p _ g v hL h2 h3 hv hx hy
  have key := lamC_eqn g.lam hx hy h2 h3 (wpD_sq hL hv)
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff]
    simp only [GL3Theta.G1.W, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆, wModel, GlobalTheory.EvenTheta.xAt, GlobalTheory.ThetaPar.yAt,
      lamC_neg_div_four g.lam h2, lamC_neg_div_four g.lam h3]
    linear_combination ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 6 / 4 * key
  · simp only [GL3Theta.G1.W, WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₃, wModel, GlobalTheory.EvenTheta.xAt, GlobalTheory.ThetaPar.yAt]
    ring

end GlobalTheory.ThetaPar.ModelPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicModelTangentLawAtDouble
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ModelDouble

open _root_.WeierstrassCurve

theorem weierstrassP_two_mul (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) (h2 : 2 * P ∉ L.lattice) :
    L.derivWeierstrassP P ≠ 0 ∧
      L.weierstrassP (2 * P) =
        ((3 * L.weierstrassP P ^ 2 - L.g₂ / 4) / L.derivWeierstrassP P) ^ 2 - 2 * L.weierstrassP P := by
  have hPP : P + P ∉ L.lattice := by rwa [← two_mul]
  have hd : L.derivWeierstrassP P ≠ 0 := (GlobalTheory.derivWeierstrassP_eq_zero_iff L hP).not.mpr hPP
  refine ⟨hd, ?_⟩
  have h := GlobalTheory.latticePoint_add L P P
  have hy : L.derivWeierstrassP P / 2 ≠
      (GlobalTheory.latticeCurve L).toAffine.negY (L.weierstrassP P) (L.derivWeierstrassP P / 2) := by
    simp only [Affine.negY, GlobalTheory.latticeCurve]
    intro e; apply hd; linear_combination e
  rw [GlobalTheory.latticePoint_of_notMem L hP, GlobalTheory.latticePoint_of_notMem L hPP,
    Affine.Point.add_of_Y_ne hy, Affine.Point.some.injEq] at h
  rw [two_mul, h.1, Affine.slope_of_Y_ne rfl hy]
  simp only [Affine.addX, Affine.negY, GlobalTheory.latticeCurve]
  rw [show L.derivWeierstrassP P / 2 - (-(L.derivWeierstrassP P / 2) - 0 * L.weierstrassP P - 0) = L.derivWeierstrassP P by ring]
  field_simp
  ring

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  simp [lamC, x.2]

theorem lamC_ne_zero (lam : Qbar →+* ℂ_[p]) {x : Qbar} (hx : x ≠ 0) : lam x ≠ 0 :=
  (map_ne_zero lam).mpr hx

theorem tangent_law : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (P : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → P ∉ g.abelian₂ → 2 * P ∉ g.abelian₂ → wpF g.abelian₂ P ∈ Qbar → wpD g.abelian₂ P ∈ Qbar → 2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃ ≠ 0 ∧ GlobalTheory.EvenTheta.xAt g (2 * P) = ((3 * GlobalTheory.EvenTheta.xAt g P ^ 2 + 2 * g.W.a₂ * GlobalTheory.EvenTheta.xAt g P + g.W.a₄ - g.W.a₁ * GlobalTheory.ThetaPar.yAt g P) / (2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃)) ^ 2 + g.W.a₁ * ((3 * GlobalTheory.EvenTheta.xAt g P ^ 2 + 2 * g.W.a₂ * GlobalTheory.EvenTheta.xAt g P + g.W.a₄ - g.W.a₁ * GlobalTheory.ThetaPar.yAt g P) / (2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃)) - g.W.a₂ - 2 * GlobalTheory.EvenTheta.xAt g P := by
  intro p _ g P hlat hg2 _ hP h2P hwF hwD
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair _ hlat
  obtain ⟨hd, hdup⟩ := weierstrassP_two_mul L ((hL P).not.mp hP) ((hL _).not.mp h2P)
  simp only [← GlobalTheory.LatticeInvariants.wpF_eq hL, ← GlobalTheory.LatticeInvariants.wpD_eq hL,
    ← GlobalTheory.LatticeInvariants.g2_eq hL] at hd hdup
  set a : Qbar := ⟨wpF g.abelian₂ P, hwF⟩ with ha
  set d : Qbar := ⟨wpD g.abelian₂ P, hwD⟩ with hd'
  set G : Qbar := ⟨g2 g.abelian₂, hg2⟩ with hG
  have hd0 : d ≠ 0 := fun h => hd (congrArg Subtype.val h)
  have he : wpF g.abelian₂ (2 * P) = (((((3 * a ^ 2 - G / 4) / d) ^ 2 - 2 * a : Qbar)) : ℂ) := by
    rw [hdup]; simp [a, d, G]; norm_cast
  have lX : lamC g.lam (wpF g.abelian₂ P) = g.lam a := lamC_coe _ a
  have lD : lamC g.lam (wpD g.abelian₂ P) = g.lam d := lamC_coe _ d
  have l2 : lamC g.lam (wpF g.abelian₂ (2 * P)) = ((3 * g.lam a ^ 2 - g.lam G / 4) / g.lam d) ^ 2 - 2 * g.lam a := by
    rw [he, lamC_coe]; simp [map_div₀, map_ofNat]
  have lA : lamC g.lam (-(g2 g.abelian₂) / 4) = -(g.lam G) / 4 := by
    rw [show -(g2 g.abelian₂) / 4 = ((-G / 4 : Qbar) : ℂ) by simp [G]; norm_cast, lamC_coe]; simp [map_div₀, map_ofNat]
  have lD0 : g.lam d ≠ 0 := lamC_ne_zero _ hd0
  have ε0 : ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ≠ 0 := Units.ne_zero _
  simp only [GlobalTheory.EvenTheta.xAt, GlobalTheory.ThetaPar.yAt, GL3Theta.G1.W, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, wModel, lX, lD, l2, lA]
  set ε := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])
  set X := g.lam a
  set D := g.lam d
  have hden : 2 * (ε ^ 3 * (D / 2 - g.C.s * (X - g.C.r) - g.C.t)) + ε * (0 + 2 * g.C.s) * (ε ^ 2 * (X - g.C.r)) +
      ε ^ 3 * (0 + g.C.r * 0 + 2 * g.C.t) = ε ^ 3 * D := by ring
  rw [hden]
  refine ⟨mul_ne_zero (pow_ne_zero _ ε0) lD0, ?_⟩
  field_simp
  ring

end GlobalTheory.ModelDouble
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubmatrixMulVec
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames
open scoped Matrix

namespace GlobalTheory.FlatChange

theorem exists_blockMat {J : Type} [Fintype J] {m : J → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ, Fin (m τ))
    (K : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) ℂ) :
    ∃ V : Matrix (Fin g) (Fin g) ℂ, ∀ (z : Fin g → ℂ) τ i,
      (V *ᵥ z) (e.symm ⟨τ, i⟩) = (K τ *ᵥ fun j => z (e.symm ⟨τ, j⟩)) i := by
  classical
  refine ⟨(Matrix.blockDiagonal' K).submatrix e e, fun z τ i => ?_⟩
  rw [Matrix.mulVec, dotProduct, ← e.symm.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single τ]
  · simp [Matrix.mulVec, dotProduct]
  · intro τ' _ h
    simp [Matrix.blockDiagonal'_apply_ne _ _ _ h.symm]
  · simp

theorem det_mul_eq_one {n r : ℕ} (h : n = r) (B : Matrix (Fin r) (Fin r) ℂ) (C : Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ i, B.submatrix (Fin.cast h) (Fin.cast h) *ᵥ C i = Pi.single i 1) : B.det * C.det = 1 := by
  subst h
  have : B * Cᵀ = 1 := by
    ext a i
    have := congrFun (hC i) a
    rw [Pi.single_apply] at this
    rw [Matrix.one_apply, ← this]
    rfl
  rw [← Matrix.det_transpose C, ← Matrix.det_mul, this, Matrix.det_one]

theorem submatrix_mulVec {n r : ℕ} (h : n = r) (B : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) (i : Fin n) :
    (B.submatrix (Fin.cast h) (Fin.cast h) *ᵥ fun j => v (Fin.cast h j)) i = (B *ᵥ v) (Fin.cast h i) := by
  subst h
  rfl

theorem perFr_of_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {n r : ℕ} (h : n = r) (X : Data E r)
    (h0 : X.p0 = 0) (x : Frame X.Ψ r) (v : Fin r → E) {ρ : E →+* ℂ} (hρ : ρ ∈ X.Ψ) (i : Fin n) :
    perFr X x v ρ i = ((mat x ⟨ρ, hρ⟩)⁻¹ *ᵥ Data.emb ρ v) (Fin.cast h i) := by
  have hi : X.p0 + (i : ℕ) < r := by have := i.2; omega
  unfold perFr
  rw [dif_pos hρ, dif_pos hi]
  congr 1
  ext
  simp [h0]


set_option maxHeartbeats 1000000 in
theorem det_frChg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), Dw.q = 0 → GoodEmb c σ → IsUnf U → ∀ (k : U.Comp) (x x' : (U.X k).dom) (τ : Psi H) (hτ : relab c σ τ.1 ∈ (U.X k).Ψ) (g : (∀ ρ : E →+* ℂ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) (CAt σ))) (a : CAt σ), FrChg g a (U.un k x) (U.un k x') → (mat x'.1 ⟨_, hτ⟩).det = toC (g τ.1).det * (mat x.1 ⟨_, hτ⟩).det := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hq hσ hU k x x' τ hτ cf a hchg
  obtain ⟨hr, hty, -, -, -, g, e, F, ik, φ, -, hpt⟩ := hU
  obtain ⟨-, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hΨ⟩ := hty k
  obtain ⟨P, hPe, p, hx, hd, -⟩ := hpt k x
  obtain ⟨P', hPe', p', -, hd', -⟩ := hpt k x'
  have hm : ∀ ρ, relab c σ ρ ∈ (U.X k).Ψ → Dw.mult ρ = r := fun ρ h => by
    unfold Datum.mult
    rw [if_pos ((hrt ρ).1 ((hΨ _).1 h))]; omega
  have hm' : ∀ ρ, Fin (Dw.mult ρ) → relab c σ ρ ∈ (U.X k).Ψ := fun ρ i => by
    by_contra h
    have h1 : Dw.mult ρ = 0 := by
      unfold Datum.mult
      rw [if_neg (fun h' => h ((hΨ _).2 ((hrt ρ).2 h'))), hq]
    have := i.2
    omega
  let B : (U.X k).Ψ → Matrix (Fin r) (Fin r) ℂ := fun ρ => (mat x'.1 ρ)⁻¹ * mat x.1 ρ
  let K : ∀ ρ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) ℂ := fun ρ =>
    if h : relab c σ ρ ∈ (U.X k).Ψ then (B ⟨_, h⟩).submatrix (Fin.cast (hm ρ h)) (Fin.cast (hm ρ h)) else 0
  have hK : ∀ ρ (h : relab c σ ρ ∈ (U.X k).Ψ),
      K ρ = (B ⟨_, h⟩).submatrix (Fin.cast (hm ρ h)) (Fin.cast (hm ρ h)) := fun ρ h => dif_pos h
  obtain ⟨V, hV⟩ := exists_blockMat e K
  have hPV : ∀ b, P' b = V *ᵥ P b := by
    intro b
    funext j
    obtain ⟨⟨ρ, i⟩, rfl⟩ := e.symm.surjective j
    have h := hm' ρ i
    have h1 : ∀ (y : Frame (U.X k).Ψ r) (i : Fin (Dw.mult ρ)),
        perFr (U.X k) y (φ k b : Fin r → E) (relab c σ (e (e.symm ⟨ρ, i⟩)).1) (e (e.symm ⟨ρ, i⟩)).2 =
          ((mat y ⟨_, h⟩)⁻¹ *ᵥ Data.emb (relab c σ ρ) (φ k b : Fin r → E)) (Fin.cast (hm ρ h) i) := fun y i => by
      rw [Equiv.apply_symm_apply]
      exact perFr_of_zero (hm ρ h) _ (hp0.trans hq) y _ h i
    rw [hV, hPe', h1, hK ρ h]
    simp only [hPe, h1]
    rw [submatrix_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.2 (x.2 _).1)]
  obtain ⟨-, -, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F (ik k) P P'
    (LinearEquiv.refl _ _) V p p' (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩) (fun a => ⟨0, by simp⟩) hPV
  have hcol : ∀ i, V *ᵥ (∑ j, (show ℂ from cf τ.1 i j) • (Pi.single (e.symm ⟨τ.1, j⟩) 1 : Fin g → ℂ)) =
      Pi.single (e.symm ⟨τ.1, i⟩) 1 := by
    intro i
    have hc : IsCombAt (F.u (ik k) P) ((U.un k x).u τ.1) (show Fin (Dw.mult τ.1) → ℂ from cf τ.1 i)
        ((U.un k x').u τ.1 i) := by
      rw [← hx]; exact hchg.2.1 τ.1 i
    have d1 := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F (ik k) P p _ ((U.un k x).u τ.1) _
      (hd τ.1) (cf τ.1 i) _).1 hc
    have d2 := (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F (ik k) P p (ik k) P' (Matrix.mulVecLin V) p'
      hex _ _).1 d1
    have tn := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F (ik k) P' p'
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 (hd' τ.1 i)
  have hs : ∀ (i j : Fin (Dw.mult τ.1)),
      (Pi.single (e.symm ⟨τ.1, i⟩) 1 : Fin g → ℂ) (e.symm ⟨τ.1, j⟩) = (Pi.single i 1 : _ → ℂ) j := by
    intro i j
    simp [Pi.single_apply]
  have hdet := det_mul_eq_one (hm _ hτ) (B ⟨_, hτ⟩) (show Matrix _ _ ℂ from cf τ.1) fun i => by
    funext j
    rw [← hs, ← hcol, hV, hK _ hτ]
    congr 2
    funext j'
    refine (?_ : ∀ w : Fin (Dw.mult τ.1) → ℂ,
      w j' = (∑ j, w j • (Pi.single (e.symm ⟨τ.1, j⟩) 1 : Fin g → ℂ)) (e.symm ⟨τ.1, j'⟩)) (cf τ.1 i)
    intro w
    simp only [Finset.sum_apply, Pi.smul_apply, hs, smul_eq_mul]
    simp [Pi.single_apply]
  have hx' := (x'.2 ⟨_, hτ⟩).1
  simp only [B, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at hdet
  change _ = Matrix.det (show Matrix _ _ ℂ from cf τ.1) * _
  field_simp at hdet
  linear_combination -hdet

end GlobalTheory.FlatChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateModifiedSigmaAddMulSubAtZero
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory

theorem translate_modifiedSigma_add_mul_sub_at_zero :
    ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P Q : ℂ, P ∉ Λ → Q ∉ Λ →
      U1 Λ (P + Q) (sgStar Λ) 0 * U1 Λ (P - Q) (sgStar Λ) 0 =
        (wpF Λ Q - wpF Λ P) * U1 Λ P (sgStar Λ) 0 ^ 2 * U1 Λ Q (sgStar Λ) 0 ^ 2 := by
  intro Λ hΛ P Q hP hQ
  have hlaw := (GlobalTheory.OddTheta.sgStar_laws Λ hΛ).2.2.2.1 P Q hP hQ
  have hσ : sgStar Λ (P + Q) * sgStar Λ (P - Q) =
      (wpF Λ Q - wpF Λ P) * sgStar Λ P ^ 2 * sgStar Λ Q ^ 2 := by
    linear_combination hlaw
  simp only [U1, zero_add, mul_zero, zero_mul, zero_div, zero_sub]
  have hexp : ∀ x : ℂ, Complex.exp x ^ 2 = Complex.exp (2 * x) := by
    intro x; rw [← Complex.exp_nat_mul]; norm_num
  have key : Complex.exp (-(↑Real.pi * (P + Q) * (starRingEnd ℂ) (P + Q) / (2 * ↑(area Λ)))) *
      Complex.exp (-(↑Real.pi * (P - Q) * (starRingEnd ℂ) (P - Q) / (2 * ↑(area Λ)))) =
      Complex.exp (-(↑Real.pi * P * (starRingEnd ℂ) P / (2 * ↑(area Λ)))) ^ 2 *
      Complex.exp (-(↑Real.pi * Q * (starRingEnd ℂ) Q / (2 * ↑(area Λ)))) ^ 2 := by
    rw [hexp, hexp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [map_add (f := _), map_sub]
    ring
  calc _ = (sgStar Λ (P + Q) * sgStar Λ (P - Q)) *
      (Complex.exp (-(↑Real.pi * (P + Q) * (starRingEnd ℂ) (P + Q) / (2 * ↑(area Λ)))) *
      Complex.exp (-(↑Real.pi * (P - Q) * (starRingEnd ℂ) (P - Q) / (2 * ↑(area Λ))))) := by ring
    _ = _ := by rw [hσ, key]; ring

end GlobalTheory
end

