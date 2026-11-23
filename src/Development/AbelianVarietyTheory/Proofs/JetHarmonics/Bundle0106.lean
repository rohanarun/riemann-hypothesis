module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TwistedMeasureMomentsEqShiftedSeriesJets
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0085
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MatrixUnitZeroZeroEqInsert

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MeasureOfProducts
section
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.ProdMeasure
variable {q : ℕ} [Fact q.Prime]

theorem hasSum_pi_prod : ∀ (g : ℕ) (u : Fin g → ℕ → ℂ_[q]) (s : Fin g → ℂ_[q]),
    (∀ i, HasSum (u i) (s i)) → HasSum (fun ν : Fin g → ℕ => ∏ i, u i (ν i)) (∏ i, s i) := by
  haveI : NonarchimedeanRing ℂ_[q] := ⟨NonarchimedeanAddGroup.is_nonarchimedean⟩
  intro g
  induction g with
  | zero =>
    intro u s _
    simpa using hasSum_fintype (fun ν : Fin 0 → ℕ => ∏ i, u i (ν i))
  | succ g ih =>
    intro u s h
    have h1 := (h 0).mul_of_nonarchimedean (ih (fun i => u i.succ) (fun i => s i.succ) fun i => h _)
    rw [← (Fin.consEquiv (fun _ : Fin (g + 1) => ℕ)).hasSum_iff, Fin.prod_univ_succ]
    convert h1 using 1
    funext p
    simp [Fin.consEquiv, Fin.prod_univ_succ]

theorem bd_one_pow {f : ℂ_[q]⟦X⟧} (h : Bd 1 f) (a : ℕ) : Bd 1 (f ^ a) := by
  induction a with
  | zero =>
    intro n
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ a ih =>
    have := ((sup_norm_laws q).1 _ _ _ _ ih h).2
    rwa [mul_one, ← pow_succ] at this

theorem shiftS_pow {ζ : ℂ_[q]} (hζ : ‖ζ - 1‖ < 1) {f : ℂ_[q]⟦X⟧} (h : Bd 1 f) (a : ℕ) :
    shiftS ζ (f ^ a) = shiftS ζ f ^ a := by
  have H := Shift.shift_laws q ζ hζ
  induction a with
  | zero => simpa using H.2.2.1 1
  | succ a ih => rw [pow_succ, (H.2.1 _ _ ⟨1, bd_one_pow h a⟩ ⟨1, h⟩).2, ih, pow_succ]

theorem hat_pow (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (hl : constantCoeff ℓ = 0) (G : ℂ → ℂ)
    (hG : AnalyticAt ℂ G 0) (a : ℕ) : hat ι ℓ (fun z => G z ^ a) = hat ι ℓ G ^ a := by
  have H := TaylorRead.hat_laws q ι ℓ hl
  induction a with
  | zero => simpa using H.2.1 1
  | succ a ih =>
    simp only [pow_succ]
    rw [(H.1 (fun z => G z ^ a) G (hG.pow a) hG).2.1, ih]

theorem prod_fiber_pow {g k : ℕ} (σ : Fin k → Fin g) (x : Fin g → ℂ_[q]) :
    ∏ l, x (σ l) = ∏ i, x i ^ (Finset.univ.filter (fun l => σ l = i)).card := by
  rw [← Finset.prod_fiberwise Finset.univ σ (fun l => x (σ l))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_const]
  exact Finset.prod_congr rfl fun l hl => by rw [(Finset.mem_filter.mp hl).2]

theorem measure_of_products : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (δ : ℂ) (Ω : ℂ_[q]) (θ : ℂ → ℂ), 0 < d → δ ≠ 0 → Ω ≠ 0 → Differentiable ℂ θ → ThetaLaws ι d (Ω / ι δ) θ → ∀ (g m : ℕ) (a : Fin g → ℕ) (c : Fin m → ℂ) (t : Fin m → Fin g → ℂ), (∀ j i, PrimeTo d q (t j i)) → ∃ μ : C(Fin g → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q], (∀ B : ℝ, 0 ≤ B → (‖μ‖ ≤ B ↔ ∀ ν : Fin g → ℕ, ‖∑ j, ι (c j) * ∏ i, coeff (ν i) (hat ι (C (Ω / ι δ) * logS) (U1 d (t j i) θ) ^ a i)‖ ≤ B)) ∧ ∀ (n s : ℕ) (y : Fin g → ℂ), Nat.Coprime s q → (∀ j i, InOK d ((s : ℂ) * t j i)) → (∀ i, Good ι d n s (y i)) → ∀ (k : ℕ) (ys : Fin k → Fin g → ℂ) (F : C(Fin g → ℤ_[q], ℂ_[q])), (∀ A, F A = (∏ i, ι (kap1 d 1 (y i)) ^ (PadicInt.toZModPow n (A i)).val) * ∏ l, (Ω⁻¹ * ∑ i, ι (ys l i) * zc (A i))) → ι (iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∑ j, c j * ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) 0 (fun l => δ⁻¹ • ys l)) = μ F := by
  intro d q _ ι δ Ω θ hd hδ hΩ hθ hL g m a c t ht
  set ω : ℂ_[q] := Ω / ι δ with hω
  have hS : ∀ j i, Bd 1 (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i) :=
    fun j i => bd_one_pow (hL.1 _ (ht j i)) _
  obtain ⟨μ, hμ1, hμ2⟩ := GlobalTheory.MultiMahler.exists_measure_of_bounded_moments q g
    (fun ν => ∑ j, ι (c j) * ∏ i, coeff (ν i) (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i))
    ⟨∑ j, ‖ι (c j)‖, fun ν => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by
      rw [norm_mul, norm_prod]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hS j i _))⟩
  refine ⟨μ, hμ1, ?_⟩
  intro n s y hs hst hy k ys F hF
  have hl : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
    simp [logS, ← coeff_zero_eq_constantCoeff_apply]
  have hdiff : ∀ j i, Differentiable ℂ (W1 d (y i) (U1 d (t j i) θ)) := fun j i =>
    ((heisenbergOne d hd).2.2.1 _ _ ((heisenbergOne d hd).2.2.1 _ _ hθ).1).2
  have hroot : ∀ i, ι (kap1 d 1 (y i)) ^ (q ^ n) = 1 := fun i =>
    (hL.2.1 0 (y i) n s hs ⟨0, 0, by simp⟩ (hy i)).1
  have hf : ∀ (i : Fin g) (e : ℕ), ∃ f : C(ℤ_[q], ℂ_[q]),
      (∀ A, f A = ι (kap1 d 1 (y i)) ^ (PadicInt.toZModPow n A).val * zc A ^ e) ∧
      ∀ j, HasSum (fun r : ℕ => coeff r (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i) *
        (fwdDiff (1 : ℤ_[q]))^[r] f 0)
        (ω ^ e * ι (iteratedDeriv e (fun z => W1 d (y i) (U1 d (t j i) θ) z ^ a i) 0)) := by
    intro i e
    obtain ⟨f, hf, -⟩ := _root_.GlobalTheory.MomOne.TwistMom.twisted_moments q 0 _ n e ⟨0, fun r => by simp⟩ (hroot i)
    refine ⟨f, hf, fun j => ?_⟩
    obtain ⟨f', hf', h⟩ := _root_.GlobalTheory.MomOne.TwistMom.twisted_moments q _ _ n e ⟨1, hS j i⟩ (hroot i)
    obtain rfl : f' = f := by ext A; rw [hf, hf']
    have han := (hdiff j i).analyticAt 0
    rw [shiftS_pow (ShiftComp.norm_sub_one_lt_of_root (hroot i)) (hL.1 _ (ht j i)),
      ← (hL.2.1 _ _ n s hs (hst j i) (hy i)).2, ← hat_pow ι _ hl _ han,
      (hat_multiplicative_chart q ι ω (fun z => W1 d (y i) (U1 d (t j i) θ) z ^ a i)
        (han.pow (a i))).2.1 e] at h
    exact h
  choose f hf1 hf2 using hf
  let P : (Fin k → Fin g) → C(Fin g → ℤ_[q], ℂ_[q]) := fun σ =>
    ⟨fun A => ∏ i, f i (Finset.univ.filter (fun l => σ l = i)).card (A i), by fun_prop⟩
  have hP : ∀ σ, μ (P σ) = ∑ j, ι (c j) * ∏ i, (ω ^ (Finset.univ.filter (fun l => σ l = i)).card *
      ι (iteratedDeriv (Finset.univ.filter (fun l => σ l = i)).card
        (fun z => W1 d (y i) (U1 d (t j i) θ) z ^ a i) 0)) := by
    intro σ
    refine (hμ2 (fun i => f i (Finset.univ.filter (fun l => σ l = i)).card) (P σ) fun _ => rfl).unique ?_
    have := hasSum_sum (s := Finset.univ) fun j _ =>
      (hasSum_pi_prod g _ _ fun i => hf2 i (Finset.univ.filter (fun l => σ l = i)).card j).mul_left (ι (c j))
    simp only [Finset.sum_mul, mul_assoc]
    simp only [Finset.prod_mul_distrib] at this ⊢
    exact this
  have hFP : F = ∑ σ : Fin k → Fin g, (∏ l, Ω⁻¹ * ι (ys l (σ l))) • P σ := by
    ext A
    rw [hF]
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply,
      smul_eq_mul, P, ContinuousMap.coe_mk, hf1, Finset.mul_sum]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib (f := fun i => ι (kap1 d 1 (y i)) ^ (PadicInt.toZModPow n (A i)).val),
      ← prod_fiber_pow σ (fun i => zc (A i))]
    simp only [← mul_assoc]
    rw [Finset.prod_mul_distrib (g := fun l => zc (A (σ l)))]
    ring
  have hcd : ∀ j, ContDiff ℂ k (fun z : Fin g → ℂ => ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) :=
    fun j => contDiff_prod fun i _ => (((hdiff j i).contDiff).comp (contDiff_apply ℂ (fun _ => ℂ) i)).pow _
  have hit : iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∑ j, c j * ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) 0
      = ∑ j, c j • iteratedFDeriv ℂ k
        (fun z : Fin g → ℂ => ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) 0 := by
    rw [iteratedFDeriv_sum (fun j _ => contDiff_const.mul (hcd j)), Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact iteratedFDeriv_const_smul_apply' (a := c j) (x := 0) (hcd j).contDiffAt
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hit, hFP, map_sum μ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, hP, smul_eq_mul, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.smul_apply, Finset.mul_sum, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.CoordProdDeriv.iteratedFDeriv_prod_coord g k
    (fun i z => W1 d (y i) (U1 d (t j i) θ) z ^ a i) _ (fun i => (hdiff j i).pow _)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.mul_sum, map_sum, map_mul, map_prod, Pi.smul_apply, smul_eq_mul, map_inv₀]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib (f := fun i => ω ^ (Finset.univ.filter (fun l => σ l = i)).card),
    ← prod_fiber_pow σ (fun _ => ω)]
  have e : ∏ l, (ι δ)⁻¹ * ι (ys l (σ l)) = (∏ l, Ω⁻¹ * ι (ys l (σ l))) * ∏ _l : Fin k, ω := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [hω]; field_simp
  rw [e]
  ring

end GlobalTheory.MomOne.ProdMeasure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.OperatorOnPullbackEqSum
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGenerators

open _root_.GlobalTheory.TorusExt

attribute [local instance] gtGroup

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem exists_lift (hG : GlobalFnsSt) (hB : D.TauBimult) (oa : D.OAct O) (a : O) (N k : ℕ)
    (haa : a * star a = (N : O)) (u v : O) (huv : u * N + v * k = 1) (p : QkPt D F k) :
    ∃ (p' : QkPt D F k) (p₁ : QkPt D F (k * N)), QkPt.Equiv D F p p' ∧ GtAct oa a p₁.g p'.g ∧
      p₁.y = star a • p'.y ∧ ∀ b : O, QkPt.Equiv D F (qkZero hB F k) (qkSmul hB hG oa b p) →
        QkPt.Equiv D F (qkZero hB F (k * N)) (qkSmul hB hG oa b p₁) := by
  letI := gtModule hG oa F
  have hs : ∀ (c : O) (g : GtPtF D F), gtSmul hG oa c g = c • g := fun _ _ => rfl
  have hι : ∀ (c : O) (y : D.X), iota hB F (c • y) = c • iota hB F y := iota_smul hG oa hB
  have hp : (k : O) • p.g = iota hB F p.y := by rw [Nat.cast_smul_eq_nsmul]; exact qk_nsmul hB p
  have e : u * N = 1 + k * -v := by linear_combination huv
  refine ⟨qkSmul hB hG oa (u * N) p, qkMk hB (star a • (u * N) • p.y) ((u * star a) • p.g) ?_, ?_, ?_, rfl, ?_⟩
  · rw [hι, hι, ← hp, ← Nat.cast_smul_eq_nsmul O, smul_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  · refine (equiv_iff hB _ _).2 ⟨(-v) • p.y, ?_, ?_⟩
    · show (u * N) • p.y = p.y + k • (-v) • p.y
      rw [e, add_smul, one_smul, mul_smul, Nat.cast_smul_eq_nsmul]
    · show (u * N) • p.g = p.g + iota hB F ((-v) • p.y)
      rw [hι, ← hp, e, add_smul, one_smul, mul_comm, mul_smul]
  · refine (gtAct_iff_eq_gtSmul hG oa _ _ _).2 ?_
    show (u * N) • p.g = a • (u * star a) • p.g
    rw [smul_smul, ← haa]
    congr 1
    ring
  · intro b hb
    obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 hb
    have hy' : b • p.y = (k : O) • z := by
      rw [Nat.cast_smul_eq_nsmul]; exact hy.trans (zero_add _)
    have hg' : b • p.g = iota hB F z := hg.trans (zero_add _)
    refine (equiv_iff hB _ _).2 ⟨(u * star a) • z, ?_, ?_⟩
    · show b • star a • (u * N) • p.y = 0 + (k * N) • (u * star a) • z
      rw [zero_add, smul_comm b, smul_comm b, hy', ← Nat.cast_smul_eq_nsmul O, smul_smul, smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    · show b • (u * star a) • p.g = 0 + iota hB F ((u * star a) • z)
      rw [zero_add, smul_comm b, hg', hι]

theorem killed_iff (hG : GlobalFnsSt) (hB : D.TauBimult) (oa : D.OAct O) {k : ℕ} {G : Type} [Group G]
    (f : QkPt D F k → G) (act : O → G → G) (h₁ : ∀ p p', f p = f p' ↔ QkPt.Equiv D F p p')
    (h₂ : ∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p')
    (h₃ : ∀ a p p', QkAct oa a p p' → f p' = act a (f p)) (b : O) (p : QkPt D F k) :
    act b (f p) = 1 ↔ QkPt.Equiv D F (qkZero hB F k) (qkSmul hB hG oa b p) := by
  have z : f (qkZero hB F k) = 1 := by
    have e : qkAdd hB (qkZero hB F k) (qkZero hB F k) = qkZero hB F k := qk_ext (add_zero _) (add_zero _)
    have := h₂ _ _ _ (qkAdd_qkAdd hB (qkZero hB F k) (qkZero hB F k))
    rw [e] at this
    exact left_eq_mul.1 this
  rw [← h₁, z, h₃ b p _ (qkAct_qkSmul hB hG oa b p), eq_comm]

end Points

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem exists_operator (hL : Laws) (oa : D.toPre.OAct O) (w0 : O) (hw0 : TraceFormTwistIso D.toPre oa w0) (a : O) (N k : ℕ)
    (hN : 1 ≤ N) (hk : 1 ≤ k) (haa : a * star a = (N : O))
    (π : Fam D.toPre F k →ₗ[F] Fam D.toPre F (k * N)) (hπ : Function.Injective π)
    (hπ' : ∀ s s', PullAl D F oa a k N s s' ↔ s' = π s) (θ : Fam D.toPre F k) (hθ : θ ≠ 0)
    (p p' : QkPt D.toPre F k) (p₀ p₁ p₂ : QkPt D.toPre F (k * N)) (he : QkPt.Equiv D.toPre F p p')
    (hg : GtAct oa a p₁.g p'.g) (hy : p₁.y = star a • p'.y) (hy₂ : p₂.y = p₀.y + p₁.y) (hg₂ : p₀.g.IsAdd p₁.g p₂.g)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
    (w₀ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₀.g.b) (DegPre.lineε (k * N)))) (hw₀ : w₀.IsGen)
    (ζ ζ₀ : F) (hζ : FinOrd D F k p w ζ) (hζ₀ : FinOrd D F (k * N) p₀ w₀ ζ₀) :
    ∃ w₂ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₂.g.b) (DegPre.lineε (k * N))), w₂.IsGen ∧
      FinOrd D F (k * N) p₂ w₂ (ζ₀ * ζ) ∧ ∀ s t t', PhiRel D.toPre F k p w s t →
        PhiRel D.toPre F (k * N) p₀ w₀ (π t) t' → PhiRel D.toPre F (k * N) p₂ w₂ (π s) t' := by
  have hkN : 1 ≤ k * N := Nat.mul_pos hk hN
  obtain ⟨w', hw', h'⟩ := phiRel_of_qkEquiv hL V D F k hk p p' he w hw
  obtain ⟨w₁, hw₁, h₁⟩ := ThetaPull.phiRel_pullAl hL V D F O oa w0 hw0 a N k hN hk haa p' p₁ hg hy w' hw'
  obtain ⟨w₂, hw₂, h₂⟩ := phi_mul hL V D F (k * N) hkN p₀ p₁ p₂ hy₂ hg₂ w₀ w₁ hw₀ hw₁
  have hc : ∀ s t, PhiRel D.toPre F k p w s t → PhiRel D.toPre F (k * N) p₁ w₁ (π s) (π t) := fun s t h =>
    h₁ s t _ _ ((h' s t).1 h) ((hπ' _ _).2 rfl) ((hπ' _ _).2 rfl)
  refine ⟨w₂, hw₂, ?_, fun s t t' h h₀ => h₂ _ _ _ (hc s t h) h₀⟩
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL V _ D F k hk p w hw
  obtain ⟨Φ₁, hΦ₁⟩ := phiFun_of hL V _ D F (k * N) hkN p₁ w₁ hw₁
  obtain ⟨M, hM, hU⟩ := (ThetaFinOrd.finOrd_iff p w ζ Φ hΦ).1 hζ
  have hn : ∀ (n : ℕ) (s : Fam D.toPre F k), ((ζ • Φ₁ : Module.End F (Fam D.toPre F (k * N))) ^ n) (π s) =
      π (((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ n) s) := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← ih, LinearMap.smul_apply,
        LinearMap.smul_apply, map_smul π, (hΦ₁ _ _).1 (hc s _ ((hΦ _ _).2 rfl))]
  obtain ⟨c₁, c₂⟩ := finOrd_criteria hL V D F (k * N) hkN
  refine c₂ p₀ p₁ p₂ hy₂ hg₂ w₀ w₁ w₂ hw₀ hw₁ hw₂ h₂ ζ₀ ζ hζ₀
    (c₁ p₁ w₁ hw₁ ζ Φ₁ hΦ₁ (π θ) M (fun h => hθ (hπ (h.trans (map_zero π).symm))) hM ?_)
  exact (hn M θ).trans (by rw [hU]; rfl)

end GlobalTheory.ThetaGenerators

namespace GlobalTheory


open ThetaGenerators _root_.GlobalTheory.TorusExt in
theorem operator_on_pullback_eq_sum : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso → letI := H.starRing; ∀ (a a' : 𝓞 E) (N N' : ℕ), 1 ≤ N → 1 ≤ N' → Nat.Coprime N N' → a * star a = (N : 𝓞 E) → a' * star a' = (N' : 𝓞 E) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (θ' s : Fam P.D.toPre F (1 * N')) (θ₂ s₂ t₀ h : Fam P.D.toPre F (1 * N' * N)), θ' ≠ 0 → PullAl P.D F P.oD a (1 * N') N θ' θ₂ → PullAl P.D F P.oD a (1 * N') N s s₂ → ∀ (m : ℕ) (c : Fin m → F) (p : Fin m → QkPt P.D.toPre F (1 * N')) (x : Fin m → (TFK (R := V) F ⟶ P.A.A)) (w : ∀ i, LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p i).g.b) (DegPre.lineε (1 * N')))) (ζ : Fin m → F) (tt : Fin m → Fam P.D.toPre F (1 * N')), ((∀ i, P.ToA F (1 * N') (p i) (x i)) ∧ (∀ i, x i ≫ P.oA.act (star (a')) = 1) ∧ (∀ i, (w i).IsGen ∧ ζ i ≠ 0 ∧ FinOrd P.D F (1 * N') (p i) (w i) (ζ i)) ∧ (∀ i, ∃ t' : Fam P.D.toPre F (1 * N'), PhiRel P.D.toPre F (1 * N') (p i) (w i) θ' t' ∧ Fam.IsSmul P.D.toPre F (ζ i) t' (tt i)) ∧ s = ∑ i, c i • tt i) → ∀ (p₀ : QkPt P.D.toPre F (1 * N' * N)) (x₀ : TFK (R := V) F ⟶ P.A.A) (w₀ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p₀.g.b) (DegPre.lineε (1 * N' * N)))) (ζ₀ : F), P.ToA F (1 * N' * N) p₀ x₀ → x₀ ≫ P.oA.act (star a) = 1 → w₀.IsGen → ζ₀ ≠ 0 → FinOrd P.D F (1 * N' * N) p₀ w₀ ζ₀ → PhiRel P.D.toPre F (1 * N' * N) p₀ w₀ s₂ t₀ → Fam.IsSmul P.D.toPre F ζ₀ t₀ h → ∃ (p₂ : Fin m → QkPt P.D.toPre F (1 * N' * N)) (x₂ : Fin m → (TFK (R := V) F ⟶ P.A.A)) (w₂ : ∀ i, LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p₂ i).g.b) (DegPre.lineε (1 * N' * N)))) (ζ₂ : Fin m → F) (t₂ : Fin m → Fam P.D.toPre F (1 * N' * N)), (∀ i, P.ToA F (1 * N' * N) (p₂ i) (x₂ i)) ∧ (∀ i, x₂ i ≫ P.oA.act (star (a' * a)) = 1) ∧ (∀ i, (w₂ i).IsGen ∧ ζ₂ i ≠ 0 ∧ FinOrd P.D F (1 * N' * N) (p₂ i) (w₂ i) (ζ₂ i)) ∧ (∀ i, ∃ t' : Fam P.D.toPre F (1 * N' * N), PhiRel P.D.toPre F (1 * N' * N) (p₂ i) (w₂ i) θ₂ t' ∧ Fam.IsSmul P.D.toPre F (ζ₂ i) t' (t₂ i)) ∧ h = ∑ i, c i • t₂ i := by
  intro hL E _ _ _ H V _ _ _ t P hT
  letI := H.starRing
  intro a a' N N' hN hN' hco haa _ F _ _ _ θ' s θ₂ s₂ t₀ h hθ hθ₂ hs₂ m c p x w ζ tt ⟨hx, hxa, hw, htt, hs⟩
    p₀ x₀ w₀ ζ₀ hx₀ hxa₀ hw₀ hζ₀ hf₀ ht₀ hh
  have hG := hL.globalFns
  have hB := P.D.tau_bimult
  have hk : 1 ≤ 1 * N' := by omega
  have hkN : 1 ≤ 1 * N' * N := Nat.mul_pos hk hN
  obtain ⟨u, v, huv⟩ : IsCoprime (N : 𝓞 E) ((1 * N' : ℕ) : 𝓞 E) := by
    rw [_root_.one_mul]; exact hco.cast
  obtain ⟨π, hπ, hπ'⟩ := PullLin.exists_pull_linearMap hL V P.D F (𝓞 E) P.oD H.w0 P.w0 a N (1 * N') hN hk haa
  obtain rfl := (hπ' _ _).1 hθ₂
  obtain rfl := (hπ' _ _).1 hs₂
  obtain ⟨f, f₀, -, f₁, f₂, f₃, -⟩ := hT F (1 * N') hk
  obtain ⟨g, g₀, -, g₁, g₂, g₃, -⟩ := hT F (1 * N' * N) hkN
  obtain ⟨Φ₀, hΦ₀⟩ := phiFun_of hL V _ P.D F (1 * N' * N) hkN p₀ w₀ hw₀
  choose p' p₁ he hg hy hb using fun i => exists_lift hG hB P.oD a N (1 * N') haa u v huv (p i)
  choose w₂ hw₂ hf₂ hΦ₂ using fun i => exists_operator hL P.oD H.w0 P.w0 a N (1 * N') hN hk haa π hπ hπ' θ' hθ
    (p i) (p' i) p₀ (p₁ i) (qkAdd hB p₀ (p₁ i)) (he i) (hg i) (hy i) rfl ((isAdd_iff_eq _ _ _).2 rfl)
    (w i) (hw i).1 w₀ hw₀ (ζ i) ζ₀ (hw i).2.2 hf₀
  choose t' ht' htt' using htt
  refine ⟨fun i => qkAdd hB p₀ (p₁ i), fun i => g (qkAdd hB p₀ (p₁ i)), w₂, fun i => ζ₀ * ζ i,
    fun i => (ζ₀ * ζ i) • Φ₀ (π (t' i)), fun i => (g₀ _ _).2 rfl, fun i => ?_,
    fun i => ⟨hw₂ i, mul_ne_zero hζ₀ (hw i).2.1, hf₂ i⟩,
    fun i => ⟨_, hΦ₂ i _ _ _ (ht' i) ((hΦ₀ _ _).2 rfl), (DVR.isSmul_iff _ _ _).2 rfl⟩, ?_⟩
  · have k₁ : g (p₁ i) ≫ P.oA.act (star a') = 1 :=
      (killed_iff hG hB P.oD g (fun b y => y ≫ P.oA.act b) g₁ g₂ g₃ (star a') (p₁ i)).2 (hb i _
        ((killed_iff hG hB P.oD f (fun b y => y ≫ P.oA.act b) f₁ f₂ f₃ (star a') (p i)).1
          ((f₀ _ _).1 (hx i) ▸ hxa i)))
    have := P.oA.hom (star (a' * a))
    have := P.oA.hom (star a')
    have := P.oA.hom (star a)
    have e₀ : x₀ ≫ P.oA.act (star (a' * a)) = 1 := by
      rw [star_mul', P.oA.map_mul, ← Category.assoc, hxa₀, MonObj.one_comp]
    have e₁ : g (p₁ i) ≫ P.oA.act (star (a' * a)) = 1 := by
      rw [star_mul, P.oA.map_mul, ← Category.assoc, k₁, MonObj.one_comp]
    show g (qkAdd hB p₀ (p₁ i)) ≫ P.oA.act (star (a' * a)) = 1
    rw [g₂ _ _ _ (qkAdd_qkAdd hB p₀ (p₁ i)), ← (g₀ _ _).1 hx₀, MonObj.mul_comp, e₀, e₁, _root_.mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [(DVR.isSmul_iff _ _ _).1 hh, (hΦ₀ _ _).1 ht₀, hs, map_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [(DVR.isSmul_iff _ _ _).1 (htt' i), map_smul, map_smul, map_smul, map_smul, smul_comm, smul_smul ζ₀]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordOperatorColumnMemNormalFormProductSpan
section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]


omit [StarModule ℂ A] in
theorem word_one_mem_nfSpan (d : Q.NFData P A) (T : Set A) : (1 : A) ∈ nfSpan d T 0 0 0 :=
  Submodule.subset_span ⟨1, one_mem _, [], rfl, by simp, by simp⟩


omit [StarModule ℂ A] in
theorem word_letter_mem_nfSpan (d : Q.NFData P A) (T : Set A) {X : A} (hX : X ∈ T) : X ∈ nfSpan d T 0 0 1 :=
  Submodule.subset_span ⟨1, one_mem _, [X], rfl, by simpa using hX, by simp⟩

theorem word_mul_mem_nfSpan (d : Q.NFData P A) (hd : HatHyp d) {n : ℕ} {x y : A}
    (hx : x ∈ nfSpan d (hats d.L) 1 0 1) (hy : y ∈ nfSpan d (hats d.L) n 0 n) :
    x * y ∈ nfSpan d (hats d.L) (n + 1) 0 (n + 1) := by
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.HatNF.SpanMul.span_mul P A d hd (hats d.L)
  unfold nfSpan at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, H, hH, hT, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := List.length_eq_one_iff.mp hH
    have ht : t ∈ hats d.L := hT t (by simp)
    have a1 := h2 0 (fun X hX => word_letter_mem_nfSpan d _ hX) n 0 n t ht y hy
    have a2 := (h1 _ _ _ _ a1).2.1
    have a3 := (h1 _ _ _ _ a2).1 b hb
    simpa [mul_assoc] using a3
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ ih ih' => rw [add_mul]; exact add_mem ih ih'
  | smul c x _ ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ih

end

theorem word_mem_nfSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (Letter ℂ S), admitted st w → ∀ e : Ix S, ((ofWord L st w).F * TL.bTA L w) e e1 ∈ nfSpan d (hats d.L) w.length 0 w.length := by
  intro P A _ _ _ _ d hd L st s ht S _ _ w
  induction w with
  | nil =>
    intro _ e
    have : ((ofWord L st ([] : List (Letter ℂ S))).F * TL.bTA L []) = 1 := by
      simp [ofWord, Start.frame, TL.bTA, bT]
    rw [this, Matrix.one_apply]
    split_ifs
    · exact word_one_mem_nfSpan d _
    · exact zero_mem _
  | cons l w ih =>
    intro hA e
    have hAw : admitted st w := ⟨(List.nodup_cons.mp (by simpa only [List.map_cons] using hA.1)).2,
      fun l' h => hA.2.1 l' (by simp [h]), fun l' h => hA.2.2.1 l' (by simp [h]), (List.pairwise_cons.mp hA.2.2.2).2⟩
    rw [Formalism.FourierDecayAlt.P.word_recursion A S P.r L st l w ht.1 hA e, Matrix.mul_apply]
    refine Submodule.sum_mem _ fun e' _ => ?_
    have h1 : ((∑ i : Fin 2, eU l.intersection_update_fsHerm_neg_one i 0 * TL.letterCol L st l w i : SlopeTestRemainingChoices S A) e e') ∈
        nfSpan d (hats d.L) 1 0 1 := by
      rw [Matrix.sum_apply]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Matrix.mul_apply]
      refine Submodule.sum_mem _ fun e'' _ => ?_
      simp only [eU, Matrix.of_apply]
      split_ifs
      · rw [one_mul]; exact _root_.GlobalTheory.HatNF.LetterEntries.letterCol_mem P A d hd L st s ht S l w hA i e'' e'
      · rw [zero_mul]; exact zero_mem _
    exact word_mul_mem_nfSpan d hd h1 (ih hAw e')

end GlobalTheory.HatNF
end

