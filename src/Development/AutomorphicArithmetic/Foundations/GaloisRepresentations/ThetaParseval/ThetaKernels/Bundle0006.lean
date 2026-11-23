module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesConvergent
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.HermitianFormRealCoordinateMatrixHermitianDetNeZ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsLocUnit

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GodementSumK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
  {J : Type} [Fintype J]
end GlobalTheory.CompanionTheory.GodementH
end
noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {J : Type} [Fintype J]
end GlobalTheory.CompanionTheory.GodementH
end
noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {n : ℕ}
end GlobalTheory.CompanionTheory.GodementH
end
noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
end GlobalTheory.CompanionTheory.GodementH
end
noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
end GlobalTheory.CompanionTheory.GodementH
end
noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
theorem godement_sum_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∃ σ₀ : ℝ, ∀ σ' : ℝ, σ₀ < σ' → ∃ (C : ℝ) (N : ℕ), ∀ x : G2 σ Y, Summable (fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ σ') ∧ ∑' q : Cos σ Y, a ((Quotient.out q).1 * x) ^ σ' ≤ C * (ht2 x : ℝ) ^ N := by
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY b K a hb hK ha
  have hcm : IsCMExt F E σ := hB.cm
  obtain ⟨C, hC⟩ := key_bound hcm hb.2 hK ha
  have hrat : ∀ q : Cos σ Y, ∃ g : GL (Ix n) E,
      Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) g = (Quotient.out q).1.1 := fun q => by
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.1 (Quotient.out q).2
    exact ⟨g, hg⟩
  choose g hg using hrat
  have hnz : ∀ q, ∃ f, mnr (pl b (g q)) f ≠ 0 := fun q => by
    have hP : ∃ P : Matrix (Fin n) (Ix n) E, P * (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) = 1 :=
      ⟨Matrix.fromCols 1 0, by rw [diagCols, Matrix.fromCols_mul_fromRows]; simp⟩
    obtain ⟨P, hP⟩ := hP
    have hg1 : ((g q).1 : Matrix (Ix n) (Ix n) E) * ((g q)⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hb1 : (b.1 : Matrix (Ix n) (Ix n) E) * (b⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine _root_.GlobalTheory.CompanionTheory.GodementH.exists_mnr_ne_zero_of_left_inverse E (Ix n) n (pl b (g q)) ((P * ((g q).1 : Matrix (Ix n) (Ix n) E)) * (b.1 : Matrix (Ix n) (Ix n) E)) ?_
    calc (P * ((g q).1 : Matrix (Ix n) (Ix n) E)) * (b.1 : Matrix (Ix n) (Ix n) E) * pl b (g q)
        = P * ((g q).1 : Matrix (Ix n) (Ix n) E) * ((b.1 : Matrix (Ix n) (Ix n) E) * (b⁻¹).1) * ((g q)⁻¹).1 *
          (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) := by simp only [pl, Matrix.mul_assoc]
      _ = P * (((g q).1 : Matrix (Ix n) (Ix n) E) * ((g q)⁻¹).1) *
          (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) := by rw [hb1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hg1, Matrix.mul_one, hP]
  choose f₀ hf₀ using hnz
  let u : Cos σ Y → (Fin n → Ix n) → E := fun q f => mnr (pl b (g q)) f / mnr (pl b (g q)) (f₀ q)
  have hu1 : ∀ q, u q (f₀ q) = 1 := fun q => div_self (hf₀ q)
  have hinj : Function.Injective u := by
    intro q q' e
    obtain ⟨c, hc⟩ := _root_.GlobalTheory.CompanionTheory.GodementH.Cramer.main E (Ix n) n _ _ _ _ (hf₀ q) (hf₀ q') (fun f => congrFun e f)
    have hp := isPar_of_pl (hg q) (hg q') hc
    have : (Quotient.mk _ (Quotient.out q') : Cos σ Y) = Quotient.mk _ (Quotient.out q) :=
      cos_eq.2 (Subgroup.subset_closure ⟨_, hp⟩)
    rw [Quotient.out_eq, Quotient.out_eq] at this
    exact this.symm
  obtain ⟨C₁, c, hC₁, hcount⟩ := count hcm (Fin n → Ix n) (σ := σ)
  let h : Cos σ Y → ℝ := fun q => vecHt σ (u q)
  have h1 : ∀ q, 1 ≤ h q := fun q => by
    have := one_le_vecHt (σ := σ) (hu1 q)
    exact_mod_cast this
  have hcnt : ∀ T : ℝ, 1 ≤ T → {q | h q ≤ T}.Finite ∧ (Set.ncard {q | h q ≤ T} : ℝ) ≤ C₁ * T ^ c := by
    intro T hT
    obtain ⟨hfin, hle⟩ := hcount T hT
    have hmaps : Set.MapsTo u {q | h q ≤ T} {u : (Fin n → Ix n) → E | (∃ f₀, u f₀ = 1) ∧ (vecHt σ u : ℝ) ≤ T} :=
      fun q hq => ⟨⟨f₀ q, hu1 q⟩, hq⟩
    refine ⟨Set.Finite.of_injOn hmaps hinj.injOn hfin, le_trans ?_ hle⟩
    exact_mod_cast Set.ncard_le_ncard_of_injOn u hmaps hinj.injOn hfin
  have a_nonneg : ∀ y, 0 ≤ a y := fun y => by
    obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa y
    rw [ha.val p t hp k hk]; exact NNReal.coe_nonneg _
  refine ⟨c, fun s' hs' => ?_⟩
  have hs0 : 0 < s' := lt_of_le_of_lt (Nat.cast_nonneg c) hs'
  have hsum : Summable fun q => h q ^ (-s') := _root_.GlobalTheory.CompanionTheory.GodementH.summable_rpow_neg_of_polynomial_count _ h h1 C₁ c hcnt s' hs'
  have hterm : ∀ (x : G2 σ Y) (q : Cos σ Y), a ((Quotient.out q).1 * x) ^ s' ≤
      ((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) ^ s' * h q ^ (-s') := by
    intro x q
    have hb1 := hC (Quotient.out q).1 (g q) (hg q) (f₀ q) (hf₀ q) x
    have hpos : 0 < h q := lt_of_lt_of_le one_pos (h1 q)
    have hb2 : a ((Quotient.out q).1 * x) ≤ ((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) * (h q)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact hb1
    calc _ ≤ (((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) * (h q)⁻¹) ^ s' := Real.rpow_le_rpow (a_nonneg _) hb2 hs0.le
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hpos.le, Real.rpow_neg hpos.le]
  refine ⟨(C : ℝ) ^ s' * ∑' q, h q ^ (-s'), ⌈2 * n * s'⌉₊, fun x => ?_⟩
  have hS : Summable fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ s' :=
    Summable.of_nonneg_of_le (fun q => Real.rpow_nonneg (a_nonneg _) _) (hterm x) (hsum.mul_left _)
  refine ⟨hS, ?_⟩
  have hx1 : (1 : ℝ) ≤ ht2 x := by exact_mod_cast one_le_heightGL F x.1
  have hx0 : (0 : ℝ) ≤ ht2 x := by positivity
  have hpow : ((ht2 x : ℝ) ^ (2 * n)) ^ s' ≤ (ht2 x : ℝ) ^ ⌈2 * n * s'⌉₊ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
    push_cast
    exact Nat.le_ceil _
  have hT : 0 ≤ ∑' q, h q ^ (-s') := tsum_nonneg fun q => Real.rpow_nonneg (lt_of_lt_of_le one_pos (h1 q)).le _
  calc ∑' q : Cos σ Y, a ((Quotient.out q).1 * x) ^ s' ≤ ∑' q, ((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) ^ s' * h q ^ (-s') :=
        hS.tsum_le_tsum (hterm x) (hsum.mul_left _)
    _ = (C : ℝ) ^ s' * ((ht2 x : ℝ) ^ (2 * n)) ^ s' * ∑' q, h q ^ (-s') := by
        rw [tsum_mul_left, Real.mul_rpow (by positivity) (by positivity)]
    _ ≤ (C : ℝ) ^ s' * (ht2 x : ℝ) ^ ⌈2 * n * s'⌉₊ * ∑' q, h q ^ (-s') := by gcongr
    _ = _ := by ring
end GlobalTheory.CompanionTheory.GodementH
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HeisCK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.AdelicSchwartzProperties
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem heis_C_k {σ : E →ₐ[F] E} {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (N : ℕ)
    (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F)) (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N)
    (hCe : ∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u))
    (he : ∀ w w', symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ w w' = symV (e w) (e w'))
    (Φ : (Fin N → AF F) → ℂ) (y : WOF F E nS nT) :
    heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dC (AF F ⊗[F] E) nT * y) (thV B.ψ Φ ∘ e) =
      thV B.ψ (fun x => B.ψ (x ⬝ᵥ β y) * Φ x) ∘ e := by
  have hCy : e (dC (AF F ⊗[F] E) nT * y) = (0, β y) := by
    have h := hCe y 0
    rw [Matrix.mul_zero, add_zero, map_zero] at h
    exact h
  have h2 : (⅟(2 : AF F)) = algebraMap F (AF F) (1 / 2) := by
    refine invOf_eq_right_inv ?_
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
    norm_num
  funext w
  simp only [Function.comp_apply, heisOF, thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr]
  rw [map_add (f := _), hCy]
  have hph : symplOHF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ w (dC (AF F ⊗[F] E) nT * y) =
      ⅟(2 : AF F) * ((e w).1 ⬝ᵥ β y) := by
    rw [symplOHF, he, hCy, h2]
    simp [symV]
  rw [hph, ← tsum_mul_left]
  refine tsum_congr fun ξ => ?_
  set x₁ := (e w).1
  set y₁ := (e w).2
  set b := β y
  set r : Fin N → AF F := fun i => algebraMap F (AF F) (ξ i)
  have hw : e w = (x₁, y₁) := rfl
  simp only [hw, Prod.mk_add_mk, add_zero]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  have h22 : (⅟(2 : AF F)) + ⅟2 = 1 := invOf_two_add_invOf_two
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (x₁ ⬝ᵥ b) * h22
end PositivityTheory.ThKW.AdelicSchwartzProperties
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HeisOFDerivFixK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
noncomputable section
namespace GlobalTheory.HeisDerivCM
open Formalism.IndefR.DatumF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem heisOF_deriv_fix_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ u : Formalism.IndefR.DatumF.WOF F E nS nT, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 → Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) f = f →
      Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) (fun w => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0) = fun w => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ _ f L _ hL u hu hf
  funext w
  have key : ∀ t : ℝ, B.ψ (symplOHF σ JS JT ξ₀ w u) * heisOF σ JS JT ξ₀ B.ψ (L t) f (w + u) =
      heisOF σ JS JT ξ₀ B.ψ (L t) f w := by
    intro t
    obtain ⟨h1, h2⟩ := symplOHF_fin_real σ JS JT ξ₀ u (L t) hu (hL t)
    have hfx := congrFun hf (w + L t)
    simp only [heisOF] at hfx ⊢
    conv_rhs => rw [← hfx]
    rw [symplOHF_add_left, symplOHF_add_left, h1, h2, add_zero, add_zero,
      show w + u + L t = w + L t + u by abel]
    ring
  show B.ψ (symplOHF σ JS JT ξ₀ w u) * deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + u)) 0 = _
  rw [← deriv_const_mul_field]
  exact congrArg (fun g : ℝ → ℂ => deriv g 0) (funext key)
end GlobalTheory.HeisDerivCM
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HeisOFLineAddK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
noncomputable section
namespace GlobalTheory.HeisLineF
open Formalism.IndefR.DatumF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
end GlobalTheory.HeisLineF
open GlobalTheory.HeisLineF in
theorem GlobalTheory.heisOF_line_add_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ) (w : Formalism.IndefR.DatumF.WOF F E nS nT) (s t : ℝ),
      Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L (s + t)) f w = B.ψ (Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ w (L s)) * Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L s) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ _ L hL _ f w s t
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
    apply τ.injective
    rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
  have key : Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ (L s) (L t) = 0 := by
    by_cases ht : t = 0
    · rw [ht, map_zero L, symplOF_zero_right]
    · let g : ℝ →+ AF F := AddMonoidHom.mk' (fun u => Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ (L u) (L t))
        (fun a b => by simp only [map_add L, symplOF_add_left])
      have hg : Continuous g := (continuous_symplOF_left σ JS JT ξ₀ (L t)).comp hL
      have h0 : g t = 0 := symplOF_self σ JS JT hσ hS hT ξ₀ hξ (L t)
      have := line_zero g hg t h0 (s / t)
      rwa [div_mul_cancel₀ s ht] at this
  have k2 : Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (L s) (L t) = 0 := by
    unfold Formalism.IndefR.DatumF.symplOHF; rw [key, mul_zero]
  unfold Formalism.IndefR.DatumF.heisOF
  rw [map_add L, symplOHF_add_right, symplOHF_add_left, k2, add_zero, AddChar.map_add_eq_mul, add_assoc, mul_assoc]
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HermitianFormSelfadjointGlobal
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
open PositivityTheory.ThKW.RealC
theorem PositivityTheory.ThKW.hermitian_form_selfadjoint_global : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1))ᴴ = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) ∧ (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)).det ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ
  have hτ := hB.cm.2.2.2
  constructor
  · unfold HMF
    rw [blk_conjTranspose]
    congr 1 <;> funext w
    · rw [conjTranspose_smul, herm_map (hτ _) hT]
      simp
    · rw [conjTranspose_nonsing_inv, herm_map (hτ _) hS]
  · have h0 : ∀ w : InfinitePlace F, ((2 * ((B.emb w).1 ξ₀).im : ℝ) : ℂ) ≠ 0 := fun w =>
      Complex.ofReal_ne_zero.2 (mul_ne_zero two_ne_zero (im_xi (hτ _) hξ hσ))
    have : HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *
        blk (fun w => ((2 * ((B.emb w).1 ξ₀).im : ℝ) : ℂ)⁻¹ • (JT.map (B.emb w).1)⁻¹)
          (fun w => JS.map (B.emb w).1) = 1 := by
      unfold HMF
      rw [blk_mul, ← blk_one]
      congr 1 <;> funext w
      · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (h0 w), one_smul,
          mul_nonsing_inv _ (unit_map _ hT)]
      · rw [mul_nonsing_inv _ (unit_map _ hS)]
    exact (isUnit_det_of_right_inverse this).ne_zero
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsCompactKK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.CompanionTheory.StdK
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter _root_.Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem isCompact_K_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → IsCompact (K : Set (G2 σ Y)) := by
  intro F E _ _ _ _ _ σ B n Y r s hB _ _ b K a _ hK _
  exact isCompact_of_isStdK B hB.cm b K hK
end GlobalTheory.CompanionTheory.StdK
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsFieldTensorOfIsInertAtK
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
namespace GlobalTheory.InertTensorField
theorem isField_tensor_of_isInertAt_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) := by
  intro F E _ _ _ _ _ σ B hB v w hvw
  have hp : (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime := by
    rw [show v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal from hvw]
    exact w.isPrime
  exact GlobalTheory.InertField.isField_of_inert F E hB.cm.2.2.1 v hp
end GlobalTheory.InertTensorField
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsHermUnitSpcK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ldexb.UnitHermitianSpace
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isHerm_unitSpc_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (n : ℕ) : (unitSpc F E n).IsHerm σ B n 0 := by
  refine ⟨fun i j => ?_, fun w => ?_, isLattice_stdLattice, fun y => ?_, fun w => ?_, fun v => ?_⟩
  · simp only [unitSpc, Matrix.one_apply]
    split_ifs with h1 h2 h2
    · exact map_one σ
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · exact map_zero σ
  · simp only [unitSpc, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hasSig_one
  · simp only [unitSpc]
    rw [mem_std]
    constructor
    · intro hy x hx
      rw [mem_std] at hx
      rw [form_one]
      exact IsIntegral.sum _ fun i _ => (hy i).mul (map_isIntegral_int σ (hx i))
    · intro h i
      have hx : (Pi.single i (1 : E) : Fin n → E) ∈ stdLattice E n := by
        rw [mem_std]
        intro j
        by_cases e : j = i
        · subst e; simpa using isIntegral_one
        · simpa [Pi.single_apply, e] using isIntegral_zero
      have := h _ hx
      rw [form_one] at this
      simpa [Pi.single_apply] using this
  · simp only [unitSpc, Matrix.map_one _ (map_zero _) (map_one _)]
    exact isCartan_one
  · exact isSplitBasis_stdLattice (B.τ v) hB.cm
end PositivityTheory.SiegelWeilFormula.Ldexb.UnitHermitianSpace
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsStdCharFOfIsGoodK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.StdCharWeilDatum
section Char
variable {F : Type} [Field F] [NumberField F]
end Char
section Trace
variable {F : Type} [Field F] [NumberField F]
end Trace
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem isStdCharF_of_isGood_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) := by
  intro F E _ _ _ _ _ σ B hB
  haveI : IsTotallyReal F := hB.cm.1
  refine ⟨isCharAF hB.std, ⟨?_, fun θ hθ x => ?_⟩⟩
  · choose θ hθ using fun w : InfinitePlace F =>
      GlobalTheory.DualPairCompare.gen_inf_exists (B.emb w).1 w (B.emb w).2.symm
    exact ⟨θ, hθ⟩
  · show B.ψ (pairA F x 0) = _
    rw [psi_pairA hB.std, sum_infFam B θ hθ x]
    congr 1
    push_cast
    ring
end GlobalTheory.StdCharWeilDatum
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LocUnit
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem UpperTheory.TP.K.exists_locUnit {B : Base F E} (hB : UpperTheory.TP.W.GoodK σ B) {ξ : E} (hξ : ξ ≠ 0) (hσξ : σ ξ = -ξ) (v : Pl (F := F)) :
    ∃ u : (Fv F v ⊗[F] E)ˣ, (u : Fv F v ⊗[F] E) ∈ intLoc F E v ∧ ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v ∧
      sigR (Fv F v) σ (u : Fv F v ⊗[F] E) = -(u : Fv F v ⊗[F] E) :=
  _root_.UpperTheory.Reformulated.B.Gs6.exists_locUnit hB hξ hσξ v

end
end

