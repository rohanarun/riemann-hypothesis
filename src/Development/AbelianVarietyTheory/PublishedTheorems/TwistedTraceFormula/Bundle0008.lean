module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0311
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
section
open MeasureTheory Set Filter Matrix Polynomial GlobalTheory.Orb GlobalTheory.OpTrace
open GlobalTheory.AutomorphicL2Unitary (descend LeftInv mk measurable_mk)
open Formalism.REAL (UJ KG muK Jm)
open Formalism.QuantumDeterminants (IsHCParam IsCRepOn)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsDS UJset)
open GlobalTheory.FlagMeas (IsIsoFlag flagM)
open GlobalTheory.RealInd (IsIrrAdm IsIndModel IndModule Flag groupRep indFun leviOne mats)
open scoped ENNReal NNReal Topology

noncomputable section

namespace GlobalTheory.HCChar

section Disc

variable {n : ℕ}

def weylDisc (x : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  resultant x.charpoly (derivative x.charpoly) n (n - 1) / x.det ^ (n - 1)

end Disc

section Cartan

variable {n : ℕ} {ε : Fin n → Bool}

theorem continuous_ujMat : Continuous (ujMat ε) := Units.continuous_val.comp continuous_subtype_val

def IsCartanSub (T : Subgroup (UJ ε)) : Prop := ∃ s, IsRegSS (ujMat ε s) ∧ T = cent s

def IsCartanSystem (𝒯 : Finset (Subgroup (UJ ε))) : Prop :=
  (∀ T ∈ 𝒯, IsCartanSub T) ∧
    ∀ T : Subgroup (UJ ε), IsCartanSub T → ∃! T', T' ∈ 𝒯 ∧ ∃ x, T.map (MulAut.conj x).toMonoidHom = T'

def weylOrder {H : Type} [Group H] (T : Subgroup H) : ℕ := T.relIndex (Subgroup.normalizer (T : Set H))

end Cartan

section Char

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

def IsAnalyticAt (Θ : UJ ε → ℂ) (s : UJ ε) : Prop :=
  ∃ Φ : (Fin n → Fin n → ℂ) → ℂ, AnalyticAt ℝ Φ (matCoord (ujMat ε) s) ∧ ∀ᶠ g in 𝓝 s, Θ g = Φ (matCoord (ujMat ε) g)

def IsGlobalChar (μ : Measure (UJ ε)) (π : UJ ε →* (V →L[ℂ] V)) (Θ : UJ ε → ℂ) : Prop :=
  IsCharFn (ujMat ε) μ π Θ ∧ ∀ s, IsRegSS (ujMat ε s) → IsAnalyticAt Θ s ∧ ∀ x, Θ (x⁻¹ * s * x) = Θ s

end Char

section Torus

variable {n : ℕ}

def torusPt (ε : Fin n → Bool) (θ : Fin n → ℝ) : UJ ε :=
  ⟨⟨diagonal fun a => Complex.exp (θ a * Complex.I), diagonal fun a => Complex.exp (-(θ a * Complex.I)),
    by simp [← Complex.exp_add], by simp [← Complex.exp_add]⟩, by
      change _ᴴ * Jm ε * _ = Jm ε
      simp only [Jm, diagonal_conjTranspose, diagonal_mul_diagonal]
      congr 1
      funext a
      rw [mul_right_comm, Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      simp⟩

theorem ujMat_torusPt (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    ujMat ε (torusPt ε θ) = diagonal fun a => Complex.exp (θ a * Complex.I) := rfl

def wtVal (μ θ : Fin n → ℝ) : ℂ := Complex.exp ((∑ a, μ a * θ a : ℝ) * Complex.I)

def weylDenom (θ : Fin n → ℝ) : ℂ :=
  ∏ a, ∏ b ∈ Finset.Ioi a, (Complex.exp (((θ a - θ b) / 2 : ℝ) * Complex.I) -
    Complex.exp ((-((θ a - θ b) / 2) : ℝ) * Complex.I))

def compactWeyl (ε : Fin n → Bool) : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter fun w => ε ∘ w = ε

def halfDim (ε : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun a => ε a = true).card * (Finset.univ.filter fun a => ε a = false).card

def dsChar (ε : Fin n → Bool) (lam θ : Fin n → ℝ) : ℂ :=
  (-1) ^ halfDim ε * (∑ w ∈ compactWeyl ε, ((Equiv.Perm.sign w : ℤ) : ℂ) * wtVal (lam ∘ w.symm) θ) / weylDenom θ

theorem weylDenom_mul (θ : Fin n → ℝ) : weylDenom θ * wtVal (fun _ => ((n : ℝ) - 1) / 2) θ =
    ∏ a, ∏ b ∈ Finset.Ioi a, (Complex.exp (θ a * Complex.I) - Complex.exp (θ b * Complex.I)) := by
  have h : ∑ a, ((n : ℝ) - 1) / 2 * θ a = ∑ a, ∑ b ∈ Finset.Ioi a, (θ a + θ b) / 2 := by
    have h1 : ∑ a, ∑ b ∈ Finset.Ioi a, θ b = ∑ b, ∑ _a ∈ Finset.Iio b, θ b :=
      Finset.sum_comm' (by simp)
    simp only [← Finset.sum_div, Finset.sum_add_distrib, h1, Finset.sum_const, Fin.card_Ioi, Fin.card_Iio,
      nsmul_eq_mul]
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := a.isLt
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [weylDenom, wtVal, h]
  simp only [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  rw [sub_mul, ← Complex.exp_add, ← Complex.exp_add]
  congr 2 <;> push_cast <;> ring

theorem dsChar_eq (ε : Fin n → Bool) {lam : Fin n → ℝ} {m : Fin n → ℤ} (hm : ∀ a, lam a + ((n : ℝ) - 1) / 2 = m a)
    (θ : Fin n → ℝ) : dsChar ε lam θ = (-1) ^ halfDim ε *
      (∑ w ∈ compactWeyl ε, ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ a, Complex.exp (θ a * Complex.I) ^ m (w.symm a)) /
        ∏ a, ∏ b ∈ Finset.Ioi a, (Complex.exp (θ a * Complex.I) - Complex.exp (θ b * Complex.I)) := by
  rw [dsChar, ← weylDenom_mul, ← mul_div_mul_right _ _ (c := wtVal (fun _ => ((n : ℝ) - 1) / 2) θ) (Complex.exp_ne_zero _),
    mul_assoc, Finset.sum_mul]
  congr 2
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [mul_assoc, wtVal, wtVal, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, ← Finset.sum_add_distrib]
  simp only [← add_mul, Function.comp, hm, ← Complex.exp_int_mul, ← Complex.exp_sum, Complex.ofReal_sum,
    Finset.sum_mul]
  simp [mul_assoc]

theorem exists_isRegSS_torusPt (ε : Fin n → Bool) : ∃ θ, IsRegSS (ujMat ε (torusPt ε θ)) := by
  refine ⟨fun a => 1 / ((a : ℕ) + 1), ?_⟩
  rw [IsRegSS, ujMat_torusPt, charpoly_diagonal, separable_prod_X_sub_C_iff]
  have hb : ∀ a : Fin n, -Real.pi < (((1 / ((a : ℕ) + 1) : ℝ) : ℂ) * Complex.I).im ∧
      (((1 / ((a : ℕ) + 1) : ℝ) : ℂ) * Complex.I).im ≤ Real.pi := fun a => by
    have h1 : (0 : ℝ) < 1 / ((a : ℕ) + 1) := by positivity
    have h2 : (1 : ℝ) / ((a : ℕ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; simp
    rw [Complex.mul_I_im, Complex.ofReal_re]
    constructor <;> linarith [Real.pi_gt_three]
  intro a b h
  have := Complex.exp_inj_of_neg_pi_lt_of_le_pi (hb a).1 (hb a).2 (hb b).1 (hb b).2 h
  rw [mul_left_inj' Complex.I_ne_zero, Complex.ofReal_inj, one_div, one_div, _root_.inv_inj, add_left_inj,
    Nat.cast_inj] at this
  exact Fin.ext this

end Torus

end GlobalTheory.HCChar

namespace GlobalTheory.Published

open GlobalTheory.HCChar

def CharacterRegularity : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h : IsIrrAdm ε π),
    ∃ Θ, IsGlobalChar μ (groupRep ε h.2.1.1) Θ

def DiscreteSeriesCharacter : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)),
    IsHCParam lam → IsDS ε lam σ → ∀ h : IsURepOn (UJset ε) σ, ∃ Θ, IsGlobalChar μ (ujRep h) Θ ∧
      ∀ θ : Fin n → ℝ, IsRegSS (ujMat ε (torusPt ε θ)) → Θ (torusPt ε θ) = dsChar ε lam θ

def WeylIntegrationFormula : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), (∃ 𝒯 : Finset (Subgroup (UJ ε)), IsCartanSystem 𝒯) ∧
    (∀ T : Subgroup (UJ ε), IsCartanSub T → weylOrder T ≠ 0) ∧
    ∀ (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (𝒯 : Finset (Subgroup (UJ ε))), IsCartanSystem 𝒯 →
      ∀ dt : ∀ T : Subgroup (UJ ε), Measure T, (∀ T ∈ 𝒯, (dt T).IsHaarMeasure) →
        ∀ F : UJ ε → ℝ≥0∞, Measurable F →
          ∫⁻ g, F g ∂μ = ∑ T ∈ 𝒯, (weylOrder T : ℝ≥0∞)⁻¹ *
            ∫⁻ t : T, ‖weylDisc (ujMat ε t)‖ₑ * ∫⁻ q, F (q.out⁻¹ * t * q.out) ∂quotMeas T (dt T) μ ∂dt T

def InducedCharacterSupport : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (a : ℕ) (j : Fin a → ℕ) (W : Flag n a),
    IsIsoFlag ε j W → (∀ i, 1 ≤ j i) → a ≠ 0 →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] [Nontrivial V]
      (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (mats (leviOne ε W)) σ → IsIrredOn (mats (leviOne ε W)) σ →
      ∀ (s : Fin a → ℂ) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
        (ρ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (ι : indFun (ε := ε) ⊤ j W σ s →ₗ[ℂ] X),
        IsIndModel ⊤ (KG ε) (muK ε) _ ρ ι → ∀ h : IsCRepOn (UJset ε) ρ, ∃ Θ, IsGlobalChar μ (groupRep ε h) Θ ∧
          ∀ g, IsRegSS (ujMat ε g) → (∀ x, x * g * x⁻¹ ∉ flagM ε W) → Θ g = 0

def HarishChandraCharacters : Prop :=
  CharacterRegularity ∧ DiscreteSeriesCharacter ∧ WeylIntegrationFormula ∧ InducedCharacterSupport

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
section
noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar)
open scoped InnerProductSpace Topology

namespace GlobalTheory.Published

namespace Langlands

def IsRightDeriv {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (X : Matrix (Fin n) (Fin n) ℂ) (f f' : UJ ε → V) : Prop :=
  ∀ g, HasDerivAt (fun t : ℝ => f (g * expG ε X t)) (f' g) 0

def Induced : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε),
    IsAdmRep ε I.ρ ∧ HasFiniteLength ε I.ρ ∧ IsGKSub ε I.ρ (kFinVec ε I.ρ) ∧
    (∀ w, IsKFin ε I.ρ w ↔ ∃ f : I.fns, IsKFinFun f.1 ∧ I.ι f = w) ∧
    (∀ f : I.fns, IsKFinFun f.1 → ∀ X ∈ lieSet ε,
      ∃ f' : I.fns, IsRightDeriv X f.1 f'.1 ∧ dRep I.ρ X (I.ι f) = I.ι f') ∧
    ∀ f ∈ I.fns, ∀ f' ∈ I.dualFns, ∀ y : UJ ε,
      ∫ k : KG ε, ⟪f' (k * y), f (k * y)⟫_ℂ ∂muK ε = ∫ k : KG ε, ⟪f' k, f k⟫_ℂ ∂muK ε

def Quotient : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε), I.Positive → ∀ ν : Measure (UJ ε), IsHaarSub I.Nbar ν →
    (∀ f ∈ I.fns, IsKFinFun f → ∃ h ∈ I.oppFns, IsKFinFun h ∧ I.IsIntegral ν f h) ∧
    (∀ f ∈ I.fns, IsKFinFun f → ∀ X ∈ lieSet ε, ∀ f' h h', IsRightDeriv X f f' → I.IsIntegral ν f h →
      I.IsIntegral ν f' h' → IsRightDeriv X h h') ∧
    ∃ Z : Submodule ℂ I.H, (Z : Set I.H) = I.intKer ν ∧ IsGKSub ε I.ρ Z ∧ Z ≠ kFinVec ε I.ρ ∧
      (∀ Y, IsGKSub ε I.ρ Y → Y = kFinVec ε I.ρ ∨ Y ≤ Z) ∧
      ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
        (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsIrrAdm ε π ∧ IsFactor ε I.ρ Z (kFinVec ε I.ρ) π

def Classification : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (b : ℕ) (W₀ : Flag n b), IsMinimalFlag ε W₀ →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsIrrAdm ε π →
      (∃ I : IndModule ε, I.IsStandard W₀ ∧ ∃ Z, IsFactor ε I.ρ Z (kFinVec ε I.ρ) π ∧
        ∀ ν : Measure (UJ ε), IsHaarSub I.Nbar ν → (Z : Set I.H) = I.intKer ν) ∧
      ∀ I I' : IndModule ε, I.IsStandard W₀ → I'.IsStandard W₀ → ∀ Z Z', IsFactor ε I.ρ Z (kFinVec ε I.ρ) π →
        IsFactor ε I'.ρ Z' (kFinVec ε I'.ρ) π → I.Equiv I'.toDatum

def Limit : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (D : Datum ε), D.Positive → ∀ ν' : Measure (UJ ε), IsHaarSub D.Nbar ν' →
    ∃ c : ℝ, 0 < c ∧
      (∀ φ ∈ indFun ⊤ D.j D.W (fun _ => (1 : ℂ →L[ℂ] ℂ)) (rho n D.j),
        Integrable φ ν' ∧ ∫ k : KG ε, φ k ∂muK ε = c * ∫ u, φ u ∂ν') ∧
      ∀ f ∈ D.fns, IsKFinFun f → ∀ f' ∈ D.dualFns, IsKFinFun f' → ∀ x, InChamber x →
        ∀ t : ℝ → UJ ε, (∀ r, IsSplit ε D.W (r • x) (t r)) →
          Integrable (fun u => ⟪f' 1, f u⟫_ℂ) ν' ∧
          Tendsto (fun r : ℝ => Complex.exp (r * pairing D.j (rho n D.j - D.s) x) *
              ∫ k : KG ε, ⟪f' k, f (k * t r)⟫_ℂ ∂muK ε) atTop (𝓝 (c * ∫ u, ⟪f' 1, f u⟫_ℂ ∂ν'))

def StandardSpan : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (b : ℕ) (W₀ : Flag n b), IsMinimalFlag ε W₀ →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hπ : IsIrrAdm ε π),
      ∃ (N : ℕ) (I : Fin N → IndModule ε) (c : Fin N → ℤ),
        (∀ i, (I i).IsStandard W₀) ∧ (∀ i l, (I i).Equiv (I l).toDatum → i = l) ∧ (∀ i, c i ≠ 0) ∧
        (∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
          (π' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), IsIrrAdm ε π' →
          ((mult ε π π').toNat : ℤ) = ∑ i, c i * (mult ε (I i).ρ π').toNat) ∧
        (∀ i χ, HasInfChar ε χ (I i).ρ ↔ HasInfChar ε χ π) ∧
        ∀ (μ : Measure (UJ ε)) [μ.IsHaarMeasure], ∀ f ∈ GlobalTheory.Orb.CcMat (GlobalTheory.Orb.ujMat ε),
          (∀ i, IsTraceClass (repOp (I i).rep μ f)) ∧
          HasTrace (repOp (groupRep ε hπ.2.1.1) μ f) (∑ i, c i * trace (repOp (I i).rep μ f))

def StandardIndependent : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (b : ℕ) (W₀ : Flag n b), IsMinimalFlag ε W₀ →
    ∀ (N : ℕ) (I : Fin N → IndModule ε) (c : Fin N → ℤ),
      (∀ i, (I i).IsStandard W₀) → (∀ i l, (I i).Equiv (I l).toDatum → i = l) →
      (∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
        (π' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), IsIrrAdm ε π' →
        ∑ i, c i * (mult ε (I i).ρ π').toNat = 0) → c = 0

def TemperedLevi : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (D : Datum ε) (b : ℕ) (W' : Flag n b), IsIsoFlag ε (fun _ => 1) W' →
    (∀ i, D.W i ∈ Set.range W') → W' (Fin.last b) = D.W (Fin.last D.a) →
    ∃ (U : Type) (_ : NormedAddCommGroup U) (_ : InnerProductSpace ℂ U) (_ : CompleteSpace U)
      (τ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U)) (y : Fin b → ℝ), IsIrrTempered (leviOne ε W') τ ∧
      ∀ μ : Measure ↥(KG ε ⊓ D.M), μ.IsHaarMeasure → IsProbabilityMeasure μ →
        ∃ ι : indFun D.M (fun _ => 1) W' τ (fun l => Complex.I * y l) →ₗ[ℂ] D.V,
          IsIndModel D.M (KG ε ⊓ D.M) μ _ D.σ ι

end Langlands


open Langlands in
def LanglandsClassification : Prop :=
  Induced ∧ Quotient ∧ Classification ∧ Limit ∧ StandardSpan ∧ StandardIndependent ∧ TemperedLevi

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
section
open MeasureTheory GlobalTheory.Orb GlobalTheory.AdelicU Formalism.MainNotions.S

noncomputable section

namespace GlobalTheory.Published

def PseudoCoefficientUpq : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (σ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (h : GlobalTheory.Dec.IsSqIntIrr ε σ)
    (μ : Measure (Formalism.REAL.UJ ε)) [μ.IsHaarMeasure],
    haveI := h.1
    ∃ f : Formalism.REAL.UJ ε → ℂ, IsBiFinite (Formalism.REAL.KG ε) f ∧ IsPseudoCoeff (ujMat ε) μ (ujRep h.2.2.1) f


end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentationIff
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.LocGL GlobalTheory.Published
open GlobalTheory.Parabolic (isIrreducible_of_equiv)

namespace GlobalTheory.SegmentRepModel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def Concl {d : ℕ} (σ : Representation ℂ (GL (Fin d) k) V) (l : ℕ) : Prop :=
  ∃ S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ l)),
    S.toRepresentation.IsIrreducible ∧
    (∀ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ l)),
      S'.toRepresentation.IsIrreducible → S' = S) ∧
    Nonempty ((GlobalTheory.SmGL.jac (consecBlocks l d) S.toRepresentation).Equiv (piTensor (segTerm σ l)))

def jacCongr {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {π : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (φ : π.Equiv τ) : (GlobalTheory.SmGL.jac e π).Equiv (GlobalTheory.SmGL.jac e τ) :=
  equivOfBijective (jacMap e φ.toIntertwiningMap) (Function.bijective_iff_has_inverse.2
    ⟨jacMap e φ.symm.toIntertwiningMap,
      fun y => by
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        exact congrArg Submodule.Quotient.mk (φ.symm_apply_apply v),
      fun y => by
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        exact congrArg Submodule.Quotient.mk (φ.apply_symm_apply v)⟩)

theorem concl_of_isSocle {d l : ℕ} {σ : Representation ℂ (GL (Fin d) k) V}
    {τ : Representation ℂ (GL (Fin (l * d)) k) W}
    (h : IsSocle τ (multiProd (consecBlocks l d) (segTerm σ l)))
    (hj : Nonempty ((GlobalTheory.SmGL.jac (consecBlocks l d) τ).Equiv (piTensor (segTerm σ l)))) : Concl σ l := by
  obtain ⟨hi, f, hf, hS⟩ := h
  have inc : ∀ S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ l)),
      ∃ g : S.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ l)),
        Function.Injective g ∧ g.range = S := fun S =>
    ⟨⟨S.toSubmodule.subtype, fun _ => rfl⟩, Subtype.val_injective,
      Subrepresentation.toSubmodule_injective (Submodule.range_subtype _)⟩
  obtain ⟨g, hg, hr⟩ := inc f.range
  obtain ⟨φ⟩ := nonempty_equiv_of_range_eq f hf g hg hr.symm
  obtain ⟨ψ⟩ := hj
  refine ⟨f.range, isIrreducible_of_equiv φ hi, fun S' hS' => ?_, ⟨(jacCongr _ φ.symm).trans ψ⟩⟩
  obtain ⟨g', hg', hr'⟩ := inc S'
  exact hS _ (hr' ▸ isAtom_range hS' g' hg')

theorem concl_two {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) : Concl (detRep (Fin 1) χ) 2 := by
  classical
  have he : consecBlocks 2 1 = (ProjLine.pts : (Σ _ : Fin 2, Fin 1) ≃ Fin (2 * 1)) := by
    ext ⟨a, j⟩
    rw [consecBlocks_val, ProjLine.pts_apply]
    omega
  have hη : IsSmoothChar (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2)) := hχ.mul (isSmoothChar_absPow _)
  obtain ⟨ψ⟩ := nonempty_jac_det_equiv (consecBlocks 2 1) χ
  refine concl_of_isSocle (τ := detRep (Fin (2 * 1)) (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2))) ?_ ⟨ψ⟩
  obtain ⟨X, _, _, π, f, ⟨φ⟩, hf, h0, h, -⟩ := ProjLine.exists_line hη
  let a : (ofChar (detLevi (consecBlocks 2 1) (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2)))).Equiv
      (GlobalTheory.SmGL.jac (consecBlocks 2 1) (detRep (Fin (2 * 1)) (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2)))) :=
    .mk (Submodule.quotEquivOfEqBot _ (twKer_detRep _ _)).symm fun g => LinearMap.ext fun c => by
      simp only [LinearMap.comp_apply]
      rw [Model.jac_detRep, ofChar_apply]
      exact map_smul _ (_ : ℂ) c
  have b := parIndEquiv (consecBlocks 2 1) (a.trans ψ)
  have φ' : π.Equiv (parInd (consecBlocks 2 1)
      (ofChar (detLevi (consecBlocks 2 1) (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2))))) := by
    rw [he]; exact φ
  exact (ProjLine.isSocle_of_le (isIrreducible_ofChar _) f hf h0 h).of_equiv (.refl _) (φ'.trans b)

end GlobalTheory.SegmentRepModel

end
end

