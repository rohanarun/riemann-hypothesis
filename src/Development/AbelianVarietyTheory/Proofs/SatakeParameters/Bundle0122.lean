module

public import Mathlib
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsMulMinusculeTopTerm
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0004
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0120
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.Bundle0001
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.KapAll

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CartanExponentsNonnegMinusculeTopProduct
section
open IsDedekindDomain NumberField Matrix

noncomputable section

namespace GlobalTheory.Hk3.MinuscTopLocal

theorem ov_eq (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Formalism.UG.Ov F v = Formalism.UG.intL (v.adicCompletion F) := by
  ext x
  exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) (K := F) v).trans Iff.rfl

theorem zpow_int {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    {ϖ : v.adicCompletion F} (hϖ : Formalism.UG.IsUnifV F v ϖ) (m : ℤ) :
    ϖ ^ m ∈ Formalism.UG.intL (v.adicCompletion F) ↔ 0 ≤ m := by
  rw [← ov_eq]
  show ϖ ^ m ∈ v.adicCompletionIntegers F ↔ 0 ≤ m
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_zpow₀, hϖ, ← WithZero.coe_zpow,
    ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zsmul, ← ofAdd_zero, Multiplicative.ofAdd_le,
    smul_eq_mul]
  omega

def dU {L : Type} [Field L] {n : ℕ} {ϖ : L} (h0 : ϖ ≠ 0) (e : Fin n → ℤ) : GL (Fin n) L where
  val := Matrix.diagonal fun i => ϖ ^ e i
  inv := Matrix.diagonal fun i => ϖ ^ (-e i)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; rw [← zpow_add₀ h0]; simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; rw [← zpow_add₀ h0]; simp

theorem intM_mul {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) :
    ∀ i j, (A * B) i j ∈ Formalism.UG.intL L := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hA _ _) (hB _ _)

theorem intM_diag {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    {ϖ : v.adicCompletion F} (hϖ : Formalism.UG.IsUnifV F v ϖ) {e : Fin n → ℤ} (he : ∀ i, 0 ≤ e i) :
    ∀ i j, (Matrix.diagonal fun i => ϖ ^ e i) i j ∈ Formalism.UG.intL (v.adicCompletion F) := fun i j => by
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · exact (zpow_int hϖ _).2 (he i)
  · exact zero_mem _

theorem unif_ne_zero {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    {ϖ : v.adicCompletion F} (hϖ : Formalism.UG.IsUnifV F v ϖ) : ϖ ≠ 0 := by
  intro h
  rw [Formalism.UG.IsUnifV, h, map_zero] at hϖ
  exact WithZero.zero_ne_coe hϖ

theorem cartan_top_step : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F), Formalism.UG.IsUnifV F v ϖ → ∀ (d : Fin n → ℤ) (k : ℕ), Antitone d → (∀ i, 0 ≤ d i) → (∀ i : Fin n, 0 < d i ↔ (i : ℕ) < k) → ∀ a₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ a₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ a₃ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ d' : Fin n → ℤ, Antitone d' → ∀ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), (a₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ (fun i => if 0 < d i then d i - 1 else d i) * (a₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ (fun i => if (i : ℕ) < k then 1 else 0) * (a₃ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (k₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ d' * (k₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → (∀ i, 0 ≤ d' i) ∧ (d' = d ∨ (∑ i, d' i = ∑ i, d i ∧ ∑ i, d' i ^ 2 < ∑ i, d i ^ 2)) := by
  intro F _ _ v n ϖ hϖ d k hd hd0 hk a₁ ha₁ a₂ ha₂ a₃ ha₃ d' hd' k₁ hk₁ k₂ hk₂ e
  have h0 : ϖ ≠ 0 := unif_ne_zero hϖ
  rw [ov_eq] at ha₁ ha₂ ha₃ hk₁ hk₂
  have hm0 : ∀ i, 0 ≤ (fun i => if 0 < d i then d i - 1 else d i) i := fun i => by
    have := hd0 i; dsimp only; split_ifs <;> omega
  have hw0 : ∀ i : Fin n, 0 ≤ (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) i := fun i => by
    dsimp only; split_ifs <;> omega
  have hG : a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂ *
      dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃ = k₁ * dU h0 d' * k₂ :=
    Units.ext (by simp only [Units.val_mul]; exact e)
  have hD : k₁⁻¹ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂ *
      dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * k₂⁻¹ = dU h0 d' := by
    rw [hG]; group
  have hd'0 : ∀ i, 0 ≤ d' i := by
    intro i
    have hI : ∀ a b, ((k₁⁻¹ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂ *
        dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * k₂⁻¹ : GL (Fin n) _) :
          Matrix (Fin n) (Fin n) _) a b ∈ Formalism.UG.intL (v.adicCompletion F) := by
      simp only [Units.val_mul]
      refine intM_mul (intM_mul (GlobalTheory.Hk3.MinuscTop.glint_entry (inv_mem hk₁)) ?_)
        (GlobalTheory.Hk3.MinuscTop.glint_entry (inv_mem hk₂))
      refine intM_mul (intM_mul (intM_mul (intM_mul (GlobalTheory.Hk3.MinuscTop.glint_entry ha₁) ?_)
        (GlobalTheory.Hk3.MinuscTop.glint_entry ha₂)) ?_) (GlobalTheory.Hk3.MinuscTop.glint_entry ha₃)
      · exact intM_diag hϖ hm0
      · exact intM_diag hϖ hw0
    have := hI i i
    rw [hD] at this
    change (Matrix.diagonal fun i => ϖ ^ d' i) i i ∈ _ at this
    rw [Matrix.diagonal_apply_eq] at this
    exact (zpow_int hϖ _).1 this
  obtain ⟨dN, hdN⟩ : ∃ f : Fin n → ℕ, ∀ i, (f i : ℤ) = d i :=
    ⟨fun i => (d i).toNat, fun i => Int.toNat_of_nonneg (hd0 i)⟩
  obtain ⟨d'N, hd'N⟩ : ∃ f : Fin n → ℕ, ∀ i, (f i : ℤ) = d' i :=
    ⟨fun i => (d' i).toNat, fun i => Int.toNat_of_nonneg (hd'0 i)⟩
  have hdA : Antitone dN := fun i j h => by have := hd h; have := hdN i; have := hdN j; omega
  have hd'A : Antitone d'N := fun i j h => by have := hd' h; have := hd'N i; have := hd'N j; omega
  have hkN : ∀ i : Fin n, 0 < dN i ↔ (i : ℕ) < k := fun i => by rw [← hk i, ← hdN i]; omega
  have hg : ∃ l₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ∃ l₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ((l₁ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂) * l₂ : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) _) = Matrix.diagonal fun i => ϖ ^ (dN i - 1) := by
    refine ⟨a₁⁻¹, inv_mem ha₁, a₂⁻¹, inv_mem ha₂, ?_⟩
    have : a₁⁻¹ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂) * a₂⁻¹ =
        dU h0 (fun i => if 0 < d i then d i - 1 else d i) := by group
    rw [this]
    change (Matrix.diagonal fun i => ϖ ^ (if 0 < d i then d i - 1 else d i)) = _
    congr 1; funext i
    rw [← zpow_natCast]; congr 1
    have := hdN i
    split_ifs <;> omega
  have ha : ∃ l₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ∃ l₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ((l₁ * (dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * l₂ : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) _) = Matrix.diagonal fun i : Fin n => if (i : ℕ) < k then ϖ else 1 := by
    refine ⟨1, one_mem _, a₃⁻¹, inv_mem ha₃, ?_⟩
    have : 1 * (dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * a₃⁻¹ =
        dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) := by group
    rw [this]
    change (Matrix.diagonal fun i : Fin n => ϖ ^ (if (i : ℕ) < k then (1 : ℤ) else 0)) = _
    congr 1; funext i
    split_ifs <;> simp
  have hga : ∃ l₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ∃ l₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ((l₁ * ((a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂) *
        (dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃)) * l₂ : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) _) = Matrix.diagonal fun i => ϖ ^ d'N i := by
    refine ⟨k₁⁻¹, inv_mem hk₁, k₂⁻¹, inv_mem hk₂, ?_⟩
    rw [← mul_assoc (a₁ * _ * a₂), hD]
    change (Matrix.diagonal fun i => ϖ ^ d' i) = _
    congr 1; funext i
    rw [← hd'N i, zpow_natCast]
  have key := GlobalTheory.Hk3.MinuscTop.elemDiv_mul_minuscule (v.adicCompletion F) ϖ n hϖ dN k hdA hkN _ _ hg ha
    d'N hd'A hga
  refine ⟨hd'0, ?_⟩
  have s1 : ∑ i, d' i = ((∑ i, d'N i : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => (hd'N i).symm
  have s2 : ∑ i, d i = ((∑ i, dN i : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => (hdN i).symm
  have s3 : ∑ i, d' i ^ 2 = ((∑ i, d'N i ^ 2 : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => by rw [hd'N i]
  have s4 : ∑ i, d i ^ 2 = ((∑ i, dN i ^ 2 : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => by rw [hdN i]
  rcases key with h | ⟨h1, h2⟩
  · left; funext i; rw [← hd'N i, ← hdN i, h]
  · right
    rw [s1, s2, s3, s4]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

end GlobalTheory.Hk3.MinuscTopLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainLocalDataIntegralOffLevels
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.PhiRootVal

def RootOrZero {K : Type} [Field K] (z : K) : Prop := z = 0 ∨ ∃ n : ℕ, 0 < n ∧ z ^ n = 1

variable {K : Type} [Field K]

theorem RootOrZero.zero : RootOrZero (0 : K) := Or.inl rfl

theorem RootOrZero.one : RootOrZero (1 : K) := Or.inr ⟨1, one_pos, one_pow 1⟩

theorem RootOrZero.mul {z w : K} (hz : RootOrZero z) (hw : RootOrZero w) : RootOrZero (z * w) := by
  rcases hz with rfl | ⟨n, hn, hz⟩
  · exact Or.inl (zero_mul w)
  rcases hw with rfl | ⟨m, hm, hw⟩
  · exact Or.inl (mul_zero z)
  refine Or.inr ⟨n * m, Nat.mul_pos hn hm, ?_⟩
  rw [mul_pow, pow_mul, hz, one_pow, one_mul, mul_comm n m, pow_mul, hw, one_pow]

theorem RootOrZero.inv {z : K} (hz : RootOrZero z) : RootOrZero z⁻¹ := by
  rcases hz with rfl | ⟨n, hn, hz⟩
  · exact Or.inl inv_zero
  exact Or.inr ⟨n, hn, by rw [inv_pow, hz, inv_one]⟩

theorem RootOrZero.prod {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, RootOrZero (f i)) :
    RootOrZero (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (RootOrZero.one : RootOrZero (1 : K))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem RootOrZero.intOff {z : K} (hz : RootOrZero z) (σ : K →+* ℂ) (S : Finset ℕ) : IntOff S (σ z) := by
  rcases hz with rfl | ⟨n, hn, hz⟩
  · rw [map_zero]; exact IntOff.zero
  exact IntOff.of_pow hn (by rw [← map_pow, hz, map_one])

theorem addChar_root {A : Type} [AddCommGroup A] [Finite A] (ψ : AddChar A K) (a : A) : RootOrZero (ψ a) := by
  refine Or.inr ⟨Nat.card A, Nat.card_pos, ?_⟩
  rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]

theorem hom_root {G : Type} [Group G] [Finite G] (χ : G →* Kˣ) (g : G) : RootOrZero ((χ g : Kˣ) : K) := by
  refine Or.inr ⟨Nat.card G, Nat.card_pos, ?_⟩
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

section Loc
variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem unitV_root (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) : RootOrZero (LocE.unitV χ a) := by
  unfold LocE.unitV
  split_ifs with h
  · exact hom_root χ _
  · exact RootOrZero.zero

end Loc
end GlobalTheory.PhiRootVal

namespace GlobalTheory.PhiRootVal
variable {K : Type} [Field K]
section Loc2
variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem phiQ_root (q : ℕ) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ) (x) :
    RootOrZero (LocE.PhiQ q ξ k₀ r c' n' c n x) := by
  unfold LocE.PhiQ
  split_ifs
  · exact unitV_root ξ _
  · exact RootOrZero.zero

theorem lamGv_root (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (r t j : ℕ) (M : ℕ → ℕ → E) :
    RootOrZero (LocE.lamGv ψ₀ χ r t j M) := by
  unfold LocE.lamGv
  exact (addChar_root ψ₀ _).mul (RootOrZero.prod _ _ fun i _ => unitV_root (χ i) _)

theorem lamGvS_root (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r t j : ℕ) (M : ℕ → ℕ → E) :
    RootOrZero (LocE.lamGvS ψ₀ χ k₀ r t j M) := by
  unfold LocE.lamGvS
  exact (addChar_root ψ₀ _).mul (RootOrZero.prod _ _ fun i _ => unitV_root (χ i) _)

theorem phiG_root (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (sharp : Bool)
    (k₀ r t j c' n' c n : ℕ) (x) : RootOrZero (LocE.PhiG q ψ₀ χ sharp k₀ r t j c' n' c n x) := by
  unfold LocE.PhiG
  dsimp only
  split_ifs
  · exact (lamGv_root ψ₀ χ _ _ _ _).mul (unitV_root _ _).inv
  · exact RootOrZero.zero

theorem phiGS_root (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ rS r t j c' n' c n : ℕ) (x) : RootOrZero (LocE.PhiGS q ψ₀ χ k₀ rS r t j c' n' c n x) := by
  unfold LocE.PhiGS
  dsimp only
  split_ifs
  · exact (lamGvS_root ψ₀ χ _ _ _ _ _).mul (unitV_root _ _).inv
  · exact RootOrZero.zero

end Loc2

section Chain
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem phiAt_root (sharp : Bool) (i : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (x) :
    RootOrZero (PhiAt (R := R) Ch mu sharp i P x) := by
  unfold PhiAt
  split_ifs
  · exact phiGS_root (x := x) ..
  · exact phiG_root (x := x) ..
  · exact phiQ_root (x := x) ..

theorem phiTop_root (sharp : Bool) (m2 : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (x) :
    RootOrZero (PhiTop (R := R) Ch mu sharp m2 P x) := by
  unfold PhiTop
  split_ifs
  · exact phiGS_root (x := x) ..
  · exact phiG_root (x := x) ..
  · exact phiQ_root (x := x) ..

end Chain

theorem phi_intOff : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ (P : HeightOneSpectrum (𝓞 t.X.E)), (∀ (i : ℕ) x, IntOff (t.O u μ).S (t.seam.σ₀ (PhiAt (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp i P x))) ∧ ∀ x, IntOff (t.O u μ).S (t.seam.σ₀ (PhiTop (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp t.m2 P x)) := by
  intro D L hT Gi Gl K Y cX ex t u μ P
  exact ⟨fun i x => (phiAt_root _ _ _ _ _ x).intOff _ _, fun x => (phiTop_root _ _ _ _ _ x).intOff _ _⟩

end GlobalTheory.PhiRootVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CombOfTied
section
noncomputable section

namespace GlobalTheory.Ggeo.KerComb

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

theorem comb_of_tied : Formalism.L2.KerInert.AlgTAll → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → ∀ u μ w, LevFree Y u μ w → ∀ i < D.R.m, ∀ c c', TaylorLogMetric.admitted D _ _ ((t.O u μ).lat i c).1 ((t.O u μ).lat (i + 1) c').1 ∧ TaylorLogMetric.IsComb D t.B.tor (t.B.eNat t.χ) (t.ent.lam w) ((t.O u μ).lat i c).1 ((t.O u μ).lat (i + 1) c').1 (TaylorLogMetric.pSer D (t.ent.lam w) ((t.O u μ).Th i c c')) := by
  intro hAlg D L hT Gi Gl K Y cX ex t hH u μ w hw i hi c c'
  have hEven : ∀ j, Even (D.R.N j) := fun j => D.R.k_even.add (D.R.t_odd.add_one.mul_left j)
  have hAdm : TaylorLogMetric.admitted D _ _ ((t.O u μ).lat i c).1 ((t.O u μ).lat (i + 1) c').1 :=
    ⟨hEven i, hEven (i + 1), ((t.O u μ).lat i c).2, ((t.O u μ).lat (i + 1) c').2⟩
  refine ⟨hAdm, ?_⟩
  have hTA : TransAlg D t.B.tor (t.B.eNat t.χ) :=
    transcendence_algebraic_eigen D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok (KS.Lat.delta_ne t.cc_ok t.δ_ok) (t.B.stdOK t.cc_ok t.δ_ok)
      (hAlg D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok)
  have hS : D.what₂.places.resChar w ∉ (t.O u μ).S := by
    obtain ⟨h1, h2, h3⟩ := hw
    rw [t.O_S u μ]
    intro hm
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, not_or] at h2 hm
    rcases hm with h | (h | h) | h
    exacts [h1 h, h2.1 h, h2.2 h, h3 h]
  have hA' := hAdm
  rw [t.O_lat u μ i c, t.O_lat u μ (i + 1) c'] at hA' ⊢
  rw [t.O_Th u μ i c c']
  exact first_kernel_law_reading D t.X u (D.chTw u μ) (t.rd u μ) t.seam t.amb t.cc t.δ (t.B.eNat t.χ) (t.O u μ).S i (hH u μ i hi) hTA c c' hA' _ (t.ent.lam w) hS

end GlobalTheory.Ggeo.KerComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DifferentiableSumU
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerFinEntire

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem differentiable_opU (H : Sesq V) {F : V → ℂ} (hF : Differentiable ℂ F) (x : V) :
    Differentiable ℂ (opU H x F) := by
  have h : Differentiable ℂ fun z => H z x := (LinearMap.toContinuousLinearMap (H.flip x)).differentiable
  unfold opU
  fun_prop

theorem differentiable_sumU (H : Sesq V) (α : V → ℂ) (S : Finset V) {F : V → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (sumU H α S F) := by
  unfold sumU
  exact Differentiable.fun_sum fun x _ => (differentiable_opU H hF x).const_mul _

theorem differentiable_xiL (H : Sesq V) (α : V → ℂ) (vol : ℝ) (SX SA SB : Finset V) (Φ : V → ℂ) {e : V → ℂ}
    (he : Differentiable ℂ e) : Differentiable ℂ (xiL H α vol SX SA SB Φ e) := by
  unfold xiL xiS
  exact Differentiable.fun_sum fun x _ => (differentiable_opU H (differentiable_sumU H _ SB he) x).const_mul _

end General

theorem differentiable_thC {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}
    (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (c : ℕ) (Ξ : HomE E a b → ℂ) {θ : VV ι a b → ℂ}
    (hθ : Differentiable ℂ θ) : Differentiable ℂ (thC emb δ d sc AA0 SS N N' c Ξ θ) := by
  unfold thC xiV
  exact differentiable_xiL _ _ _ _ _ _ _ hθ

theorem kerFin_entire : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') → ∀ (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (c : ℕ) (Ξ : HomE X.E a b → ℂ), Differentiable ℂ (thC (X.embC (ambOf s B χ cD : Amb X).σ₀) (ambOf s B χ cD : Amb X).δ (ambOf s B χ cD : Amb X).d (ambOf s B χ cD : Amb X).sc (ambOf s B χ cD : Amb X).AA SS N N' c Ξ ((ambOf s B χ cD : Amb X).e a b N N')) := by
  intro D X s cc δ B χ cD _ hcc hδ hχ a b N N' hA SS c Ξ
  have hE : Differentiable ℂ (B.eNat χ a b (s.lat N) (s.lat N')) :=
    (B.vec_mem_ne hcc hδ (Formalism.L2.Ker.KS.Lat.delta_ne hcc hδ) (B.stdOK hcc hδ) χ hχ a b _ _ hA).1.1
  let T : VCx X.Tau a b →L[ℂ] TaylorLogMetric.VC D a b := ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (s.iT.symm τ)
  have he : Differentiable ℂ ((ambOf s B χ cD : Amb X).e a b N N') := hE.comp T.differentiable
  exact differentiable_thC _ _ _ _ _ _ _ _ _ _ he

end GlobalTheory.KerFinEntire
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigSumMulProjEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3


open _root_.Formalism.L2.Col in
theorem eigSum_mul_proj_eq {E I C : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (h : I → Module.End ℂ E) (e : Module.End ℂ E) (Ec : C → Submodule ℂ E) (lab : C → I → ℂ)
    (he : e * e = e) (hr : (⨆ c, Ec c) = LinearMap.range e)
    (hh : ∀ c, ∀ w ∈ Ec c, ∀ i, h i w = lab c i • w) :
    PairComm (fun i => h i * e) ∧ ∀ Q : (I → ℂ) → Prop, ¬ Q 0 →
      eigSum (fun i => h i * e) Q = ⨆ (c : C) (_ : Q (lab c)), Ec c := by
  first
  | exact @_root_.GlobalTheory.IndependentInfimum.main
  | exact _root_.GlobalTheory.IndependentInfimum.main
  | (apply _root_.GlobalTheory.IndependentInfimum.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IndependentInfimum.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IndependentInfimum.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IndependentInfimum.main ..)

end GlobalTheory.Hk3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOffSplitOfEqOffSplitPrime
section
noncomputable section

namespace GlobalTheory.EqOffSplitOfSplit

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

theorem isSplit_conj (D : D7) {P Q : HeightOneSpectrum (𝓞 D.host.E)} (hP : GL3Theta.SplitP D P)
    (hQ : ∀ x : 𝓞 D.host.E, x ∈ Q.asIdeal ↔ Formalism.L2.PairingIndexBounds.Rec.cO D x ∈ P.asIdeal) : GL3Theta.SplitP D Q := by
  obtain ⟨a, b, hab, ha, hb⟩ := hP
  have hb' : b = Formalism.L2.PairingIndexBounds.Rec.cO D a := Subtype.ext (hab.trans rfl)
  refine ⟨b, a, ?_, ?_, ?_⟩
  · rw [hab]; exact (Formalism.L2.PairingIndexBounds.Rec.conj_conj' D (a : D.host.E)).symm
  · rw [hQ, hb', Formalism.L2.PairingIndexBounds.Rec.cO_cO]; exact ha
  · rw [hQ, ← hb']; exact hb

theorem eqOffSplit_of_eqOff : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ)
    (L L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
    GL3Theta.SplitP D P → GL3Theta.EqOff D P L L₀ → GL3Theta.EqOffSplit D L L₀ := by
  intro D P n L L₀ hP hoff
  obtain ⟨m, hm⟩ := hoff
  obtain ⟨x, hx0, hxP, hxM⟩ := Formalism.L2.PairingIndexBounds.Rec.genPow D P
  have hc0 : ∀ y : 𝓞 D.host.E, y ≠ 0 → Formalism.L2.PairingIndexBounds.Rec.cO D y ≠ 0 := fun y hy h => hy (by
    rw [← Formalism.L2.PairingIndexBounds.Rec.cO_cO D y, h, map_zero])
  have hg0 : x ^ m ≠ 0 := pow_ne_zero m hx0
  obtain ⟨h1, h2⟩ := hm (x ^ m) (Formalism.L2.PairingIndexBounds.Rec.cO D (x ^ m)) rfl (Ideal.pow_mem_pow hxP m)
  refine ⟨x ^ m * Formalism.L2.PairingIndexBounds.Rec.cO D (x ^ m), mul_ne_zero hg0 (hc0 _ hg0), fun Q hQ => ?_, h1, h2⟩
  rcases Q.isPrime.mem_or_mem hQ with h | h
  · have e : P.asIdeal = Q.asIdeal := hxM _ Q.isPrime (Q.isPrime.mem_of_pow_mem m h)
    have e' : P = Q := HeightOneSpectrum.ext e
    exact e' ▸ hP
  · rw [map_pow] at h
    have h3 : Formalism.L2.PairingIndexBounds.Rec.cO D x ∈ Q.asIdeal := Q.isPrime.mem_of_pow_mem m h
    have e : P.asIdeal = (Formalism.L2.PairingIndexBounds.Rec.cQ D Q).asIdeal :=
      hxM _ (Formalism.L2.PairingIndexBounds.Rec.cQ D Q).isPrime ((Formalism.L2.PairingIndexBounds.Rec.mem_cQ D Q x).2 h3)
    refine isSplit_conj D hP fun y => ?_
    rw [e, Formalism.L2.PairingIndexBounds.Rec.mem_cQ, Formalism.L2.PairingIndexBounds.Rec.cO_cO]

end GlobalTheory.EqOffSplitOfSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KappaNormAtSplitPrimes
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory

theorem kappaSplit_all : ∀ D : D7, KappaSplit D :=
  fun D => Formalism.L2.Ker.KS.kappaSplit D

end GlobalTheory
end

