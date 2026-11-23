module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainSupportAtOfPattern
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0061
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardKerSubspacesAndHeckePolyOfConvolution
public import Formalism.LocalToGlobal.HermitianForms.Bundle0003
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormalGroupHeightLeTwoGoodReduction
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TypeChainPrincipalEntryNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralEqFiniteSumOverNumberField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0055

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AllPositionsHolds
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem allPositions_holds : AllPositions := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _
  have hpat : S.Pattern t := _root_.GlobalTheory.SymChain.pattern_iter k s κ S t
  have hsupp : S.SupportAt t := _root_.GlobalTheory.SymSupportP.supportAt_of_pattern k s κ S t hpat
  have hclass : S.ClassAt t ν := _root_.GlobalTheory.SymChain.classAt_all k ν hν s κ S t
  exact ⟨_root_.GlobalTheory.SymChain.oneIndexAt_of_classAt_supportAt k ν hν s κ S t hclass hsupp, _root_.GlobalTheory.SymChain.ExchangeProof.exchangeAt k ν hν s κ S t hpat⟩

end GlobalTheory.SymChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardSubspacesContainingRangeQVandermonde
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.RangeKerCount

open GlobalTheory.KerRangeCount _root_.Formalism.L2.Col

theorem card_above_range_eq_sum : ∀ (κ : Type) [Field κ] [Finite κ] (U U' : Type) [AddCommGroup U] [Module κ U] [FiniteDimensional κ U] [AddCommGroup U'] [Module κ U'] [FiniteDimensional κ U'] (f : U →ₗ[κ] U') (t e : ℕ), Module.finrank κ U' = Module.finrank κ U + t → e ≤ Module.finrank κ U' → Nat.card {X : Submodule κ U' // LinearMap.range f ≤ X ∧ Module.finrank κ X + e = Module.finrank κ U'} = ∑ n ∈ Finset.range (Module.finrank κ U + 1), (if n ≤ e then Nat.card κ ^ (n * (t - (e - n))) * Formalism.L2.Col.gaussBin (Nat.card κ) t (e - n) else 0) * Nat.card {X : Submodule κ U // X ≤ LinearMap.ker f ∧ Module.finrank κ X = n} := by
  intro κ _ _ U U' _ _ _ _ _ _ f t e hU' he
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  rw [Nat.card_eq_fintype_card (α := κ)]
  have hq0 : Fintype.card κ ≠ 0 := Fintype.card_ne_zero
  have hrk := f.finrank_range_add_finrank_ker
  have hin : ∀ n, Nat.card {X : Submodule κ U // X ≤ LinearMap.ker f ∧ Module.finrank κ X = n} =
      Formalism.L2.Col.gaussBin (Fintype.card κ) (Module.finrank κ (LinearMap.ker f)) n := by
    intro n
    rw [← card_below (LinearMap.ker f) n]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun X => and_comm)
  have hL : Nat.card {X : Submodule κ U' // LinearMap.range f ≤ X ∧ Module.finrank κ X + e = Module.finrank κ U'} =
      Formalism.L2.Col.gaussBin (Fintype.card κ) (Module.finrank κ (LinearMap.ker f) + t) e := by
    by_cases hem : e ≤ Module.finrank κ (LinearMap.ker f) + t
    · rw [gaussBin_symm hq0 (Module.finrank κ (LinearMap.ker f) + t) e
        (Module.finrank κ (LinearMap.ker f) + t - e) (by omega)]
      have h := card_above (k := κ) (LinearMap.range f) (Module.finrank κ (LinearMap.ker f) + t - e)
      rw [show Module.finrank κ U' - Module.finrank κ (LinearMap.range f) =
        Module.finrank κ (LinearMap.ker f) + t by omega] at h
      rw [← h]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun X =>
        ⟨fun h => ⟨by omega, h.1⟩, fun h => ⟨h.2, by omega⟩⟩)
    · have : IsEmpty {X : Submodule κ U' // LinearMap.range f ≤ X ∧ Module.finrank κ X + e = Module.finrank κ U'} :=
        ⟨fun X => by have := Submodule.finrank_mono X.2.1; have := X.2.2; omega⟩
      rw [Nat.card_of_isEmpty, gaussBin_eq_zero _ (by omega)]
  set q := Fintype.card κ
  set m := Module.finrank κ (LinearMap.ker f)
  set g : ℕ → ℕ := fun n => (if n ≤ e then q ^ (n * (t - (e - n))) * Formalism.L2.Col.gaussBin q t (e - n) else 0) *
    Formalism.L2.Col.gaussBin q m n with hg
  have hR : ∑ n ∈ Finset.range (Module.finrank κ U + 1), (if n ≤ e then q ^ (n * (t - (e - n))) *
      Formalism.L2.Col.gaussBin q t (e - n) else 0) *
      Nat.card {X : Submodule κ U // X ≤ LinearMap.ker f ∧ Module.finrank κ X = n} =
      ∑ n ∈ Finset.range (Module.finrank κ U + 1), g n :=
    Finset.sum_congr rfl fun n _ => by rw [hin]
  have h2 : ∑ n ∈ Finset.range (e + 1), g n = ∑ n ∈ Finset.range (e + Module.finrank κ U + 1), g n :=
    Finset.sum_subset (Finset.range_mono (by omega)) fun n _ hn => by
      rw [Finset.mem_range] at hn
      simp only [hg]
      rw [if_neg (by omega), zero_mul]
  have h3 : ∑ n ∈ Finset.range (Module.finrank κ U + 1), g n =
      ∑ n ∈ Finset.range (e + Module.finrank κ U + 1), g n :=
    Finset.sum_subset (Finset.range_mono (by omega)) fun n _ hn => by
      rw [Finset.mem_range] at hn
      simp only [hg]
      rw [gaussBin_eq_zero q (show m < n by omega), mul_zero]
  rw [hL, hR, h3, ← h2, gaussBin_add hq0 m t e, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_range] at hn
  simp only [hg]
  rw [if_pos (by omega), show e + 1 - 1 - n = e - n by omega, show e - (e - n) = n by omega]
  ring

end GlobalTheory.RangeKerCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousPhiPrV
section
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.LevelCharOpen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

theorem redM_eq_one (v : HeightOneSpectrum (𝓞 F)) (X : Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hX : ∀ i j, Valued.v (X i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) < 1) : redM F v X = 1 := by
  ext i j
  have h1 : (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := by
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hd : X i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := (hX i j).le
  have hx : X i j ∈ v.adicCompletionIntegers F := by
    have := add_mem hd h1
    rwa [sub_add_cancel] at this
  have h0 : IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hd⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact (hX i j).ne
  have e : (⟨X i j, hx⟩ : v.adicCompletionIntegers F) = ⟨_, hd⟩ + ⟨_, h1⟩ := Subtype.ext (sub_add_cancel _ _).symm
  simp only [redM, dif_pos hx]
  rw [e, map_add (f := _), h0, zero_add]
  by_cases hij : i = j
  · subst hij
    have : (⟨_, h1⟩ : v.adicCompletionIntegers F) = 1 := Subtype.ext (Matrix.one_apply_eq i)
    rw [this, map_one, Matrix.one_apply_eq]
  · have : (⟨_, h1⟩ : v.adicCompletionIntegers F) = 0 := Subtype.ext (Matrix.one_apply_ne hij)
    rw [this, map_zero, Matrix.one_apply_ne hij]

theorem continuous_phi_prV (G : GLoc F E σ gp) (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal) :
    letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    Continuous ((G.phi a v h).comp (prV (E := E) v)) := by
  letI : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Algebra.TensorProduct.rightAlgebra
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  refine IsModuleTopology.continuous_of_ringHom (R := FiniteAdeleRing (𝓞 F) F) _ ?_
  have hv : Continuous (Formalism.UG.evalV F v) := RestrictedProduct.continuous_eval v
  refine hv.congr fun r => ?_
  show _ = (G.sp a v h ((1 : E) ⊗ₜ[F] Formalism.UG.evalV F v r)).1
  rw [G.sp_alg]

end GlobalTheory.LevelCharOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormalGroupHeightLeTwoGoodReductionStatement
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroup_height_le_two_good_reduction : ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (l : ℂ_[l]))‖ = 1 := by
  first | exact @GlobalTheory.HeightTwo.height_le_two | exact GlobalTheory.HeightTwo.height_le_two | (intros; apply GlobalTheory.HeightTwo.height_le_two <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemStabLocalizedStdLatticeIffIntegralGLStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_stabLocalizedStdLattice_iff_integralGL : ∀ {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (ι : E →+* k), (∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) → ∀ {A : Type} [Fintype A] [DecidableEq A] {M : ℕ} (e : A ≃ Fin M) (x : Sp E M ≃ₗ[E] Sp E M), x ∈ stabL E M (stdAt E M P) ↔ locHom ι e x ∈ KO k A := by
  first | exact @GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO | exact GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO | (intros; apply GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepDatumCompletionEqColumnTestFunction
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.LastStepProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hat_coset_of_not [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) {ε : k}
    (hε : valuation k ε = 1) (y₀ : n → k) {η : n → k} (hη : ¬ ∀ i, η i ∈ 𝒪[k]) :
    hat ψ ν ε (cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀)) η = 0 := by
  classical
  have := hν.1
  have := secondCountable k
  have hs : ∀ z ∈ box n (1 : kˣ), ∀ x,
      cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) (x + z) =
      cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) x := fun z hz x => by
    have : (Submodule.Quotient.mk (x + z) : (n → k) ⧸ box n (1 : kˣ)) = Submodule.Quotient.mk x :=
      (Submodule.Quotient.eq _).2 (by simpa using hz)
    simp only [cosetInd, Set.indicator_apply, Set.mem_setOf_eq, this]
  refine Eq.trans ?_ (FourierPi.fourier_eq_zero_pi (Measure.pi fun _ => ν) hψ (s := 1)
    (fun z hz x => hs z (fun i => hz i trivial) x) (y := ε • η) fun h' => hη fun i => ?_)
  · simp only [hat, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  · simpa [cball, hε, Valuation.mem_integer_iff] using h' i trivial

theorem topAgree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀)
    (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (S : SymData k s R.k) [MeasurableSpace k]
    [BorelSpace k] (ν : Measure k), IsUnitVol ν → AtType Ch sel mu cst σ₀ P ι S → TopAgree Ch sel mu cst σ₀ P ι S ν := by
  classical
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s S _ _ ν hν hA e' e he' he
  refine ⟨1, one_ne_zero, fun y y' hy' => ?_⟩
  have hm : R.m = s + 2 := hA.steps
  have hT := hA.tie
  have hint : ∀ a : X.E, ι a ∈ 𝒪[k] ↔ IntAt P.1 a := hT.compl.int
  have hlast : (e (Sum.inr ())).val = R.N R.m - 1 := he (Sum.inr ())
  have hNpos : R.N R.m - 1 < R.N R.m := by have := (e (Sum.inr ())).isLt; omega

  have hq : (qOf P.1 : X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, qOf, Ne, Ideal.absNorm_eq_zero_iff]; exact P.1.ne_bot
  set η' := atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y with hη'
  have hη'v : ∀ v, η' v = y v (e (Sum.inr ())) := fun v => by
    simp only [hη', LinearMap.comp_apply, atNL, dif_pos hNpos, LinearMap.proj_apply]
    rw [show (⟨R.N R.m - 1, hNpos⟩ : Fin (R.N R.m)) = e (Sum.inr ()) from Fin.ext hlast.symm]
  have hrow : (toLoc ι e e' y) (Sum.inr ()) = fun a => ι (η' (Pi.single (e' a) 1)) := by
    funext a; simp [toLoc, hη'v]
  have hsum : η' y' = ∑ i, y' i * η' (Pi.single i 1) := by
    have : y' = ∑ i, y' i • Pi.single i (1 : X.E) := by ext j; simp [Pi.single_apply]
    conv_lhs => rw [this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul]
  have hdot : (fun a => ι (η' (Pi.single (e' a) 1))) ⬝ᵥ (fun a => ι (y' (e' a))) = ι (η' y') := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum, dotProduct]
    exact Fintype.sum_equiv e' _ _ (fun a => by simp [mul_comm])
  have hB : hat S.ψ ν (-1) (cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk fun a => ι (y' (e' a))))
      ((toLoc ι e e' y) (Sum.inr ())) = σ₀ (ftY sel mu cst P η' y') := by
    rw [hrow, ftY, if_pos hA.mem]
    by_cases hη : ∀ i : Fin (R.N (s + 1)), IntAt P.1 (η' (Pi.single i 1))
    · rw [if_pos hη, GlobalTheory.StepData.Model.hat_coset S.cond hν (neg_mem (one_mem _)) _
        (fun a => (hint _).2 (hη _)), hdot]
      have hi : IntAt P.1 ((qOf P.1 : X.E) * ((epsSg : X.E) * η' y')) := by
        rw [← hint, hsum]
        have : (qOf P.1 : X.E) * ((epsSg : X.E) * ∑ i, y' i * η' (Pi.single i 1)) =
            -∑ i, ((qOf P.1 : X.E) * y' i) * η' (Pi.single i 1) := by
          simp only [epsSg, Int.cast_neg, Int.cast_one, Finset.mul_sum]; ring_nf; simp [Finset.sum_neg_distrib]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [this, map_neg, map_sum]
        exact neg_mem (sum_mem fun i _ => by rw [map_mul]; exact mul_mem ((hint _).2 (hy' i)) ((hint _).2 (hη i)))
      have h1 := hT.psi _ hi
      have h2 := hA.psi0 _ hi
      rw [mul_div_cancel_left₀ _ hq] at h1 h2
      rw [h2, ← h1]
      simp [epsSg]
    · rw [if_neg hη, map_zero]
      exact LastStepProof.hat_coset_of_not S.cond hν (by simp) _
        fun h => hη fun i => by simpa using (hint _).1 (h (e'.symm i))

  have hc : cOf R (s + 1) = 0 := by unfold cOf; omega
  have hρ : R.rS = S.ρ := by have := S.odd; unfold Ranks.rS; omega
  have hr : R.r = R.k + s + 1 := by unfold Ranks.r; omega
  have hN : R.N R.m - 1 = R.k + s + 1 + (s + 2) * R.t := by
    unfold Ranks.N; rw [hm]
    have : (s + 2) * (R.t + 1) = (s + 2) * R.t + (s + 2) := by ring
    omega
  let E1' : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1)) :=
    (Equiv.sumEmpty _ _).trans (e'.trans (finCongr (by omega)))
  have hbd : ∀ z, (e (Sum.inl z)).val < R.N R.m - 1 + 0 := fun z => by
    have h1 := (e (Sum.inl z)).isLt
    have h2 : e (Sum.inl z) ≠ e (Sum.inr ()) := e.injective.ne (by simp)
    have h3 : (e (Sum.inl z)).val ≠ R.N R.m - 1 := fun h => h2 (Fin.ext (h.trans hlast.symm))
    omega
  let f1 : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) → Fin (R.N R.m - 1 + 0) := fun z => ⟨(e (Sum.inl z)).val, hbd z⟩
  have hf1 : Function.Bijective f1 := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun z z' h => ?_, ?_⟩
    · have h' := Fin.val_eq_of_eq h
      have : e (Sum.inl z) = e (Sum.inl z') := Fin.ext h'
      exact Sum.inl_injective (e.injective this)
    · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      omega
  let E1 := Equiv.ofBijective f1 hf1
  have hE1' : IsOrd (yPos xPos (R.N (s + 1))) E1' := by
    rintro (a | a)
    · exact he' a
    · exact a.elim0
  have hE1 : IsOrd zPos E1 := fun z => he (Sum.inl z)
  have hPT := _root_.GlobalTheory.SymBridge.phiTopAgree_of_tie X.E X.K k P.1 (qOf P.1) ι σ₀ (psi0P Ch P.1) (chiP Ch P.1) s R.k S hT R.t (R.N (s + 1))
    (cOf R (s + 1)) (R.N R.m - 1) rfl hc hN E1' E1 hE1' hE1
  have hmat : fromCols (toLoc ι e e' y).toRows₁ 0 =
      toLoc ι E1 E1' (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1)))) := by
    ext z c
    rcases c with c | c
    · simp only [fromCols_apply_inl, toRows₁_apply, toLoc, LinearMap.comp_apply, prXp, LinearMap.funLeft_apply]
      have hs : LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))) (Pi.single (E1' (Sum.inl c)) 1) =
          Pi.single (e' c) 1 := by
        funext i
        simp [E1', Pi.single_apply, Fin.ext_iff]
      rw [hs]
      rfl
    · exact c.elim0
  have hkey : ∀ c' n' c n : ℕ, LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k R.rS R.r R.t R.m c' n' c n =
      LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k S.ρ (R.k + s + 1) R.t (s + 2) c' n' c n := by
    intro c' n' c n; rw [hρ, hr, hm]
  have hA' : (S.T (Fin R.t)).PhiTop (fromCols (toLoc ι e e' y).toRows₁ 0) =
      σ₀ (PhiTop Ch mu cst.sharp s P.1
        (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))))) := by
    rw [hmat, hPT, PhiTop, if_pos hA.mem, hA.sharp, if_pos rfl, hkey]
  simp only [Chain.xiTop]
  rw [one_mul, map_mul, hA', hB]

end GlobalTheory.SymBridge.LastStepProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralPositionOneEqFiniteSumStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingIntegral_positionOne_eq_finite_sum : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K]
    [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ) (σ₀ : K →+* ℂ) (ψ : AddChar k Circle) (ν : Measure k)
    (psi : E → K) (N : ℕ),
    GlobalTheory.SymBridge.IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → HasConductor ψ 1 → IsUnitVol ν →
    (∀ a, IntAt P ((q : E) ^ N * a) → (ψ (ι a) : ℂ) = σ₀ (psi a)) →
    ∀ (U' U : Type) [Fintype U'] [DecidableEq U'] [Fintype U] [DecidableEq U] (c n' c' n c₂ A B : ℕ),
      1 ≤ c → c' = c + 1 → c₂ = c → N ≤ A → N ≤ B →
    ∀ (d' : U' ≃ Fin n') (d : U ≃ Fin n) (e' : U' ⊕ Fin (c + 1) ≃ Fin (n' + c')) (e : U ⊕ Fin c ≃ Fin (n + c₂)),
      GlobalTheory.SymBridge.IsOrd (GlobalTheory.SymBridge.yPos (fun a => (d' a).val) n') e' →
      GlobalTheory.SymBridge.IsOrd (GlobalTheory.SymBridge.yPos (fun a => (d a).val) n) e →
    ∀ (Φ : Matrix (U ⊕ Fin c) (U' ⊕ Fin (c + 1)) k → ℂ) (ΦE : Loc.SF E K (n' + c') (n + c₂)) (C : ℂ),
      (∀ x, Φ (GlobalTheory.SymBridge.toLoc ι e e' x) = C * σ₀ (ΦE x)) →
      (∀ x, Φ x ≠ 0 → ∀ r s, valuation k (x r s) ≤ valuation k (((ϖ ^ N)⁻¹ : kˣ) : k)) →
      (∀ x y, (∀ r s, valuation k (y r s) ≤ valuation k ((ϖ : k) ^ N)) → Φ (x + y) = Φ x) →
      ∀ x₀, opE ψ ν 1 Φ (GlobalTheory.SymBridge.toLoc ι d d' x₀) =
        C * σ₀ (Loc.E1 (n' := n') (c' := c') (n := n) (c := c₂) psi (LocE.valsQ E q A B) (((q : K) ^ B)⁻¹) ΦE x₀) := by
  first | exact @GlobalTheory.UnfoldSumBd.sumAgreeBd | exact GlobalTheory.UnfoldSumBd.sumAgreeBd | (intros; apply GlobalTheory.UnfoldSumBd.sumAgreeBd <;> assumption)
end

