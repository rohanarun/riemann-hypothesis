module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0250
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0257
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0321
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedLevelStabilizerIffAllData
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem ramIff_all : ∀ D : D7, RamIff D := by
  intro D k _ _ _ _ p n _ _ S β P g hg φ
  letI := Fintype.ofFinite 𝓀[k]ˣ
  have rp : ∀ x (F : GA D S → ℂ), β.rep x F = rTrans (β.gl x) F := fun _ _ => rfl
  rw [finsum_eq_sum_of_fintype]
  constructor
  · rintro ⟨Φ, ⟨he, hr, hc⟩, rfl⟩
    refine ⟨hc P, fun x hx => ?_, ?_⟩
    · rw [← rp, ← he x P, hx]
    · rw [← (mem_Mram Φ).1 hr P]
      exact Finset.sum_congr rfl fun s _ => by rw [← rp, ← he, hg]
  · rintro ⟨hc, hs, h0⟩
    let v : levelVec β.rep P := ⟨φ, fun x hx => hs x hx⟩
    have hv : ∀ x : GL n k, formOf β.rep P v (x • P) = β.rep x φ := formOf_smul β.rep P v
    refine ⟨formOf β.rep P v, ⟨formOf_mem _ _ _, (mem_Mram _).2 fun Q => ?_, fun Q => ?_⟩, by simpa using hv 1⟩
    · obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) P Q
      have : ∀ s : 𝓀[k]ˣ, formOf β.rep P v (s • h • P) = β.rep h (rTrans (β.gl (g s)) φ) := by
        intro s
        rw [← smul_comm h s P, ← hg, smul_smul, hv, map_mul, Module.End.mul_apply, rp (g s)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_congr rfl fun s _ => this s, ← map_sum, h0, map_zero]
    · obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) P Q
      rw [hv, rp]
      exact ⟨fun γ hγ y => by simp only [rTrans]; rw [mul_assoc, hc.1 γ hγ], hc.2.comp (continuous_id.mul continuous_const)⟩

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalAdelicMatricesSelfAnnihilator
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GramAnnih

variable {D : D7} {m n : ℕ}

theorem pairing_rat (T : Matrix (Fin m) (Fin m) D.host.E) (ψ : AddChar (AF D.host.F) ℂ)
    (ξ : Matrix (Fin m) (Fin n) D.host.E) (x : Mx D m n) :
    GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ (GlobalTheory.MixModel.rat ξ) x =
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (GlobalTheory.MixModel.rat (ξᴴ * T) * x))) := by
  rw [rat_mul, rat_conjTranspose]
  rfl

theorem rat_single (j : Fin n) (i : Fin m) (e : D.host.E) :
    GlobalTheory.MixModel.rat (D := D) (Matrix.single j i e) = Matrix.single j i (incA D e) :=
  Matrix.map_single j i e (incA D)

theorem trace_tmul_half (t : AF D.host.F) :
    Algebra.trace (AF D.host.F) (AE D) (t ⊗ₜ[D.host.F] (2 : D.host.E)⁻¹) = t := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have e : (2 : D.host.E)⁻¹ = algebraMap D.host.F D.host.E 2⁻¹ := by rw [map_inv₀, map_ofNat]
  rw [e, GlobalTheory.LatVac.trace_tmul, Algebra.trace_algebraMap, D.sp.cm.deg2]
  simp

theorem ratMx_annihilator : ∀ (D : D7) (m n : ℕ) (T : Matrix (Fin m) (Fin m) D.host.E), IsHermND D.sp.cm.sig T → ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → (∀ x : Mx D m n, (∀ γ ∈ ratMx D m n, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ γ x = 1) ↔ x ∈ ratMx D m n) ∧ ∀ γ ∈ ratMx D m n, (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ γ x = 1) → γ = 0 := by
  intro D m n T hT ψ hψ
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have hU : IsUnit T.det := isUnit_iff_ne_zero.2 hT.2
  refine ⟨fun x => ⟨fun h => ?_, ?_⟩, ?_⟩
  · have key : ∀ i j (e : D.host.E), ψ (Algebra.trace (AF D.host.F) (AE D) (incA D e * x i j)) = 1 := by
      intro i j e
      have h1 := h _ (rat_mem (Matrix.single j i e * T⁻¹)ᴴ)
      rw [pairing_rat, Matrix.conjTranspose_conjTranspose, Matrix.nonsing_inv_mul_cancel_right _ _ hU, rat_single,
        Matrix.trace_single_mul, smul_eq_mul] at h1
      exact h1
    have hent : ∀ i j, ∃ e : D.host.E, x i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := fun i j =>
      GlobalTheory.RatAnnih.tensor_rat (x i j) fun e =>
        (GlobalTheory.SWQ.Annihilator.self_annihilator D.host.F inferInstance ψ hψ).2 _ fun c =>
          (congrArg ψ (GlobalTheory.RatAnnih.trace_mul_algebraMap (x i j) e c)).trans (key i j (c • e))
    choose M hM using hent
    exact ⟨Matrix.of M, Matrix.ext fun i j => (hM i j).symm⟩
  · rintro ⟨η, rfl⟩ _ ⟨ξ, rfl⟩
    change GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ (GlobalTheory.MixModel.rat ξ) (GlobalTheory.MixModel.rat η) = 1
    have e : Matrix.trace (GlobalTheory.MixModel.rat (D := D) (ξᴴ * T * η)) =
        (1 : AF D.host.F) ⊗ₜ[D.host.F] Matrix.trace (ξᴴ * T * η) :=
      (AddMonoidHom.map_trace (incA D) _).symm
    rw [pairing_rat, ← rat_mul, e, GlobalTheory.LatVac.trace_tmul, one_mul]
    exact hψ.2.2.1 _
  · rintro _ ⟨ξ, rfl⟩ h
    change GlobalTheory.MixModel.rat ξ = 0
    have hM : ξᴴ * T = 0 := by
      refine Matrix.ext fun j i => ?_
      by_contra ha
      replace ha : (ξᴴ * T) j i ≠ 0 := ha
      obtain ⟨t, ht⟩ := hψ.2.2.2
      have h1 : GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ (GlobalTheory.MixModel.rat ξ) _ = 1 :=
        h (Matrix.single i j (t ⊗ₜ[D.host.F] ((2 : D.host.E)⁻¹ * ((ξᴴ * T) j i)⁻¹)))
      have e : (t ⊗ₜ[D.host.F] ((2 : D.host.E)⁻¹ * ((ξᴴ * T) j i)⁻¹)) * GlobalTheory.MixModel.rat (D := D) (ξᴴ * T) j i =
          t ⊗ₜ[D.host.F] (2 : D.host.E)⁻¹ := by
        change _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] (ξᴴ * T) j i) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, inv_mul_cancel_right₀ ha]
      rw [pairing_rat, Matrix.trace_mul_comm, Matrix.trace_single_mul, smul_eq_mul, e, trace_tmul_half] at h1
      exact ht h1
    have h0 : ξᴴ = 0 := by
      rw [← Matrix.mul_nonsing_inv_cancel_right T ξᴴ hU, hM, Matrix.zero_mul]
    rw [Matrix.conjTranspose_eq_zero.1 h0, rat_zero]

end GlobalTheory.GramAnnih
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleLiftCombinationOfLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

variable {D : D7}

theorem sum_support_comb {Y Z G : Type*} [AddCommMonoid G] [Module ℂ G] (n : ℕ) (a : Fin n → Y →₀ ℂ)
    (b : Fin n → Y → Z →₀ ℂ) (R : Z → G) :
    ∑ z ∈ (∑ i, ∑ y ∈ (a i).support, a i y • b i y).support, (∑ i, ∑ y ∈ (a i).support, a i y • b i y) z • R z =
      ∑ i, ∑ y ∈ (a i).support, a i y • ∑ z ∈ (b i y).support, b i y z • R z := by
  change Finsupp.sum _ (fun z r => r • R z) = _
  rw [← Finsupp.sum_finsetSum_index (by simp) (by intros; exact add_smul _ _ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finsupp.sum_finsetSum_index (by simp) (by intros; exact add_smul _ _ _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finsupp.sum_smul_index' (by simp)]
  simp only [Finsupp.sum, Finset.smul_sum, smul_smul, smul_eq_mul]

theorem twoX_of_laws : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), BiAct D → CenFock D → LiftSum D → c.Is →
    (∀ s, (t s).Is) → RealEq t → KerX t → RdX t → TwoX t := by
  intro D c 𝒯 t hBi hCen hLS hc ht hreal hker hrd
  intro j hj C hC y
  have hj0 : j < D.R.m := by omega
  have hj1 : j + 1 < D.R.m := by omega
  obtain ⟨χ, hχ⟩ := hrd j (by omega)
  have step1 : ∃ (n : ℕ) (P : Fin n → PolF D (c.X (j + 1)).rank (c.X j).rank)
      (P' : Fin n → PolF D (c.X (j + 1 + 1)).rank (c.X (j + 1)).rank), ∀ s, ∀ ψ ∈ (t s).Ram j, ∀ β,
        (t s).two j (fun α => (t s).rd j α ψ y) C β = ∑ i, ∑ γ,
          ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (∑ α, ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) := by
    by_cases hex : ∃ (s : 𝒯) (_ : (t s).Ch j) (γ : (t s).Ch (j + 1)) (_ : (t s).Ch (j + 1 + 1)), True
    · obtain ⟨s₀, α₀, γ₀, β₀, -⟩ := hex
      obtain ⟨n, P, P', hF⟩ := _root_.GlobalTheory.SeeSaw.fockRed_uniform D hBi hCen hLS c.ψ c.θ hc.inf (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))
        (c.x j) (c.x (j + 1)) (c.x (j + 1 + 1)) (hc.x j (by omega)) (hc.x (j + 1) (by omega)) (hc.x (j + 1 + 1) (by omega))
        ((t s₀).ker j α₀ γ₀) ((t s₀).ker (j + 1) γ₀ β₀) ((ht s₀).ker j hj0 α₀ γ₀) ((ht s₀).ker (j + 1) hj1 γ₀ β₀) χ C hC.1 hC.2
      refine ⟨n, P, P', fun s ψ hψ β => ?_⟩
      have hrdψ := fun α => hχ s ψ hψ α y
      have e1 : ∀ α γ, biLift ((t s).kom j) ((t s).kom (j + 1)) (c.x j).vol (c.x (j + 1)).vol ((t s).rd j α ψ y)
          (biComb c.ψ _ _ _ ((t s).dd j α γ) ((t s).dd (j + 1) γ β) C) =
          ∑ i, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) := fun α γ =>
        hF ((t s).ker j α γ) ((t s).ker (j + 1) γ β) ((ht s).ker j hj0 α γ) ((ht s).ker (j + 1) hj1 γ β) rfl rfl
          (fun a ha b hb f hf => hreal j hj0 s s₀ a ha b hb f hf)
          (fun a ha b hb f hf => hreal (j + 1) hj1 s s₀ a ha b hb f hf) _ (hrdψ α).1 (hrdψ α).2
      have e2 : ∀ i γ, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (∑ α, ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) =
          ∑ α, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) := by
        intro i γ
        have h := (hLS c.ψ c.θ hc.inf _ _ (c.x (j + 1)) (c.x (j + 1 + 1)) (hc.x _ (by omega)) (hc.x _ (by omega)) _
          ((ht s).ker (j + 1) hj1 γ β) (P' i)).2.2 ((t s).Ch j) Finset.univ (fun _ => 1)
          (fun α => ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y))
          (fun α _ => (hLS c.ψ c.θ hc.inf _ _ (c.x j) (c.x (j + 1)) (hc.x _ (by omega)) (hc.x _ (by omega)) _
            ((ht s).ker j hj0 α γ) (P i)).2.1 _ (hrdψ α).1)
        simpa using h
      simp only [Tup.two, e1, e2]
      rw [Finset.sum_comm]
      calc _ = ∑ γ, ∑ i, ∑ α, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) :=
            Finset.sum_congr rfl fun γ _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    · push Not at hex
      refine ⟨0, Fin.elim0, Fin.elim0, fun s ψ _ β => ?_⟩
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      refine Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun γ _ => ?_
      exact ((hex s α γ β).elim)
  obtain ⟨n, P, P', hstep⟩ := step1
  choose a ha using fun i : Fin n => hker j hj0 y (P i)
  choose b hb using fun (i : Fin n) (y' : c.Fr (j + 1)) => hker (j + 1) hj1 y' (P' i)
  obtain ⟨χ', hχ'⟩ := hrd (j + 1) (by omega)
  refine ⟨∑ i, ∑ y' ∈ (a i).support, a i y' • b i y', fun s ψ hψ β => ?_⟩
  rw [hstep s ψ hψ β, sum_support_comb]
  have hKψ := (ht s).stabK j hj0 ψ hψ
  have e3 : ∀ i γ, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
        (∑ α, ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) =
      ∑ y' ∈ (a i).support, ((t s).cK j * a i y') • ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1))
        (P' i) ((t s).rd (j + 1) γ ((t s).K j ψ) y') := by
    intro i γ
    rw [ha i s ψ hψ γ, Finset.smul_sum]
    simp only [smul_smul]
    exact (hLS c.ψ c.θ hc.inf _ _ (c.x (j + 1)) (c.x (j + 1 + 1)) (hc.x _ (by omega)) (hc.x _ (by omega)) _
      ((ht s).ker (j + 1) hj1 γ β) (P' i)).2.2 _ _ _ _ (fun y' _ => (hχ' s _ hKψ γ y').1)
  simp only [e3]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [← Finset.smul_sum, hb i y' s _ hKψ β, smul_smul, smul_smul]
  congr 1
  ring

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.LeftInvSect
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model
variable {D : D7} {n : ℕ}

theorem rat_mat {γ : G D n} (h : γ ∈ GF D n) :
    ∃ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) := by
  obtain ⟨x, -, hx⟩ := h
  exact ⟨x.1, (congrArg Units.val hx).symm⟩

theorem det_rat {γ : G D n} (h : γ ∈ GF D n) (a : GL (Fin n) (AE D)) (ha : blkA (mat γ) = a.1) :
    ∃ u : D.host.Eˣ, Matrix.GeneralLinearGroup.det a = Units.map (incA D).toMonoidHom u := by
  haveI : Nontrivial (AF D.host.F) := inferInstanceAs (Nontrivial (Ainf D.host.F × Af D.host.F))
  haveI : Nontrivial (AE D) := inferInstance
  obtain ⟨x, hx⟩ := rat_mat h
  have e : ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) = incA D (blkA x).det := by
    rw [RingHom.map_det]
    change a.1.det = _
    rw [← ha, hx]; rfl
  have h0 : (blkA x).det ≠ 0 := fun h0 => Units.ne_zero _ (e.trans (by rw [h0, map_zero]))
  exact ⟨Units.mk0 _ h0, Units.ext e⟩

theorem siegelParabolicUnn_matrix_blockUpperTriangular {p : G D n} (hp : p ∈ P D n) : ∃ b d, mat p = blk4 (blkA (mat p)) b 0 d := by
  refine ⟨((mat p).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    ((mat p).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · rfl
  · exact lower_eq_zero hp i j
  · rfl

theorem mat_inj {g h : G D n} (e : mat g = mat h) : g = h := Subtype.ext (Units.ext e)

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : G D n) = 1 := rfl

theorem levi_mul_inv (a : GL (Fin n) (AE D)) :
    (blk4 a.1 0 0 (adj (a⁻¹).1) : Mx D (n + n) (n + n)) * blk4 (a⁻¹).1 0 0 (adj a.1) = 1 := by
  have h2 : (adj (a⁻¹).1 : Mx D n n) * adj a.1 = 1 := by rw [← adj_mul]; simp [adj_one]
  simp [submatrix_fromBlocks_mul, h2, block_matrix_one, -Matrix.coe_units_inv]

theorem exists_levi_unip {p : G D n} (hp : p ∈ P D n) (a : GL (Fin n) (AE D)) (ha' : blkA (mat p) = a.1) :
    ∃ (m u : G D n) (b : Mx D n n), p = m * u ∧ mat m = blk4 a.1 0 0 (adj (a⁻¹).1) ∧ mat u = blk4 1 b 0 1 := by
  obtain ⟨m, hm⟩ := exists_levi a
  obtain ⟨m', hm'⟩ := exists_levi a⁻¹
  obtain ⟨b, d, hb⟩ := siegelParabolicUnn_matrix_blockUpperTriangular hp
  rw [ha'] at hb
  rw [inv_inv] at hm'
  have hu : mat (m' * p) = blk4 1 ((a⁻¹).1 * b) 0 (adj a.1 * d) := by
    rw [mat_mul, hm', hb, submatrix_fromBlocks_mul]
    simp [-Matrix.coe_units_inv]
  have hd : (adj a.1 : Mx D n n) * d = 1 := by
    have h : adj (mat (m' * p)) * JR (AF D.host.F) (Jst D n) * mat (m' * p) = JR (AF D.host.F) (Jst D n) := (m' * p).2
    rw [JR_Jst, hu] at h
    generalize (adj a.1 : Mx D n n) * d = d' at h ⊢
    generalize (a⁻¹).1 * b = b' at h
    simp only [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, adj_one, adj_zero, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, mul_neg,
      neg_mul, neg_zero] at h
    exact (blockMatrixTwoByTwoFin_injective h).2.1
  have hmm : m * m' = 1 := mat_inj (by rw [mat_mul, mat_one, hm, hm', levi_mul_inv])
  refine ⟨m, m' * p, (a⁻¹).1 * b, by rw [← mul_assoc, hmm, one_mul], hm, by rw [hu, hd]⟩

theorem exists_blkA {p : G D n} (hp : p ∈ P D n) : ∃ a : GL (Fin n) (AE D), blkA (mat p) = a.1 :=
  ⟨levi (D := D) (n := n) ⟨p, hp⟩, rfl⟩

theorem height_inv (hI : ∀ g : G D n, ∃ p ∈ P D n, ∃ k ∈ K D n, g = p * k) {H : G D n → ℝ≥0} (hH : IsHeight H)
    {γ : G D n} (hp : γ ∈ P D n) (a : GL (Fin n) (AE D)) (ha : blkA (mat γ) = a.1)
    (h1 : absA D (Matrix.GeneralLinearGroup.det a) = 1) (g : G D n) : H (γ * g) = H g := by
  obtain ⟨p, hp', k, hk, rfl⟩ := hI g
  obtain ⟨c, hc⟩ := exists_blkA hp'
  have e : blkA (mat (γ * p)) = (a * c).1 := by rw [blkA_mul hp', ha, hc, Units.val_mul]
  rw [← mul_assoc, hH _ ((P D n).mul_mem hp hp') (a * c) e k hk, hH p hp' c hc k hk, map_mul, map_mul, h1, one_mul]

theorem leftInv_sect : ∀ (D : D7) (n : ℕ), (∀ g : GlobalTheory.StdUnn.G D n, ∃ p ∈ GlobalTheory.StdUnn.P D n, ∃ k ∈ GlobalTheory.StdUnn.K D n, g = p * k) → ∀ (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : GlobalTheory.StdUnn.G D n →* Module.End ℂ (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ V.rank n)), IsHeckeChar D χ → GlobalTheory.StdUnn.IsWeilSch ψ χ θ V μ ω → ∀ H : GlobalTheory.StdUnn.G D n → ℝ≥0, GlobalTheory.StdUnn.IsHeight H → ∀ (Φ : GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ V.rank n) (z : ℂ), GlobalTheory.AutomorphicL2Unitary.LeftInv (GlobalTheory.StdUnn.P D n ⊓ GlobalTheory.StdUnn.GF D n) (GlobalTheory.StdUnn.sect ω H Φ z) := by
  intro D n hI V ψ χ θ μ ω hχ hω H hH Φ z γ hγ g
  obtain ⟨hp, hr⟩ := Subgroup.mem_inf.1 hγ
  obtain ⟨a, ha⟩ := exists_blkA hp
  obtain ⟨u, hu⟩ := det_rat hr a ha
  have h1 : absA D (Matrix.GeneralLinearGroup.det a) = 1 := by
    rw [hu]; exact absE_inclR u
  have h2 : χ (Matrix.GeneralLinearGroup.det a) = 1 := by
    rw [hu]; exact hχ.2 u
  have hHe : H (γ * g) = H g := height_inv hI hH hp a ha h1 g
  have hW : (ω (γ * g) Φ).1 0 = (ω g Φ).1 0 := by
    obtain ⟨m, v, b, e, hm, hv⟩ := exists_levi_unip hp a ha
    have e' : ω (γ * g) Φ = ω m (ω v (ω g Φ)) := by
      rw [e, map_mul, map_mul]; rfl
    have z1 : ∀ a : Mx D n n, ((0 : Mx D V.rank n) ⬝ a : Mx D V.rank n) = 0 := fun a => Matrix.zero_mul a
    have z2 : StdUnn.inner V (0 : Mx D V.rank n) 0 = 0 := by rw [StdUnn.inner, adj_zero, Matrix.zero_mul]
    rw [e', hω.levi m _ hm, h1, h2, z1, hω.unip v b hv, z2]
    simp [halfTr, npow]
  simp only [sect, hHe, hW]

end GlobalTheory.StdUnn.LeftInvSect
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentVacuumHyperspecialDictionary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)

namespace GlobalTheory.PlaceDict

theorem conjP_eq_conjPl (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ P = Formalism.DivisionValues.conjPl P := by
  apply HeightOneSpectrum.ext
  ext x
  show Formalism.L2.Col.cO _ x ∈ P.asIdeal ↔ x ∈ Ideal.map (Formalism.DivisionValues.cO D.host.E) P.asIdeal
  rw [← Ideal.comap_symm, Ideal.mem_comap]
  have : (Formalism.DivisionValues.cO D.host.E).symm x = Formalism.L2.Col.cO _ x := by
    apply RingOfIntegers.ext
    simp [Formalism.DivisionValues.cO, Formalism.L2.Col.cO]
    rfl
  rw [this]

theorem isSplit_iff_conjPl_ne (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hvw : w.under (𝓞 D.host.F) = v) : IsSplit (E := D.host.E) v ↔ Formalism.DivisionValues.conjPl w ≠ w := by
  have hu : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) = v ↔
      Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) Q.asIdeal = v.asIdeal := fun Q =>
    ⟨fun h => congrArg HeightOneSpectrum.asIdeal h, fun h => HeightOneSpectrum.ext h⟩
  constructor
  · rintro ⟨P, Q, hPQ, hP, hQ⟩ hc
    have hP' := (hu P).2 hP
    have hQ' := (hu Q).2 hQ
    have key : ∀ R : HeightOneSpectrum (𝓞 D.host.E), R.under (𝓞 D.host.F) = v → R = w := fun R hR => by
      rcases GlobalTheory.GridPlaces.eq_or_eq_conjP (P := w) (Q := R) (by rw [hR, hvw]) with h | h
      · exact h
      · rw [h, conjP_eq_conjPl, hc]
    exact hPQ ((key P hP').trans (key Q hQ').symm)
  · intro hne
    refine ⟨w, Formalism.DivisionValues.conjPl w, hne.symm, (hu w).1 hvw, (hu _).1 ?_⟩
    rw [← conjP_eq_conjPl, GlobalTheory.GridPlaces.under_conjP, hvw]

theorem dictionary : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → (IsSplit (E := D.host.E) v ↔ Formalism.DivisionValues.conjPl w ≠ w) ∧ (∀ χ : (AE D)ˣ →* Circle, (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χ w') → UnrPl w χ) ∧ (∀ (V : HSp D) (g : GA D V), g ∈ GlobalTheory.Hk3.hyp V w ↔ ∃ k ∈ Kv V v, g = embV V v k) ∧ (∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ), VacFin ψ S T v f → IsVacAt ψ S T w f) ∧ (IsSplit (E := D.host.E) v → ∀ χ : (AE D)ˣ →* Circle, UnrAt χ w → ∃ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ), Formalism.L2.NTheta.IsIdemAt e w ∧ ϖ ∈ w.asIdeal ∧ ϖ ∉ w.asIdeal ^ 2 ∧ (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) ∧ ∀ χ' : (AE D)ˣ →* Circle, UnrAt χ' w → ((χ' x : Circle) : ℂ) = ((val (F := D.host.F) χ' w : ℂˣ) : ℂ)) := by
  intro D v w hvw
  refine ⟨isSplit_iff_conjPl_ne D v w hvw, _root_.GlobalTheory.UnrPlDict.unrPl_of_unrAt D v w hvw, _root_.GlobalTheory.HypDict.mem_hyp_iff_embV D v w hvw, fun ψ S T f hf => ?_, GlobalTheory.T.splitPlace_uniformiserIdele_value_unramifiedChar D v w hvw⟩
  by_cases hc : Formalism.DivisionValues.conjPl w = w
  · exact _root_.GlobalTheory.VacInertAt.isVacAt_of_vacFin D v w hvw hc ψ S T f hf
  · exact _root_.GlobalTheory.VacSplit.isVacAt_of_vacFin D v w hvw hc ψ S T f hf

end GlobalTheory.PlaceDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageWittIndexLtAndPlacesTwoSplitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStage_wittIndex_lt_and_places_two_split : ∀ (D : D7) (c : Com D) (j : ℕ) (s : PiLocalization₂ D), j ≤ D.R.m → s.Is c j → GlobalTheory.Cusp.wittIndex s.V < D.R.t ∧ ∀ v : HeightOneSpectrum (𝓞 D.host.F), (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.ChainOnto.WittTwo.wittIndex_lt_and_two_split | exact GlobalTheory.ChainOnto.WittTwo.wittIndex_lt_and_two_split | (intros; apply GlobalTheory.ChainOnto.WittTwo.wittIndex_lt_and_two_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaPairAnalyticHypothesesOfDiscreteSeries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairLift

theorem inputs_of_chosenSeries :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
      GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (X : ProvA), ChosenSeries X → Inputs D X := by
  intro hDS hHC hDec hCW D X hX
  exact
    { chosen := hX
      hc := hHC
      decay := hDec
      bridge := GlobalTheory.CoverModel.modelsAreCoverSeries_all hDS hHC D
      vacChar := GlobalTheory.VacuumCharacter.vacChar D
      lie := GlobalTheory.LieScalar.lieFockAll D
      cpt := GlobalTheory.CompactFockAction.compactFockAll D
      dense := GlobalTheory.FockDensity.fockDense D
      laws := GlobalTheory.Chain.LiftReg.liftProps_obj hDec D
      const := _root_.GlobalTheory.TowerConstTermObj.towerConstTerm D
      ext := _root_.GlobalTheory.GKExtensionToSmoothVectors.gkExtension hHC hCW D }

end GlobalTheory.PairLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeParahoricEntriesEqColumnDataStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPrime_parahoricEntries_eq_columnData : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → EntryAgree Ch sel mu cst σ₀ P ι s W ν L := by
  first | exact @GlobalTheory.EntryAtTwist.entryAgree | exact GlobalTheory.EntryAtTwist.entryAgree | (intros; apply GlobalTheory.EntryAtTwist.entryAgree <;> assumption)
end

