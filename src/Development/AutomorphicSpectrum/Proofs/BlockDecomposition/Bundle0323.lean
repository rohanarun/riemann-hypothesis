module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import GroundTheory.AutomorphicForms.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0300
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0302
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0313
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RefinedBlockOrderCompat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0293
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0315
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0317

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivGaussianExponentialAtZero
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.DilFam

variable {m n : ℕ}

def pt (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) : Fin m × Fin n × Bool → ℂ :=
  fun k => (if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1) * Complex.exp (z * X k.2.1)

def Fam (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (P : PositivityTheory.Rg.Sw.PX m n) (z : ℂ) : ℂ :=
  Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * MvPolynomial.eval (pt X v z) P *
    Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))

theorem hasDerivAt_pt (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) (k : Fin m × Fin n × Bool) :
    HasDerivAt (fun w => pt X v w k) ((X k.2.1 : ℂ) * pt X v z k) z := by
  have h : HasDerivAt (fun w : ℂ => w * (X k.2.1 : ℂ)) (X k.2.1 : ℂ) z := by
    simpa using (hasDerivAt_id z).mul_const (X k.2.1 : ℂ)
  refine ((h.cexp).const_mul (if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1)).congr_deriv ?_
  rw [show GlobalTheory.CompanionTheory.DilFam.pt X v z k =
      (if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1) * Complex.exp (z * X k.2.1) from rfl]
  ring

theorem hasDerivAt_eval {σ : Type*} [Fintype σ] (x : ℂ → σ → ℂ) (x' : σ → ℂ) (z : ℂ)
    (hx : ∀ k, HasDerivAt (fun w => x w k) (x' k) z) (P : MvPolynomial σ ℂ) :
    HasDerivAt (fun w => MvPolynomial.eval (x w) P)
      (∑ k, x' k * MvPolynomial.eval (x z) (MvPolynomial.pderiv k P)) z := by
  classical
  induction P using MvPolynomial.induction_on
  next a =>
    simp only [MvPolynomial.eval_C, MvPolynomial.pderiv_C, map_zero, mul_zero, Finset.sum_const_zero]
    exact hasDerivAt_const z a
  next p q hp hq =>
    simp only [map_add (f := _), mul_add, Finset.sum_add_distrib]
    exact hp.add hq
  next p i hp =>
    have hX : ∀ k, MvPolynomial.eval (x z) (MvPolynomial.pderiv k (MvPolynomial.X i : MvPolynomial σ ℂ)) =
        if k = i then 1 else 0 := by
      intro k
      by_cases h : k = i
      · subst h
        simp [MvPolynomial.pderiv_X_self]
      · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm h), map_zero, if_neg h]
    have hf : (fun w => MvPolynomial.eval (x w) (p * MvPolynomial.X i)) =
        fun w => MvPolynomial.eval (x w) p * x w i := by
      funext w
      simp only [map_mul, MvPolynomial.eval_X]
    rw [hf]
    refine (hp.mul (hx i)).congr_deriv ?_
    symm
    have hs : ∀ k, x' k * MvPolynomial.eval (x z) (MvPolynomial.pderiv k (p * MvPolynomial.X i)) =
        x' k * MvPolynomial.eval (x z) (MvPolynomial.pderiv k p) * x z i +
          (if k = i then x' k else 0) * MvPolynomial.eval (x z) p := by
      intro k
      rw [MvPolynomial.pderiv_mul, map_add (f := _), map_mul, map_mul, MvPolynomial.eval_X, hX k]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun k _ => hs k), Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring

theorem pt_mul (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) (a : Fin m) (j : Fin n) :
    pt X v z (a, j, false) * pt X v z (a, j, true) =
      Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ) := by
  show v a j * Complex.exp (z * ((X j : ℝ) : ℂ)) * (star (v a j) * Complex.exp (z * ((X j : ℝ) : ℂ))) = _
  rw [show (2 * z * ((X j : ℝ) : ℂ)) = z * X j + z * X j by ring, Complex.exp_add]
  rw [show ((‖v a j‖ ^ 2 : ℝ) : ℂ) = v a j * star (v a j) by
    rw [Complex.star_def, Complex.mul_conj']; norm_cast]
  ring

theorem sum_pt (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) (f : Fin m × Fin n × Bool → ℂ) :
    ∑ k, (X k.2.1 : ℂ) * pt X v z k * f k =
      ∑ j, (X j : ℂ) * ∑ a, (pt X v z (a, j, false) * f (a, j, false) +
        pt X v z (a, j, true) * f (a, j, true)) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem eval_dil (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) (P : PositivityTheory.Rg.Sw.PX m n) :
    MvPolynomial.eval (pt X v z) (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) =
      (m : ℂ) * (∑ j, (X j : ℂ)) * MvPolynomial.eval (pt X v z) P +
      (∑ k, (X k.2.1 : ℂ) * pt X v z k * MvPolynomial.eval (pt X v z) (MvPolynomial.pderiv k P)) +
      (-(4 * Real.pi : ℂ)) * (∑ a, ∑ j, (X j : ℂ) * (Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))) *
        MvPolynomial.eval (pt X v z) P := by
  have hA : MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) =
      ∑ j, (X j : ℂ) * ((m : ℂ) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P +
        ∑ a, (GlobalTheory.CompanionTheory.DilFam.pt X v z (a, j, false) *
            MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) (MvPolynomial.pderiv (a, j, false) P) +
          GlobalTheory.CompanionTheory.DilFam.pt X v z (a, j, true) *
            MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) (MvPolynomial.pderiv (a, j, true) P) -
          2 * ((2 * Real.pi : ℝ) : ℂ) * (GlobalTheory.CompanionTheory.DilFam.pt X v z (a, j, false) *
            GlobalTheory.CompanionTheory.DilFam.pt X v z (a, j, true) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [PositivityTheory.Rg.Sw.dil, Finset.sum_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, LinearMap.id_apply, Derivation.coeFn_coe, map_sum, map_add, map_sub,
      MvPolynomial.smul_eval, map_mul, MvPolynomial.eval_X]
  rw [hA, GlobalTheory.CompanionTheory.DilFam.sum_pt X v z
    (fun k => MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) (MvPolynomial.pderiv k P))]
  simp only [GlobalTheory.CompanionTheory.DilFam.pt_mul]
  have h1 : (m : ℂ) * (∑ j, (X j : ℂ)) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P =
      ∑ j, (X j : ℂ) * ((m : ℂ) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h3 : (-(4 * Real.pi : ℂ)) * (∑ a, ∑ j, (X j : ℂ) * (Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))) *
        MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P =
      ∑ j, (X j : ℂ) * -(∑ a, 2 * ((2 * Real.pi : ℝ) : ℂ) *
        (Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P)) := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    push_cast
    ring
  rw [h1, h3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_sub_distrib]
  ring

theorem hasDerivAt_gauss (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * w * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))
      (Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) *
        ((-(4 * Real.pi : ℂ)) * ∑ a, ∑ j, (X j : ℂ) * (Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) z := by
  have hin : HasDerivAt
      (fun w : ℂ => -(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * w * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))
      (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * (2 * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) z := by
    apply HasDerivAt.const_mul
    apply HasDerivAt.fun_sum
    intro a _
    apply HasDerivAt.fun_sum
    intro j _
    apply HasDerivAt.mul_const
    have h : HasDerivAt (fun w : ℂ => 2 * w * (X j : ℂ)) (2 * X j) z := by
      simpa using ((hasDerivAt_id z).const_mul (2 : ℂ)).mul_const (X j : ℂ)
    exact h.cexp
  convert hin.cexp using 1
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hasDerivAt_Fam (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (P : PositivityTheory.Rg.Sw.PX m n) (z : ℂ) :
    HasDerivAt (Fam X v P) (Fam X v (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) z) z := by
  have he : HasDerivAt (fun w : ℂ => Complex.exp ((m : ℂ) * w * ∑ j, (X j : ℂ)))
      (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * ((m : ℂ) * ∑ j, (X j : ℂ))) z := by
    have h : HasDerivAt (fun w : ℂ => (m : ℂ) * w * ∑ j, (X j : ℂ)) ((m : ℂ) * ∑ j, (X j : ℂ)) z := by
      simpa using ((hasDerivAt_id z).const_mul (m : ℂ)).mul_const (∑ j, (X j : ℂ))
    exact h.cexp
  have hp := GlobalTheory.CompanionTheory.DilFam.hasDerivAt_eval (GlobalTheory.CompanionTheory.DilFam.pt X v)
    (fun k => (X k.2.1 : ℂ) * GlobalTheory.CompanionTheory.DilFam.pt X v z k) z (GlobalTheory.CompanionTheory.DilFam.hasDerivAt_pt X v z) P
  have hg := GlobalTheory.CompanionTheory.DilFam.hasDerivAt_gauss X v z
  have h := (he.mul hp).mul hg
  refine h.congr_deriv ?_
  rw [show GlobalTheory.CompanionTheory.DilFam.Fam X v (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) z =
      Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) *
        MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) *
        Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) from rfl,
    GlobalTheory.CompanionTheory.DilFam.eval_dil]
  simp only [Pi.mul_apply]
  ring

theorem Fam_one (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) :
    Fam X v 1 = fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) *
      Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))) := by
  funext z
  simp only [GlobalTheory.CompanionTheory.DilFam.Fam, map_one, mul_one]

theorem Fam_zero (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (P : PositivityTheory.Rg.Sw.PX m n) :
    Fam X v P 0 = PositivityTheory.Rg.Sw.evX P v * PositivityTheory.Rg.Sw.gs (2 * Real.pi) v := by
  have hD : GlobalTheory.CompanionTheory.DilFam.pt X v 0 = fun k => if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1 := by
    funext k
    simp only [GlobalTheory.CompanionTheory.DilFam.pt, zero_mul, Complex.exp_zero, mul_one]
  simp only [GlobalTheory.CompanionTheory.DilFam.Fam, PositivityTheory.Rg.Sw.evX, PositivityTheory.Rg.Sw.gs, hD, mul_zero,
    zero_mul, Complex.exp_zero, one_mul]
  congr 1
  congr 1
  push_cast
  ring

theorem iteratedDeriv_Fam (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (r : ℕ) (P : PositivityTheory.Rg.Sw.PX m n) :
    iteratedDeriv r (Fam X v P) = Fam X v ((PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X ^ r) P) := by
  induction r generalizing P with
  | zero => rw [iteratedDeriv_zero, pow_zero, Module.End.one_apply]
  | succ r ih =>
    have hd : deriv (GlobalTheory.CompanionTheory.DilFam.Fam X v P) =
        GlobalTheory.CompanionTheory.DilFam.Fam X v (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) := by
      funext z
      exact (GlobalTheory.CompanionTheory.DilFam.hasDerivAt_Fam X v P z).deriv
    rw [iteratedDeriv_succ', hd, ih, pow_succ, Module.End.mul_apply]

theorem main : ∀ (m n : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ), Differentiable ℂ (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) ∧ ∀ r : ℕ, iteratedDeriv r (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 = PositivityTheory.Rg.Sw.evX ((PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X ^ r) 1) v * PositivityTheory.Rg.Sw.gs (2 * Real.pi) v := by
  intro m n X v
  rw [← GlobalTheory.CompanionTheory.DilFam.Fam_one X v]
  refine ⟨fun z => (GlobalTheory.CompanionTheory.DilFam.hasDerivAt_Fam X v 1 z).differentiableAt, fun r => ?_⟩
  rw [GlobalTheory.CompanionTheory.DilFam.iteratedDeriv_Fam, GlobalTheory.CompanionTheory.DilFam.Fam_zero]

end GlobalTheory.CompanionTheory.DilFam
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIntersectionConjugate
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

noncomputable section

namespace GlobalTheory.CompanionTheory.GeomCell

open GroundTheory.Automorphic.Parabolic (leviPar normLeviParSqrtModular normLeviParInvSqrtModular innerJacquetSpace leviUnipotent cellLeviSubIncl cellInnerHom leviInfIncl levJacquetAction innerJacquetRep)

theorem nonempty_indRep_comp_equiv {G L : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group L] [TopologicalSpace L] [IsTopologicalGroup L] (Φ : L ≃* G) (hΦ : Continuous Φ)
    (hΦ' : Continuous Φ.symm) (H : Subgroup G) (P : Subgroup L) (hHP : ∀ p, p ∈ P ↔ Φ p ∈ H)
    {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (σ : Representation ℂ H V) (τ : Representation ℂ P V') (T : V ≃ₗ[ℂ] V')
    (hT : ∀ (p : P) (v : V), T (σ ⟨Φ p, (hHP p.1).1 p.2⟩ v) = τ p (T v)) :
    Nonempty (Representation.Equiv ((indRep H σ).comp Φ.toMonoidHom) (GlobalTheory.PRep.smInd P τ)) := by
  have hTs : ∀ (p : P) (v : V'), T.symm (τ p v) = σ ⟨Φ p, (hHP p.1).1 p.2⟩ (T.symm v) := by
    intro p v
    apply T.injective
    rw [hT, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let A : GroundTheory.Automorphic.indSpace H σ ≃ₗ[ℂ] GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind P τ) :=
    { toFun := fun φ => ⟨⟨fun l => T ((φ : G → V) (Φ l)), fun p x => by
          obtain ⟨h1, -⟩ := GroundTheory.Automorphic.mem_indSpace.1 φ.2
          have := h1 ⟨Φ p, (hHP p.1).1 p.2⟩ (Φ x)
          show T ((φ : G → V) (Φ (p * x))) = _
          rw [map_mul]
          exact (congrArg T this).trans (hT p _)⟩, by
          obtain ⟨-, K, hK, hKφ⟩ := GroundTheory.Automorphic.mem_indSpace.1 φ.2
          refine mem_smoothPart_of_nhds (Filter.mem_of_superset
            ((hK.preimage hΦ).mem_nhds (by simp [one_mem])) fun l hl => ?_)
          apply Subtype.ext
          funext x
          show T ((φ : G → V) (Φ (x * l))) = T ((φ : G → V) (Φ x))
          rw [map_mul, hKφ _ hl]⟩
      invFun := fun ψ => ⟨fun x => T.symm (ψ.1.1 (Φ.symm x)), by
          refine GroundTheory.Automorphic.mem_indSpace.2 ⟨fun h x => ?_, ?_⟩
          · have hp : Φ.symm h ∈ P := (hHP _).2 (by simp)
            have h1 := ψ.1.2 ⟨Φ.symm h, hp⟩ (Φ.symm x)
            have h2 : Φ.symm ((h : G) * x) = Φ.symm h * Φ.symm x := map_mul _ _ _
            show T.symm (ψ.1.1 (Φ.symm ((h : G) * x))) = σ h (T.symm (ψ.1.1 (Φ.symm x)))
            rw [h2]
            refine (congrArg T.symm h1).trans ((hTs _ _).trans ?_)
            congr 2
            exact Subtype.ext (by simp)
          · let S : Subgroup L :=
              { carrier := {l | GlobalTheory.PRep.ind P τ l ψ.1 = ψ.1}
                mul_mem' := by
                  intro a b ha hb
                  simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
                  rw [hb, ha]
                one_mem' := by simp
                inv_mem' := by
                  intro a ha
                  simp only [Set.mem_ofPred_eq] at *
                  conv_lhs => rw [← ha]
                  rw [← Module.End.mul_apply, ← map_mul]
                  simp }
            refine ⟨S.comap Φ.symm.toMonoidHom, ?_, fun g hg x => ?_⟩
            · exact IsOpen.preimage hΦ' ψ.2
            · have h3 : GlobalTheory.PRep.ind P τ (Φ.symm g) ψ.1 = ψ.1 := hg
              have h4 := congrFun (congrArg Subtype.val h3) (Φ.symm x)
              have h5 : Φ.symm (x * g) = Φ.symm x * Φ.symm g := map_mul _ _ _
              show T.symm (ψ.1.1 (Φ.symm (x * g))) = T.symm (ψ.1.1 (Φ.symm x))
              rw [h5]
              exact congrArg T.symm h4⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (funext fun l => map_add T _ _))
      map_smul' := fun c a => Subtype.ext (Subtype.ext (funext fun l => map_smul T _ _))
      left_inv := fun a => Subtype.ext (funext fun x => by simp)
      right_inv := fun a => Subtype.ext (Subtype.ext (funext fun x => by simp)) }
  refine ⟨.mk A fun l => ?_⟩
  refine LinearMap.ext fun a => Subtype.ext (Subtype.ext (funext fun x => ?_))
  show T ((a : G → V) (Φ x * Φ l)) = T ((a : G → V) (Φ (x * l)))
  rw [map_mul]

def coinvEquiv {M G W : Type} [Group M] [Group G] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ M W) (φ : M ≃* G) (U : Subgroup M) (U' : Subgroup G)
    (hU : ∀ u, u ∈ U ↔ φ u ∈ U') :
    Representation.Coinvariants ((ρ.comp φ.symm.toMonoidHom).comp U'.subtype) ≃ₗ[ℂ]
      GlobalTheory.PRep.Jacquet ρ U :=
  Submodule.quotEquivOfEq _ _ (by
    refine congrArg (Submodule.span ℂ) (Set.ext fun y => ⟨?_, ?_⟩)
    · rintro ⟨⟨u', v⟩, rfl⟩
      have hu : φ.symm (u' : G) ∈ U := (hU _).2 (by simp)
      exact ⟨⟨_, hu⟩, v, by simp⟩
    · rintro ⟨u, v, rfl⟩
      exact ⟨⟨⟨φ u, (hU _).1 u.2⟩, v⟩, by simp⟩)

theorem coinvEquiv_mk {M G W : Type} [Group M] [Group G] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ M W) (φ : M ≃* G) (U : Subgroup M) (U' : Subgroup G)
    (hU : ∀ u, u ∈ U ↔ φ u ∈ U') (x : W) :
    coinvEquiv ρ φ U U' hU (Representation.Coinvariants.mk _ x) = Submodule.Quotient.mk x := rfl

section
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ}
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
  {c : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]

theorem relProj_relEmb (f : ∀ i, (Σ j, c i j) ≃ m i) (q : ∀ i, Levi k (c i))
    (hq : relEmb k f q ∈ relParab k f) : relProj k f ⟨relEmb k f q, hq⟩ = q := by
  funext i
  exact leviProj_leviEmb k (f i) (q i)

theorem relEmb_mem_relParab (f : ∀ i, (Σ j, c i j) ≃ m i) (q : ∀ i, Levi k (c i)) :
    relEmb k f q ∈ relParab k f := fun i _ => leviEmb_mem_parab k (f i) (q i)

variable {k}

theorem cell_equiv (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j)
    (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ) (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y)
    (φ : Levi k m ≃* levi k N β)
    (hφ : ∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g)
    (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ) (hγ : ∀ x y, γ x < γ y ↔ blk e' x < blk e' y)
    (φ' : Levi k m' ≃* levi k N γ)
    (hφ' : ∀ g, ((φ' g : levi k N γ) : GL (Fin N) k) = leviEmb k e' g)
    {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W)
    (w : Equiv.Perm (Fin N))
    (hcell : ∀ i j (t : c i j), w (e' ⟨j, g j ⟨i, t⟩⟩) = e ⟨i, f i ⟨j, t⟩⟩) :
    Nonempty (Representation.Equiv
      ((indRep (cellLeviSub k β γ w) (normInducing (ρ.comp φ.symm.toMonoidHom) γ w)).comp
        φ'.toMonoidHom) (cellFunctor f g ρ)) := by
  have hδg : ∀ j i i' (t : c i j) (t' : c i' j),
      (β ∘ w) (e' ⟨j, g j ⟨i, t⟩⟩) < (β ∘ w) (e' ⟨j, g j ⟨i', t'⟩⟩) ↔ i < i' := by
    intro j i i' t t'
    simp only [Function.comp, hcell, hβ, blk_apply]
  have hδf : ∀ i j j' (t : c i j) (t' : c i j'),
      (γ ∘ ⇑w⁻¹) (e ⟨i, f i ⟨j, t⟩⟩) < (γ ∘ ⇑w⁻¹) (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j' := by
    intro i j j' t t'
    simp only [Function.comp, ← hcell, Equiv.Perm.inv_def, Equiv.symm_apply_apply, hγ, blk_apply]
  have hP : ∀ p, p ∈ relParab k g ↔ φ' p ∈ cellLeviSub k β γ w := by
    intro p
    rw [_root_.GlobalTheory.CompanionTheory.CellCompare.mem_relParab_iff_leviEmb_mem_blockUpper k e' g (β ∘ w) hδg p, Subgroup.mem_subgroupOf]
    refine ⟨fun h => ⟨(φ' p).2, by rw [hφ']; exact h⟩, fun h => ?_⟩
    have := h.2
    rwa [hφ'] at this
  have hU : ∀ u, u ∈ relUnip k f ↔ φ u ∈ leviUnipotent k N β (γ ∘ ⇑w⁻¹) := by
    intro u
    rw [_root_.GlobalTheory.CompanionTheory.RelUnipBridge.mem_relUnip_iff_leviEmb_mem k e f (γ ∘ ⇑w⁻¹) hδf u, leviUnipotent, Subgroup.mem_subgroupOf, hφ]
  obtain ⟨hc, hc'⟩ := GlobalTheory.T.levi_equiv_continuous k e' γ φ' hφ'
  refine nonempty_indRep_comp_equiv φ' hc hc' (cellLeviSub k β γ w) (relParab k g) hP _ _
    (coinvEquiv ρ φ (relUnip k f) (leviUnipotent k N β (γ ∘ ⇑w⁻¹)) hU) ?_
  intro p v
  obtain ⟨x, rfl⟩ := Representation.Coinvariants.mk_surjective _ v
  set b : cellLeviSub k β γ w := ⟨φ' p, (hP p.1).1 p.2⟩ with hbdef
  set q := relProj k g p with hq
  set sq := swapBlocks k c q with hsq
  have hbG : (((b : levi k N γ)) : GL (Fin N) k) = leviEmb k e' p.1 := hφ' _
  have hxm : permGL k w * leviEmb k e' p.1 * (permGL k w)⁻¹ ∈ blockUpper k N β := by
    rw [← hbG]
    exact (GroundTheory.Automorphic.Parabolic.permConj k β w ⟨_, b.2.2⟩).2
  have hin : GroundTheory.Automorphic.Parabolic.leviInfIncl β (γ ∘ ⇑w⁻¹)
      (cellInnerHom β γ w (cellLeviSubIncl k β γ w b)) = φ (relEmb k f sq) := by
    apply Subtype.ext
    rw [hφ, ← _root_.GlobalTheory.CompanionTheory.GeomCell.innerMat k e β hβ e' f g w hcell p.1 p.2 hxm]
    show ((GroundTheory.Automorphic.Parabolic.leviProj k N β _ : levi k N β) : GL (Fin N) k) = _
    congr 2
    exact Subtype.ext (show permGL k w * (((b : levi k N γ)) : GL (Fin N) k) * (permGL k w)⁻¹ = _ by
      rw [hbG])
  have h4 : normLeviParSqrtModular k γ (β ∘ w) (cellLeviSubIncl k β γ w b) =
      ((relDeltaHalf k (fun j i => c i j) q : ℂˣ) : ℂ) :=
    _root_.GlobalTheory.CompanionTheory.CellChar.normLeviParSqrtModular_eq_relDeltaHalf k e' g γ (β ∘ w) hγ hδg (_root_.GlobalTheory.CompanionTheory.CellCompare.mem_relParab_iff_leviEmb_mem_blockUpper k e' g (β ∘ w) hδg) φ' hφ'
      p.1 p.2 b.2
  have hmemh : ((φ (relEmb k f sq) : levi k N β) : GL (Fin N) k) ∈ leviPar k N β (γ ∘ ⇑w⁻¹) := by
    rw [← hin]
    exact (cellInnerHom β γ w (cellLeviSubIncl k β γ w b)).2
  have h5 : normLeviParInvSqrtModular k β (γ ∘ ⇑w⁻¹)
      (cellInnerHom β γ w (cellLeviSubIncl k β γ w b)) =
      (((relDeltaHalf k c sq)⁻¹ : ℂˣ) : ℂ) := by
    have h6 := _root_.GlobalTheory.CompanionTheory.CellChar.normLeviParSqrtModular_eq_relDeltaHalf k e f β (γ ∘ ⇑w⁻¹) hβ hδf
      (_root_.GlobalTheory.CompanionTheory.CellCompare.mem_relParab_iff_leviEmb_mem_blockUpper k e f (γ ∘ ⇑w⁻¹) hδf) φ hφ (relEmb k f sq) (relEmb_mem_relParab k f sq)
      hmemh
    rw [relProj_relEmb] at h6
    have h7 : cellInnerHom β γ w (cellLeviSubIncl k β γ w b) =
        ⟨((φ (relEmb k f sq) : levi k N β) : GL (Fin N) k), hmemh⟩ :=
      Subtype.ext (congrArg (fun z : levi k N β => (z : GL (Fin N) k)) hin)
    show (normLeviParSqrtModular k β (γ ∘ ⇑w⁻¹) _)⁻¹ = _
    rw [h7, h6, Units.val_inv_eq_inv_val]
  have hact : (ρ.comp φ.symm.toMonoidHom) (GroundTheory.Automorphic.Parabolic.leviInfIncl β (γ ∘ ⇑w⁻¹)
      (cellInnerHom β γ w (cellLeviSubIncl k β γ w b))) x = ρ (relEmb k f sq) x := by
    rw [hin]
    simp
  have hL : (normInducing (ρ.comp φ.symm.toMonoidHom) γ w) b
      (Representation.Coinvariants.mk _ x) =
      normLeviParSqrtModular k γ (β ∘ w) (cellLeviSubIncl k β γ w b) •
        normLeviParInvSqrtModular k β (γ ∘ ⇑w⁻¹) (cellInnerHom β γ w (cellLeviSubIncl k β γ w b)) •
          Representation.Coinvariants.mk _ ((ρ.comp φ.symm.toMonoidHom)
            (GroundTheory.Automorphic.Parabolic.leviInfIncl β (γ ∘ ⇑w⁻¹)
              (cellInnerHom β γ w (cellLeviSubIncl k β γ w b))) x) := rfl
  rw [hL, h4, h5, hact, map_smul, map_smul, coinvEquiv_mk]
  rfl

end

theorem cell_iso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ), (∀ x y, γ x < γ y ↔ blk e' x < blk e' y) → ∀ (φ' : Levi k m' ≃* levi k N γ), (∀ g, ((φ' g : levi k N γ) : GL (Fin N) k) = leviEmb k e' g) → ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W) (w : Equiv.Perm (Fin N)), ∃ (f : ∀ i, (Σ j, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m i) (g : ∀ j, (Σ i, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m' j), Nonempty (Representation.Equiv ((indRep (cellLeviSub k β γ w) (normInducing (ρ.comp φ.symm.toMonoidHom) γ w)).comp φ'.toMonoidHom) (cellFunctor f g ρ)) := by
  intro k _ _ _ _ α _ _ N m _ _ β' _ _ m' _ _ e β hβ φ hφ e' γ hγ φ' hφ' W _ _ ρ w
  obtain ⟨f, g, hcell⟩ := _root_.GlobalTheory.CompanionTheory.Cell.cell_row_column_partitions e e' w
  exact ⟨f, g, cell_equiv f g e β hβ φ hφ e' γ hγ φ' hφ' ρ w hcell⟩

end GlobalTheory.CompanionTheory.GeomCell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParahoricUnipotentTimesKernel
section
noncomputable section

namespace GlobalTheory.CompanionTheory.GxSplit

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead _root_.Topology

theorem exists_mul_of_mem_sup {G : Type*} [Group G] {A K : Subgroup G}
    (hc : ∀ w ∈ A, ∀ g ∈ K, w * g * w⁻¹ ∈ K) {g : G} (hg : g ∈ K ⊔ A) :
    ∃ u ∈ A, ∃ h ∈ K, g = u * h := by
  let H : Subgroup G :=
    { carrier := {g | ∃ u ∈ A, ∃ h ∈ K, g = u * h}
      mul_mem' := by
        rintro _ _ ⟨u₁, hu₁, h₁, hh₁, rfl⟩ ⟨u₂, hu₂, h₂, hh₂, rfl⟩
        refine ⟨u₁ * u₂, A.mul_mem hu₁ hu₂, (u₂⁻¹ * h₁ * u₂⁻¹⁻¹) * h₂,
          K.mul_mem (hc _ (A.inv_mem hu₂) _ hh₁) hh₂, ?_⟩
        group
      one_mem' := ⟨1, A.one_mem, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨u, hu, h, hh, rfl⟩
        refine ⟨u⁻¹, A.inv_mem hu, u * h⁻¹ * u⁻¹, hc _ hu _ (K.inv_mem hh), ?_⟩
        group }
  have hle : K ⊔ A ≤ H := sup_le (fun h hh => ⟨1, A.one_mem, h, hh, by simp⟩)
    (fun u hu => ⟨u, hu, 1, K.one_mem, by simp⟩)
  exact hle hg

theorem gx_split : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ Gx k e,
    ∃ u ∈ unipRad k e ⊓ KO k (Fin n), ∃ h ∈ KOne k (Fin n), g = u * h := by
  intro k _ _ _ _ n s d e g hg
  exact exists_mul_of_mem_sup
    (fun w hw h hh => GlobalTheory.DepthZeroJac.conj_mem_KOne (Subgroup.mem_inf.1 hw).2 hh) hg

end GlobalTheory.CompanionTheory.GxSplit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionsEqUnivOffBadSupportStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_eq_univ_off_bad_support : ∀ {X : Scheme.{0}} {P : X.Modules}, P.IsQuasicoherent → ∀ (S : Subobject P), (S : X.Modules).IsQuasicoherent → ∀ U : X.Opens, IsAffineOpen U → Disjoint (U : Set X) (GlobalTheory.CompanionTheory.GE.PSupp.badSet S) → secs S U = Set.univ := by
  first | exact @GlobalTheory.CompanionTheory.GE.PSupp.secs_eq_univ_of_disjoint_badSet | exact GlobalTheory.CompanionTheory.GE.PSupp.secs_eq_univ_of_disjoint_badSet | (intros; apply GlobalTheory.CompanionTheory.GE.PSupp.secs_eq_univ_of_disjoint_badSet <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedGradedGenerationGlobalSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_graded_generation_global_sections : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) {P : X.Modules} (S : ℕ → Subobject P) (hS : ClosedSys I P S) {k : ℕ} (g : Fin k → A), (∀ i, g i ∈ I) → ∀ (hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i))) (n : ℤ) (e : ℕ), Submodule.span Γ(X, ⊤) (⋃ i, Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grT (anti hS) (hr i) e)).app ⊤)) = ⊤ → Lifts I H hS n e → Lifts I H hS n (e + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.lifts_succ | exact GlobalTheory.CompanionTheory.GE.Step.lifts_succ | (intros; apply GlobalTheory.CompanionTheory.GE.Step.lifts_succ <;> assumption)
end

