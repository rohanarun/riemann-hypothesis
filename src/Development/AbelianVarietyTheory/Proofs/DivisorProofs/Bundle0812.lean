module

public import Mathlib
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.ConjugateSelfDual.Statement
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0794
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0047
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0651
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0041
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG Polynomial
open scoped TensorProduct

namespace GlobalTheory.SphPar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def HasDiv {n : ℕ} (O : Subring L) (d : List ℤ) (g : GL (Fin n) L) : Prop :=
  ∃ ϖ : L, Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ∧
    ∃ a ∈ GLint (Fin n) O, ∃ b ∈ GLint (Fin n) O,
      (g : Matrix (Fin n) (Fin n) L) =
        (a : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) * (b : Matrix (Fin n) (Fin n) L)

def divInd {n : ℕ} (O : Subring L) (d : List ℤ) : GL (Fin n) L → ℂ := Set.indicator {g | HasDiv O d g} 1

end Local

section Global

variable {E : Type} [Field E] [NumberField E]

variable [StarRing E]

end Global

variable {D : D7}

end GlobalTheory.SphPar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorTranslateRatioGlobalUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT.Hecke.PullInj

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke.PullInj

theorem gen_transl_ratio : ∀ (X X' : Scheme.{0}) (π : X ⟶ X') (Q₁ Q₂ : LB X'), Q₁.IsLB → Q₂.IsLB →
    ∀ (w : LB.Iso (Q₁.pull π) (Q₂.pull π)), w.IsGen → ∀ τ : X ⟶ X, τ ≫ π = π → ∃ f : Γ(X, ⊤)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)),
        r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
        gm (r ≫ τ) z _ (w.s k) = gm r z ⊤ f * gm r z _ (w.s k) := by
  intro X X' π Q₁ Q₂ hQ₁ hQ₂ w hw τ hτ
  have hπτ : ∀ x : X, π (τ x) = π x := fun x => by
    rw [← Scheme.Hom.comp_apply, hτ]
  have hmem : ∀ {x : X} {k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)},
      x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k → τ x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k := by
    intro x k hx
    rw [mem_divPull] at hx ⊢
    rw [hπτ]; exact hx
  have hle : ∀ k, (LB.div (Q₂.pull π) (Q₁.pull π)).U k ≤ τ ⁻¹ᵁ (LB.div (Q₂.pull π) (Q₁.pull π)).U k :=
    fun k x hx => hmem hx
  let u : ∀ k, Γ(X, (LB.div (Q₂.pull π) (Q₁.pull π)).U k)ˣ := fun k =>
    res (hle k) (pullU τ _ (w.s k)) * (w.s k)⁻¹
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) k, r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
      gm r z _ (u k) = gm (r ≫ τ) z _ (w.s k) * (gm r z _ (w.s k))⁻¹ := by
    intro Z r z k hz
    show gm r z _ (res (hle k) (pullU τ _ (w.s k)) * (w.s k)⁻¹) = _
    rw [map_mul, map_inv, gm_res r z (hle k) hz, gm_pull r τ z _ (hmem hz)]
  have hg : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) k l, r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
      r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U l →
      gm (r ≫ τ) z _ ((LB.div (Q₂.pull π) (Q₁.pull π)).g k l) = gm r z _ ((LB.div (Q₂.pull π) (Q₁.pull π)).g k l) := by
    intro Z r z k l hk hl
    have hk' := hmem hk
    have hl' := hmem hl
    rw [germ_div_g _ _ (r ≫ τ) z hk' hl', germ_div_g _ _ r z hk hl]
    have hk₀ := mem_divPull.1 hk
    have hl₀ := mem_divPull.1 hl
    have hk₁ := mem_divPull.1 hk'
    have hl₁ := mem_divPull.1 hl'
    rw [gm_pull_g Q₂ π (r ≫ τ) z hk₁.1 hl₁.1, gm_pull_g Q₁ π (r ≫ τ) z hk₁.2 hl₁.2,
      gm_pull_g Q₂ π r z hk₀.1 hl₀.1, gm_pull_g Q₁ π r z hk₀.2 hl₀.2, Category.assoc, hτ]
  have hc : (⊤ : X.Opens) ≤ iSup (LB.div (Q₂.pull π) (Q₁.pull π)).U := by
    intro x _
    obtain ⟨i, hi⟩ := exists_chart hQ₂ (π x)
    obtain ⟨j, hj⟩ := exists_chart hQ₁ (π x)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => i, fun _ => j), mem_divPull.2 ⟨hi, hj⟩⟩
  obtain ⟨f, hf⟩ := glue_unit (⊤ : X.Opens) (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => le_top) hc u (by
    intro k l x hx
    rw [hu _ _ _ k hx.1, hu _ _ _ l hx.2, gen_germ hw (𝟙 X ≫ τ) x (hmem hx.1) (hmem hx.2),
      gen_germ hw (𝟙 X) x hx.1 hx.2, hg _ _ _ k l hx.1 hx.2]
    simp only [← div_eq_mul_inv]
    exact mul_div_mul_left_eq_div _ _ _)
  refine ⟨f, fun Z r z k hz => ?_⟩
  rw [← gm_res r z (le_top : (LB.div (Q₂.pull π) (Q₁.pull π)).U k ≤ ⊤) hz f, hf k, hu Z r z k hz,
    inv_mul_cancel_right]

end GlobalTheory.UPel.HT.Hecke.PullInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricPointDvrFactorsValuationSubringClosure
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem geomPoint_factors_valuationSubring_algClosure :
    ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L]
      [IsFractionRing W L] (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp W),
      ∃ (U : ValuationSubring (AlgebraicClosure L)) (j : W →+* U) (h : U →+* k),
        (algebraMap U (AlgebraicClosure L)).comp j = (algebraMap L (AlgebraicClosure L)).comp (algebraMap W L) ∧
          x = spMap h ≫ spMap j := by
  intro W L _ _ _ _ _ _ k _ _ x
  set j' : W →+* AlgebraicClosure L := (algebraMap L (AlgebraicClosure L)).comp (algebraMap W L) with hj'
  have hinj : Function.Injective j' :=
    (algebraMap L (AlgebraicClosure L)).injective.comp (IsFractionRing.injective W L)
  set g : W →+* k := (Spec.preimage x).hom with hg
  obtain ⟨U, hU, h, hh⟩ := _root_.GlobalTheory.ValExt.exists_valuationSubring_ext W (AlgebraicClosure L) k j' hinj g
  refine ⟨U, j'.codRestrict U.toSubring hU, h, ?_, ?_⟩
  · ext w; rfl
  · have hcomp : h.comp (j'.codRestrict U.toSubring hU) = g := by
      ext w; exact hh w
    have hx : x = Spec.map (Spec.preimage x) := (Spec.map_preimage x).symm
    rw [hx]
    simp only [spMap, Sp]
    rw [← Spec.map_comp]
    congr 1
    ext w
    change g w = h (j'.codRestrict U.toSubring hU w)
    rw [← hcomp]; rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramRePosDefAdjointPeriod
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PELU

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

private def reHermBilin {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm z w).re)
    (fun a b c => by simp [hermForm, add_dotProduct])
    (fun r a b => by simp [hermForm, smul_dotProduct])
    (fun a b c => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun r a b => by
      simp only [hermForm, star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul]
      simp)

private theorem hermForm_swap' {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = star (hermForm Hm z w) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, star_star, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hH.apply i j, star_star]
  ring

private theorem form_eq_zero_of_im_span' {g : ℕ} (s : Set (Fin g → ℂ)) (hs : Submodule.span ℝ s = ⊤)
    (B : (Fin g → ℂ) → (Fin g → ℂ) → ℂ) (h1 : ∀ z z' w, B (z + z') w = B z w + B z' w)
    (h2 : ∀ (r : ℂ) z w, B (r • z) w = r * B z w) (h3 : ∀ z w w', B z (w + w') = B z w + B z w')
    (h4 : ∀ (r : ℝ) z w, B z (r • w) = r * B z w) (h0 : ∀ z ∈ s, ∀ w ∈ s, (B z w).im = 0) (z w : Fin g → ℂ) :
    B z w = 0 := by
  have hA : ∀ z ∈ s, ∀ w, (B z w).im = 0 := by
    intro z hz w
    have hw : w ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w hw => exact h0 z hz w hw
    | zero => simpa using congrArg Complex.im (h4 0 z 0)
    | add w w' _ _ e e' => rw [h3, Complex.add_im, e, e', add_zero]
    | smul r w _ e => rw [h4, Complex.im_ofReal_mul, e, mul_zero]
  have hB : ∀ z w, (B z w).im = 0 := by
    intro z w
    have hz : z ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => exact hA z hz w
    | zero => simpa using congrArg Complex.im (h2 0 0 w)
    | add z z' _ _ e e' => rw [h1, Complex.add_im, e, e', add_zero]
    | smul r z _ e =>
      have : r • z = (r : ℂ) • z := by ext k; simp
      rw [this, h2, Complex.im_ofReal_mul, e, mul_zero]
  apply Complex.ext
  · have := hB (Complex.I • z) w
    rw [h2] at this
    simpa using this
  · simpa using hB z w

private theorem hermForm_adj_of_im_span' {g : ℕ} (s : Set (Fin g → ℂ)) (hs : Submodule.span ℝ s = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (A A' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h0 : ∀ z ∈ s, ∀ w ∈ s, (hermForm Hm (A z) w).im = (hermForm Hm z (A' w)).im) (z w : Fin g → ℂ) :
    hermForm Hm (A z) w = hermForm Hm z (A' w) := by
  have hr : ∀ (r : ℝ) (w : Fin g → ℂ), r • w = (r : ℂ) • w := fun r w => by ext k; simp
  have l1 : ∀ z z' w, hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := fun z z' w => by
    simp only [hermForm, add_dotProduct]
  have l2 : ∀ (r : ℂ) z w, hermForm Hm (r • z) w = r * hermForm Hm z w := fun r z w => by
    simp only [hermForm, smul_dotProduct, smul_eq_mul]
  have l3 : ∀ z w w', hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := fun z w w' => by
    simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]
  have l4 : ∀ (r : ℝ) z w, hermForm Hm z ((r : ℂ) • w) = r * hermForm Hm z w := fun r z w => by
    simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.star_def,
      Complex.conj_ofReal]
  refine sub_eq_zero.mp (form_eq_zero_of_im_span' s hs
    (fun z w => hermForm Hm (A z) w - hermForm Hm z (A' w)) ?_ ?_ ?_ ?_ ?_ z w)
  · intro z z' w
    simp only [map_add (f := _), l1]; ring
  · intro r z w
    simp only [map_smul, l2]; ring
  · intro z w w'
    simp only [map_add (f := _), l3]; ring
  · intro r z w
    simp only [hr, map_smul, l4]; ring
  · intro z hz w hw
    simp only [Complex.sub_im, h0 z hz w hw, sub_self]

theorem gram_re_posdef_adj : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ)
    (D : PLat O bar) (P : D.La →+ (Fin g → ℂ)) (r : ℕ) (e : Module.Basis (Fin r) ℤ D.La), IsPeriod D ρ P →
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.IsHermitian ∧ (∀ z : Fin r → ℂ, z ≠ 0 → 0 < (star z ⬝ᵥ (Q *ᵥ z)).re) ∧
      ∀ a : O, Q * actM D e ℂ (bar a) = (actM D e ℂ a)ᴴ * Q := by
  intro O _ bar g ρ D P r e hP
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, hE⟩ := hP
  set B := reHermBilin Hm with hBdef
  have hB : ∀ z w, B z w = (hermForm Hm z w).re := fun _ _ => rfl
  have hind : LinearIndependent ℝ (fun i => P (e i)) := by
    haveI : DiscreteTopology (LinearMap.range P.toIntLinearMap) := hdisc
    haveI : IsZLattice ℝ (LinearMap.range P.toIntLinearMap) := ⟨hspan⟩
    let bL := e.map (LinearEquiv.ofInjective P.toIntLinearMap hinj)
    have hfun : (fun i => P (e i)) = ⇑(bL.ofZLatticeBasis ℝ (LinearMap.range P.toIntLinearMap)) := by
      funext i
      rw [Module.Basis.ofZLatticeBasis_apply, Module.Basis.map_apply]
      rfl
    rw [hfun]
    exact (bL.ofZLatticeBasis ℝ (LinearMap.range P.toIntLinearMap)).linearIndependent
  have hBpos : ∀ v, v ≠ 0 → 0 < B v v := fun v hv => hpos v hv
  have hBnn : ∀ v, 0 ≤ B v v := fun v => by
    by_cases hv : v = 0
    · subst hv; simp
    · exact (hBpos v hv).le
  have hBsymm : ∀ v w, B v w = B w v := fun v w => by
    rw [hB, hB, hermForm_swap' hH v w]; simp
  refine ⟨Matrix.of fun i j => ((B (P (e i)) (P (e j)) : ℝ) : ℂ), ?_, ?_, ?_⟩
  · ext i j
    simp [Matrix.conjTranspose_apply, hBsymm]
  · intro z hz
    have hexp : ∀ x : Fin r → ℝ, B (∑ j, x j • P (e j)) (∑ j, x j • P (e j)) =
        ∑ i, ∑ j, B (P (e i)) (P (e j)) * (x i * x j) := by
      intro x
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hBsymm (P (e j))]
      ring
    have hq : (star z ⬝ᵥ (Matrix.of (fun i j => ((B (P (e i)) (P (e j)) : ℝ) : ℂ)) *ᵥ z)).re =
        ∑ i, ∑ j, B (P (e i)) (P (e j)) * ((z i).re * (z j).re) +
          ∑ i, ∑ j, B (P (e i)) (P (e j)) * ((z i).im * (z j).im) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Complex.re_sum, Finset.mul_sum, Pi.star_apply,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp [Complex.mul_re, Complex.mul_im]
      ring
    rw [hq, ← hexp, ← hexp]
    have hor : (fun i => (z i).re) ≠ 0 ∨ (fun i => (z i).im) ≠ 0 := by
      by_contra h
      push_neg at h
      apply hz
      funext i
      exact Complex.ext (congrFun h.1 i) (congrFun h.2 i)
    rcases hor with h | h
    · have hv : ∑ j, (z j).re • P (e j) ≠ 0 := fun h0 =>
        h (funext fun i => Fintype.linearIndependent_iff.1 hind _ h0 i)
      exact add_pos_of_pos_of_nonneg (hBpos _ hv) (hBnn _)
    · have hv : ∑ j, (z j).im • P (e j) ≠ 0 := fun h0 =>
        h (funext fun i => Fintype.linearIndependent_iff.1 hind _ h0 i)
      exact add_pos_of_nonneg_of_pos (hBnn _) (hBpos _ hv)
  · intro a
    have hadj : ∀ z w, hermForm Hm (ρ a *ᵥ z) w = hermForm Hm z (ρ (bar a) *ᵥ w) :=
      hermForm_adj_of_im_span' (Set.range P) hspan Hm (Matrix.mulVecLin (ρ a)) (Matrix.mulVecLin (ρ (bar a))) (by
        rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
        simp only [Matrix.mulVecLin_apply]
        rw [← hlin, ← hlin, hE, hE, D.adj])
    have hexpand : ∀ v : D.La, P v = ∑ k, e.repr v k • P (e k) := fun v => by
      conv_lhs => rw [← e.sum_repr v]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zsmul]
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, actM, Matrix.conjTranspose_apply, star_intCast]
    have h1 : B (P (e i)) (P (bar a • e j)) = ∑ k, B (P (e i)) (P (e k)) * (e.repr (bar a • e j) k : ℝ) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hexpand (bar a • e j), map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, zsmul_eq_mul, mul_comm]
    have h2 : B (P (a • e i)) (P (e j)) = ∑ k, (e.repr (a • e i) k : ℝ) * B (P (e k)) (P (e j)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hBsymm, hexpand (a • e i), map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, zsmul_eq_mul, hBsymm]
    have h3 : B (P (e i)) (P (bar a • e j)) = B (P (a • e i)) (P (e j)) := by
      rw [hB, hB, hlin, hlin, hadj]
    have := congrArg (fun t : ℝ => (t : ℂ)) (h1.symm.trans (h3.trans h2))
    push_cast at this
    exact this

end GlobalTheory.PELU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpHomOfProportionalGeneratingCombinations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section
namespace GlobalTheory.HomFixUniv

variable {A₀ B₀ X Z T : Scheme.{0}} {N : LB A₀} {H : LB B₀} {mA mB : ℕ}

theorem comb_pull (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (r : Z ⟶ X) (z : Z) (q : N.ι) (h : φ (r z) ∈ N.U q) (j : Fin mB) :
    comb a (r ≫ φ) (r ≫ p) c z q j = (r.stalkMap z).hom (comb a φ p c (r z) q j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [comb, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_comp r p z ⊤ trivial, gs_comp r φ z _ h]

theorem Generates.pull {a : Fin mA → LB.Sec N} {φ : X ⟶ A₀} {p : X ⟶ T} {c : Fin mA → Fin mB → Γ(T, ⊤)}
    (hg : Generates a φ p c) (r : Z ⟶ X) : Generates a (r ≫ φ) (r ≫ p) c := by
  intro z q hz
  obtain ⟨j, hj⟩ := hg (r z) q hz
  exact ⟨j, by rw [comb_pull a φ p c r z q hz]; exact hj.map _⟩

theorem Proport.pull {a : Fin mA → LB.Sec N} {b : Fin mB → LB.Sec H} {φ : X ⟶ A₀} {p : X ⟶ T} {Ψ : X ⟶ B₀}
    {c : Fin mA → Fin mB → Γ(T, ⊤)} (hp : Proport a b φ p Ψ c) (r : Z ⟶ X) :
    Proport a b (r ≫ φ) (r ≫ p) (r ≫ Ψ) c := by
  intro z q k hq hk j j'
  rw [comb_pull a φ p c r z q hq, comb_pull a φ p c r z q hq, gs_comp r Ψ z _ hk, gs_comp r Ψ z _ hk,
    ← map_mul, ← map_mul, hp (r z) q k hq hk j j']

theorem gs_top_comp {S : Scheme.{0}} (t : T ⟶ S) (z : T) (x : Γ(S, ⊤)) :
    (t.stalkMap z).hom (gs (𝟙 S) (t z) ⊤ x) = gs (𝟙 T) z ⊤ (t.appTop x) := by
  rw [← gs_comp t (𝟙 S) z ⊤ trivial, Category.comp_id]
  have e := gs_pull (𝟙 T) t z ⊤ trivial x
  rw [Category.id_comp] at e
  exact e.symm

theorem proport_zero {S : Scheme.{0}} {a : Fin mA → LB.Sec N} {b : Fin mB → LB.Sec H} {eA : S ⟶ A₀} {eB : S ⟶ B₀}
    {uA : ∀ z : S, N.ι → (S.presheaf.stalk z)ˣ} {uB : ∀ z : S, H.ι → (S.presheaf.stalk z)ˣ}
    {α : Fin mA → Γ(S, ⊤)} {β : Fin mB → Γ(S, ⊤)} (t : T ⟶ S) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (ha : ∀ i, IsVal eA uA (a i) (α i)) (hb : ∀ j, IsVal eB uB (b j) (β j)) (hn : Normal t c α β) :
    Proport a b (t ≫ eA) (𝟙 T) (t ≫ eB) c := by
  intro z q k hq hk j j'
  have hc : ∀ j, comb a (t ≫ eA) (𝟙 T) c z q j =
      gs (𝟙 T) z ⊤ (t.appTop (β j)) * (t.stalkMap z).hom (uA (t z) q).val := by
    intro j
    simp only [comb]
    have e : ∀ i, gs (t ≫ eA) z (N.U q) ((a i).f q) =
        gs (𝟙 T) z ⊤ (t.appTop (α i)) * (t.stalkMap z).hom (uA (t z) q).val := by
      intro i
      rw [gs_comp t eA z _ hq, ha i (t z) q hq, map_mul, gs_top_comp]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [e, hn j, gs_eq (𝟙 T) z ⊤ trivial, map_sum, map_mul, Finset.sum_mul, _root_.mul_assoc]
  have hbj : ∀ j, gs (t ≫ eB) z (H.U k) ((b j).f k) =
      gs (𝟙 T) z ⊤ (t.appTop (β j)) * (t.stalkMap z).hom (uB (t z) k).val := by
    intro j
    rw [gs_comp t eB z _ hk, hb j (t z) k hk, map_mul, gs_top_comp]
  rw [hc, hc, hbj, hbj]
  ring

end GlobalTheory.HomFixUniv

namespace GlobalTheory.HomFixUniv

theorem snd_θ {Rg : Type} [CommRing Rg] (B : Over (Sp Rg)) : (snd (topS Rg) B).left ≫ θ B = 𝟙 _ := by
  have key : ∀ h : B ⟶ topS Rg, snd (topS Rg) B ≫ lift h (𝟙 B) = 𝟙 _ := by
    intro h
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Category.id_comp]
      apply Over.OverMorphism.ext
      have : Mono (topS Rg).hom := by
        show Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
      apply (cancel_mono (topS Rg).hom).1
      exact (Over.w _).trans (Over.w _).symm
    · rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
  rw [θ, ← Over.comp_left, key]
  rfl

theorem θ_comp_structure {Rg : Type} [CommRing Rg] (B : Over (Sp Rg)) : θ B ≫ fA B = B.hom := by
  rw [θ]; exact Over.w _

end GlobalTheory.HomFixUniv

theorem GlobalTheory.HomFixUniv.hom_of_proport : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (T : Scheme.{0}) (t : T ⟶ Sp Rg) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Ψ : A'.left ⟶ (topS Rg ⊗ B).left) (c : Fin mA → Fin mB → Γ(T, ⊤)), Hyps L M k bA bB eA eB → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → Ψ ≫ GlobalTheory.HomFixUniv.fA B = A'.hom ≫ t → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c → GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom Ψ c → GlobalTheory.HomFixUniv.Normal t c αA βB → ∃ Φ : A' ⟶ B', IsMonHom Φ ∧ Φ.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B = Ψ := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB αA βB T t A' B' _ _ φA' φB' Ψ c hH hvA hvB hA' hB' hΨ hgen hprop hnorm
  obtain ⟨hA, hB, hL, hM, -, -, -, hk, hva, -, hbB⟩ := hH
  have hA'ab : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hA'
  have hB'ab : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB hB'
  have hsnd : (snd (topS Rg) B).left ≫ B.hom = fA B := Over.w (snd (topS Rg) B)
  let Φl : A'.left ⟶ B'.left :=
    hB'.1.lift (Ψ ≫ (snd (topS Rg) B).left) A'.hom (by rw [Category.assoc, hsnd, hΨ])
  have hΦ1 : Φl ≫ φB' = Ψ ≫ (snd (topS Rg) B).left := hB'.1.lift_fst _ _ _
  have hΦ2 : Φl ≫ B'.hom = A'.hom := hB'.1.lift_snd _ _ _
  let Φ : A' ⟶ B' := Over.homMk Φl hΦ2
  have hΨΦ : Φ.left ≫ φB' ≫ θ B = Ψ := by
    show Φl ≫ φB' ≫ θ B = Ψ
    rw [← Category.assoc, hΦ1, Category.assoc, snd_θ, Category.comp_id]
  let e' : T ⟶ A'.left := η[A'].left
  have hEA : e' ≫ φA' = t ≫ eSec A := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left hA'
  have hEB : (η[B'].left : T ⟶ B'.left) ≫ φB' = t ≫ eSec B := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left hB'
  have hηA : e' ≫ A'.hom = 𝟙 T := Over.w η[A']
  have heB : eSec B ≫ B.hom = 𝟙 _ := Over.w η[B]
  have hzero : e' ≫ Ψ = t ≫ eSec B ≫ θ B := by
    have hgen' := hgen.pull e'
    have hprop' := hprop.pull e'
    rw [← Category.assoc, hEA, hηA, Category.assoc] at hgen' hprop'
    refine GlobalTheory.T.eq_of_pullbackSectionsProportionalToCombinations Rg _ _ T T (fA B) (LPow A L k (topS Rg)) (LPow B M k (topS Rg)) mA mB bA bB _ (𝟙 T) c _ _
      (GlobalTheory.T.sectionsEmbed_of_baseChangeStableBasis Rg B M k mB bB hB hM hk hva hbB) (LB.isLB_linComb hM _ _) (LB.isLB_linComb hL _ _) hgen' hprop'
      (proport_zero t c hvA hvB hnorm) ?_
    rw [Category.assoc, hΨ, ← Category.assoc, hηA, Category.id_comp, Category.assoc, Category.assoc, θ_comp_structure,
      heB]
    exact (Category.comp_id _).symm
  have hz : η[A'] ≫ Φ = η[B'] := by
    apply Over.OverMorphism.ext
    apply hB'.1.hom_ext
    · show e' ≫ Φl ≫ φB' = _
      rw [hΦ1, ← Category.assoc, hzero, hEB, Category.assoc, Category.assoc, θ_snd, Category.comp_id]
    · exact (Over.w _).trans (Over.w _).symm
  exact ⟨Φ, GlobalTheory.rigidity_holds T A' B' hA'ab hB'ab Φ hz, hΨΦ⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastRowTopComponentDualWeylEqMonomialMulStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRow_top_component_dualWeyl_eq_monomial_mul : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : Fin n → ℕ) (G : BP K n), G ∈ dualWeyl K (n + 1) n lam → ∀ b : Fin n → ℕ, (∀ s, b s ≤ lam s) → (∀ β', zcomp K n β' G ≠ 0 → omg β' ≤ omg fun s => (b s : ℤ)) → ∃ f ∈ dualWeyl K n n (fun s => lam s - b s), zcomp K n (fun s => (b s : ℤ)) G = zmon K n b * emb K n f := by
  first | exact @GlobalTheory.BrCompare.zcomp_top_eq_zmon_mul_emb | exact GlobalTheory.BrCompare.zcomp_top_eq_zmon_mul_emb | (intros; apply GlobalTheory.BrCompare.zcomp_top_eq_zmon_mul_emb <;> assumption)
end

