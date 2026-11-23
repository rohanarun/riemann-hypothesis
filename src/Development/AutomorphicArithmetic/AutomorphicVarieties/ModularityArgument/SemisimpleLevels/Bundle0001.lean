module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0364
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsCalcP
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.CompanionTheory.RelOpsLeaf

namespace UpperTheory.V.Lev

variable {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {A : ValuationSubring Ω}
  {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}

private theorem char_comm (χ : ↥(Weil h) →* ℂˣ) (g g' : ↥(Weil h)) : χ (g * g' * g⁻¹ * g'⁻¹) = 1 := by
  simp only [map_mul, map_inv]
  rw [mul_comm (χ g) (χ g'), mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]

private theorem abW_of_sum {x y : WD h} (H : AbW (x.lpSum y)) : AbW x ∧ AbW y := by
  have key : ∀ g g' : Weil h, x.charPol (g * g' * g⁻¹ * g'⁻¹) = (X - 1) ^ x.lpDim ∧
      y.charPol (g * g' * g⁻¹ * g'⁻¹) = (X - 1) ^ y.lpDim := fun g g' => by
    have e := H g g'
    rw [WD.charPol_lpSum, WD.lpDim_sum] at e
    exact pow_of_mul_eq_pow (WD.charPol_monic _ _) (WD.charPol_monic _ _)
      (WD.charPol_natDegree _ _) (WD.charPol_natDegree _ _) e
  exact ⟨fun g g' => (key g g').1, fun g g' => (key g g').2⟩

private theorem scaleRoots_cancel {p q : ℂ[X]} {c : ℂ} (hc : c ≠ 0) (e : p.scaleRoots c = q.scaleRoots c) :
    p = q := by
  have e' := congrArg (fun r : ℂ[X] => r.scaleRoots c⁻¹) e
  simp only [← scaleRoots_mul, inv_mul_cancel₀ hc, mul_inv_cancel₀ hc, scaleRoots_one] at e'
  exact e'

end UpperTheory.V.Lev

theorem UpperTheory.V.Lev.ssCalc :
    UpperTheory.V.Lev.SsCalc := by
  intro K Ω _ _ _ _ _ A v h
  refine ⟨?_, ?_, ?_⟩
  · intro n x μ hx g g'
    have hdeg : x.lpDim = n := by
      rw [← WD.charPol_natDegree x 1, hx 1, natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
      simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    rw [hx, hdeg]
    simp [char_comm]
  · intro x x' y y' hxy hxy' hab s
    rw [WD.charPol_lpSum, WD.charPol_lpSum]
    rcases hab with hab | hab
    · obtain ⟨h1, h2⟩ := abW_of_sum hab
      rw [hxy (Or.inl h1) s, hxy' (Or.inl h2) s]
    · obtain ⟨h1, h2⟩ := abW_of_sum hab
      rw [hxy (Or.inr h1) s, hxy' (Or.inr h2) s]
  · intro x y z hz
    obtain ⟨χ, hχ⟩ := exists_char_of_lpDim_eq_one z hz
    have hdim : ∀ w : WD h, (w.lpChar z).lpDim = w.lpDim := by
      intro w
      rw [← WD.charPol_natDegree (w.lpChar z) 1, hχ, natDegree_scaleRoots, WD.charPol_natDegree]
    have hab : ∀ w : WD h, AbW (w.lpChar z) ↔ AbW w := by
      intro w
      unfold AbW
      simp only [hχ, hdim, char_comm, Units.val_one, scaleRoots_one]
    unfold SsCmp
    rw [hab, hab]
    constructor
    · intro H hw s
      exact scaleRoots_cancel (χ s).ne_zero (by rw [← hχ, ← hχ]; exact H hw s)
    · intro H hw s
      rw [hχ, hχ, H hw s]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsMonoOdd
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open _root_.GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Lev

def CsdMonoOdd : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a → Odd a →
    ∀ π : CuspSub E a, GlobalTheory.ContraPair.DualIsConj π → GKCoh.IsCohomological π →
    ∃ R : G E Ω →* GL (Fin a) (Qbar l), Continuous R ∧ IsSSRep R ∧
      (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → WO ι R (rc (algNorm σ))) ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
        ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
          (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
          (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
          IsPstAt P Bw (R.comp (Dec (F := E) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
            (wdAt P ι Bw h hj (R.comp (Dec (F := E) A).subtype)).mono0 → (rc (algNorm σ)).mono0

theorem csdMonoOdd_of_full (H : GlobalTheory.Published.CaraianiLocalGlobalDual) : CsdMonoOdd := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha _ π hd hc
  obtain ⟨R, h1, h2, h3, h4⟩ := H E Ω l ι a ha π hd hc
  refine ⟨R, h1, h2, h3, fun P AI hT w A h O _ _ _ Bw hj => ?_⟩
  exact ⟨(h4 P AI hT w A h O Bw hj).1, fun σ hσ rc hrc hm => (h4 P AI hT w A h O Bw hj).2 σ hσ rc hrc ▸ hm⟩

end UpperTheory.V.Lev

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsMoveP
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

theorem UpperTheory.V.Lev.ssMove :
    UpperTheory.V.Lev.SsMove := by
  intro F K Ω _ _ _ _ _ _ _ _ _ A v w h h' j i hP x y x' y' hx hy H
  obtain ⟨c, hc, -⟩ := _root_.GlobalTheory.WeilTransport.weil_equiv F Ω A v h K Ω A w h' _ _ i hP
  have key : ∀ (z : WD h) (z' : WD h'), WDRel (RingEquiv.refl Ω) z z' →
      (∀ s, z.charPol s = z'.charPol (c s)) ∧ z.lpDim = z'.lpDim := by
    rintro _ _ ⟨n, b, b', rfl, rfl, -, hρ⟩
    refine ⟨fun s => ?_, ?_⟩
    · rw [WD.charPol_mk, WD.charPol_mk, hρ s (c s) ((hc s (c s)).mpr rfl)]
    · rw [WD.lpDim_mk, WD.lpDim_mk]
  have ab : ∀ (z : WD h) (z' : WD h'), WDRel (RingEquiv.refl Ω) z z' →
      UpperTheory.V.Lev.AbW z → UpperTheory.V.Lev.AbW z' := by
    intro z z' hz a g g'
    obtain ⟨h1, h2⟩ := key z z' hz
    obtain ⟨g, rfl⟩ := c.surjective g
    obtain ⟨g', rfl⟩ := c.surjective g'
    rw [← h2, ← a g g', h1, map_mul, map_mul, map_mul, map_inv, map_inv]
  intro hab s
  rw [(key x x' hx).1, (key y y' hy).1]
  exact H (hab.imp (ab x x' hx) (ab y y' hy)) (c s)
end

