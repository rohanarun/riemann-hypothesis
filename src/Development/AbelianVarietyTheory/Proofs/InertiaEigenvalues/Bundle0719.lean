module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0715
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0167
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrExtensionQkPointsRational
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)

namespace GlobalTheory.QkRationalExt

open GlobalTheory.ArcPull GlobalTheory.TorusExt GlobalTheory.QkNumberField

theorem exists_ringHom_extend {K L F : Type} [Field K] [Field L] [Field F] [Algebra K L] [Algebra.IsAlgebraic K L]
    [IsAlgClosed F] (M : IntermediateField K L) (f : M →+* F) : ∃ σ : L →+* F, σ.comp M.val.toRingHom = f := by
  letI : Algebra M F := f.toAlgebra
  have : Algebra.IsAlgebraic M L := Algebra.IsAlgebraic.tower_top (K := K) M
  have : Module.IsTorsionFree M F := DivisionSemiring.to_moduleIsTorsionFree
  have : Module.IsTorsionFree M L := DivisionSemiring.to_moduleIsTorsionFree
  let σ : L →ₐ[M] F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨σ.toRingHom, RingHom.ext fun x => σ.commutes x⟩

section Ext

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem qkExt_g (hB : D.TauBimult) {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
    [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') {k : ℕ} (z : QkPt D F k) :
    (qkExt hB f hf z).g = gtExt D f hf z.g := by
  unfold qkExt qkMk
  rfl

theorem qkExt_y (hB : D.TauBimult) {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
    [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') {k : ℕ} (z : QkPt D F k) :
    (qkExt hB f hf z).y = z.y := ((qkExt_iff hB f hf z _).2 rfl).1

theorem qkExt_qkExt (hB : D.TauBimult) {F F' F'' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
    [Algebra (FractionRing R) F'] [Field F''] [Algebra (FractionRing R) F''] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') (f' : F' →+* F'')
    (hf' : f'.comp (algebraMap (FractionRing R) F') = algebraMap (FractionRing R) F'') (f'' : F →+* F'')
    (hf'' : f''.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F'') (e : f'.comp f = f'')
    {k : ℕ} (z : QkPt D F k) : qkExt hB f' hf' (qkExt hB f hf z) = qkExt hB f'' hf'' z := by
  refine qk_ext ?_ ?_
  · rw [qkExt_y, qkExt_y, qkExt_y]
  · rw [qkExt_g, qkExt_g, qkExt_g]
    exact gtExt_gtExt f hf f' hf' f'' hf'' e z.g

theorem qkExt_pullQk (hD : IsPullDeg φ D D') (hG : GlobalFnsSt) (hB : D.TauBimult) (hB' : D'.TauBimult)
    {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] [Field F']
    [Algebra (FractionRing R) F'] [Algebra (FractionRing R') F'] (hF : Compat φ F) (hF' : Compat φ F') (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
    (hf' : f.comp (algebraMap (FractionRing R') F) = algebraMap (FractionRing R') F') {k : ℕ} (z : QkPt D F k) :
    QkExt f (pullQk hD hG hF hB hB' z) (pullQk hD hG hF' hB hB' (qkExt hB f hf z)) := by
  have h₁ : QkExt f z (qkExt hB f hf z) := (qkExt_iff hB f hf _ _).2 rfl
  have h₂ : QkExt f (pullQk hD hG hF hB hB' z) (qkExt hB' f hf' (pullQk hD hG hF hB hB' z)) :=
    (qkExt_iff hB' f hf' _ _).2 rfl
  have h₃ : IsPullGtF φ hD F z.g (pullQk hD hG hF hB hB' z).g := ((eq_pullQk_iff hD hG hF hB hB' z _).1 rfl).2
  have h₄ := isPullGtF_ext hD hF' f hf' h₃ h₁ h₂
  have h₅ : (qkExt hB' f hf' (pullQk hD hG hF hB hB' z)).y = hD.xe.symm (qkExt hB f hf z).y := by
    rw [h₂.1, h₁.1, pullQk_y]
  rw [← (eq_pullQk_iff hD hG hF' hB hB' _ _).2 ⟨h₅, h₄⟩]
  exact h₂

end Ext

theorem exists_rational_of_finite (hL : Laws) {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    {φ : R →+* R'} (hφ : Function.Injective φ) {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D')
    (hB : D.TauBimult) (hB' : D'.TauBimult) {L : Type} [Field L] [Algebra (FractionRing R) L]
    [Algebra.IsAlgebraic (FractionRing R) L] [IsAlgClosed L] [CharZero L]
    (M : IntermediateField (FractionRing R) L) (j : M →+* FractionRing R')
    (hj : ∀ r : R, j (algebraMap (FractionRing R) M (algebraMap R _ r)) = algebraMap R' _ (φ r))
    {k : ℕ} (hk : k ≠ 0)
    (H : ∀ q : QkPt D L k, ∃ z : QkPt D M k, qkExt hB M.val.toRingHom (val_comp M) z = q)
    {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R') F] (q : QkPt D' F k) :
    ∃ p : QkPt D' (FractionRing R') k, QkExt (algebraMap (FractionRing R') F) p q := by
  have hG := hL.globalFns
  letI : Algebra (FractionRing R) (FractionRing R') := (fracMap hφ).toAlgebra
  letI : Algebra (FractionRing R) F := ((algebraMap (FractionRing R') F).comp (fracMap hφ)).toAlgebra
  have hK : Compat φ (FractionRing R') := fracMap_algebraMap hφ
  have hF : Compat φ F := fun r => congrArg (algebraMap (FractionRing R') F) (fracMap_algebraMap hφ r)
  obtain ⟨q₀, rfl⟩ := pullQk_surjective hD hG hF hB hB' q
  have hjf : j.comp (algebraMap (FractionRing R) M) = algebraMap (FractionRing R) (FractionRing R') :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r =>
      (hj r).trans (fracMap_algebraMap hφ r).symm)
  obtain ⟨σ, e⟩ := exists_ringHom_extend M ((algebraMap (FractionRing R') F).comp j)
  have hh : (algebraMap (FractionRing R') F).comp (algebraMap (FractionRing R) (FractionRing R')) =
      algebraMap (FractionRing R) F := rfl
  have hc : ((algebraMap (FractionRing R') F).comp j).comp
      (algebraMap (FractionRing R) M) = algebraMap (FractionRing R) F := by
    rw [RingHom.comp_assoc, hjf, hh]
  have hσ : σ.comp (algebraMap (FractionRing R) L) = algebraMap (FractionRing R) F := by
    rw [← val_comp M, ← RingHom.comp_assoc, e, hc]
  obtain ⟨x, rfl⟩ := GlobalTheory.ArcExt.exists_qkExt σ hσ hB hL (Nat.cast_ne_zero.2 hk) q₀
  obtain ⟨z, rfl⟩ := H x
  refine ⟨pullQk hD hG hK hB hB' (qkExt hB j hjf z), ?_⟩
  rw [qkExt_qkExt hB _ (val_comp M) σ hσ _ hc e z, ← qkExt_qkExt hB j hjf _ hh _ hc rfl z]
  exact qkExt_pullQk hD hG hB hB' hK hF _ hh (RingHom.comp_id _) _

theorem exists_cdvr_ext_rational : ∀ (T : Formalism.L2.Pj.CDVR) (D : DegPre T.V), D.TauBimult → ∀ N : ℕ, 0 < N → ∀ ϖ : T.V, Irreducible ϖ → ∃ (T' : Formalism.L2.Pj.CDVR) (g : T.V →+* T'.V) (ϖ' : T'.V) (e : ℕ), Function.Injective g ∧ g.Finite ∧ Irreducible ϖ' ∧ N ∣ e ∧ Associated (g ϖ) (ϖ' ^ e) ∧ ∀ (D' : DegPre T'.V) (_ : IsPullDeg g D D'), D'.TauBimult → ∀ k : ℕ, k ∣ N → ∀ q : QkPt D' (AlgebraicClosure (FractionRing T'.V)) k, ∃ p : QkPt D' (FractionRing T'.V) k, QkExt (algebraMap (FractionRing T'.V) (AlgebraicClosure (FractionRing T'.V))) p q := by
  intro T D hB N hN ϖ hϖ
  have hL : Laws := GlobalTheory.allSixLaws.1
  have : CharZero (FractionRing T.V) := charZero_of_injective_algebraMap (IsFractionRing.injective T.V _)
  obtain ⟨M, hM, H⟩ := exists_finite_qk (D := D) (L := AlgebraicClosure (FractionRing T.V)) hL hB
    (Nat.cast_ne_zero.2 hN.ne')
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))
    (algebraMap T.V _ ϖ)) hN
  have h₁ : FiniteDimensional (FractionRing T.V) (IntermediateField.adjoin (FractionRing T.V) {π}) :=
    IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  let M₂ := M ⊔ IntermediateField.adjoin (FractionRing T.V) {π}
  have h₂ : FiniteDimensional (FractionRing T.V) M₂ := inferInstance
  let π₂ : M₂ := ⟨π, (le_sup_right : _ ≤ M₂) (IntermediateField.mem_adjoin_simple_self _ π)⟩
  have hπ₂ : π₂ ^ N = algebraMap (FractionRing T.V) M₂ (algebraMap T.V _ ϖ) := Subtype.ext hπ
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, hinj, -, hint, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension T.V (FractionRing T.V) M₂
  have : CharZero W := charZero_of_injective_algebraMap hinj
  obtain ⟨w, hw⟩ := hint π₂ ⟨Polynomial.X ^ N - Polynomial.C ϖ, Polynomial.monic_X_pow_sub_C _ hN.ne', by
    simp [hπ₂]⟩
  have hwN : w ^ N = algebraMap T.V W ϖ := IsFractionRing.injective W M₂ (by
    rw [map_pow, hw, hπ₂]; exact (RingHom.congr_fun hc ϖ).symm)
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hwN
    exact hϖ.ne_zero (hinj (hwN.symm.trans (map_zero _).symm))
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hw0 hϖ'
  let ε := FractionRing.algEquiv W M₂
  let j : M →+* FractionRing W := ε.symm.toRingEquiv.toRingHom.comp
    (IntermediateField.inclusion (le_sup_left : M ≤ M₂)).toRingHom
  have hj : ∀ r : T.V, j (algebraMap (FractionRing T.V) M (algebraMap T.V _ r)) =
      algebraMap W _ (algebraMap T.V W r) := fun r => ε.injective (by
    refine (ε.apply_symm_apply _).trans (Eq.trans ?_ (ε.commutes _).symm)
    exact (RingHom.congr_fun hc r).symm)
  refine ⟨Formalism.L2.Pj.CDVR.mk W, algebraMap T.V W, ϖ', m * N, hinj, RingHom.finite_algebraMap.2 hfin, hϖ',
    Dvd.intro_left m rfl, ?_, ?_⟩
  · rw [← hwN, pow_mul]
    exact hm.pow_pow
  · intro D' hD hB' k hk q
    have hk0 : k ≠ 0 := by rintro rfl; exact hN.ne' (Nat.eq_zero_of_zero_dvd hk)
    exact exists_rational_of_finite hL hinj hD hB hB' M j hj hk0 (H k hk) q

end GlobalTheory.QkRationalExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleSmoothQuotient
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.SmGL.IrrQuot

theorem exists_irreducible_smooth_quotient : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V), IsSmooth ρ → HasFiniteLength ρ → Nontrivial V →
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y),
      IsSmooth τ ∧ τ.IsIrreducible ∧ ∃ q : ρ.IntertwiningMap τ, Function.Surjective q := by
  intro G V _ _ _ _ _ ρ hsm hfl hnt
  haveI : WellFoundedGT (Subrepresentation ρ) := ((hasFiniteLength_iff_wellFounded ρ).1 hfl).1
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hmem : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← h] at hmem
    exact hx ((Submodule.mem_bot ℂ).1 hmem)
  obtain ⟨M, hM, -⟩ := (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt
  let W : Submodule ℂ V := M.toSubmodule
  have hW : ∀ g : G, W ≤ W.comap (ρ g) := fun g v hv => M.apply_mem_toSubmodule g hv
  let τ : Representation ℂ G (V ⧸ W) := ρ.quotient W hW
  have hτ : ∀ (g : G) (v : V), τ g (W.mkQ v) = W.mkQ (ρ g v) := fun g v => rfl
  let q : ρ.IntertwiningMap τ := ⟨W.mkQ, fun g => by ext v; rfl⟩
  have hq : Function.Surjective q := Submodule.mkQ_surjective W
  refine ⟨V ⧸ W, inferInstance, inferInstance, τ, ?_, ?_, q, hq⟩
  ·
    intro x
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W x
    let stab : (u : Type) → [AddCommGroup u] → [Module ℂ u] → (σ : Representation ℂ G u) → u → Subgroup G :=
      fun u _ _ σ y =>
        { carrier := {g | σ g y = y}
          mul_mem' := by
            intro a b ha hb
            simp only [Set.mem_setOf_eq] at ha hb ⊢
            rw [map_mul, Module.End.mul_apply, hb, ha]
          one_mem' := by simp
          inv_mem' := by
            intro a ha
            simp only [Set.mem_setOf_eq] at ha ⊢
            conv_lhs => rw [← ha]
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    have hle : stab V ρ v ≤ stab (V ⧸ W) τ (W.mkQ v) := by
      intro g hg
      change τ g (W.mkQ v) = W.mkQ v
      rw [hτ]
      exact congrArg W.mkQ hg
    exact Subgroup.isOpen_mono hle (hsm v)
  ·
    have hMtop : M ≠ ⊤ := hM.1
    refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
    · intro h
      apply hMtop
      apply Subrepresentation.toSubmodule_injective
      apply eq_top_iff.2
      intro v _
      have hmem : W.mkQ v ∈ (⊤ : Subrepresentation τ).toSubmodule := Submodule.mem_top
      rw [← h] at hmem
      exact (Submodule.Quotient.mk_eq_zero W).1 ((Submodule.mem_bot ℂ).1 hmem)
    · intro S
      let T : Subrepresentation ρ := ⟨S.toSubmodule.comap W.mkQ, fun g v hv => by
        change W.mkQ (ρ g v) ∈ S.toSubmodule
        rw [← hτ]
        exact S.apply_mem_toSubmodule g hv⟩
      have hMT : M ≤ T := by
        intro v hv
        change W.mkQ v ∈ S.toSubmodule
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 hv]
        exact S.toSubmodule.zero_mem
      rcases hM.le_iff.1 hMT with h | h
      · right
        apply Subrepresentation.toSubmodule_injective
        apply eq_top_iff.2
        intro x _
        obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W x
        have hvT : v ∈ T.toSubmodule := by rw [h]; exact Submodule.mem_top
        exact hvT
      · left
        apply Subrepresentation.toSubmodule_injective
        apply eq_bot_iff.2
        intro x hx
        obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W x
        have hvT : v ∈ T.toSubmodule := hx
        rw [h] at hvT
        exact (Submodule.mem_bot ℂ).2 (by rw [Submodule.mkQ_apply]; exact (Submodule.Quotient.mk_eq_zero W).2 hvT)

end GlobalTheory.SmGL.IrrQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtTensorTwistApply
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.IndChain.SuppStep

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LocGL
open scoped TensorProduct

variable {g : ℕ} [Fact g.Prime]

theorem isUnram_of_supp {ν : ℚ_[g]ˣ →* ℂˣ} (h : Supp.IsUnram ν) : GlobalTheory.SplitWeil.IsUnram ν := by
  intro x hx
  have a1 := GlobalTheory.SplitWeil.padic_valuation_lt_iff g (x : ℚ_[g]) 1
  have a2 := GlobalTheory.SplitWeil.padic_valuation_lt_iff g 1 (x : ℚ_[g])
  rw [hx, map_one] at a1 a2
  have h1 : ‖(x : ℚ_[g])‖ = 1 := by
    simp only [lt_self_iff_false, norm_one, false_iff, not_lt] at a1 a2
    exact le_antisymm a2 a1
  have := h (PadicInt.mkUnits h1)
  convert this using 2
  exact Units.ext rfl

theorem extTensor_twist_apply {a b : ℕ} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W')
    (χ₁ : GL (Fin a) ℚ_[g] →* ℂˣ) (χ₂ : GL (Fin b) ℚ_[g] →* ℂˣ) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g])
    (w : W ⊗[ℂ] W') :
    extTensor (twist σ χ₁) (twist ρ χ₂) (x, y) w = ((χ₁ x * χ₂ y : ℂˣ) : ℂ) • TensorProduct.map (σ x) (ρ y) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add (f := _), hu, hv, map_add (f := _), smul_add]
  | tmul u v =>
    rw [extTensor_tmul, TensorProduct.map_tmul, twist_apply, twist_apply, TensorProduct.smul_tmul_smul,
      Units.val_mul]

theorem scal_eq (ν₁ ν₂ A B : ℚ_[g]ˣ →* ℂˣ) (u v : ℚ_[g]ˣ) :
    (A u * B v) * ((ν₁ * A⁻¹) u * (ν₂ * B⁻¹) v) = ν₁ u * ν₂ v := by
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
  simp [mul_assoc, mul_comm, mul_left_comm]

theorem law {a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (π : Representation ℂ (GL (Fin (a + b)) ℚ_[g]) V)
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W')
    (ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ) (Λ : V →ₗ[ℂ] W ⊗[ℂ] W')
    (hΛ : ∀ (p : GL (Fin (a + b)) ℚ_[g]) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g]),
      (∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j = 0) →
      (∀ i j : Fin a, (x : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
        Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j) →
      (∀ i j : Fin b, (y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
        Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (a + i) (a + j)) →
      ∀ v, Λ (π p v) = ((ν₁ (Matrix.GeneralLinearGroup.det x) * ν₂ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) •
        TensorProduct.map (σ x) (ρ y) (Λ v))
    (q : parab ℚ_[g] (two (stdSum (rfl : a + b = a + b)))) (w : V) :
    Λ (π q w) = (deltaHalf ℚ_[g] (Two (Fin a) (Fin b)) (leviProj ℚ_[g] _ q) : ℂ) •
      extTensor (twist σ (detChar (Fin a) (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹)))
        (twist ρ (detChar (Fin b) (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹)))
        ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)) (Λ w) := by
  set X := ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)).1 with hX
  set Y := ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)).2 with hY
  have hL : leviProj ℚ_[g] _ q = leviTwo ℚ_[g] _ _ (X, Y) := (MulEquiv.apply_symm_apply _ _).symm
  have hpar := (mem_parab_two ℚ_[g]).1 q.2
  have h0 : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) →
      ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j = 0 := by
    intro i j hj hi
    have e1 : stdSum (rfl : a + b = a + b) (.inr ⟨i - a, by omega⟩) = i := Fin.ext (by rw [stdSum_inr]; simp; omega)
    have e2 : stdSum (rfl : a + b = a + b) (.inl ⟨j, hj⟩) = j := Fin.ext (by rw [stdSum_inl])
    have := hpar ⟨i - a, by omega⟩ ⟨j, hj⟩
    rwa [e1, e2] at this
  have hx : ∀ i j : Fin a, (X : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j := by
    intro i j
    have hi := i.2
    have hj := j.2
    rw [Formalism.MainNotions.ArithmeticCylinders.entN, dite_eq_left ⟨by omega, by omega⟩]
    show ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (stdSum (rfl : a + b = a + b) (.inl i)) (stdSum (rfl : a + b = a + b) (.inl j)) = _
    congr 1 <;> exact Fin.ext (stdSum_inl _ _)
  have hy : ∀ i j : Fin b, (Y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (a + i) (a + j) := by
    intro i j
    have hi := i.2
    have hj := j.2
    rw [Formalism.MainNotions.ArithmeticCylinders.entN, dite_eq_left ⟨by omega, by omega⟩]
    show ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (stdSum (rfl : a + b = a + b) (.inr i)) (stdSum (rfl : a + b = a + b) (.inr j)) = _
    congr 1 <;> exact Fin.ext (stdSum_inr _ _)
  rw [hΛ q X Y h0 hx hy w, hL, MulEquiv.symm_apply_apply, deltaHalf_two, extTensor_twist_apply, smul_smul,
    ← Units.val_mul, detChar_apply, detChar_apply]
  simp only [Fintype.card_fin]
  rw [scal_eq]

theorem supp_of_mapsToProd : GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (g : ℕ) [Fact g.Prime] (n a b : ℕ) (V W W' : Type)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W)
    (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W'),
    GlobalTheory.PRep.IsSmooth π → π.IsIrreducible → Supp.MapsToProd π σ ρ →
    ∀ (ys yr : Multiset (GlobalTheory.LocGL.IrrGL (k := ℚ_[g]))), GlobalTheory.LocGL.HasSupport σ ys → GlobalTheory.LocGL.HasSupport ρ yr →
    ∃ (μ₁ μ₂ : ℚ_[g]ˣ →* ℂˣ) (h₁ : GlobalTheory.SplitWeil.IsUnram μ₁) (h₂ : GlobalTheory.SplitWeil.IsUnram μ₂),
      GlobalTheory.LocGL.HasSupport π (ys.map (fun x => x.tw μ₁ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₁)) +
        yr.map (fun x => x.tw μ₂ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₂))) := by
  intro hZ g _ n a b V W W' _ _ _ _ _ _ π σ ρ hs hπ hM ys yr hys hyr
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hZ ℚ_[g]
  obtain ⟨hn, ν₁, ν₂, Λ, h₁, h₂, hΛ0, hΛ⟩ := hM
  subst hn
  have hμ₁ : GlobalTheory.SplitWeil.IsUnram (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹) :=
    isUnram_mul (isUnram_of_supp h₁) (isUnram_inv (isUnram_absPow _ _))
  have hμ₂ : GlobalTheory.SplitWeil.IsUnram (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹) :=
    isUnram_mul (isUnram_of_supp h₂) (isUnram_inv (isUnram_absPow _ _))
  refine ⟨_, _, hμ₁, hμ₂, ?_⟩
  let T : π.IntertwiningMap (prod₂ (twist σ (detChar (Fin a) (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹)))
      (twist ρ (detChar (Fin b) (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹)))) :=
    { toFun := fun v => ⟨⟨fun x => Λ (π x v), fun q x => by
          show Λ (π (q * x) v) = _
          rw [map_mul, Module.End.mul_apply]
          exact law π σ ρ ν₁ ν₂ Λ hΛ q (π x v)⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hs v).mem_nhds (by simp)) fun h hh => by
          have hh' : π h v = v := hh
          refine Subtype.ext (funext fun x => ?_)
          show Λ (π (x * h) v) = Λ (π x v)
          rw [map_mul, Module.End.mul_apply, hh'])⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by
        show Λ (π x (v + w)) = Λ (π x v) + Λ (π x w)
        rw [map_add (f := _), map_add (f := _)]))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by
        show Λ (π x (c • v)) = c • Λ (π x v)
        rw [map_smul, map_smul]))
      isIntertwining' := fun h => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
        show Λ (π x (π h v)) = Λ (π (x * h) v)
        rw [map_mul, Module.End.mul_apply])) }
  have hT : Function.Injective T := by
    haveI := hπ
    refine (Representation.IsIrreducible.injective_or_eq_zero T).resolve_right fun h0 => hΛ0 (LinearMap.ext fun v => ?_)
    have h1 : (T v).1.1 1 = 0 := by rw [h0]; rfl
    change Λ (π 1 v) = 0 at h1
    simpa using h1
  have hσ' := hys.tw _ (isSmoothChar_of_isUnram hμ₁)
  have hρ' := hyr.tw _ (isSmoothChar_of_isUnram hμ₂)
  obtain ⟨φ⟩ := nonempty_prod₂_equiv_prodIrr _ hσ'.isSmooth hσ'.isIrreducible _ hρ'.isSmooth hρ'.isIrreducible
    (Fin.sum_univ_two _)
  have hsub := (IsSubquotient.of_injective T hT).trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have key := SupportRing.hasSupport_of_isSubquotient_prodIrr hΨ
    (t := ![_, _]) (Fin.forall_fin_two.2 ⟨hσ'.of_equiv (IrrGL.equivOf _ _ _), hρ'.of_equiv (IrrGL.equivOf _ _ _)⟩)
    hπ hsub
  rw [Fin.sum_univ_two] at key
  exact key

end GlobalTheory.IndChain.SuppStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharLocalEqOneOfTrivialOnNormsSplit
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open _root_.GlobalTheory

namespace GlobalTheory.NormKill

theorem loc_eq_one_of_compNorm_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ε : Formalism.L2.Host.HChar (maximalRealSubfield E)),
    compNorm E ε = 1 → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v →
    ∀ x, ε.loc v x = 1 := by
  intro E _ _ _ ε hε v hv x
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _

  have hnorm : Neutral.B1.localIdele (maximalRealSubfield E) v x ∈
      GlobalTheory.QuadSymbol.normGroup (maximalRealSubfield E) E
        (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) := by
    rw [GlobalTheory.IdeleNormChar.mem_normGroup_iff_everywhereNorm]
    refine ⟨fun w => ?_, fun w => ?_⟩
    · by_cases hw : w = v
      · subst hw
        have hx : GlobalTheory.IdeleNormChar.finComp (Neutral.B1.localIdele (maximalRealSubfield E) w x) w = x :=
          Units.ext (Neutral.B1.localIdele_snd_self _ w x)
        rw [hx]
        exact GlobalTheory.LFun.mem_normGroup_of_isSplit h2 hv x
      · have h1 : GlobalTheory.IdeleNormChar.finComp (Neutral.B1.localIdele (maximalRealSubfield E) v x) w = 1 := by
          apply Units.ext
          show (Neutral.B1.finiteSingle (maximalRealSubfield E) v (x : v.adicCompletion _)) w = 1
          exact GlobalTheory.LFun.finSingle_ne hw _
        rw [h1]
        exact one_mem _
    · have h1 : GlobalTheory.IdeleNormChar.infComp (Neutral.B1.localIdele (maximalRealSubfield E) v x) w = 1 :=
        Units.ext rfl
      rw [h1]
      exact one_mem _

  obtain ⟨z, hz⟩ := hnorm
  let y : (AdeleRing (𝓞 E) E)ˣ :=
    Units.map (GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (GlobalTheory.GalOfCusp.isCMExt_real E)).toRingHom.toMonoidHom z
  have hy : GlobalTheory.GalOfCusp.ideleNorm E y = Neutral.B1.localIdele (maximalRealSubfield E) v x := by
    apply Units.ext
    show Algebra.norm _ ((GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (GlobalTheory.GalOfCusp.isCMExt_real E)).symm
      ((GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (GlobalTheory.GalOfCusp.isCMExt_real E)) (z : _))) = _
    rw [RingEquiv.symm_apply_apply]
    exact congrArg Units.val hz
  have key : (GlobalTheory.GalOfCusp.compNorm E ε).1 y = (1 : Formalism.L2.Host.HChar E).1 y :=
    congrArg (fun χ : Formalism.L2.Host.HChar E => χ.1 y) hε
  rw [GlobalTheory.GalOfCusp.compNorm_apply, hy] at key
  exact key

end GlobalTheory.NormKill
end
end

