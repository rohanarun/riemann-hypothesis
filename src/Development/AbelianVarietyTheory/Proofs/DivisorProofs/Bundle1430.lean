module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralTypeTestVanish
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0840
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicIdempotentGivesDualStableSubspaces
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.IdemIsotropic

open Matrix Formalism.UG

variable {D : D7}

theorem hT_eq_hform (V : HSp D) (x y : V.V) :
    V.hT x y = hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram (V.frame.repr x) (V.frame.repr y) := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hform,
    HSpace.gram, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show _ = star _ * _ * _
  rw [starRingEnd_apply]
  ring

theorem hform_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J M N : Matrix n n A) (a b : n → A) :
    hform σ J (M *ᵥ a) (N *ᵥ b) = hform σ (cT σ M * J * N) a b := by
  have h2 : (fun i => σ ((M *ᵥ a) i)) = (M.map σ) *ᵥ (fun i => σ (a i)) := by
    funext i; simp [Matrix.mulVec, dotProduct]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.hform_eq, GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.hform_eq, h2, Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, cT, Matrix.mul_assoc]

theorem hform_zero {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A) (a b : n → A) :
    hform σ (0 : Matrix n n A) a b = 0 := by
  simp [hform]

theorem cT_sub' {A : Type} [CommRing A] {n : Type} (σ : A →+* A) (M N : Matrix n n A) :
    cT σ (M - N) = cT σ M - cT σ N := by
  ext i j; simp [cT]

theorem hT_toLin (V : HSp D) (M N : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (a b : V.V) :
    V.hT (Matrix.toLin V.frame V.frame M a) (Matrix.toLin V.frame V.frame N b) =
      hform (D.sp.cm.sig : D.host.E →+* D.host.E) (cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * N)
        (V.frame.repr a) (V.frame.repr b) := by
  rw [hT_eq_hform, Matrix.repr_toLin, Matrix.repr_toLin, hform_mulVec]

theorem gram_herm (V : HSp D) : cT (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram = V.gram := by
  refine Matrix.ext fun i j => ?_
  show star (V.hT (V.frame j) (V.frame i)) = V.hT (V.frame i) (V.frame j)
  exact V.herm.eq (V.frame j) (V.frame i)

theorem idem_isotropic_pair : ∀ {D : D7} {V : HSp D} (γ : GF V) (ε : Matrix (Fin V.rank) (Fin V.rank) D.host.E), ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg γ.1.1 → ε * ε = ε → ε ≠ 0 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) ε * V.gram * ε = 0 → ∃ X X' : Submodule D.host.E V.V, X ≠ ⊥ ∧ X ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X ∧ X' ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X' ∧ (∀ x ∈ X, GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ X) ∧ (∀ x ∈ X', GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ X') ∧ (∀ x ∈ X, (∀ y ∈ X', V.hD x y = 0) → x = 0) ∧ (∀ y ∈ X', (∀ x ∈ X, V.hD x y = 0) → y = 0) := by
  intro D V γ ε hmem hidem hne hiso
  set σ := (D.sp.cm.sig : D.host.E →+* D.host.E) with hσ
  set J := V.gram with hJdef
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.2 (GlobalTheory.Mem.Vol.hspace_gram_det_ne_zero V)
  have hJJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hJJ' : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul _ hdet
  have cancel : ∀ A B : Matrix (Fin V.rank) (Fin V.rank) D.host.E, J * A = J * B → A = B := by
    intro A B h
    rw [← Matrix.one_mul A, ← Matrix.one_mul B, ← hJJ', Matrix.mul_assoc, h, ← Matrix.mul_assoc]
  set ε' := J⁻¹ * cT σ ε * J with hε'
  have hR : J * ε' = cT σ ε * J := by
    rw [hε', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  clear_value ε'
  have hTL : ∀ (M N : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (a b : V.V),
      V.hT (Matrix.toLin V.frame V.frame M a) (Matrix.toLin V.frame V.frame N b) =
        hform σ (cT σ M * J * N) (V.frame.repr a) (V.frame.repr b) := hT_toLin V
  have hσσ : ∀ e, σ (σ e) = e := fun e => star_star e
  have cTcT : ∀ M : Matrix (Fin V.rank) (Fin V.rank) D.host.E, cT σ (cT σ M) = M := by
    intro M; ext i j; simp [cT, hσσ]
  have herm : cT σ J = J := gram_herm V
  have hR' : cT σ ε' * J = J * ε := by
    have h := congrArg (cT σ) hR
    rw [cT_mul, cT_mul, herm, cTcT] at h
    exact h
  have h0 : ε' * ε = 0 := cancel _ _ (by rw [← Matrix.mul_assoc, hR, hiso, Matrix.mul_zero])
  set g := (γ.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) with hg
  set gi := ((γ.1⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) with hgi
  have hγ : cT σ g * J * g = J := γ.2
  have hggi : g * gi = 1 := Units.mul_inv γ.1
  have hgig : gi * g = 1 := Units.inv_mul γ.1
  have hmem' : ε ∈ Algebra.adjoin D.host.E {g} := hmem
  have hJg : J * g = cT σ gi * J := by
    calc J * g = cT σ (g * gi) * J * g := by rw [hggi, cT_one, Matrix.one_mul]
      _ = cT σ gi * (cT σ g * J * g) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ gi * J := by rw [hγ]
  have hεgi : Commute gi ε :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hmem' (by rw [Commute, SemiconjBy, hgig, hggi])
  have hε'g : ε' * g = g * ε' := cancel _ _ (by
    rw [← Matrix.mul_assoc, hR, Matrix.mul_assoc, hJg, ← Matrix.mul_assoc J g, hJg, Matrix.mul_assoc, hR,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, ← cT_mul, hεgi.eq])
  have hcomm : Commute ε' ε := Algebra.commute_of_mem_adjoin_singleton_of_commute hmem' hε'g
  have hgε : Commute g ε := Algebra.commute_of_mem_adjoin_singleton_of_commute hmem' (Commute.refl g)
  have h1 : ε * ε' = 0 := by rw [← hcomm.eq, h0]
  have mA : cT σ (1 - ε - ε') * J * ε = 0 := by
    rw [cT_sub', cT_sub', cT_one, Matrix.sub_mul, Matrix.sub_mul, Matrix.sub_mul, Matrix.sub_mul,
      Matrix.one_mul, hiso, hR', Matrix.mul_assoc, hidem, sub_zero, sub_self]
  have mB : cT σ ε' * J * (1 - ε - ε') = 0 := by
    rw [hR', Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, Matrix.mul_assoc,
      hidem, h1, Matrix.mul_zero, sub_self, sub_zero]
  have mC : cT σ ε' * J * ε' = 0 := by rw [hR', Matrix.mul_assoc, h1, Matrix.mul_zero]
  have split : ∀ v : V.V, v = Matrix.toLin V.frame V.frame ε v + Matrix.toLin V.frame V.frame ε' v +
      Matrix.toLin V.frame V.frame (1 - ε - ε') v := by
    intro v
    simp only [map_sub, Matrix.toLin_one, LinearMap.sub_apply, LinearMap.id_apply]
    abel
  have mem_perp : ∀ (W : Submodule D.host.E V.V) (y : V.V),
      y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W ↔ ∀ w ∈ W, V.hT w y = 0 := by
    intro W y
    simp [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf, LinearMap.mem_ker]
  have ratAct_eq : ∀ x, GlobalTheory.Cusp.ratAct D.sp.cm V γ x = Matrix.toLin V.frame V.frame g x := fun _ => rfl
  refine ⟨LinearMap.range (Matrix.toLin V.frame V.frame ε), LinearMap.range (Matrix.toLin V.frame V.frame ε'),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [LinearMap.range_eq_bot] at h
    exact hne ((Matrix.toLin V.frame V.frame).map_eq_zero_iff.1 h)
  · rintro _ ⟨b, rfl⟩
    rw [mem_perp]
    rintro _ ⟨a, rfl⟩
    rw [hTL, hiso, hform_zero]
  · rintro _ ⟨b, rfl⟩
    rw [mem_perp]
    rintro _ ⟨a, rfl⟩
    rw [hTL, mC, hform_zero]
  · rintro _ ⟨a, rfl⟩
    refine ⟨Matrix.toLin V.frame V.frame g a, ?_⟩
    rw [ratAct_eq, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← Matrix.toLin_mul, ← Matrix.toLin_mul,
      hgε.eq]
  · rintro _ ⟨a, rfl⟩
    refine ⟨Matrix.toLin V.frame V.frame g a, ?_⟩
    rw [ratAct_eq, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← Matrix.toLin_mul, ← Matrix.toLin_mul,
      hε'g]
  · rintro _ ⟨a, rfl⟩ hy
    refine V.nondeg.2 _ fun v => ?_
    rw [split v, map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hTL ε ε, hiso, hform_zero,
      hTL (1 - ε - ε') ε, mA, hform_zero, zero_add, add_zero]
    exact hy _ ⟨v, rfl⟩
  · rintro _ ⟨b, rfl⟩ hx
    refine V.nondeg.1 _ fun v => ?_
    have e1 : V.hT (Matrix.toLin V.frame V.frame ε' b) v =
        V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame ε v) +
        V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame ε' v) +
        V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame (1 - ε - ε') v) := by
      conv_lhs => rw [split v]
      simp only [map_add (f := _)]
    have e2 : V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame ε' v) = 0 := by
      rw [hTL, mC, hform_zero]
    have e3 : V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame (1 - ε - ε') v) = 0 := by
      rw [hTL, mB, hform_zero]
    have e4 : V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame ε v) = 0 := hx _ ⟨v, rfl⟩
    linear_combination e1 + e2 + e3 + e4

end GlobalTheory.IdemIsotropic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevMoveCommLevelMapOfTrivialMod
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open OverMove in
theorem levMove_comm_levelMap_of_trivial_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → ∀ (ρ₂ : d.Xo₂.X ⟶ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂) (g gA : Dw.La →ₗ[𝓞 E] Dw.La), IsIso ρ₂ → IsLevMove ρ₂ ν₂ g gA → (∀ a, g a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ρ₂ ≫ d.r = d.r ∧ ν₂.φ ≫ d.m.φ = d.m.φ := by
  intro E _ _ _ H Dw l Xo c n d _ hLev hA2 hover ρ₂ ν₂ g gA _ hmv hg
  have hL : Out.Laws := _root_.GlobalTheory.abelianSchemeLaws_all.1
  obtain ⟨hd, hM, -, -, -, hE, -⟩ := hLev
  have hA : l.A = 1 := Nat.eq_one_of_dvd_one (hA2 ▸ hd.2.2)
  have hK : KA l ≤ KA d.l₂ := by
    show IntermediateField.adjoin ℚ {H.rt0, zeta l.A} ≤ IntermediateField.adjoin ℚ {H.rt0, zeta d.l₂.A}
    rw [hA, hA2]
  have hb := hover hK
  have hred : IsReduced d.Xo₂.X := by
    haveI := d.Xo₂.smooth
    exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ d.Xo₂.s
      (SmoothOfRelativeDimension.smooth Dw.dim _)).1
  have hpd : d.pd = d.l₂.M / l.M := by
    rw [hM, Nat.mul_div_cancel_left _ (lt_of_lt_of_le (by norm_num) l.three_le)]
  have L₁ : Lev d.m := ⟨hpd ▸ hE.1, hE.2⟩
  obtain ⟨o, ⟨p⟩⟩ := obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (d.r ≫ Xo.s) d.r rfl rfl
    (by rw [LevelFibre.spMap_id', Category.comp_id]) Xo.univ
  obtain ⟨u, hu, F₁⟩ := exists_fib p L₁ (x := 𝟙 _) (Category.id_comp _)
  obtain ⟨u₂, hu₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν₂ u
  have hA1 : ∀ a, d.Xo₂.univ.etaA a = 1 := fun a => by
    have := d.Xo₂.univ.etaA_ker a
    rwa [hA2, one_smul] at this
  have hfix : ∀ a, (d.Xo₂.univ.eta (g a) ^ (d.l₂.M / l.M)).left = (d.Xo₂.univ.eta a ^ (d.l₂.M / l.M)).left :=
    fun a => by
      apply d.m.cart.1.hom_ext
      · rw [L₁.1, L₁.1, LevelActionLaws.eta_congr Xo (hg a)]
      · rw [LevelFibre.sec_w, LevelFibre.sec_w]
  have hone : (1 : 𝟙_ (Over d.Xo₂.X) ⟶ d.Xo₂.univ.t.G).left ≫ ν₂.φ = ρ₂ ≫ (1 : 𝟙_ (Over d.Xo₂.X) ⟶ d.Xo₂.univ.t.G).left := by
    have := hmv.2.2 0
    rwa [hA1, hA1] at this
  have F₂ : Fib o u₂ := by
    refine ⟨fun a => ?_, fun a => ?_⟩
    · rw [hu₂, ← Category.assoc, F₁.1, Category.id_comp, ← hfix, pow_left_comp ν₂ (hmv.2.1 a), Category.id_comp, hfix]
    · rw [hu₂, ← Category.assoc, F₁.2, Category.id_comp, Category.id_comp, hA1, one_pow]
      exact hone
  obtain ⟨q, hq⟩ := exists_objMap F₂ L₁
  have hr : (𝟙 _ ≫ ρ₂) ≫ d.r = d.r := by
    refine (Xo.rep d.Xo₂.X (d.r ≫ Xo.s) hred o).unique ⟨?_, ⟨q⟩⟩ ⟨rfl, ⟨p⟩⟩
    rw [Category.id_comp, Category.assoc, hb, ← Category.assoc, hmv.1]
  obtain ⟨q', hq'⟩ := LevelFibre.sab_cast hr q.toSABMap
  have e : p.toSABMap.φ = q'.φ := sabMap_eq_of_level_eq hL obj_isAbelianScheme_dim_rigidified_sym E H Dw l _ _ _ _ _ _
    _ _ Xo.univ o _ (Or.inl hred) p.toSABMap q' fun a => ⟨_, p.eta a, by rw [hq']; exact (q.eta a).trans (by rw [hr])⟩
  rw [hq', hq, ← hu, hu₂, Category.assoc] at e
  have : IsIso u.φ := u.cart.1.isIso_fst_of_isIso
  refine ⟨by simpa using hr, ((cancel_epi u.φ).1 e).symm⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieTypeOfUnif
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

noncomputable section

namespace GlobalTheory.LieEigenspaceFinrank

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)}

theorem isLieEigen_iff (he : IsExp y e) {F : Type} [Field F] [NumberField F]
    (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (act : OAct (𝓞 F) G)
    (hM : ∀ c z, e (φ c *ᵥ z) = e z ≫ act.act c) (τ : F →+* ℂ) (τ' : 𝓞 F →+* ℂ)
    (hτ : ∀ c : 𝓞 F, τ (c : F) = τ' c) (w : Fin g → ℂ) :
    IsLieEigen act y τ' (expDer he w) ↔ w ∈ eigSp φ τ := by
  rw [mem_eigSp]
  constructor
  · intro h c
    rw [hτ]
    exact (expDer_eigen_iff he (φ c) (act.act c) (hM c) (τ' c) w).1 (h.2 c)
  · intro h
    refine ⟨expDer_base he w, fun c => ?_⟩
    exact (expDer_eigen_iff he (φ c) (act.act c) (hM c) (τ' c) w).2 (by rw [← hτ]; exact h c)

theorem comb_iff (he : IsExp y e) {n : ℕ} (w : Fin n → Fin g → ℂ) (c : Fin n → ℂ) (z : Fin g → ℂ) :
    (∃ u : Fin n → (epsPt y ⟶ G), (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (expDer he (w i)).left) ∧
      expDer he z = (List.ofFn u).prod) ↔ z = ∑ i, c i • w i := by
  constructor
  · rintro ⟨u, hu, hz⟩
    have hu' : u = fun i => expDer he (c i • w i) := by
      funext i
      exact Over.OverMorphism.ext (by rw [hu i, expDer_smul he])
    rw [hu', expDer_prod he (fun i => c i • w i)] at hz
    exact expDer_injective he hz
  · intro hz
    refine ⟨fun i => expDer he (c i • w i), fun i => expDer_smul he _ _, ?_⟩
    rw [expDer_prod he (fun i => c i • w i), hz]

theorem finrank_eigSp (he : IsExp y e) {F : Type} [Field F] [NumberField F]
    (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (act : OAct (𝓞 F) G)
    (hM : ∀ c z, e (φ c *ᵥ z) = e z ≫ act.act c) (τ : F →+* ℂ) (τ' : 𝓞 F →+* ℂ)
    (hτ : ∀ c : 𝓞 F, τ (c : F) = τ' c) (n : ℕ) (h : LieMult act y τ' n) :
    Module.finrank ℂ (eigSp φ τ) = n := by
  obtain ⟨v, hv, hb⟩ := h
  choose w hw using fun i => expDer_surj he (v i) (hv i).1
  obtain rfl : v = fun i => expDer he (w i) := funext fun i => (hw i).symm
  have hwm : ∀ i, w i ∈ eigSp φ τ := fun i => (isLieEigen_iff he φ act hM τ τ' hτ _).1 (hv i)
  have key : ∀ z ∈ eigSp φ τ, ∃! c : Fin n → ℂ, z = ∑ i, c i • w i := by
    intro z hz
    have := hb _ ((isLieEigen_iff he φ act hM τ τ' hτ z).2 hz)
    simpa only [comb_iff he w] using this
  let L : (Fin n → ℂ) →ₗ[ℂ] eigSp φ τ := Fintype.linearCombination ℂ (fun i => (⟨w i, hwm i⟩ : eigSp φ τ))
  have hL : ∀ c, (L c : Fin g → ℂ) = ∑ i, c i • w i := by
    intro c
    simp [L, Fintype.linearCombination_apply]
  have hbij : Function.Bijective L := by
    rw [Function.bijective_iff_existsUnique]
    intro z
    obtain ⟨c, hc, hu⟩ := key z.1 z.2
    refine ⟨c, Subtype.ext (by rw [hL]; exact hc.symm), fun c' hc' => hu c' ?_⟩
    exact (congrArg Subtype.val hc').symm.trans (hL c')
  rw [← (LinearEquiv.ofBijective L hbij).finrank_eq]
  simp

theorem lie_type_of_unif (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ))
    (h : SmoothOfRelativeDimension D.g o.A.hom) (hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB)
    (D' : PLat D.O D.inv) (t : D.La → D'.La) (Q : D'.La →+ (Fin D.g → ℂ))
    (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ (o.fam h hL).A))
    (hU : UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 (Sp ℂ)) e) (τ : Fin D.a → D.F →+* ℂ)
    (hτ : ∀ (i : Fin D.a) (c : 𝓞 D.F), τ i (c : D.F) = σ (b.t i c)) :
    (∀ i, Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i)) = D.m) ∧
      ∀ u : Fin D.g → ℂ, ρ (algebraMap (𝓞 D.F) D.O D.ω) *ᵥ u = σ b.ρ • u →
        u ∈ ⨆ i, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i) := by
  have he : IsExp (G := o.A) (𝟙 (Sp ℂ)) e := hU.2.2.1
  have hM : ∀ (a : D.O) z, e (ρ a *ᵥ z) = e z ≫ o.act.act a := hU.2.2.2.2.1
  have hx : 𝟙 (Sp ℂ) ≫ spMap σ = spMap σ := Category.id_comp _
  have hM' : ∀ (c : 𝓞 D.F) z, e ((ρ.comp (algebraMap (𝓞 D.F) D.O)) c *ᵥ z) = e z ≫ (o.act.toF D).act c :=
    fun c z => hM _ z
  refine ⟨fun i => ?_, fun u hu => ?_⟩
  · exact finrank_eigSp (G := o.A) he _ (o.act.toF D) hM' (τ i) (σ.comp (b.t i)) (hτ i) _
      (o.lieRank ℂ (𝟙 _) σ hx i)
  · obtain ⟨v, hv, hprod⟩ := o.lie ℂ σ (𝟙 _) hx (expDer (G := o.A) he u)
      ⟨expDer_base he u, (expDer_eigen_iff (G := o.A) he _ _ (hM _) (σ b.ρ) u).2 hu⟩
    choose w hw using fun i => expDer_surj (G := o.A) he (v i) (hv i 0).1
    obtain rfl : v = fun i => expDer (G := o.A) he (w i) := funext fun i => (hw i).symm
    have hu' : u = ∑ i, w i := expDer_injective he (hprod.trans (expDer_prod he w))
    rw [hu']
    refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ?_
    exact (isLieEigen_iff (G := o.A) he _ (o.act.toF D) hM' (τ i) (σ.comp (b.t i)) (hτ i) _).1
      ⟨(hv i 0).1, fun c => (hv i c).2⟩

end GlobalTheory.LieEigenspaceFinrank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSectionFiniteInOpenOffBadForm
section
set_option autoImplicit false

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

noncomputable section

namespace GlobalTheory.HSShort.Supp

theorem finite_of_finite_pts {k : Type} [Field k] (S : LinSys k) (hS : S.IsVariety) (Ω : Type) [Field Ω]
    [Algebra k Ω] [IsAlgClosed Ω] (Z : Set S.Y) (hZ : IsClosed Z)
    (h : {x : S.Pt Ω | ptOf x.1 ∈ Z}.Finite) : Z.Finite := by
  haveI := hS.smooth
  haveI : Smooth S.str := SmoothOfRelativeDimension.smooth S.D S.str
  haveI : JacobsonSpace S.Y := LocallyOfFiniteType.jacobsonSpace S.str
  have hf : (Z ∩ closedPoints S.Y).Finite := by
    refine (h.image fun x => ptOf x.1).subset ?_
    rintro y ⟨hyZ, hy⟩
    by_contra hne
    refine subset_of_forall_pt_mem k S hS Ω {y} hy ∅ isOpen_empty (fun x hx => hne ⟨x, ?_, hx⟩) rfl
    have e : ptOf x.1 = y := hx
    change ptOf x.1 ∈ Z
    rw [e]
    exact hyZ
  have hc : IsClosed (Z ∩ closedPoints S.Y) := by
    rw [← Set.biUnion_of_singleton (Z ∩ closedPoints S.Y)]
    exact hf.isClosed_biUnion fun y hy => hy.2
  rw [← JacobsonSpace.closure_inter_closedPoints hZ, hc.closure_eq]
  exact hf

theorem exists_finite_lines {K : Type} [Field K] [IsAlgClosed K] {N : ℕ} {G : MvPolynomial (Fin 1 × Fin N) K}
    (hG : G ≠ 0) : ∃ R : Set (Fin N → K), R.Finite ∧ ∀ y : Fin N → K, y ≠ 0 →
      (∀ ξ : Fin N → K, ∑ j, ξ j * y j = 0 → eval (fun p => ξ p.2) G = 0) → ∃ r ∈ R, ∃ c : K, y = c • r := by
  classical
  refine ⟨(fun p : MvPolynomial (Fin 1 × Fin N) K => fun j => AddMonoidAlgebra.coeff p (Finsupp.single ((0 : Fin 1), j) 1)) ''
    (UniqueFactorizationMonoid.factors G).toFinset, (Finset.finite_toSet _).image _, fun y hy hz => ?_⟩
  have irr := HyperplaneFactor.irreducible_lin hy
  obtain ⟨n, hn⟩ := HyperplaneFactor.exists_dvd_pow_of_zeros (a := lin y) (b := G) fun x hx => by
    have e : (fun p : Fin 1 × Fin N => x (0, p.2)) = x := by
      funext ⟨i, j⟩
      rw [Subsingleton.elim i 0]
    have h1 := hz (fun j => x (0, j)) (by rwa [HyperplaneFactor.eval_lin] at hx)
    simpa only [e] using h1
  obtain ⟨q, hq, ha⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hG irr (irr.prime.dvd_of_dvd_pow hn)
  obtain ⟨a, ha⟩ := ha.symm
  obtain ⟨t, -, ht⟩ := isUnit_iff_eq_C_of_isReduced.1 a.isUnit
  rw [ht, mul_comm] at ha
  refine ⟨_, ⟨q, by simpa using hq, rfl⟩, t, funext fun j => ?_⟩
  have h1 := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single ((0 : Fin 1), j) 1)) ha
  rw [coeff_C_mul, HyperplaneFactor.coeff_lin] at h1
  simpa using h1.symm

theorem finite_and_inOpen : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → ∀ (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), IsChowForm T.imageIdeal T.D δ f → ∀ (g : MvPolynomial (Fin T.N) F), (∀ (K : Type) [Field K] [Algebra F K] (x : T.Pt K), ptOf x.1 ∈ T.bd → aeval (T.coords x.1) g = 0) → (∀ (K : Type) [Field K] [Algebra F K] (y : Fin T.N → K), {x : T.Pt K | aeval (T.coords x.1) g ≠ 0 ∧ ∃ c : K, T.coords x.1 = c • y}.Finite) → ∀ (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E), spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f ≠ 0 → (∀ x ∈ T.geomPts E (T.linSection E s), aeval (T.coords (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1) g ≠ 0) → ((T.linSection E s).support : Set (T.toLinSys.baseChange E).Y).Finite ∧ T.InOpen E (T.linSection E s) := by
  intro F _ _ T hT δ f hf g hbd hfin E _ _ s hG hg
  have hv : (T.toLinSys.baseChange E).IsVariety := hT.alg.variety.baseChange E
  refine ⟨finite_of_finite_pts _ hv (AlgebraicClosure E) _ (T.linSection E s).support.isClosed ?_, ?_⟩
  · obtain ⟨R, hR, hl⟩ := exists_finite_lines hG
    refine ((hR.biUnion fun y _ => hfin (AlgebraicClosure E) y).preimage
      (T.toLinSys.toBase_bijective E (AlgebraicClosure E)).1.injOn).subset fun x hx => ?_
    have hm : x ∈ T.geomPts E (T.linSection E s) := (LinSys.mem_subPts_iff _ _ x).2 hx
    have hy := hT.alg.bpf.coords_ne_zero (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1
    obtain ⟨r, hr, hc⟩ := hl _ hy fun ξ hξ => by
      rw [EtaleSection.eval_spec]
      refine (_root_.GlobalTheory.ChowZeroExt.zero_set_ext F T.D T.N δ _ f hf).1 _ _ ξ _ hy (fun p hp => ?_)
        ((T.toLinSys.mem_subPts_cut_baseChange_iff E s x).1 hm) hξ
      have := T.toLinSys.eval₂_coords_eq_zero (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1 hp
      rwa [LinSys.baseHom_ptOver] at this
    exact Set.mem_biUnion hr ⟨hg x hm, hc⟩
  · exact subset_of_forall_pt_mem E _ hv (AlgebraicClosure E) _ (T.linSection E s).support.isClosed
      (T.toLinSys.bcFst E ⁻¹' (T.U : Set T.Y)) (T.U.isOpen.preimage (T.toLinSys.bcFst E).continuous)
      fun x hx hb => hg x ((LinSys.mem_subPts_iff _ _ x).2 hx)
        (hbd (AlgebraicClosure E) (LinSys.toBase x) hb)

end GlobalTheory.HSShort.Supp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalQuotientTransitionCocycleStatement
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_quotient_transition_cocycle : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)
    (B : ∀ j, Over (𝒰.X j)) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j) (b : ∀ j k, pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left),
    (∀ j, Flat (q j).left) → (∀ j, Surjective (q j).left) → (∀ j, QuasiCompact (q j).left) →
    (∀ j k, b j k ≫ (B k).hom = pullback.snd _ _) →
    (∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ (q k).left) →
    ∀ (j k l : 𝒰.I₀) (T : Scheme.{0}) (x : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k))
      (y : T ⟶ pullback ((B k).hom ≫ 𝒰.f k) (𝒰.f l)) (z : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f l)),
      x ≫ b j k = y ≫ pullback.fst _ _ → x ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ → y ≫ b k l = z ≫ b j l := by
  first | (exact @GlobalTheory.cocycle_local_quotient_transition) | (exact GlobalTheory.cocycle_local_quotient_transition) | (intros; apply GlobalTheory.cocycle_local_quotient_transition  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorCommuteWeightVectorFunctionEStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryHeckeOperator_commute_weightVectorFunction_explicit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (w : Wsp lam), hop S K' f (phiFun lam F w) = phiFun lam (hopM S lam K' f F) w := by
  first | exact @GlobalTheory.BCT.TrKer.hop_phiFun_comm | exact GlobalTheory.BCT.TrKer.hop_phiFun_comm | (intros; apply GlobalTheory.BCT.TrKer.hop_phiFun_comm <;> assumption)
end

