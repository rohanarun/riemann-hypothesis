module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0200
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.RightInvariantOfCovolume
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LeviFactorCharactersSplitPlace
section
namespace I195MixedCoordinates_a6b848dc850707252261af49

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_a6b848dc850707252261af49

public noncomputable abbrev _root_.I195MixedCoordinates_3f9f8d8466fd251acacc5207.source :=
  @_root_.I195MixedCoordinates_a6b848dc850707252261af49.source

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
namespace GlobalTheory.LeviSplitChar

theorem circle_eq_one_of_pos {u : Circle} {t : ℝ} (ht : 0 < t) (h : (u : ℂ) = t) : u = 1 := by
  have h1 : ‖(u : ℂ)‖ = 1 := Circle.norm_coe u
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at h1
  apply Circle.ext
  rw [h, h1, Circle.coe_one]
  simp

variable {D : D7}

theorem suppAt_one (e : AE D) (V : HSp D) : SuppAt e V 1 := by
  intro i j
  simp [Formalism.L2.Theta.SuppAt, Formalism.L2.Theta.mt]

theorem isDetAt_one (e : AE D) (V : HSp D) : IsDetAt e V 1 1 := by
  simp [Formalism.L2.Theta.IsDetAt, Formalism.L2.Theta.mt]

end GlobalTheory.LeviSplitChar

namespace GlobalTheory.LeviSplitChar

variable {D : D7}

theorem exists_form (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ)
    (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T)
    (hω : IsWeilDatumO ψ S T χS χT om) (hω₀ : IsWeilDatumO ψ S₀ T χS χT om₀)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕)
    (α : GL (Fin ρ) (AE D) →* Circle) (ξ : GA D S₀ →* Circle)
    (H : ∀ a g f, IsThetaFunO ψ S T f → (_root_.I195MixedCoordinates_a6b848dc850707252261af49.source d) T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) 0 =
      ((α a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ) * (ξ g : ℂ)) • om₀ (g, 1) ((_root_.I195MixedCoordinates_a6b848dc850707252261af49.source d) T ψ μ 𝓕 (f) 0))
    (e : AE D) (he : IsSplitIdem D e) :
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧
      (∃ f, IsThetaFunO ψ S T f ∧ ℓ f ≠ 0) ∧
      ∀ a g, SuppAt e S₀ g → ∀ x₀, IsDetAt e S₀ g x₀ → ∃ R : ℝ, 0 < R ∧ ∀ f, IsThetaFunO ψ S T f →
        ℓ (om (d.levi a * d.emb0 g, 1) f) = (R : ℂ) * ((α a : ℂ) * (ξ g : ℂ) * (splitFacO χS χT x₀ 1 : ℂ)) * ℓ f := by
  obtain ⟨ℓ₀, hinv₀, f₀, hf₀, hne₀⟩ := _root_.GlobalTheory.HalfCoinv.exists_invariant_form D ψ hω.std S₀ T e he
  obtain ⟨ℓ, hinv, hne, hcmp⟩ := _root_.GlobalTheory.SplitPlaceForm.exists_form_of_core D ψ hω.std S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ hinv₀ ⟨f₀, hf₀, hne₀⟩
  refine ⟨ℓ, hinv, hne, fun a g hg x₀ hx₀ => ?_⟩
  obtain ⟨r₀, hr₀, hsp₀⟩ := hω₀.om_split e he g 1 hg (suppAt_one e T) x₀ 1 hx₀ (isDetAt_one e T)
  obtain ⟨r, hr, hc⟩ := hcmp 1 a
  have hmv := (_root_.GlobalTheory.MixValues.mixed_values D ψ hω.std).1 S S₀ T ρ d μ 𝓕 hμ
  have hbr := (_root_.GlobalTheory.Bridge.heis_bridge D ψ S S₀ T ρ d).2.2.2.2.2.2.1
  have hm := GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod_pos T.rank a
  refine ⟨r * r₀ * GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a, by positivity, fun f hf => ?_⟩
  have key := hc f (om (d.levi a * d.emb0 g, 1) f)
    ((α a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ) * (ξ g : ℂ) * (r₀ : ℂ) * (splitFacO χS χT x₀ 1 : ℂ))
    hf (hω.om_pres _ f hf) (fun x _ => ?_)
  · rw [key]; push_cast; ring
  · have hmove := (_root_.GlobalTheory.WMove.main D ψ S S₀ T ρ d χS χT om hω μ 𝓕 hμ f hf x).2.1 a g
    simp only [Units.val_one, Matrix.one_mul]
    change ℓ₀ (_root_.I195MixedCoordinates_a6b848dc850707252261af49.source d T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) x) =
      _ * ℓ₀ (_root_.I195MixedCoordinates_a6b848dc850707252261af49.source d T ψ μ 𝓕 f (x * a.1))
    change _root_.I195MixedCoordinates_a6b848dc850707252261af49.source d T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) x =
      _root_.I195MixedCoordinates_a6b848dc850707252261af49.source d T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) (heisO ψ S T (d.extX T (x * a.1)) f)) 0 at hmove
    have hb : _root_.I195MixedCoordinates_a6b848dc850707252261af49.source d T ψ μ 𝓕 f (x * a.1) =
        _root_.I195MixedCoordinates_a6b848dc850707252261af49.source d T ψ μ 𝓕 (heisO ψ S T (d.extX T (x * a.1)) f) 0 := hbr μ 𝓕 f (x * a.1)
    conv_lhs =>
      rw [hmove, H a g _ (GlobalTheory.TwistFactorCompare.isTheta_heisO hω.std hf _), ← hb, map_smul,
        smul_eq_mul, hsp₀ ℓ₀ hinv₀ _ (hmv f hf _)]
    ring

end GlobalTheory.LeviSplitChar

namespace GlobalTheory.LeviSplitChar

theorem levi_chars_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ (α : GL (Fin ρ) (AE D) →* Circle) (ξ : GA D S₀ →* Circle), (∀ a g f, IsThetaFunO ψ S T f → (_root_.I195MixedCoordinates_a6b848dc850707252261af49.source d) T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) 0 = ((α a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ) * (ξ g : ℂ)) • om₀ (g, 1) ((_root_.I195MixedCoordinates_a6b848dc850707252261af49.source d) T ψ μ 𝓕 (f) 0)) → ∀ e, IsSplitIdem D e → (∀ g, SuppAt e S₀ g → ξ g = 1) ∧ ∀ a : GL (Fin ρ) (AE D), (∀ i j, (e + cA D e) * (a.1 - 1) i j = (a.1 - 1) i j) → α a = (χT (Matrix.GeneralLinearGroup.det a))⁻¹ := by
  intro D ψ S S₀ T ρ d χS χT om om₀ hω hω₀ μ 𝓕 hμ α ξ H e he
  obtain ⟨ℓ, hinv, ⟨f, hf, hℓf⟩, hkey⟩ := exists_form ψ S S₀ T ρ d χS χT om om₀ hω hω₀ μ 𝓕 hμ α ξ H e he
  have hsd := _root_.GlobalTheory.splitLeviDet D S S₀ ρ d e he
  constructor
  · intro g hg
    obtain ⟨hS, x, hx₀, hx⟩ := hsd.1 g hg
    obtain ⟨R, hR, hk⟩ := hkey 1 g hg x hx₀
    obtain ⟨r', hr', hsp⟩ := hω.om_split e he (d.emb0 g) 1 hS (suppAt_one e T) x 1 hx (isDetAt_one e T)
    have h1 := hk f hf
    have h2 := hsp ℓ hinv f hf
    rw [map_one, one_mul] at h1
    rw [h1, map_one, Circle.coe_one] at h2
    have hs : (splitFacO χS χT x 1 : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have h3 : (R : ℂ) * (ξ g : ℂ) = r' := by
      have := mul_right_cancel₀ hℓf (by rw [← h2]; ring : ((R : ℂ) * (ξ g : ℂ)) * (splitFacO χS χT x 1 : ℂ) * ℓ f = (r' : ℂ) * (splitFacO χS χT x 1 : ℂ) * ℓ f)
      exact mul_right_cancel₀ hs this
    apply circle_eq_one_of_pos (div_pos hr' hR)
    have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    push_cast
    rw [← h3]
    field_simp
  · intro a ha
    obtain ⟨hS, x, hx, hχ⟩ := hsd.2 χT T.rank hω.hecT hω.resT a ha
    obtain ⟨R, hR, hk⟩ := hkey a 1 (suppAt_one e S₀) 1 (isDetAt_one e S₀)
    obtain ⟨r', hr', hsp⟩ := hω.om_split e he (d.levi a) 1 hS (suppAt_one e T) x 1 hx (isDetAt_one e T)
    have h1 := hk f hf
    have h2 := hsp ℓ hinv f hf
    rw [map_one, mul_one] at h1
    rw [h1] at h2
    simp only [splitFacO, map_one, inv_one, mul_one, Circle.coe_one, hχ, Circle.coe_mul, Circle.coe_inv] at h2
    have hd : ((χT (Matrix.GeneralLinearGroup.det a) : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have h3 : (R : ℂ) * ((α a : ℂ) * (χT (Matrix.GeneralLinearGroup.det a) : ℂ)) = r' := by
      have := mul_right_cancel₀ hℓf h2
      rw [← mul_assoc, this]
      field_simp
    have hu : α a * χT (Matrix.GeneralLinearGroup.det a) = 1 := by
      apply circle_eq_one_of_pos (div_pos hr' hR)
      have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
      push_cast
      rw [← h3]
      field_simp
    exact eq_inv_of_mul_eq_one_left hu

end GlobalTheory.LeviSplitChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftPairPositiveDefiniteWittIndexZeroCartan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.PairSetting

theorem main : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GlobalTheory.Cusp.wittIndex (Vc D i) = 0 ∧ (Wc D i).rank < D.R.t ∧ ∃ cA : GlobalTheory.Mem.Th.CptF (Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.HidaSetting R.θ (Wc D i) (Vc D i) (cart (R.MW i σ)) (fun _ => 1) D.R.t cA ∧ ∀ U ∈ R.Wall i σ, ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, U (fun ρ => v ρ) ∈ GlobalTheory.Cusp.A0 R.θ (Wc D i) cA := by
  intro D G _ _ Pl0 T' A Ks _ _ _ R F hC _ i σ
  have hi1 : 1 ≤ (i : ℕ) + 1 := Nat.le_add_left 1 _
  have hi2 : (i : ℕ) + 1 ≤ D.R.m := i.isLt
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ hi1 hi2
  have hV : (Vc D i).rank = D.R.nV := D.sp.V_rank _ hi1 hi2
  have hk := D.R.rank_add_five_le
  have hm := D.R.two_le_m
  obtain ⟨cA, hF, hcart, hJ, hA0⟩ := _root_.GlobalTheory.ChainOnto.RealData.multiplicityMap_value_kFinite_mem_cuspForms D R.θ hC.models.inf (Wc D i) (D.sp.W_sig _) _ (R.MW i σ)
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig (↑i + 1) (tauE D τ)
    rw [hC.models.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  refine ⟨GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Per.isAniso_of_posDef (D.sp.V_sig _) (hC.models.vpos i)), ?_, cA, ⟨?_, ?_, ?_, hC.models.inf, D.sp.W_sig _, hF, hcart, fun τ => ⟨by simp, by simp, by simpa using hpos τ⟩, hJ⟩, ?_⟩
  · rw [hW]; simp only [Ranks.r] at *; omega
  · rw [hW]; simp only [Ranks.r] at *; omega
  · simp only [Ranks.r] at *; omega
  · rw [hV, hW]; rfl
  · intro U hU v
    exact hA0 _ _ U hU (fun ρ => v ρ) (fun τ => _root_.GlobalTheory.LowKFin.lowT_mem_kfin D (Wc D i) _ (R.MW i σ) τ (v τ))

end GlobalTheory.PairSetting
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MainXOfStepXLastX
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.DoubleInd

variable {D : D7} {c : Comm D}

def W (t : Tup c) (k : ℕ) : ℂ :=
  ∏ l ∈ Finset.range k, t.cV (2 * l) * t.cK (2 * l) * t.cK (2 * l + 1)

theorem up_succ (t : Tup c) (k : ℕ) (ψ : t.Col 0) :
    t.up (k + 1) ψ = t.K (2 * k + 1) (t.K (2 * k) (t.S (2 * k) (t.up k ψ))) := rfl

theorem up_mem (t : Tup c) (ht : t.Is) (ψ : t.Col 0) (hψ : ψ ∈ t.Ram 0) :
    ∀ k, 2 * k ≤ D.R.m → t.up k ψ ∈ t.Ram (2 * k) := by
  intro k
  induction k with
  | zero => intro _; exact hψ
  | succ k ih =>
    intro hk
    rw [up_succ]
    have h0 := ih (by omega)
    have h1 := ht.stabS (2 * k) (by omega) _ h0
    have h2 := ht.stabK (2 * k) (by omega) _ h1
    exact ht.stabK (2 * k + 1) (by omega) _ h2

theorem up_ind {𝒯 : Type} (t : 𝒯 → Tup c) (ht : ∀ s, (t s).Is) (hS : StepX t) :
    ∀ k ρ (h : 2 * k + 2 * ρ + 2 = D.R.m) (I : Type) [Fintype I] (s : I → 𝒯) (β : I → ℂ) (ψ : ∀ i, (t (s i)).Col 0)
      (G : ∀ i, (t (s i)).CC (2 * k)), (∀ i, ψ i ∈ (t (s i)).Ram 0) →
      (∀ y v, ∑ i, β i * W (t (s i)) k * (t (s i)).per (2 * k) ρ h ((t (s i)).up k (ψ i)) (G i) y v = 0) →
      ∀ ρ₀ (h₀ : 0 + 2 * ρ₀ + 2 = D.R.m) y v,
        ∑ i, β i * (∏ j ∈ Finset.range (2 * k), (t (s i)).cI j) *
          (t (s i)).per 0 ρ₀ h₀ (ψ i) ((t (s i)).dn (2 * k) (G i)) y v = 0 := by
  intro k
  induction k with
  | zero =>
    intro ρ h I _ s β ψ G hψ hyp ρ₀ h₀ y v
    have hρ : ρ₀ = ρ := by omega
    subst hρ
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hyp y v)
    rw [show (∏ j ∈ Finset.range (2 * 0), (t (s i)).cI j) = (1 : ℂ) by simp,
      show W (t (s i)) 0 = 1 by simp [W]]
    rfl
  | succ k ih =>
    intro ρ h I _ s β ψ G hψ hyp ρ₀ h₀ y v
    have h' : 2 * k + 2 * (ρ + 1) + 2 = D.R.m := by omega
    have hmem : ∀ i, (t (s i)).up k (ψ i) ∈ (t (s i)).Ram (2 * k) :=
      fun i => up_mem _ (ht _) _ (hψ i) k (by omega)
    have hst := hS (2 * k) ρ h' I s (fun i => β i * W (t (s i)) k) (fun i => (t (s i)).up k (ψ i)) G hmem (by
      intro y v
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hyp y v)
      have hp : (t (s i)).per (2 * k + 1 + 1) ρ (idx_step h')
          ((t (s i)).K (2 * k + 1) ((t (s i)).K (2 * k) ((t (s i)).S (2 * k) ((t (s i)).up k (ψ i))))) (G i) y v =
          (t (s i)).per (2 * (k + 1)) ρ h ((t (s i)).up (k + 1) (ψ i)) (G i) y v := rfl
      rw [hp]
      simp only [W, Finset.prod_range_succ]
      ring)
    have hi := ih (ρ + 1) h' I s (fun i => β i * ((t (s i)).cI (2 * k) * (t (s i)).cI (2 * k + 1))) ψ
      (fun i => (t (s i)).io (2 * k) ((t (s i)).io (2 * k + 1) (G i))) hψ (by
        intro y v
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hst y v)
        ring) ρ₀ h₀ y v
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hi
    have hp : ∏ j ∈ Finset.range (2 * (k + 1)), (t (s i)).cI j =
        (∏ j ∈ Finset.range (2 * k), (t (s i)).cI j) * ((t (s i)).cI (2 * k) * (t (s i)).cI (2 * k + 1)) := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ]
      ring
    have hd : (t (s i)).per 0 ρ₀ h₀ (ψ i) ((t (s i)).dn (2 * (k + 1)) (G i)) y v =
        (t (s i)).per 0 ρ₀ h₀ (ψ i) ((t (s i)).dn (2 * k) ((t (s i)).io (2 * k) ((t (s i)).io (2 * k + 1) (G i)))) y v := rfl
    rw [hp, hd]
    ring

end GlobalTheory.SeeSaw.DoubleInd

namespace GlobalTheory.SeeSaw


open GlobalTheory.SeeSaw.DoubleInd in
theorem mainX_of_stepX_lastX : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), (∀ s, (t s).Is) → StepX t → LastX t → MainX t := by
  intro D c 𝒯 t ht hS hL
  intro n h h₀ I _ s α ψ F hψ hyp y v
  have hmem : ∀ i, (t (s i)).up n (ψ i) ∈ (t (s i)).Ram (2 * n) :=
    fun i => up_mem _ (ht _) _ (hψ i) n (by omega)
  have hL' := hL (2 * n) h I s (fun i => α i * W (t (s i)) n) (fun i => (t (s i)).up n (ψ i)) F hmem (by
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hyp
    have hp : (t (s i)).tail (2 * n + 1 + 1) h
        ((t (s i)).K (2 * n + 1) ((t (s i)).K (2 * n) ((t (s i)).S (2 * n) ((t (s i)).up n (ψ i))))) (F i) =
        (t (s i)).tail (2 * (n + 1)) h ((t (s i)).up (n + 1) (ψ i)) (F i) := rfl
    rw [hp]
    simp only [Tup.cTop, W, Finset.prod_range_succ]
    ring)
  have hu := up_ind t ht hS n 0 h I s (fun i => α i * ((t (s i)).cI (2 * n) * (t (s i)).cI (2 * n + 1))) ψ
    (fun i => (t (s i)).io (2 * n) ((t (s i)).ioT (2 * n) h (F i))) hψ (by
      intro y v
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hL' y v)
      ring) n h₀ y v
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hu
  have hc : (t (s i)).cBot =
      (∏ j ∈ Finset.range (2 * n), (t (s i)).cI j) * ((t (s i)).cI (2 * n) * (t (s i)).cI (2 * n + 1)) := by
    unfold Tup.cBot
    rw [show D.R.m = 2 * n + 1 + 1 by omega, Finset.prod_range_succ, Finset.prod_range_succ]
    ring
  have hd : (t (s i)).per 0 n h₀ (ψ i) ((t (s i)).dn (2 * n + 1) ((t (s i)).ioT (2 * n) h (F i))) y v =
      (t (s i)).per 0 n h₀ (ψ i) ((t (s i)).dn (2 * n) ((t (s i)).io (2 * n) ((t (s i)).ioT (2 * n) h (F i)))) y v := rfl
  rw [hc, hd]
  ring

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MapUnitsInvEqScal
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn

theorem compFin_cA_scal {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (z : AE D) :
    GlobalTheory.AdelicU.compFin D.host.F D.host.E v (cA D z) =
      sigR _ D.sp.cm.sig (GlobalTheory.AdelicU.compFin D.host.F D.host.E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem map_units_inv_eq_scal {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a b : Rˣ) (h : f a = f b) :
    f ((a⁻¹ : Rˣ) : R) = f ((b⁻¹ : Rˣ) : R) := by
  calc f ((a⁻¹ : Rˣ) : R) = f ((a⁻¹ : Rˣ) : R) * (f (b : R) * f ((b⁻¹ : Rˣ) : R)) := by
        rw [← map_mul, Units.mul_inv, map_one, mul_one]
    _ = (f ((a⁻¹ : Rˣ) : R) * f (a : R)) * f ((b⁻¹ : Rˣ) : R) := by rw [h, mul_assoc]
    _ = f ((b⁻¹ : Rˣ) : R) := by rw [← map_mul, Units.inv_mul, map_one, one_mul]

theorem scalData_exists : ∀ D : D7, ∃ μ : D.host.E, IsSkew μ ∧ ∃ u ε : (AE D)ˣ, ScalData μ u ε := by
  intro D
  obtain ⟨μ, hμ, u₀, ε₀, h0, hI, hI'⟩ := _root_.GlobalTheory.StdUnn.SkewNorm.exists_skew_norm_mul_unit D
  obtain ⟨u, ε, h1, hfin, hinf⟩ := _root_.GlobalTheory.StdUnn.exists_scal_real D μ hμ u₀
  have key : ∀ v, GlobalTheory.AdelicU.compFin D.host.F D.host.E v (ε : AE D) =
      GlobalTheory.AdelicU.compFin D.host.F D.host.E v (ε₀ : AE D) := by
    intro v
    have e2 : GlobalTheory.AdelicU.compFin D.host.F D.host.E v (cA D (u : AE D)) =
        GlobalTheory.AdelicU.compFin D.host.F D.host.E v (cA D (u₀ : AE D)) := by
      rw [compFin_cA_scal, compFin_cA_scal, hfin v]
    have e := congrArg (GlobalTheory.AdelicU.compFin D.host.F D.host.E v) (h1.trans h0.symm)
    simp only [map_mul] at e
    rw [hfin v, e2, mul_assoc, mul_assoc] at e
    have hu : IsUnit (GlobalTheory.AdelicU.compFin D.host.F D.host.E v (u₀ : AE D) *
        GlobalTheory.AdelicU.compFin D.host.F D.host.E v (cA D (u₀ : AE D))) := by
      refine IsUnit.mul (u₀.isUnit.map _) ?_
      have hc : IsUnit (cA D (u₀ : AE D)) := u₀.isUnit.map (cA D)
      exact hc.map _
    exact hu.mul_left_inj.mp e
  have keyInv : ∀ v, GlobalTheory.AdelicU.compFin D.host.F D.host.E v ((ε⁻¹ : (AE D)ˣ) : AE D) =
      GlobalTheory.AdelicU.compFin D.host.F D.host.E v ((ε₀⁻¹ : (AE D)ˣ) : AE D) := by
    intro v
    exact map_units_inv_eq_scal (GlobalTheory.AdelicU.compFin D.host.F D.host.E v) ε ε₀ (key v)
  refine ⟨μ, hμ, u, ε, h1, ?_, ?_, hinf⟩
  · intro v; rw [key v]; exact hI v
  · intro v; rw [keyInv v]; exact hI' v

end GlobalTheory.StdUnn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanPairingLieDerivativeAntisymm
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.Ibp

variable {D : D7} {V : HSp D}

theorem isFiniteMeasure_autMeasure (m : Measure (GA D V)) [hm : m.IsHaarMeasure] :
    IsFiniteMeasure (autMeasure V m) := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have hfd : IsFundamentalDomain (GQ V) (stdDom (GQ V)) m := isFundamentalDomain_stdDom _ m
  exact ⟨by
    rw [autMeasure, quotMeasure_univ hfd]
    exact GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V m _ hm hfd⟩

theorem isMulRightInvariant (m : Measure (GA D V)) [hm : m.IsHaarMeasure] : m.IsMulRightInvariant := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have hfd : IsFundamentalDomain (GQ V) (stdDom (GQ V)) m := isFundamentalDomain_stdDom _ m
  exact ⟨GlobalTheory.AutQuotCheck.rightInvariant_of_covolume (GQ V) m hfd (hfd.measure_ne_zero (NeZero.ne m))
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V m _ hm hfd).ne⟩

variable {θ : InfFam D} {τ : D.what₂.Tau}

end GlobalTheory.RegSch.Ibp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NegHalfPointTranslatesLastFrameRow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LineAct

theorem neg_wRow_half_rd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (S₀ A L W₀ : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (β : Frame p W₀ n) (γ : Frame p A n'') (γ₀ : Frame p S₀ (n'' ⊕ Fin 1)), IsSumFrame o ζ γ γ₀ → ∀ t : n → k, IsHalf p.e ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wRow p ζ β t)) ∧ ∀ i j, rd β γ₀ ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wRow p ζ β t)) i j = Sum.elim (fun _ => 0) (fun _ => -t j) i := by
  intro D k _ _ _ _ p n n'' _ _ _ _ S₀ A L W₀ o ζ β γ γ₀ hsum t
  have hes : ∀ a, p.e * p.sec a = p.sec a := fun a => by rw [← p.sec_pr, p.pr_sec]
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.neg_apply, wRow, Matrix.of_apply, mul_left_comm, mul_neg, hes, mul_neg]
  · set c : Fin S₀.rank → k := fun i => p.pr (ratV (vecB o ζ) i) with hc
    have hmap : Matrix.map (o.jB * -wRow p ζ β t : Mx D S₀.rank W₀.rank) p.pr = -vecMulVec c (t ᵥ* β.b') := by
      refine Matrix.ext fun a b => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.map_apply, Matrix.mul_apply, map_sum, Matrix.neg_apply, vecMulVec_apply, hc]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [ratV, vecB, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.neg_apply, wRow, Matrix.of_apply, map_neg, p.pr_sec, mul_neg, mul_assoc]
      rfl
    have hcol : (γ₀.b' *ᵥ c) i = Sum.elim (fun _ => 0) (fun _ => 1) i := by
      have h := congrFun (congrFun γ₀.b'b i) (Sum.inr 0)
      rw [hsum, Matrix.mul_apply] at h
      simp only [fromCols_apply_inr, replicateCol_apply] at h
      refine h.trans ?_
      rcases i with i | i
      · simp
      · obtain rfl := Subsingleton.elim i 0
        simp
    rw [rd, hmap, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_vecMul, β.b'b,
      Matrix.vecMul_one, Matrix.neg_apply, vecMulVec_apply, hcol]
    rcases i with i | i <;> simp

end GlobalTheory.FinPl.LineAct

end
end

