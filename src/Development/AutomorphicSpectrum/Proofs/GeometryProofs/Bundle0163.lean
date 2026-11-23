module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0136
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsProductRefinement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsProperIntegralModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegular
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0159
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0065
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0071
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0158
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0064
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0069
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPatchAtEachComponent
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0134
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0097
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0160
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0144
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionReindexed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIsMaximalOfIsFractionRing
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0086
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0053
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0156

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCoordsOfGenericPoint
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem exists_model_of_res (hRes : ResK.ResKStatement)
    (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)) (hp : IsProjOver s)
    (hn : Tor.IsNormalScheme P) (U : (pullback s (spMap (algebraMap (𝓞 F) F))).Opens) (hd : Dense (U : Set ((pullback s (spMap (algebraMap (𝓞 F) F)) : Scheme.{0})))) (e : ℕ)
    (hU : SmoothOfRelativeDimension e (U.ι ≫ pullback.snd s (spMap (algebraMap (𝓞 F) F))))
    (Ab : Set P) (hAb : pullback.fst s (spMap (algebraMap (𝓞 F) F)) ⁻¹' Ab = U)
    (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Sp Ω ⟶ P) (hξ₀ : IsCptGen ξ₀) :
    ∃ (N : ℕ) (x : Fin (N + 1) → Ω) (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (f : X ⟶ P)
      (bd : Ideal (MRing (fun _ : Unit => Fin (N + 1)))),
      (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ x ∧ ξ ≫ f = ξ₀ ∧
      Cmp.IsSncModel (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) e bd ∧
      ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) z w →
        (w ∈ mcPts bd ↔ f (centre z) ∉ Ab) := by
  obtain ⟨hred, hln, M, i, hi, his⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SncBase.genericFibre_reduced_noetherian_closed F P s hp hn
  obtain ⟨b, ξF, hF1, hF2, hFg⟩ := _root_.GlobalTheory.CompanionTheory.Ar.GenFibre.exists_point F P s Ω ξ₀ hξ₀
  have hmem := _root_.GlobalTheory.CompanionTheory.Ar.SncBase.genPt_mem_of_dense_open _ Ω ξF U hFg hd
  have hin : ResK.IsResInput M i U e := ⟨hi, hred, hd, by rw [his]; exact hU⟩
  obtain ⟨r, X', j, f', hj, hfj, hsm, hiso, hdense, hsnc⟩ := hRes F M e _ i U hin
  letI algF : Algebra F Ω := b.toAlgebra
  letI algO : Algebra (𝓞 F) Ω := (b.comp (algebraMap (𝓞 F) F)).toAlgebra
  haveI : IsScalarTower (𝓞 F) F Ω := .of_algebraMap_eq' rfl
  have hs0 : ξ₀ ≫ s = spMap (algebraMap (𝓞 F) Ω) := by
    rw [← hF1, Category.assoc, pullback.condition, ← Category.assoc, hF2]
    show _ = Spec.map (CommRingCat.ofHom (b.comp (algebraMap (𝓞 F) F)))
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  obtain ⟨nu, u, hu⟩ := _root_.GlobalTheory.CompanionTheory.Relay.projective_over_coords_exist (𝓞 F) P s hp Ω ξ₀ hξ₀ hs0
  have hproj : IsProjOver (f' ≫ i ≫ PSpace.str F M) := by
    have := _root_.GlobalTheory.CompanionTheory.Ar.SncBase.Segre.isProjOver_of_closed_product F M r X' j hj
    rwa [← Category.assoc, ← hfj, Category.assoc] at this
  have hdom := GlobalTheory.T.smooth_scheme_stalks_domains F e X' _ hsm
  obtain ⟨ξ', h1, hξ'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SncBase.exists_lift_isCptGen _ X' f' U Ω ξF hiso hmem hFg hdom
  have hξs : ξ' ≫ f' ≫ i ≫ PSpace.str F M = spMap (algebraMap F Ω) := by
    rw [← Category.assoc, h1, his, hF2]
  obtain ⟨nx, x2, hx2⟩ := _root_.GlobalTheory.CompanionTheory.Relay.projective_over_coords_exist F X' _ hproj Ω ξ' hξ' hξs
  have hg : ξ' ≫ (f' ≫ pullback.fst _ _) = ξ₀ := by rw [← Category.assoc, h1, hF1]
  have hbase := _root_.GlobalTheory.CompanionTheory.Ar.SncBase.exists_inChart_of_comp_eq X' P Ω ξ' ξ₀ _ (𝓞 F) _ u hu hg
  obtain ⟨n, ht⟩ := _root_.GlobalTheory.CompanionTheory.Ar.coordTie_add_block X' Ω ξ' F _ _ x2 u hx2 hbase
  obtain ⟨c₀, hc₀, hfrac⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SncBase.ChartFrac.chartRing_frac (𝓞 F) F Ω X' ξ' _ _ ht
  obtain ⟨X, ξ, sX, htX, hirr, -, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.exists_cl_scheme Ω (𝓞 F) _ _ c₀ hc₀ hfrac
  have hreg : ∀ (a : 𝓞 F) (p : Cpt ξ), (RingHom.id Ω) (algebraMap (𝓞 F) Ω a) ∈ regAt ξ p := by
    intro a p
    obtain ⟨c, hc⟩ := htX.cover p
    exact (htX.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ a) p hc
  have hchart : ∀ p : Cpt ξ, ∃ c, InChart ξ (fun k => (RingHom.id Ω) (u k)) c p := by
    intro p
    obtain ⟨⟨q1, q2, q3⟩, h0, hc⟩ := htX.cover p
    have hne := h0
    simp only [mul_ne_zero_iff] at hne
    refine ⟨q3, hne.2, fun c' => ?_⟩
    have := hc ⟨q1, q2, c'⟩
    have e1 : ((∏ a, x2 (q1 a)) * x2 q2 * u c') / ((∏ a, x2 (q1 a)) * x2 q2 * u q3) = u c' / u q3 := by
      field_simp [hne.1.1, hne.1.2, hne.2]
    simpa [e1] using this
  obtain ⟨f, hf, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.CoordMap.exists_dominating_map P Ω ξ₀ (𝓞 F) _ u X Ω ξ (RingHom.id Ω) hu htX.gen hirr hreg hchart
  have hf' : ξ ≫ f = ξ₀ := by
    have : ξ ≫ f = _ := hf
    rw [this]; simp
  obtain ⟨N, x, hx⟩ := _root_.GlobalTheory.CompanionTheory.Ar.coordTie_int_of_finite X Ω ξ (𝓞 F) _ _ htX
  obtain ⟨R1, R2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SncBase.FracPts.regAt_frac (𝓞 F) F Ω X X' ξ ξ' _ _ htX ht
  have hchar := GlobalTheory.T.char_zero_iff_nonzero_units F Ω X ξ _ _ htX
  have hFreg : ∀ (a : F) (p' : Cpt ξ'), algebraMap F Ω a ∈ regAt ξ' p' := by
    intro a p'
    obtain ⟨c, hc⟩ := ht.cover p'
    exact (ht.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ a) p' hc
  have hunit : ∀ (p : Cpt ξ) (p' : Cpt ξ'), regAt ξ p = regAt ξ' p' → Char0 ξ p := by
    intro p p' h
    refine (hchar p).2 fun d hd0 => ?_
    have hd1 : (algebraMap (𝓞 F) F d) ≠ 0 := by simpa using hd0
    have e1 : algebraMap (𝓞 F) Ω d = algebraMap F Ω (algebraMap (𝓞 F) F d) := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [e1]; exact (map_ne_zero _).2 hd1
    · rw [h, e1]; exact hFreg _ p'
    · rw [h, e1, ← map_inv₀]; exact hFreg _ p'
  have hPts : Pts ξ = Set.range (regAt ξ') := by
    ext R
    constructor
    · rintro ⟨p, hp0, rfl⟩
      obtain ⟨p', h⟩ := R2 p ((hchar p).1 hp0)
      exact ⟨p', h.symm⟩
    · rintro ⟨p', rfl⟩
      obtain ⟨p, h⟩ := R1 p'
      exact ⟨p, hunit p p' h, h.symm⟩
  let B : Set (Cpt ξ) := {p | Char0 ξ p ∧ f p.1 ∉ Ab}
  let T : Set X' := f'.base ⁻¹' (U : Set ((pullback s (spMap (algebraMap (𝓞 F) F)) : Scheme.{0})))ᶜ
  have hgen : ∀ (p : Cpt ξ) (p' : Cpt ξ'), regAt ξ p = regAt ξ' p' → (f p.1 ∉ Ab ↔ p'.1 ∈ T) := by
    intro p p' h
    have e1 : f p.1 = (f' ≫ pullback.fst _ _) p'.1 :=
      _root_.GlobalTheory.CompanionTheory.Ar.SncBase.image_eq_of_regAt_eq P X X' Ω ξ₀ ξ ξ' f _ (𝓞 F) _ u hu htX.gen hξ' hf' hg p p' h
    have e2 : ((f' ≫ pullback.fst s (spMap (algebraMap (𝓞 F) F))) p'.1 ∈ Ab) ↔ f' p'.1 ∈ (U : Set ((pullback s (spMap (algebraMap (𝓞 F) F)) : Scheme.{0}))) := by
      rw [← hAb]; simp
    rw [e1, e2]; rfl
  have hBd : regAt ξ '' B = regAt ξ' '' {p | p.1 ∈ T} := by
    ext R
    constructor
    · rintro ⟨p, ⟨hp0, hp1⟩, rfl⟩
      obtain ⟨p', h⟩ := R2 p ((hchar p).1 hp0)
      exact ⟨p', (hgen p p' h).1 hp1, h.symm⟩
    · rintro ⟨p', hp', rfl⟩
      obtain ⟨p, h⟩ := R1 p'
      exact ⟨p, ⟨hunit p p' h, (hgen p p' h).2 hp'⟩, h⟩
  have hpatch := _root_.GlobalTheory.CompanionTheory.Ar.SncBase.Patch.exists_patch F X' _ e T Ω ξ' hξ' hξs hsm hsnc (_root_.GlobalTheory.CompanionTheory.Ar.SncBase.eq_of_regAt_eq_of_coordTie X' Ω ξ' F _ _ ht)
  obtain ⟨bd, hm, hc⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SncBase.exists_isSncModel_of_patches Ω X ξ N x e B hx (fun p hp => hp.1) (by
    intro p hp0
    obtain ⟨p', h⟩ := R2 p ((hchar p).1 hp0)
    rw [hPts, hBd, h]
    exact hpatch p')
  refine ⟨N, x, X, ξ, f, bd, hirr, hx, hf', hm, fun z w hw => ?_⟩
  rw [hc z w hw]
  constructor
  · rintro ⟨h, -, h2⟩
    exact h2
  · intro h
    exact ⟨hirr _, _root_.GlobalTheory.CompanionTheory.Ar.SncBase.char_zero_centre_complex_point Ω X ξ z _ htX.gen, h⟩

theorem exists_sncBase : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Spec (CommRingCat.of Ω) ⟶ Y.X), IsCptGen ξ₀ → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y.X) (bd : Ideal (MRing J)), Nonempty K ∧ (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ∧ ξ ≫ f = ξ₀ ∧ Cmp.IsSncModel y D.dim bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G) := by
  intro hRes E _ _ _ H D l Xo c Y Ω _ _ ξ₀ hξ₀
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  haveI := Y.jQ_open
  have hsm : SmoothOfRelativeDimension D.dim (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange D.dim).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  have hU : SmoothOfRelativeDimension D.dim (Y.jQ.opensRange.ι ≫ pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
    apply GlobalTheory.T.smooth_open_immersion_range _ _ _ Y.jQ
    rw [Y.jQ_over]
    exact hsm
  obtain ⟨N, x, X, ξ, f, bd, hirr, hx, hf, hm, hc⟩ := exists_model_of_res hRes c.F Y.X Y.s Y.proj Y.normal Y.jQ.opensRange
    (by simpa using Y.jQ_dense) D.dim hU (abLocus Y.t.G) (by simpa using Y.ab_gen) Ω ξ₀ hξ₀
  exact ⟨Unit, inferInstance, fun _ => Fin (N + 1), fun _ => inferInstance, fun p => x p.2, X, ξ, f, bd, inferInstance,
    hirr, GlobalTheory.T.coords_single_block_segre X Ω ξ N x hx, hf, hm, hc⟩

end GlobalTheory.CompanionTheory.Ar.SncBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFirst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChgLie

section Modules

theorem mem_of_mem_iSup {Ω E I : Type} [Field Ω] [AddCommGroup E] [Module Ω E] (A : Subring Ω)
    (W : I → Submodule Ω E) (hW : iSupIndep W) (N : I → Submodule A E) (hN : ∀ s, ∀ x ∈ N s, x ∈ W s)
    {e : E} (s₀ : I) (he : e ∈ ⨆ s, N s) (hs : e ∈ W s₀) : e ∈ N s₀ := by
  classical
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp N e).1 he
  have hsum : (f.sum fun _ x => x) - f s₀ = ∑ i ∈ f.support.erase s₀, f i := by
    by_cases h0 : s₀ ∈ f.support
    · rw [Finsupp.sum, ← Finset.add_sum_erase _ _ h0]
      abel
    · rw [Finsupp.sum, Finset.erase_eq_of_notMem h0, Finsupp.notMem_support_iff.1 h0, sub_zero]
  have h1 : (f.sum fun _ x => x) - f s₀ ∈ W s₀ := sub_mem hs (hN _ _ (hf s₀))
  have h2 : (f.sum fun _ x => x) - f s₀ ∈ ⨆ (k) (_ : k ≠ s₀), W k := by
    rw [hsum]
    refine Submodule.sum_mem _ fun k hk => ?_
    exact Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hk) (hN _ _ (hf k)))
  have h3 := (Submodule.disjoint_def.1 (hW s₀)) _ h1 h2
  rw [sub_eq_zero.1 h3]
  exact hf s₀

theorem mem_eigSp_iff {R E O : Type} [CommRing R] [AddCommGroup E] [Module R E] [CommRing O]
    (ρ : O →+* Module.End R E) (σ : O →+* R) (e : E) : e ∈ eigSp ρ σ ↔ ∀ a, ρ a e = σ a • e := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

end Modules

section Points

variable {X X₀ : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀]

theorem not_inFibre_push {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {h : X ⟶ X₀}
    {i : Ω₀ →+* Ω} (hξ : IsCptGen ξ) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h i) (q : Cpt ξ) {r : ℕ}
    (hq : ¬ InFibre ξ r q) : ¬ InFibre ξ₀ r (pushCpt hd q) := by
  intro hf
  apply hf
  obtain ⟨h0, -, s, hs⟩ : unitAt ξ q (r : Ω) := not_not.1 hq
  have hmul : (r : X.presheaf.stalk q.1) * s = 1 := hξ.inj q (by
    rw [map_mul, map_one, map_natCast, hs]
    exact mul_inv_cancel₀ h0)
  have hu : IsUnit (r : X.presheaf.stalk q.1) := IsUnit.of_mul_eq_one _ hmul
  have hu₀ : IsUnit (r : X₀.presheaf.stalk (h q.1)) :=
    isUnit_of_map_unit (h.stalkMap q.1).hom _ (by rwa [map_natCast])
  have h0' : (r : Ω₀) ≠ 0 := fun e => h0 (by rw [← map_natCast i, e, map_zero])
  refine ⟨h0', ⟨_, map_natCast (genMap ξ₀ (pushCpt hd q)) r⟩, ?_⟩
  obtain ⟨u, hu'⟩ := hu₀
  refine ⟨(u⁻¹ : (X₀.presheaf.stalk (h q.1))ˣ).val, ?_⟩
  have e1 : genMap ξ₀ (pushCpt hd q) u.val = (r : Ω₀) := (congrArg _ hu').trans (map_natCast _ r)
  exact (map_units_inv (genMap ξ₀ (pushCpt hd q)) u).trans (congrArg Inv.inv e1)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem pt_inj_of_pull {S' S : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hG : IsGrpPullback G' G f φ) {ξ : Spec (CommRingCat.of Ω) ⟶ S'} {V : Type}
    [AddCommGroup V] [Module Ω V] (M : LieModel G' ξ V) {e e' : V}
    (h : (M.pt e).left ≫ φ = (M.pt e').left ≫ φ) : e = e' :=
  M.inj (Over.OverMorphism.ext (hG.1.hom_ext h ((Over.w _).trans (Over.w _).symm)))

theorem exists_value_up {t : SAB H X₀} {t' : SAB H X} {f : X ⟶ X₀} (m : SABMap t' t f)
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {i : Ω₀ →+* Ω}
    (hall : ∀ q : X, genPt ξ ⤳ q) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f i) {V V' : Type} [AddCommGroup V] [Module Ω₀ V]
    [AddCommGroup V'] [Module Ω V'] {M : LieModel t.G ξ₀ V} {M' : LieModel t'.G ξ V'} {j : V →+ V'}
    (hj : ∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) {e : V} {v₀ : epsAt (z ≫ f) ⟶ t.G} (hv : M.ValAt (z ≫ f) e v₀) :
    ∃ v : epsAt z ⟶ t'.G, M'.ValAt z (j e) v ∧ v₀.left = v.left ≫ m.φ := by
  obtain ⟨h₀, w, hw, hwz⟩ := hv
  have hp : genPt ξ₀ ⤳ f (centre z) := h₀
  have hρ : Spec.map (CommRingCat.ofHom (f.stalkMap (centre z)).hom) ≫ X₀.fromSpecStalk (f (centre z)) =
      X.fromSpecStalk (centre z) ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hρ' : (genMap ξ ⟨centre z, hall _⟩).comp (f.stalkMap (centre z)).hom = i.comp (genMap ξ₀ ⟨f (centre z), hp⟩) :=
    RingHom.ext (RegAtDom.genMap_stalkMap hd _ (hall _) hp)
  have hx' := LieCarrier.genMap_fromSpecStalk (ξ := ξ) ⟨centre z, hall _⟩
  obtain ⟨u, hu, huφ⟩ := LiePull.ext_up (A := X₀.presheaf.stalk (f (centre z))) (A' := X.presheaf.stalk (centre z))
    (g := genMap ξ₀ ⟨f (centre z), hp⟩) (g' := genMap ξ ⟨centre z, hall _⟩) (ρ := (f.stalkMap (centre z)).hom)
    (x := X₀.fromSpecStalk (f (centre z))) (x' := X.fromSpecStalk (centre z)) (M := M) (M' := M') (j := j) m.cart hj hρ
    hρ' hx' hw
  have hc : Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo z).hom) ≫ X.fromSpecStalk (centre z) = z :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
  refine ⟨LieCarrier.epsHom _ _ z hc ≫ u, ⟨hall _, u, hu, rfl⟩, ?_⟩
  have e1 : (LieCarrier.epsHom _ _ z hc ≫ u).left =
      Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫ u.left := rfl
  have e2 : (Scheme.stalkClosedPointTo (z ≫ f)).hom =
      (Scheme.stalkClosedPointTo z).hom.comp (f.stalkMap (centre z)).hom := by
    rw [Scheme.stalkClosedPointTo_comp]
    rfl
  have e4 : spMap (dualMap (Scheme.stalkClosedPointTo (z ≫ f)).hom) =
      spMap (dualMap (Scheme.stalkClosedPointTo z).hom) ≫ spMap (dualMap (f.stalkMap (centre z)).hom) := by
    rw [e2]
    exact (congrArg spMap (LiePull.dualMap_comp (f.stalkMap (centre z)).hom (Scheme.stalkClosedPointTo z).hom).symm).trans
      (spMap_comp' _ _)
  have e3 : (LieCarrier.epsHom _ _ z hc ≫ u).left ≫ m.φ = spMap (dualMap (Scheme.stalkClosedPointTo z).hom) ≫
      spMap (dualMap (f.stalkMap (centre z)).hom) ≫ w.left :=
    (congrArg (· ≫ m.φ) e1).trans ((Category.assoc _ _ _).trans
      (congrArg (spMap (dualMap (Scheme.stalkClosedPointTo z).hom) ≫ ·) huφ))
  exact hwz.trans (((congrArg (· ≫ w.left) e4).trans (Category.assoc _ _ _)).trans e3.symm)

end Points

section Main

theorem lie_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag), Function.Injective β → IsCovOf 𝔐₀ 𝔐 i h → FlagsOver Fl₀ Fl i → ∃ j : 𝔐₀.Li →+ 𝔐.Li, (∀ (a : Ω₀) e, j (a • e) = i a • j e) ∧ (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) ∧ (∀ s a, j (Fl₀.b s a) = Fl.b s a) ∧ (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐₀.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐₀.M.GramAt 𝔐₀.t.PP.L (z ≫ h) b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => j (b k)) Γ := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl hβ hcov hfl
  obtain ⟨-, hf, hcst⟩ := hcov
  obtain ⟨m₀, hφ⟩ := exists_sabMap 𝔐₀ 𝔐 h hf
  obtain ⟨j, hpt, hsemi, hind, -, hpull⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LiePullSab.lie_pull_lat E H 𝔐₀.X 𝔐₀.t 𝔐.X 𝔐.t h m₀ Ω₀ Ω 𝔐₀.ξ 𝔐.ξ i 𝔐₀.Li 𝔐.Li 𝔐₀.M 𝔐.M
    𝔐₀.tie.gen 𝔐.tie.gen hd
  have hact : ∀ a e, 𝔐.ρ a (j e) = j (𝔐₀.ρ a e) := fun a e => pt_inj_of_pull m₀.cart 𝔐.M (by
    have e1 := congrArg CommaMorphism.left (𝔐.act a (j e))
    have e2 := congrArg CommaMorphism.left (𝔐₀.act a e)
    have e3 := m₀.act a
    rw [hpt]
    refine (congrArg (· ≫ m₀.φ) e1).trans ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine (congrArg (_ ≫ ·) e3).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (𝔐₀.t.act.act a).left) (hpt e)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (spMap (dualMap i) ≫ ·) e2.symm)
  have hemb : ∀ s, 𝔐.emb s = i.comp (𝔐₀.emb s) := fun s => by
    simp only [HodgeCpt.emb, hcst, RingHom.comp_assoc]
  have heig : ∀ s e, e ∈ 𝔐₀.Vgen s → j e ∈ 𝔐.Vgen s := fun s e he => by
    refine (mem_eigSp_iff _ _ _).2 fun a => ?_
    rw [hact, (mem_eigSp_iff _ _ _).1 he a, hsemi, hemb]
    rfl
  refine ⟨j, hsemi, hind, fun s a => ?_, fun q hq s => ?_, fun z r b Γ hΓ => ?_⟩
  · refine pt_inj_of_pull 𝔐.m.cart 𝔐.M ?_
    have e1 : (𝔐.M.pt (j (Fl₀.b s a))).left ≫ 𝔐.m.φ =
        spMap (dualMap i) ≫ (𝔐₀.M.pt (Fl₀.b s a)).left ≫ 𝔐₀.m.φ := by
      rw [hφ, ← Category.assoc, hpt, Category.assoc]
    exact e1.trans (hfl s a).symm
  · have hq₀ : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐₀.ξ r (pushCpt hd q) :=
      fun r hr => not_inFibre_push 𝔐.tie.gen hd q (hq r hr)
    obtain ⟨hV, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeChar0.lattices_of_char_zero E H D l Xo c O β Y S Ω K J y 𝔐 hβ q hq
    obtain ⟨hV₀, -, hlat₀⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeChar0.lattices_of_char_zero E H D l Xo c O β Y S₀ Ω₀ K₀ J₀ y₀ 𝔐₀ hβ (pushCpt hd q) hq₀
    obtain ⟨-, -, -, -, -, -, hindep, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeCpt.basic E H D l Xo c O β Y S Ω K J y 𝔐 hβ
    rw [hV s, hV₀ s]
    let N : (CMType H ⊕ CMType H) → Submodule (regAt 𝔐.ξ q) 𝔐.Li := fun s' =>
      Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.dR s' (pushCpt hd q) : Set 𝔐₀.Li))
    have hle : ∀ s', N s' ≤ 𝔐.dR s' q := fun s' => by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨e, he, rfl⟩
      refine ⟨?_, heig s' e he.2⟩
      rw [hpull]
      exact Submodule.subset_span ⟨hd.specializes q, e, he.1, rfl⟩
    have htop : 𝔐.M.lat q ≤ ⨆ s', N s' := by
      rw [hpull]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h', e, he, rfl⟩
      have he' : e ∈ ⨆ s', 𝔐₀.dR s' (pushCpt hd q) := hlat₀ ▸ he
      refine Submodule.iSup_induction _ (motive := fun x => j x ∈ ⨆ s', N s') he' (fun s' x hx => ?_) ?_ ?_
      · exact Submodule.mem_iSup_of_mem s' (Submodule.subset_span ⟨x, hx, rfl⟩)
      · rw [map_zero]
        exact Submodule.zero_mem _
      · intro x x' hx hx'
        rw [map_add (f := _)]
        exact Submodule.add_mem _ hx hx'
    refine le_antisymm (fun e he => ?_) (hle s)
    exact mem_of_mem_iSup _ 𝔐.Vgen hindep N (fun s' x hx => (hle s' hx).2) s (htop he.1) he.2
  · obtain ⟨v₀, hv₀, hIP⟩ := hΓ
    choose v hv hvφ using fun k => exists_value_up m₀ 𝔐.all hd hpt z (hv₀ k)
    exact ⟨v, hv, fun p q => (_root_.GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_tripleMap_iff E H 𝔐₀.X 𝔐₀.t 𝔐.X 𝔐.t h m₀ z (v p) (v q) (v₀ p) (v₀ q) (Γ p q) (hvφ p) (hvφ q)).2 (hIP p q)⟩

end Main

end GlobalTheory.CompanionTheory.Ar.ChgLie
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionReindexedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_resolution_reindexed : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (D d : ℕ) (R₀ : AnLogRes (mCoordIdeal y₀) ⊤ D) (R : AnLogRes (mCoordIdeal y) ⊤ D) (h : R.X → R₀.X), Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → IsArithVar (mCoordIdeal y₀) (D + 1) → IsArithVar (mCoordIdeal y) (D + 1) → Birational y₀ → Birational y → HoloMap R.A R₀.A h → (∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (blkV bk bx p))) → (letI := i.toAlgebra; Module.finrank Ω₀ Ω = d) → 0 < d → ∃ br : Set R₀.X, IsDegreeOff R₀.A R.A h d br := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isDegreeOff_of_block | exact GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isDegreeOff_of_block | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isDegreeOff_of_block <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogPrimeMemDivisorSupportStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multihomog_prime_mem_divisor_support : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → ∀ (W : Ideal (MRing J)) (c : ∀ k, J k), W.IsPrime → IsMultiHomogIdeal W → mCoordIdeal w ≤ W → (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) → ∀ (k : B) (c₀ : J k), w ⟨k, c₀⟩ ≠ 0 → (X ⟨k, c₀⟩ : MRing J) ∈ W → W ∈ (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c₀⟩ : MRing J)}).minimalPrimes := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin.mem_minimalPrimes_of_coord | exact GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin.mem_minimalPrimes_of_coord | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin.mem_minimalPrimes_of_coord <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistAutHolds
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TwistAutProof

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.GlobalTheory.CompanionTheory.Ar

theorem eq_of_objMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    (Xo : Moduli D l) {S : Scheme.{0}} (s' : S ⟶ Sp (KA l)) (hS : IsReduced S) (o : Obj D l (baseKA l) s')
    (f₁ f₂ : S ⟶ Xo.X) (h₁ : f₁ ≫ Xo.s = s') (h₂ : f₂ ≫ Xo.s = s') (m₁ : ObjMap o Xo.univ f₁)
    (m₂ : ObjMap o Xo.univ f₂) : f₁ = f₂ :=
  (Xo.rep S s' hS o).unique ⟨h₁, ⟨m₁⟩⟩ ⟨h₂, ⟨m₂⟩⟩

theorem twistAut : TwistAut := by
  intro E _ _ _ H D l Xo g
  refine ⟨_root_.GlobalTheory.CompanionTheory.Ar.tw_iso_nonempty E H D g, fun a => ?_⟩
  have hred : IsReduced Xo.X := _root_.GlobalTheory.CompanionTheory.Ar.moduli_isReduced E H D l Xo
  obtain ⟨a', hback⟩ := _root_.GlobalTheory.CompanionTheory.Ar.twBack E H D g a
  have h : TwOK Xo.univ g a := _root_.GlobalTheory.CompanionTheory.Ar.TwistOk.twOK_obj E H D l _ (baseKA l) Xo.X Xo.s Xo.univ g a
  have h' : TwOK Xo.univ g.symm a' := _root_.GlobalTheory.CompanionTheory.Ar.TwistOk.twOK_obj E H D l _ (baseKA l) Xo.X Xo.s Xo.univ g.symm a'
  obtain ⟨Φ, hΦ, ⟨m⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.moduli_twist_phi E H D l Xo g a h
  obtain ⟨Ψ, hΨ, ⟨m'⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.moduli_twist_phi E H D l Xo g.symm a' h'
  obtain ⟨back₁, back₂⟩ := hback l _ (baseKA l) Xo.X Xo.s Xo.univ

  have e₁ : Φ ≫ Ψ = 𝟙 Xo.X := by
    have k : TwOK (twistObj Xo.univ g a h) g.symm a' :=
      _root_.GlobalTheory.CompanionTheory.Ar.TwistOk.twOK_obj E H D l _ (baseKA l) Xo.X Xo.s _ g.symm a'
    obtain ⟨n, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.objMap_twist E H D l _ (baseKA l) Xo.X Xo.s Xo.X Xo.s _ _ Φ m g.symm a' h' k
    obtain ⟨n', -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.objMap_exists_comp E H D l _ (baseKA l) Xo.X Xo.s Xo.X Xo.X Xo.s Xo.s _ _ _ Ψ Φ m' n
    obtain ⟨i⟩ := back₁ h k
    exact eq_of_objMap Xo Xo.s hred _ _ _ (by rw [Category.assoc, hΨ, hΦ]) (Category.id_comp _) n' i

  have e₂ : Ψ ≫ Φ = 𝟙 Xo.X := by
    have k : TwOK (twistObj Xo.univ g.symm a' h') g a :=
      _root_.GlobalTheory.CompanionTheory.Ar.TwistOk.twOK_obj E H D l _ (baseKA l) Xo.X Xo.s _ g a
    obtain ⟨n, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.objMap_twist E H D l _ (baseKA l) Xo.X Xo.s Xo.X Xo.s _ _ Ψ m' g a h k
    obtain ⟨n', -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.objMap_exists_comp E H D l _ (baseKA l) Xo.X Xo.s Xo.X Xo.X Xo.s Xo.s _ _ _ Φ Ψ m n
    obtain ⟨i⟩ := back₂ h' k
    exact eq_of_objMap Xo Xo.s hred _ _ _ (by rw [Category.assoc, hΦ, hΨ]) (Category.id_comp _) n' i
  exact ⟨h, ⟨Φ, Ψ, e₁, e₂⟩, hΦ, ⟨m⟩⟩

end GlobalTheory.CompanionTheory.Ar.TwistAutProof
end
end

