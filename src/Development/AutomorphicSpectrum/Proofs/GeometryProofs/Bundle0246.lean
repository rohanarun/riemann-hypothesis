module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.AbelianSchemeSpreadsOverLocalization
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0103
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0056
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0082
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwistedGramMatricesMatch
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistLatticeCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0165
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0151
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelFibresPowerFree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0584
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0048
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNormalisation
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0240
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0058
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0146
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeConstantRank
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0144
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0244
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveRootHodgeCpt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptLabelBases

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianTripleSpreadsOut
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem abelianTriple_spreads_out : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (tL : SAB H (Sp L)), IsProper tL.G.hom → ∃ (n : 𝓞 L) (_ : n ≠ 0) (T : SAB H (Sp (Localization.Away n))) (f : Localization.Away n →+* L), (∀ x : 𝓞 L, f (algebraMap _ _ x) = (x : L)) ∧ Nonempty (SABMap tL T (spMap f)) :=
  PositivityTheory.Xgn.abelian_scheme_spreads_over_localization

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmpHodgeTiedHolds
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CmpTied

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.GlobalTheory.CompanionTheory.Ar

theorem cmpHodgeTied : HodgeComparisonCompatibility := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω _ K _ J _ y A A' e x x' hβ hβ' hΦ hξ hx hx' hf hs hc hcx hR
  obtain ⟨t, tΩ, k, m, mA, mA', u, u', M₁, φ, hmA, E1, E2, E3, hk, htie, hT, hL⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.FrameRebase.tied_generic_fibre E H D l Xo c O O' β β' Y Y' g Φ n S Ω K J y A A' e x x' hβ hβ' hΦ hξ hx hx' hf hs hc hcx hR
  have E1' : m.φ ≫ k.φ ≫ A.m.φ = u.φ ≫ Y.m.φ := by rw [← Category.assoc, ← hmA, E1]
  have hact : ∀ a v, φ (A.ρ (g.s a) v) = A'.ρ a (φ v) :=
    _root_.GlobalTheory.CompanionTheory.Ar.LieIntertwining.act_intertwine E H g Ω A.X A'.X A.ξ A'.ξ A.t A'.t tΩ mA mA' A.Li A'.Li A.M A'.M A.ρ A'.ρ φ A.act A'.act
      (fun v => by
        obtain ⟨w, hw, hw'⟩ := htie v
        exact ⟨w, by rw [hmA, ← Category.assoc, hw, hk], hw'⟩)
  refine ⟨φ, fun v => ?_, hact,
    _root_.GlobalTheory.CompanionTheory.Ar.CmpBund.bund E H D l Xo c O O' β β' Y Y' g Φ n S Ω K J y A A' e x x' hβ hβ' hΦ hξ hx hx' hf hs hc hcx hR t tΩ k m mA' u u' M₁ φ E1' E2 E3 hk htie hT hL hact,
    fun z => ⟨_root_.GlobalTheory.CompanionTheory.Ar.TwistInterior.interior_iff E H D l Xo c O O' β β' Y Y' g Φ n S Ω K J y A A' e x x' hβ hβ' hΦ hξ hx hx' hf hs hc hcx hR z, fun hz r b Γ =>
      (_root_.GlobalTheory.CompanionTheory.Ar.GMove.gramAt_move E H A.X A'.X e Ω A.ξ A'.ξ A.t t k A.Li A.M M₁ hξ hk z r b Γ).symm.trans
        (_root_.PositivityTheory.UnitarySelfGeneration.twisted_gram_matrices_match E H D l Xo c O O' β β' Y Y' g Φ n S Ω K J y A A' e x x' hβ hβ' hΦ hξ hx hx' hf hs hc hcx hR t tΩ k m mA' u u' M₁ φ E1' E2 E3 hk htie hT hL z hz r b Γ)⟩⟩
  obtain ⟨w, hw, hw'⟩ := htie v
  have h1 : u'.φ ≫ Y'.oF.t.G.hom = (twistSAB tΩ g).G.hom ≫ x' := u'.cart.1.w
  have h2 : u.φ ≫ Y.oF.t.G.hom = tΩ.G.hom ≫ x := u.cart.1.w
  have key : u'.φ ≫ Y'.oF.t.G.hom ≫ pullback.snd _ _ = u.φ ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ := by
    rw [reassoc_of% h1, reassoc_of% h2, hs]
    rfl
  refine ⟨w.left ≫ u.φ, w.left ≫ u'.φ, ?_, ?_, ?_, ?_⟩
  · simp only [Category.assoc]
    rw [← E1', ← hk v, ← hw]
    simp only [Category.assoc]
  · calc (w.left ≫ u'.φ) ≫ Y'.m.φ = w.left ≫ (u'.φ ≫ Y'.m.φ) := Category.assoc _ _ _
      _ = w.left ≫ (mA'.φ ≫ A'.m.φ) := congrArg (fun f => w.left ≫ f) E2.symm
      _ = (w.left ≫ mA'.φ) ≫ A'.m.φ := (Category.assoc _ _ _).symm
      _ = _ := by rw [hw']
  · calc (w.left ≫ u'.φ) ≫ Y'.m0.toSABMap.φ = w.left ≫ (u'.φ ≫ Y'.m0.toSABMap.φ) := Category.assoc _ _ _
      _ = w.left ≫ (u.φ ≫ Y.m0.toSABMap.φ ≫ n.φ) := congrArg (fun f => w.left ≫ f) E3
      _ = _ := (Category.assoc _ _ _).symm
  · exact (Category.assoc _ _ _).trans ((congrArg (fun f => w.left ≫ f) key).trans (Category.assoc _ _ _).symm)

end GlobalTheory.CompanionTheory.Ar.CmpTied
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalModelPowerFree
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GlobalFib

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem natCast_residueField_iff {Y Z : Scheme.{0}} (f : Y ⟶ Z) (y : Y) (n : ℕ) :
    (n : Z.residueField (f y)) = 0 ↔ (n : Y.residueField y) = 0 := by
  rw [← map_natCast (f.residueFieldMap y).hom n, map_eq_zero]

theorem natCast_mem_of_residueField {Z : Scheme.{0}} {A : Type} [CommRing A] (f : Z ⟶ Sp A) (z : Z) (n : ℕ)
    (h : (n : Z.residueField z) = 0) : (n : A) ∈ (f z).asIdeal := by
  have := (f z).isPrime
  have h₁ : (n : (Sp A).residueField (f z)) = 0 := by
    rw [← map_natCast (f.residueFieldMap z).hom n, map_eq_zero] at h
    exact h
  rw [← Ideal.algebraMap_residueField_eq_zero, map_natCast,
    ← map_natCast (Scheme.Spec.residueFieldIso (CommRingCat.of A) (f z)).hom.hom n, map_eq_zero]
  exact h₁

theorem isNoetherianRing_V (c : Coeff l) (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime)
    (hW : (p : ℂ) ∈ W.nonunits) : IsNoetherianRing (c.V W) := by
  obtain ⟨b, hb, -⟩ := GlobalTheory.GlobalModelGuards.exists_incl c W
  obtain ⟨M, hM⟩ := GlobalTheory.ShFam.Pad.BCEx.exists_isLocalization hp hW b hb
  letI := b.toAlgebra
  exact IsLocalization.isNoetherianRing M (c.V W) inferInstance

theorem not_isUnit_V (c : Coeff l) (W : ValuationSubring ℂ) (x : c.V W) (hx : ((x : c.F) : ℂ) ∈ W.nonunits) :
    ¬ IsUnit x := by
  intro hu
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hvW : ((v : c.F) : ℂ) ∈ W := v.2
  have h1 : ((x : c.F) : ℂ) * ((v : c.F) : ℂ) = 1 := by
    have := congrArg (fun z : c.V W => ((z : c.F) : ℂ)) hv
    simpa using this
  rw [ValuationSubring.mem_nonunits_iff] at hx
  have h2 := (W.valuation_le_one_iff _).2 hvW
  have h3 := congrArg W.valuation h1
  rw [map_mul, map_one] at h3
  exact (mul_lt_one_of_lt_of_le hx h2).ne h3

theorem exists_place_over (c : Coeff l) (q : PrimeSpectrum (𝓞 c.F)) {p : ℕ} (hp : p.Prime)
    (hq : (p : 𝓞 c.F) ∈ q.asIdeal) :
    ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits ∧ ∀ b : 𝓞 c.F →+* c.V W,
      (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → (IsLocalRing.maximalIdeal (c.V W)).comap b = q.asIdeal := by
  have := c.fin
  have : NumberField c.F := {}
  let φ : 𝓞 c.F →+* ℂ := c.F.val.toRingHom.comp (algebraMap (𝓞 c.F) c.F)
  have hφ : Function.Injective φ := fun a b h => RingOfIntegers.coe_injective (Subtype.ext h)
  let e : 𝓞 c.F ≃+* φ.range :=
    RingEquiv.ofBijective φ.rangeRestrict ⟨fun a b h => hφ (by have h' := congrArg (fun x : φ.range => (x : ℂ)) h; exact h'), φ.rangeRestrict_surjective⟩
  let I : Ideal φ.range := q.asIdeal.comap (e.symm : φ.range →+* 𝓞 c.F)
  have hI : I ≠ ⊤ := fun h => q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have : (1 : φ.range) ∈ I := h ▸ Submodule.mem_top
    simpa [I] using this))
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hmem : ∀ x ∈ q.asIdeal, φ x ∈ W.nonunits := fun x hx =>
    hW ⟨e x, by simpa [I] using hx, rfl⟩
  refine ⟨W, ?_, fun b hb => ?_⟩
  · simpa [φ] using hmem _ hq
  have hne : q.asIdeal ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hq
    exact hp.ne_zero (by exact_mod_cast hq)
  have hmax : q.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal q.isPrime hne
  refine (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) fun x hx => ?_).symm
  refine not_isUnit_V c W (b x) ?_
  have := hmem x hx
  rw [show φ x = (((b x : c.V W) : c.F) : ℂ) by simp [φ, hb]] at this
  exact this

variable {Xo : Moduli D l} {c : Coeff l}

theorem isLocallyNoetherian_X (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) : IsLocallyNoetherian Y.X := by
  have := c.fin
  have : NumberField c.F := {}
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  exact LocallyOfFiniteType.isLocallyNoetherian Y.s

theorem isReduced_X (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) : IsReduced Y.X := by
  have : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x => by
    have := (Y.normal x).1
    infer_instance
  exact isReduced_of_isReduced_stalk Y.X

theorem generic_mem_abLocus (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (ξ : Y.X)
    (hξ : ∀ y : Y.X, y ⤳ ξ → y = ξ) : ξ ∈ abLocus Y.t.G := by
  have := c.fin
  have : NumberField c.F := {}
  have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 c.F) (S := c.F) (nonZeroDivisors (𝓞 c.F))
  have := Y.jQ_open
  have := Y.flat
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  let o : Sp c.F := IsLocalRing.closedPoint c.F
  have ho : spMap (algebraMap (𝓞 c.F) c.F) o ⤳ Y.s ξ := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => ?_
    have h1 : algebraMap (𝓞 c.F) c.F a ∈ IsLocalRing.maximalIdeal c.F := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h1
    obtain rfl : a = 0 := RingOfIntegers.coe_injective (by simpa using h1)
    exact zero_mem _
  obtain ⟨ξ', h₁, h₂⟩ := Flat.generalizingMap Y.s ho
  obtain rfl := hξ ξ' h₁
  obtain ⟨ζ, hζ⟩ : ξ' ∈ Set.range (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨o, h₂.symm⟩
  have : IsLocallyNoetherian (pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
  have : CompactSpace (pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) :) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
  have : IsNoetherian (pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := {}
  have hr : ζ ∈ Set.range Y.jQ := by
    refine GlobalTheory.TraitGeneric.mem_of_dense_of_maximal (fun y hy => ?_) Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense
    have : y = ζ := by
      refine (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.injective ?_
      rw [hζ]
      exact hξ _ (hζ ▸ hy.map (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).continuous)
    rw [this]
  rw [← Y.ab_gen] at hr
  rw [← hζ]
  exact hr

theorem global_fibPF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (Y : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W), (∀ p W hp hW i, (Y p W hp hW i).SplitFibres ∧ (Y p W hp hW i).N3) → ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (Ygl : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), (∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W), (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Dominates Ygl (Y p W hp hW ⟨l, c, hg p hp⟩) b) → PowFns Ygl.t ∧ ∀ (p : ℕ), p.Prime → ∀ z : Ygl.X, (p : Ygl.X.residueField z) = 0 → FibPF Ygl.t z := by
  intro E _ _ _ H D Xo Y hY l c hg Ygl hdom
  refine ⟨_root_.GlobalTheory.CompanionTheory.Ar.PowFn.powFns_of_generic_abelian E H Ygl.X Ygl.t (isReduced_X Ygl) (isLocallyNoetherian_X Ygl)
    (fun z hz => generic_mem_abLocus Ygl z hz), ?_⟩
  intro p hp z hz
  have hq : (p : 𝓞 c.F) ∈ (Ygl.s z).asIdeal := natCast_mem_of_residueField Ygl.s z p hz
  obtain ⟨W, hW, hc⟩ := exists_place_over c (Ygl.s z) hp hq
  obtain ⟨b, hb, -⟩ := GlobalTheory.GlobalModelGuards.exists_incl c W
  have hpt : Ygl.s z = spMap b (IsLocalRing.closedPoint (c.V W)) :=
    PrimeSpectrum.ext (hc b hb).symm
  obtain ⟨z', rfl, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Ygl.s) (g := spMap b) z _ hpt
  obtain ⟨f, t, m₁, m₂, -, -, -⟩ := hdom p W hp hW b hb
  have hN := isNoetherianRing_V c W hp hW
  have hinj : Function.Injective (c.V W).subtype := Subtype.val_injective
  have hz' : (p : ((Y p W hp hW ⟨l, c, hg p hp⟩).X).residueField (f z')) = 0 := by
    exact (natCast_residueField_iff f z' p).2 ((natCast_residueField_iff _ z' p).1 hz)
  have h₁ := _root_.GlobalTheory.CompanionTheory.Ar.ModelFib.model_fibPF E H D l (Xo l) c (c.V W) (c.V W).subtype (Y p W hp hW ⟨l, c, hg p hp⟩)
    (GlobalTheory.LocM.BaseMdl.dense_j hinj _) (hY p W hp hW _).1 (hY p W hp hW _).2 p hp (f z') hz'
  exact (_root_.GlobalTheory.CompanionTheory.Ar.FibPull.fibPF_pull_iff E H _ _ _ t _ m₁ z').1 ((_root_.GlobalTheory.CompanionTheory.Ar.FibPull.fibPF_pull_iff E H _ _ _ t f m₂ z').2 h₁)

end GlobalTheory.CompanionTheory.Ar.GlobalFib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptGoodReductionDegree
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenFlag

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi _root_.GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.FlagBun

section Model

theorem coordTie_along {o : Type} [CommRing o] {X : Scheme.{0}} {Ω : Type} [Field Ω] [Algebra o Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ κ' : Type} {x : κ → Ω} (h : CoordTie o ξ x) (e : κ' → κ)
    (he : Function.Surjective e) (x' : κ' → Ω) (hx : ∀ c, x' c = x (e c)) : CoordTie o ξ x' := by
  obtain rfl : x' = fun c => x (e c) := funext hx
  have hc : ∀ c p, InChart ξ (fun c => x (e c)) c p ↔ InChart ξ x (e c) p := fun c p =>
    and_congr Iff.rfl (he.forall (p := fun c' => x c' / x (e c) ∈ regAt ξ p)).symm
  refine ⟨h.gen, fun p => ?_, fun c h0 => ?_, fun c h0 a => ?_⟩
  · obtain ⟨c, hp⟩ := h.cover p
    obtain ⟨c, rfl⟩ := he c
    exact ⟨c, (hc c p).2 hp⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (e c) h0
    exact ⟨U, hU, fun q => (hq q).trans (exists_congr fun _ => (hc c _).symm)⟩
  · have : (Set.range fun j => x (e j) / x (e c)) = Set.range fun j => x j / x (e c) :=
      he.range_comp fun j => x j / x (e c)
    simpa only [hc, this] using h.ring (e c) h0 a

theorem closure_genField (Ω : Type) [Field Ω] {I : Type} :
    Subfield.closure (Set.range (algebraMap Ω (FractionRing (MvPolynomial I Ω))) ∪
      {a | ∃ l l' : Option I, a = (l.elim 1 fun q => algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q)) /
        (l'.elim 1 fun q => algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q))}) = ⊤ := by
  set F := Subfield.closure (Set.range (algebraMap Ω (FractionRing (MvPolynomial I Ω))) ∪
      {a | ∃ l l' : Option I, a = (l.elim 1 fun q => algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q)) /
        (l'.elim 1 fun q => algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q))}) with hF
  have hp : ∀ p : MvPolynomial I Ω, algebraMap _ (FractionRing (MvPolynomial I Ω)) p ∈ F := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      refine Subfield.subset_closure (Or.inl ⟨a, ?_⟩)
      rw [IsScalarTower.algebraMap_apply Ω (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))]
      rfl
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp (Subfield.subset_closure (Or.inr ⟨some i, none, ?_⟩))
      simp
  refine eq_top_iff.2 fun a _ => ?_
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial I Ω) a
  exact div_mem (hp p) (hp q)

end Model

theorem exists_genericFlag : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c) (d : ℕ), A.ξ ≫ A.f = y₀ ≫ Y.j → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree A p) → (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ A.R p)) → A.IsCover d → ∃ (Ω' : Type) (_ : Field Ω') (_ : CharZero Ω') (i : Ω →+* Ω') (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω') (𝔐 : HodgeCpt Y S y') (g : 𝔐.X ⟶ A.X) (b : ∀ s, Fin (labelRk D s) → 𝔐.Li) (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module 𝔐.Ω₀ Li₀) (M₀ : LieModel Y.t.G 𝔐.ξ₀ Li₀) (j : Li₀ →+ 𝔐.Li) (V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀), GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ A.ξ g i ∧ 𝔐.f = g ≫ A.f ∧ 𝔐.R = A.R ∧ (∀ p ∈ S, HT.HTFree 𝔐 p) ∧ (∀ s, Submodule.span Ω' (Set.range (b s)) = 𝔐.Vgen s) ∧ (∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap 𝔐.fn) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s) ∧ (letI := 𝔐.fn.toAlgebra; IsGenericFlag (Ω' := Ω') j V₀ b d) := by
  intro hW E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y A y₀ d hy hS hHT hζ hcov
  classical
  haveI : Finite (GenIx (labelRk D)) := by unfold GenIx; infer_instance
  let Ω' := GenField Ω (labelRk D)
  let i : Ω →+* Ω' := algebraMap Ω Ω'
  haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap Ω Ω').injective

  let x : ((k : K) → J k) → Ω := fun c' => ∏ k, y ⟨k, c' k⟩
  let M₁ : PModel ℤ x :=
    { X := A.X, ξ := A.ξ, s := specZIsTerminal.from _, hover := specZIsTerminal.hom_ext _ _, all := A.all, tie := A.tie }
  let w : Option (GenIx (labelRk D)) → Ω' :=
    fun o => o.elim 1 fun q => algebraMap (MvPolynomial (GenIx (labelRk D)) Ω) Ω' (MvPolynomial.X q)
  obtain ⟨M₂, f₂, hd₂⟩ := _root_.GlobalTheory.CompanionTheory.Ar.join_exists ℤ Ω _ x M₁ Ω' i _ w (fun a => by simp)
    ⟨none, one_ne_zero⟩ (closure_genField Ω)
  obtain ⟨κ₃, _, y₃, M₃, f₃, hd₃, hN, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.NormEx.exists_normalisation ℤ Ω' _ _ M₂ Ω'
  letI : Fintype κ₃ := Fintype.ofFinite κ₃
  let y' : (Σ _ : Unit, κ₃) → Ω' := fun q => y₃ q.2
  have htie : CoordTie ℤ M₃.ξ (fun c' : (k : Unit) → κ₃ => ∏ k, y' ⟨k, c' k⟩) :=
    coordTie_along M₃.tie (fun c' => c' ()) (fun a => ⟨fun _ => a, rfl⟩) _ fun c' => by simp [y']
  have hd₃' : M₃.ξ ≫ f₃ = M₂.ξ := by
    have h := hd₃
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at h
    rw [h, show algebraMap Ω' Ω' = RingHom.id Ω' from rfl, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have hdh : GlobalTheory.CompanionTheory.Ar.Dominates M₃.ξ A.ξ (f₃ ≫ f₂) i := by
    show M₃.ξ ≫ f₃ ≫ f₂ = _
    rw [← Category.assoc, hd₃']
    exact hd₂
  have hnormal : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₃.X := (_root_.GlobalTheory.CompanionTheory.Ar.XR.component_whole_isIntegral_and_normal _ Ω' M₃.ξ M₃.tie.gen M₃.all).2.1 hN

  obtain ⟨A', e, j₁, m, he, hf, hm, hcst, hR, hext, hpt, hHT', hV⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HcptPull.hodgeCpt_pull E H D l Xo c _ _ Y S Ω Ω' i K Unit
    J (fun _ => κ₃) y y' A y₀ M₃.X M₃.ξ (f₃ ≫ f₂) hy hS (fun p hp => (hHT p hp).2) M₃.all
    (by convert htie using 1 <;> first | exact Subsingleton.elim _ _ | skip) hnormal hdh
  have hd' : GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ (e.hom ≫ f₃ ≫ f₂) i := by
    show A'.ξ ≫ e.hom ≫ f₃ ≫ f₂ = _
    rw [← Category.assoc, he]
    exact hdh
  have hf' : A'.f = (e.hom ≫ f₃ ≫ f₂) ≫ A.f := hf.trans (Category.assoc _ _ _).symm
  have hfn : GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ₀ A'.f (i.comp A.fn) := by
    have h : A.ξ ≫ A.f = Spec.map (CommRingCat.ofHom A.fn) ≫ A.ξ₀ := A.fn_over
    have h' : A'.ξ ≫ e.hom ≫ f₃ ≫ f₂ = Spec.map (CommRingCat.ofHom i) ≫ A.ξ := hd'
    show A'.ξ ≫ A'.f = Spec.map (CommRingCat.ofHom (i.comp A.fn)) ≫ A.ξ₀
    have e1 : A'.ξ ≫ A'.f = (A'.ξ ≫ e.hom ≫ f₃ ≫ f₂) ≫ A.f :=
      (congrArg (A'.ξ ≫ ·) hf').trans (Category.assoc _ _ _).symm
    have e2 : Spec.map (CommRingCat.ofHom (i.comp A.fn)) =
        Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom A.fn) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
    rw [e1, h', Category.assoc, h, e2, Category.assoc]
  let 𝔐 : HodgeCpt Y S y' :=
    { A' with Ω₀ := A.Ω₀, fld₀ := A.fld₀, ξ₀ := A.ξ₀, gen₀ := A.gen₀, fn := i.comp A.fn, fn_over := hfn }
  have hy' : 𝔐.ξ ≫ 𝔐.f = (spMap i ≫ y₀) ≫ Y.j := by
    show A'.ξ ≫ A'.f = _
    have h' := hd'
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at h'
    rw [hf', ← Category.assoc, h', Category.assoc, hy, Category.assoc]

  obtain ⟨cst₀, y₁, h₁, h₂, h₃⟩ := _root_.GlobalTheory.CompanionTheory.Ar.GenPoint.exists_open_point E H D l Xo c Y S Ω' Unit (fun _ => κ₃) y' 𝔐 (spMap i ≫ y₀) hy'
  obtain ⟨Li₀, _, _, M₀, j, V₀, cb, hj, hsm, hV₀, hcb, hli, hspan⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HcLie.exists_lie_eig E H D l Xo c Y S Ω' Unit
    (fun _ => κ₃) y' 𝔐 (spMap i ≫ y₀) cst₀ y₁ hy' h₁ h₂ h₃
  have hfin := GlobalTheory.T.finrank_adjoin_vars_field 𝔐.Ω₀ Ω A.fn (GenIx (labelRk D)) d hcov.1 hcov.2
  obtain ⟨hsp, hgen⟩ := GlobalTheory.T.generic_flag_field_change 𝔐.Ω₀ Ω A.fn _ (labelRk D) d hcov.1 hfin Li₀ 𝔐.Li j V₀ cb hcb hsm hli
  refine ⟨Ω', inferInstance, inferInstance, i, Unit, inferInstance, fun _ => κ₃, inferInstance, y', 𝔐,
    e.hom ≫ f₃ ≫ f₂, _, Li₀, _, _, M₀, j, V₀, hd', hf', hR, fun p hp => ⟨?_, hHT' p hp⟩,
    fun s => (hsp s).trans (hspan s), hj, hV₀, hgen⟩
  exact _root_.GlobalTheory.CompanionTheory.Ar.HFlag.omP_ext hW E H D l Xo c Y S Ω Ω' i K Unit J (fun _ => κ₃) y y' A 𝔐 (e.hom ≫ f₃ ≫ f₂) m j₁ y₀ p hp hd' hf' hR
    hext hpt hy (hζ p hp) (hHT p hp).1

end GlobalTheory.CompanionTheory.Ar.GenFlag
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptLabelBasesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_label_bases : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c) (b : ∀ s, Fin (labelRk D s) → 𝔐.Li) (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module 𝔐.Ω₀ Li₀) (M₀ : LieModel Y.t.G 𝔐.ξ₀ Li₀) (j : Li₀ →+ 𝔐.Li) (V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀) (d : ℕ), 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ 𝔐.R p)) → (∀ s, Submodule.span Ω (Set.range (b s)) = 𝔐.Vgen s) → (∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap 𝔐.fn) ≫ (M₀.pt e).left) → (∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s) → (letI := 𝔐.fn.toAlgebra; IsGenericFlag (Ω' := Ω) j V₀ b d) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (𝔐' : HodgeCpt Y S y') (g : 𝔐'.X ⟶ 𝔐.X) (Fl : 𝔐'.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K' → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐'.ξ 𝔐.ξ g (RingHom.id Ω) ∧ 𝔐'.f = g ≫ 𝔐.f ∧ 𝔐'.R = 𝔐.R ∧ 𝔐'.cst = 𝔐.cst ∧ (∀ p ∈ S, HT.HTFree 𝔐' p) ∧ Fl.deg = d ∧ (∀ s i, (𝔐'.M.pt (Fl.b s i)).left ≫ 𝔐'.m.φ = spMap (dualMap (RingHom.id Ω)) ≫ (𝔐.M.pt (b s i)).left ≫ 𝔐.m.φ) ∧ Fl.RootLines xdeg e ∧ (∀ s, (𝔐'.dR s).IsFlagVBOn Set.univ (Fl.b s)) ∧ ∀ q ∈ genFib 𝔐.ξ, (∀ s, (𝔐.V s).IsFlagVBOn {q} (b s)) → IsoAt 𝔐'.ξ g (RingHom.id Ω) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HFlag.exists_flag_model | exact GlobalTheory.CompanionTheory.Ar.HFlag.exists_flag_model | (intros; apply GlobalTheory.CompanionTheory.Ar.HFlag.exists_flag_model <;> assumption)
end

