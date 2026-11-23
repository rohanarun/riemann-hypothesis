module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.FiniteNotLocFrOne
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormEqNegOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0772
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointLiesOnComponentCmCurveField
section
noncomputable section

namespace GlobalTheory.FixedPoint

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompRat GlobalTheory.CompRat.FixedConst
  GlobalTheory.AllWt GlobalTheory.FlatLine

theorem exists_descent {Y : Scheme.{0}} (K : IntermediateField ℚ ℂ) (x : Sp ℂ ⟶ Y)
    (hx : ∀ τ : ℂ ≃+* ℂ, (∀ a ∈ K, τ a = a) → spMap (τ : ℂ →+* ℂ) ≫ x = x) :
    ∃ g : Sp K ⟶ Y, spMap (algebraMap K ℂ) ≫ g = x := by
  classical
  obtain ⟨⟨y, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField ℂ Y).symm.surjective x
  have hfix : ∀ τ : ℂ ≃+* ℂ, (∀ a ∈ K, τ a = a) → φ ≫ CommRingCat.ofHom (τ : ℂ →+* ℂ) = φ := by
    intro τ hτ
    have e : spMap (τ : ℂ →+* ℂ) ≫ (Scheme.SpecToEquivOfField ℂ Y).symm ⟨y, φ⟩ =
        (Scheme.SpecToEquivOfField ℂ Y).symm ⟨y, φ ≫ CommRingCat.ofHom (τ : ℂ →+* ℂ)⟩ := by
      change Spec.map _ ≫ Spec.map φ ≫ _ = Spec.map (φ ≫ _) ≫ _
      rw [Spec.map_comp, Category.assoc]
    have h2 := (Scheme.SpecToEquivOfField ℂ Y).symm.injective (e.symm.trans (hx τ hτ))
    exact eq_of_heq (Sigma.mk.inj_iff.mp h2).2
  have hmem : ∀ r, φ.hom r ∈ K := by
    intro r
    obtain ⟨a, ha⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := K) (φ.hom r) (fun σ => by
      have h := hfix σ.toRingEquiv (fun a ha => σ.commutes ⟨a, ha⟩)
      exact congrArg (fun f => f.hom r) h)
    rw [← ha]
    exact a.2
  let ψ : Y.residueField y →+* K := φ.hom.codRestrict K hmem
  refine ⟨Spec.map (CommRingCat.ofHom ψ : Y.residueField y ⟶ CommRingCat.of K) ≫ Y.fromSpecResidueField y, ?_⟩
  have hc : (CommRingCat.ofHom ψ : Y.residueField y ⟶ CommRingCat.of K) ≫ CommRingCat.ofHom (algebraMap K ℂ) = φ := by
    ext r
    rfl
  exact (Spec.map_comp_assoc _ _ _).symm.trans (congrArg (· ≫ Y.fromSpecResidueField y) (congrArg Spec.map hc))

theorem ev_eq_of_restrict {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (W : Y.Opens) (p : Sp ℂ) (hp : x p ∈ W) (f : Γ(Y, ⊤))
    (n : ℕ) (hf : Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op f = n) : ev x f = n := by
  have hr : Set.range x ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    rwa [Subsingleton.elim q p]
  have hf' : (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom f = n := hf
  have hle : W.ι ''ᵁ ⊤ ≤ W := (Scheme.Opens.ι_image_top W).le
  have e : (homOfLE (le_top : W.ι ''ᵁ ⊤ ≤ ⊤)).op = (homOfLE (le_top : W ≤ ⊤)).op ≫ (homOfLE hle).op := rfl
  have key : (Y.presheaf.map (homOfLE (le_top : W.ι ''ᵁ ⊤ ≤ ⊤)).op).hom f = n := by
    rw [e, Functor.map_comp]
    exact (congrArg (Y.presheaf.map (homOfLE hle).op).hom hf').trans (map_natCast _ n)
  rw [← IsOpenImmersion.lift_fac W.ι x hr, ev_comp, Scheme.Opens.ι_appTop]
  exact (congrArg _ key).trans (map_natCast _ n)

theorem exists_indicator {Y : Scheme.{0}} {Z : Set Y} (hZ : IsClopen Z) :
    ∃ f : Γ(Y, ⊤), ∀ (x : Sp ℂ ⟶ Y) (p : Sp ℂ), (x p ∈ Z → ev x f = 1) ∧ (x p ∉ Z → ev x f = 0) := by
  let V : Y.Opens := ⟨Z, hZ.isOpen⟩
  let W : Y.Opens := ⟨Zᶜ, hZ.isClosed.isOpen_compl⟩
  have hVW : V ⊔ W = ⊤ := by
    apply TopologicalSpace.Opens.ext
    simp [V, W, Set.union_compl_self]
  have hdis : Disjoint V W := by
    rw [disjoint_iff]
    apply TopologicalSpace.Opens.ext
    simp [V, W]
  obtain ⟨f, hfV, hfW⟩ := exists_extension_zero V W hVW hdis 1
  refine ⟨f, fun x p => ⟨fun hp => ?_, fun hp => ?_⟩⟩
  · have h := ev_eq_of_restrict x V p hp f 1 (by rw [hfV, Nat.cast_one])
    simpa using h
  · have h := ev_eq_of_restrict x W p hp f 0 (by rw [hfW, Nat.cast_zero])
    simpa using h

private theorem exists_isTypeFn' {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p q : ℕ) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H p q ty := by
  classical
  let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then p else q
  let e := Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))
  refine ⟨_, fun i => (e.symm i).1, fun τ => ?_⟩
  have hcard : Nat.card {i // (e.symm i).1 = τ} = m τ := by
    rw [Nat.card_congr (e.symm.subtypeEquiv (p := fun i => (e.symm i).1 = τ) (q := fun s => s.1 = τ)
      (fun _ => Iff.rfl)), Nat.card_congr (Equiv.sigmaSubtype τ), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hcard]; simp [m, h]
  · rw [hcard]; simp [m, h]

private theorem spMap_comp_spMap_divisor {R₀ R R' : Type} [CommRing R₀] [CommRing R] [CommRing R'] (f : R →+* R')
    (g : R₀ →+* R) : spMap f ≫ spMap g = spMap (f.comp g) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_fixed_point (hD : 1 ≤ Dw.p + Dw.q)
    (hsig : Dw.p = 0 ∨ Dw.q = 0 ∨ (3 ≤ Dw.p + Dw.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) (Z : Comp Xo c) :
    ∃ x : Sp ℂ ⟶ Xo.XF c, x ≫ strK = spMap (algebraMap c.F ℂ) ∧ (∀ p, x p ∈ (Z : Set (Xo.XF c))) ∧
      ∀ τ : ℂ ≃+* ℂ, (∀ a ∈ c.F, τ a = a) → FixesCurve H τ l.M' → spMap (τ : ℂ →+* ℂ) ≫ x = x := by
  classical
  obtain ⟨g, ty, hty⟩ := exists_isTypeFn' H Dw.p Dw.q
  let σ₀ : KA l →+* ℂ := (algebraMap c.F ℂ).comp (IntermediateField.inclusion c.le).toRingHom
  have hσ₀ : σ₀ (baseKA l).ρ = H.rt0 := rfl
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H Dw l Xo σ₀ g ty hD hσ₀ hty

  obtain ⟨L, _, _, j, g₀, hg₀, hZ₀⟩ := GlobalTheory.FlatLine.exists_numberField_point Z
  letI : Algebra c.F L := j.toAlgebra
  haveI : IsScalarTower ℚ c.F L := IsScalarTower.of_algebraMap_eq (fun a => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ c.F), eq_ratCast (algebraMap ℚ L), map_ratCast])
  haveI : Algebra.IsAlgebraic c.F L := Algebra.IsAlgebraic.tower_top (K := ℚ) c.F
  let φ : L →ₐ[c.F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hφ : (φ : L →+* ℂ).comp j = algebraMap c.F ℂ := RingHom.ext fun a => φ.commutes a
  obtain ⟨hx₀, hZx₀⟩ := GlobalTheory.FlatLine.point_ext hg₀ hZ₀ (φ : L →+* ℂ)
  rw [hφ] at hx₀
  set x₀ : Sp ℂ ⟶ Xo.XF c := spMap (φ : L →+* ℂ) ≫ g₀ with hx₀def
  have hover : x₀ ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap σ₀ := by
    rw [pullback.condition, ← Category.assoc]
    erw [hx₀]
    rw [spMap_comp_spMap_divisor]
  obtain ⟨i, P, hP, hPx⟩ := F.onto _ (by rw [Category.assoc]; exact hover)
  obtain ⟨P', hP', hs⟩ := GlobalTheory.CompRat.exists_isSplit_period_anyLevel E H Dw l Xo σ₀ g ty F hD hσ₀ hty hsig i
  have hcond : F.u i P' ≫ Xo.s = spMap (algebraMap c.F ℂ) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [F.over_σ i P' hP', spMap_comp_spMap_divisor]
  let xs : Sp ℂ ⟶ Xo.XF c := pullback.lift (F.u i P') (spMap (algebraMap c.F ℂ)) hcond
  have hxs₁ : xs ≫ pullback.fst _ _ = F.u i P' := pullback.lift_fst _ _ _
  have hxs₂ : xs ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) := pullback.lift_snd _ _ _

  obtain ⟨f, hf⟩ := exists_indicator (GlobalTheory.TrivOrderTieCompare.isClopen_comp Z)
  have hvals : ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
      valAt' x ⊤ f ∈ ({0, 1} : Set ℂ) := by
    intro x _
    rw [valAt'_top]
    by_cases hx : x default ∈ (Z : Set (Xo.XF c))
    · simp [(hf x default).1 hx]
    · simp [(hf x default).2 hx]
  have heq := GlobalTheory.CompRat.valAt_eq_of_finite_values_anyLevel E H Dw l Xo σ₀ g ty F hD hσ₀ hty c
    (algebraMap c.F ℂ) f _ (Set.toFinite _) hvals i P P' hP hP' x₀ xs hPx.symm hx₀ hxs₁ hxs₂
  rw [valAt'_top, valAt'_top, (hf x₀ default).1 (hZx₀ default)] at heq
  refine ⟨xs, hxs₂, fun p => ?_, fun τ hτ hfix => ?_⟩
  · by_contra hp
    rw [(hf xs p).2 hp] at heq
    exact one_ne_zero heq
  · have hτσ : (τ : ℂ →+* ℂ).comp σ₀ = σ₀ := RingHom.ext fun a => hτ _ (IntermediateField.inclusion c.le a).2
    have hfixed := GlobalTheory.CompRat.AnyLevel.conj_point_eq_of_isSplit F hD hσ₀ hty τ hτσ hfix i P' hP' hs
    apply pullback.hom_ext
    · rw [Category.assoc, hxs₁, hfixed]
    · rw [Category.assoc, hxs₂, spMap_comp_spMap_divisor]
      congr 1
      exact RingHom.ext fun a => hτ a a.2

end GlobalTheory.FixedPoint

namespace GlobalTheory.FixedPoint

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
open AlgebraicGeometry CategoryTheory

theorem exists_frPt_liesOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (Dw.p = 0 ∨ Dw.q = 0 ∨ (3 ≤ Dw.p + Dw.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ (K : IntermediateField ℚ ℂ) [NumberField K] (hle : c.F ≤ K), GlobalTheory.CompRat.CurveOver H K l.M' → ∀ Z : Comp Xo c, (letI : Algebra c.F K := (IntermediateField.inclusion hle).toRingHom.toAlgebra; ∃ y : FrPt Xo c K, LiesOn Z y) := by
  intro E _ _ _ H Dw l Xo c hD hsig K _ hle hK Z
  letI : Algebra c.F K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  obtain ⟨x, _, hxZ, hxfix⟩ := exists_fixed_point (H := H) (Xo := Xo) (c := c) hD hsig Z
  obtain ⟨g, hg⟩ := exists_descent K x (fun τ hτ => hxfix τ (fun a ha => hτ a (hle ha)) (hK τ hτ))
  have hcancel : ∀ a b : Sp K ⟶ Sp c.F, spMap (algebraMap K ℂ) ≫ a = spMap (algebraMap K ℂ) ≫ b → a = b := by
    intro a b hab
    rw [← Spec.map_preimage a, ← Spec.map_preimage b] at hab ⊢
    rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at hab
    congr 1
    ext r
    exact congrArg (fun f => f.hom r) hab
  have hgK : g ≫ strK = spMap (algebraMap c.F K) := by
    apply hcancel
    rw [← Category.assoc, hg, ‹x ≫ strK = spMap (algebraMap c.F ℂ)›, spMap_comp_spMap_divisor]
    rfl
  have hfr : ∀ (x : Sp K ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c K), ∃ y : FrPt Xo c K, y.x = x := by
    intro x hx
    choose u hu using fun τ => GlobalTheory.IntFramesCompare.exists_eigenBasisAt (c := c) hx τ
    obtain ⟨s, hs⟩ := gfp_gen GlobalTheory.abelianSchemeLaws_all.2.secTwist x
    exact ⟨⟨x, hx, u, fun τ => (hu τ).1, fun τ => (hu τ).2.1, fun τ => (hu τ).2.2, s, hs⟩, rfl⟩
  obtain ⟨y, hy⟩ := hfr (g ≫ GlobalTheory.FlatLine.prX Xo c) (GlobalTheory.FlatLine.prX_over hgK)
  refine ⟨y, fun s => ?_⟩
  rw [GlobalTheory.FlatLine.ptF_eq hgK hy]
  have hs : s = spMap (algebraMap K ℂ) default := Subsingleton.elim _ _
  have h1 := hxZ default
  rw [← hg] at h1
  rw [hs]
  exact h1

end GlobalTheory.FixedPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalHarmonicCongrColumnPolynomial
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefGlob

theorem sum_smul_mem_HaO {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k] (O : Subring k) (cc : Ty → Ty)
    (isX : Ty → Prop) (a : Ty → ℕ → ℕ) {m : ℕ} (x : Fin m → k) (P : Fin m → MvPolynomial (Letter Ty r n) k)
    (hx : ∀ i, x i ∈ O) (hP : ∀ i, P i ∈ HaO r n k O cc isX a) : ∑ i, x i • P i ∈ HaO r n k O cc isX a := by
  classical
  refine ⟨⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hP i).1.1, fun σ i i' hi t => ?_,
    fun q hq => ?_⟩, fun q => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, (hP j).1.2.1 σ i i' hi t]
  · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hq)
    exact (hP j).1.2.2 q (MvPolynomial.support_smul hj)
  · rw [MvPolynomial.coeff_sum]
    exact O.sum_mem fun j _ => by
      rw [MvPolynomial.coeff_smul, smul_eq_mul]
      exact O.mul_mem (hx j) ((hP j).2 q)

theorem exists_integer_congr {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (T₀ : CDVR)
    (io₀ : K →+* T₀.Fr) (ho : OverLa w T₀.V io₀ 1)
    (hini : ∀ (T : CDVR) (io : K →+* T.Fr) (e : ℕ), OverLa w T.V io e → ∃ (g : T₀.V →+* T.V) (χ : T₀.Fr →+* T.Fr),
      IsLocalHom g ∧ χ.comp io₀ = io ∧ χ.comp (algebraMap T₀.V T₀.Fr) = (algebraMap T.V T.Fr).comp g ∧
        ∀ ϖ : T₀.V, Irreducible ϖ → vV (K' := T.Fr) T.V (algebraMap T.V T.Fr (g ϖ)) = e)
    (d : ℕ) (hd : d ≠ 0) (v : T₀.V) :
    ∃ (x : 𝓞 K) (z : T₀.V), io₀ (x : K) = algebraMap T₀.V T₀.Fr v + (d : T₀.Fr) * algebraMap T₀.V T₀.Fr z := by
  obtain ⟨k, h, e⟩ := GlobalTheory.DefPt.Model.denseIn_of_initial w T₀ io₀ hini (algebraMap T₀.V T₀.Fr v) (d : T₀.V) (Nat.cast_ne_zero.2 hd)
  have hval : ∀ y : K, valV T₀.V (io₀ y) = w.valuation K y := fun y => by
    rw [GlobalTheory.PlaceCompletion.valV_eq_pow_of_overLa ho, pow_one]
  have hk : io₀ k = algebraMap T₀.V T₀.Fr (v - d * h) := by rw [map_sub, e]; ring
  have hk1 : w.valuation K k ≤ 1 := by
    rw [← hval, hk]
    exact GlobalTheory.PlaceCompletion.valV_algebraMap_le_one _
  have hdK : (d : K) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hd0 : w.valuation K (d : K) ≠ 0 := by simpa using hd
  obtain ⟨x, hx⟩ := w.exists_valuation_sub_lt_of_integer hk1 (Units.mk0 _ hd0)
  obtain ⟨z, hz⟩ := GlobalTheory.PlaceCompletion.exists_algebraMap_eq_of_valV_le_one (V := T₀.V)
    (x := io₀ ((algebraMap (𝓞 K) K x - k) / d)) (by
      rw [hval, map_div₀]
      exact div_le_one_of_le₀ hx.le zero_le)
  refine ⟨x, z - h, ?_⟩
  have h2 : io₀ (x : K) = io₀ k + (d : T₀.Fr) * algebraMap T₀.V T₀.Fr z := by
    rw [hz, ← map_natCast io₀, ← map_mul, ← map_add (f := _), mul_div_cancel₀ _ hdK]
    exact congrArg io₀ (by simp)
  rw [h2, hk]
  simp only [map_sub, map_mul, map_natCast]
  ring

section Push

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {c : Coeff l} {T₀ T : CDVR} (g : T₀.V →+* T.V) (χ : T₀.Fr →+* T.Fr)
  (hχ : ∀ x, χ (algebraMap T₀.V T₀.Fr x) = algebraMap T.V T.Fr (g x))

include hχ

theorem isCols_map {io₀ : c.F →+* T₀.Fr} {p n : ℕ} {cx : Lt1 Dw → ℕ} {B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T₀.V}
    (hB : IsCols c T₀ io₀ p cx B) : IsCols c T (χ.comp io₀) p cx fun f b j => g (B f b j) := by
  obtain ⟨blk, hb⟩ := hB
  refine ⟨blk, fun f => ?_⟩
  obtain ⟨h1, ⟨r, h2⟩, h3⟩ := hb f
  refine ⟨fun b j hj => (congrArg g (h1 b j hj)).trans (map_zero g), ⟨r, ?_⟩, fun N => ?_⟩
  · have := h2.map g
    rw [RingHom.map_det] at this
    exact this
  · obtain ⟨x, hx1, hx2, hx3⟩ := h3 N
    refine ⟨x, hx1, fun b j => ?_, hx3⟩
    obtain ⟨z, hz⟩ := hx2 b j
    refine ⟨g z, ?_⟩
    rw [RingHom.comp_apply, hz, hχ]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]

theorem map_polyT {n : ℕ} (cx : Lt1 Dw → ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T₀.V) :
    MvPolynomial.map χ (polyT B cx) = polyT (fun f b j => g (B f b j)) cx := by
  simp only [polyT, polyP, map_prod, map_pow]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [RingHom.map_det]
  congr 2
  ext ρ i : 2
  simp [GlobalTheory.CombMinor.cMat, hχ]

end Push

theorem exists_harmA_congr_polyT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (a : (E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∀ n : ℕ, ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∀ N : ℕ, ∃ P₁ ∈ harmA (Dw := Dw) c a n, ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∃ (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V) (R : MvPolynomial (LtN Dw n) T.Fr), IsCols c T io p (gap Dw a) B ∧ R ∈ FFV (Dw := Dw) T a n ∧ MvPolynomial.map io P₁ = polyT B (gap Dw a) + ((p : T.Fr) ^ N) • R := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p hp la a ha n hn N
  obtain ⟨T₀, io₀, ho₀, -, hini⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion c.F la.1
  obtain ⟨B₀, hB₀⟩ := GlobalTheory.IsoCols.exists_isCols E H Dw l Xo c p la T₀ io₀ 1 ho₀ (gap Dw a) n
    (le_trans (Finset.sum_le_sum fun f _ => by split_ifs <;> simp) hn)
  obtain ⟨-, k, cf, Pi, hPi, hsum⟩ := GlobalTheory.totalDegree_le_and_exists_combination_of_mem_FFV E H Dw l Xo c T₀ io₀ a n _
    (polyT_mem_FFV ha hB₀)
  choose x z hxz using fun i => exists_integer_congr la.1 T₀ io₀ ho₀ hini (p ^ N)
    (pow_ne_zero N hp.out.ne_zero) (cf i)
  refine ⟨∑ i, (x i : c.F) • Pi i, sum_smul_mem_HaO _ _ _ _ _ _ (fun i => (x i).2) hPi, fun T io e ho => ?_⟩
  obtain ⟨g, χ, -, rfl, h2, -⟩ := hini T io e ho
  have hχ : ∀ y, χ (algebraMap T₀.V T₀.Fr y) = algebraMap T.V T.Fr (g y) := RingHom.congr_fun h2
  refine ⟨fun f b j => g (B₀ f b j), ∑ i, algebraMap T.V T.Fr (g (z i)) • MvPolynomial.map (χ.comp io₀) (Pi i),
    isCols_map g χ hχ hB₀, sum_smul_mem_HaO _ _ _ _ _ _ (fun i => ⟨_, rfl⟩)
      (fun i => PullbackSections.ffvMap E H Dw l c a n _ (hPi i) T _), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_polyT g χ hχ, hsum, map_sum, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_map, RingHom.comp_apply, hxz i,
    map_add, hχ, map_natCast, Nat.cast_pow, map_pow]
  ring

end GlobalTheory.RefGlob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalfDilatedReductionResidueMatrices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.HalfLiftRed

open GlobalTheory.AdelicLatMove

theorem idem_smul_mem_latO {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (sdS : IsSelfDualC S ΛS) (frS : Formalism.L2.DIV.IsFrame βS ΛS) (frT : Formalism.L2.DIV.IsFrame βT ΛT)
    {e : AE D} {P : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e P) {a : 𝓞 D.host.E} (ha : a ∉ P.asIdeal)
    (haA : (a : D.host.E) ∈ D.host.AA) {x : WO S T} (hx : IsIntM (frMapO S T βS βT x)) :
    e • x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  have ha0 : a ≠ 0 := fun h => ha (h ▸ zero_mem _)
  have ha' : (a : D.host.E) ≠ 0 := by exact_mod_cast ha0
  have hw : finPart D (e * incA D ((a : D.host.E))⁻¹) ∈ intAE D := by
    by_contra h
    exact ha ((he.2 a ha0).2 h)
  choose s hs hs' using GlobalTheory.IntHalfLat.exists_dual sdS frS
  set Y : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := HMul.hMul (x.map (toEAf D)) βS.val with hY
  have ht : ∀ j, (fun i => Y i j) ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT := fun j => by
    refine (frT _).2 fun i => ?_
    have e1 : Matrix.mulVec (βT⁻¹).val (fun i => Y i j) i = frMapO S T βS βT x i j := by
      rw [frMapO, Matrix.mul_assoc]
      rfl
    rw [e1]
    exact hx i j
  have hU := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hw _
    (sum_mem fun j (_ : j ∈ Finset.univ) => rankOne_mem_latO S T ΛS ΛT (a : D.host.E) haA (s j) (hs j) _ (ht j))
  convert hU using 1
  ext i l
  have hYZ : ∑ j, Y i j * (βS⁻¹).val j l = toEAf D (x i l) := by
    rw [← Matrix.mul_apply, hY, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Matrix.map_apply]
  have hsum : (∑ j, rankOne S T (a : D.host.E) (s j) fun i => Y i j) i l =
      incA D (a : D.host.E) * x i l * finEmb D 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.sum_apply, ← finEmb_mul, mul_one, map_mul, toEAf_incA, ← hYZ, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rankOne, Matrix.of_apply, hs' j l, mul_assoc]
  have h1 : e * finEmb D 1 = e := GlobalTheory.PlaceDatum.mul_pair_one (GlobalTheory.SplitScalar.infPart_splitIdem he.1)
  have h2 : incA D ((a : D.host.E))⁻¹ * incA D (a : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha', map_one]
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, hsum]
  linear_combination (-(x i l)) * h1 - (e * x i l * finEmb D 1) * h2

end GlobalTheory.HalfLiftRed

theorem GlobalTheory.HalfLiftRed.exists_half_dil_redM_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ x : ∀ PP : ↥Q, Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (kP PP.1), ∃ y : WO (Vc D i) (Wc D i), IsHalf eQ y ∧ dil i (ϖ : D.host.E) y ∈ lattice₂ R i ∧ ∀ PP : ↥Q, redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) y)) = x PP := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i _ Q hQ eQ he ϖ hϖ _ x
  have hSV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  obtain ⟨cV, hBV⟩ := hC.lev.βV i
  obtain ⟨cW, hBW⟩ := hC.lev.βW i
  have hFV : Formalism.L2.DIV.IsFrame (R.βV i) (R.ΛV i) := hBV.1
  have hFW : Formalism.L2.DIV.IsFrame (R.βW i) (R.ΛW i) := hBW.1
  obtain ⟨t0, hQt⟩ := hQ
  have he2 := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨hi, hres⟩ := GlobalTheory.AdjDatumNe.idemSum_res he
  obtain ⟨⟨es, h1, h2⟩, -⟩ := he
  have hk : ∀ PP ∈ Q, toEAf D (es PP) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun PP hPP => (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)).1
  have hdel : ∀ PP ∈ Q, ∀ PP' (hPP' : PP' ∈ Q),
      Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D (es PP'), hk PP' hPP'⟩ = if PP' = PP then 1 else 0 := by
    intro PP hPP PP' hPP'
    by_cases hq : PP' = PP
    · subst hq
      rw [if_pos rfl]
      exact (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP' hPP')).2
    · rw [if_neg hq]
      have hne : PP ≠ PP' := fun h => hq h.symm
      have horth : es PP * es PP' = 0 :=
        (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 PP hPP).1 (h1 PP' hPP').1).resolve_left fun h => by
          have h' := h1 PP' hPP'
          rw [← h] at h'
          exact hne (GlobalTheory.PlaceVec.isIdemAt_inj (h1 PP hPP) h')
      have h4 : (⟨toEAf D (es PP), hk PP hPP⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨toEAf D (es PP'), hk PP' hPP'⟩ = 0 :=
        Subtype.ext (by change toEAf D (es PP) * toEAf D (es PP') = 0; rw [← RingHom.map_mul, horth, RingHom.map_zero])
      have h5 := congrArg (Formalism.L2.DIV.resS D.host.F PP) h4
      rwa [RingHom.map_mul, RingHom.map_zero, (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)).2, one_mul] at h5
  choose a ha using fun (PP : ↥Q) (j : Fin (Wc D i).rank) (k : Fin (Vc D i).rank) =>
    Ideal.Quotient.mk_surjective (I := PP.1.asIdeal) (x PP j k)
  set Z : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (EAf D) := fun j k =>
    ((⟨toEAf D eQ, hi⟩ * ∑ PP ∈ Q.attach,
        ⟨toEAf D (es PP.1), hk PP.1 PP.2⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E (a PP j k) :
          Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) with hZ
  have hZe : ∀ j k, toEAf D eQ * Z j k = Z j k := fun j k => by
    simp only [hZ, MulMemClass.coe_mul]
    rw [← mul_assoc, ← RingHom.map_mul, he2]
  obtain ⟨w, hwh, -, hwZ⟩ := GlobalTheory.HalfDuality.exists_half_frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) eQ he2 Z hZe
  have hint : IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) := fun j k => by
    rw [hwZ]; exact Subtype.prop _
  have hϖE : (ϖ : D.host.E) ≠ 0 := by simpa using hϖ
  have hdil : dil i (ϖ : D.host.E) (dil i (ϖ : D.host.E)⁻¹ w) = w := by
    ext j k
    simp only [Matrix.map_apply]
    rw [← mul_assoc, ← RingHom.map_mul, mul_inv_cancel₀ hϖE, RingHom.map_one, one_mul]
  refine ⟨dil i (ϖ : D.host.E)⁻¹ w, fun j k => ?_, ?_, fun PP => ?_⟩
  · simp only [Matrix.map_apply]
    rw [mul_left_comm, hwh j k]
  · rw [hdil]
    have hxe : (∑ PP ∈ Q, es PP) • w = w := by
      rw [← h2]; exact Matrix.ext fun j k => hwh j k
    rw [← hxe, Finset.sum_smul]
    refine sum_mem fun PP hPP => ?_
    have hN : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun hm =>
      hQG.2 t0 PP (hQt hPP) (by
        push_cast
        exact Ideal.mul_mem_left _ _ hm)
    refine GlobalTheory.HalfLiftRed.idem_smul_mem_latO hSV hFV hFW (h1 PP hPP) hN ?_ hint
    rw [show (((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) : D.host.E) = ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) from
      map_natCast (algebraMap (𝓞 D.host.E) D.host.E) _]
    exact normK_mem_AA D
  · rw [hdil]
    funext j k
    unfold redM
    rw [dite_eq_left (by rw [hwZ]; exact Subtype.prop _)]
    have hsub : (⟨frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w j k, by rw [hwZ]; exact Subtype.prop _⟩ :
        Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨toEAf D eQ, hi⟩ * ∑ PP ∈ Q.attach,
        ⟨toEAf D (es PP.1), hk PP.1 PP.2⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E (a PP j k) := Subtype.ext (congrArg (fun M => M j k) hwZ)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsub, RingHom.map_mul, hres PP.1 PP.2, one_mul, map_sum]
    simp_rw [RingHom.map_mul, Formalism.L2.DIV.resS_oToS]
    rw [Finset.sum_eq_single PP]
    · rw [hdel PP.1 PP.2 PP.1 PP.2, if_pos rfl, one_mul, ha]
    · intro b _ hb
      rw [hdel PP.1 PP.2 b.1 b.2, if_neg (fun h => hb (Subtype.ext h)), zero_mul]
    · intro h; exact absurd (Finset.mem_attach _ _) h

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportIdentityOfMemComponentGroupStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTransport_identity_of_mem_componentGroup : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (k : (uAt r v i).Comp) (γ₀ : GL (Fin D.R.r) D.host.E), γ₀ ∈ ((uAt r v i).X k).Γ → IsTransp p r i v ψ 1 k k γ₀ := by
  first | exact @GlobalTheory.ShareOn.isTransp_one_of_mem_Γ | exact GlobalTheory.ShareOn.isTransp_one_of_mem_Γ | (intros; apply GlobalTheory.ShareOn.isTransp_one_of_mem_Γ <;> assumption)
end

