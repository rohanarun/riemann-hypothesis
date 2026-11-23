module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0136
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0237
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0154
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0058
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0116
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0235
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.WeilBound.CoreStatements.ProjectiveValuations.FlagEmbeddingAtlasProjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0025
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.GenericFlagTransitionMatrices
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0140
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0142
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0238
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0146
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyHodgePrimeHeight
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackEx

theorem lie_pack (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel G ξ Li)
    (B : Type) [CommRing B] (act : OAct B G) (ρ₀ : B →+* Module.End Ω Li) (h₀ : M₀.IsActOf act.act ρ₀)
    (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsFractionRing R Ω]
    (x : Spec (CommRingCat.of R) ⟶ X) (hx : spMap (algebraMap R Ω) ≫ x = ξ) :
    ∃ (L : Type) (_ : AddCommGroup L) (_ : Module R L) (M : LieModel G x L) (ρ : B →+* Module.End R L)
      (toLi : L →ₗ[R] Li) (j : Module.Dual R L →ₗ[R] Module.Dual Ω Li),
      Module.Finite R L ∧ Module.Projective R L ∧ M.IsActOf act.act ρ ∧ IsBaseChange Ω toLi ∧
      (∀ v, (M₀.pt (toLi v)).left = spMap (dualMap (algebraMap R Ω)) ≫ (M.pt v).left) ∧
      IsBaseChange Ω j ∧ (∀ u v, j u (toLi v) = algebraMap R Ω (u v)) ∧
      ∀ a v, toLi (ρ a v) = ρ₀ a (toLi v) := by
  obtain ⟨L, i1, i2, M, ρ, toLi, hf, hp, ha, hb, hpt, hρ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackLie.lieModel_along_generic X G Ω ξ Li M₀ B act ρ₀ h₀ O R x hx
  obtain ⟨j, hj, hj'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.dual_baseChange_fractionField Ω O R L Li toLi hb
  exact ⟨L, i1, i2, M, ρ, toLi, j, hf, hp, ha, hb, hpt, hj, hj', hρ⟩

theorem isIso_spMap_fracToField {Ω : Type} [Field Ω] {O : Type} [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω)
    [IsFractionRing R Ω] : IsIso (spMap (fracToField R)) := by
  have hs : Function.Surjective (fracToField R) := fun z => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    refine ⟨algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b, ?_⟩
    have h : ∀ r : R, fracToField R (algebraMap R (FractionRing R) r) = algebraMap R Ω r := fun r =>
      IsFractionRing.lift_algebraMap _ r
    rw [map_div₀, h, h]
  have : IsIso (CommRingCat.ofHom (fracToField R)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 ⟨(fracToField R).injective, hs⟩
  infer_instance

theorem finite_torsT (E : Type) [Field E] [NumberField E] (N n : ℕ) (hn : n ≠ 0) : Finite (TorsT E N n) := by
  have hI : Ideal.span {(n : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  haveI : Finite (𝓞 E ⧸ Ideal.span {(n : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  exact inferInstanceAs (Finite (Fin N → (𝓞 E ⧸ Ideal.span {(n : 𝓞 E)})))

theorem qhom_surjective (E : Type) [Field E] [NumberField E] (N n : ℕ) : Function.Surjective (qhom (E := E) N n) := fun t => by
  choose f hf using fun i => Ideal.Quotient.mk_surjective (Multiplicative.toAdd t i)
  refine ⟨Multiplicative.ofAdd f, ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  exact hf i

theorem qhom_eq_one_iff (E : Type) [Field E] [NumberField E] (N n : ℕ) (y : Fin N → 𝓞 E) :
    qhom (E := E) N n (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = n • y' := by
  have h1 : qhom (E := E) N n (Multiplicative.ofAdd y) = 1 ↔ ∀ i, (n : 𝓞 E) ∣ y i := by
    constructor
    · intro h i
      have h2 := congrFun (congrArg Multiplicative.toAdd h) i
      exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h2)
    · intro h
      apply Multiplicative.toAdd.injective
      funext i
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (h i))
  rw [h1]
  constructor
  · intro h
    choose f hf using h
    exact ⟨f, by funext i; simp [hf i, nsmul_eq_mul]⟩
  · rintro ⟨y', rfl⟩ i
    exact ⟨y' i, by simp [nsmul_eq_mul]⟩

theorem chartPack_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → Nonempty (ChartPack G O c') := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hv hpq p _ hpS hHT hp2 hdisc A _ _ _ m _ hm O _ _ _ _ _ _ _ G c' hc
  obtain ⟨hΩ, hno, hic, hfr, x, hx⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.ChartFacts.chartRing_over_place_facts E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hv p hpS A m hm O c' hc
  haveI := hno; haveI := hic; haveI := hfr; haveI := hΩ
  haveI : CharZero (CR O y c') := ⟨fun a b h => by
    have h2 := congrArg (algebraMap (CR O y c') Ω) h
    simpa using h2⟩
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨L, i1, i2, M, ρ, toLi, j, hfin, hproj, hact, hbc, hpt, hjbc, hj, hρ⟩ :=
    lie_pack 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M (𝓞 E) 𝔐.t.act 𝔐.ρ 𝔐.act O (CR O y c') x hx
  have hR : 0 < 𝔐.R p := by have := 𝔐.R_ge p hpS; omega
  obtain ⟨Γ₁, i₁, ht₁, hp₁⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.torsionAlong_of_fullTorsion 𝔐.X 𝔐.t.G 𝔐.t.semi Ω 𝔐.ξ O (CR O y c') x hx _ G.t₁.pt p (p ^ 𝔐.R p)
    (Fact.out : p.Prime).one_lt.le (dvd_pow_self p hR.ne') (𝔐.tors p hpS) G.t₁.inj G.t₁.onto
  obtain ⟨Γ₂, i₂', ht₂, hp₂⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.torsionAlong_of_fullTorsion 𝔐.X 𝔐.t.G 𝔐.t.semi Ω 𝔐.ξ O (CR O y c') x hx _ G.t₂.pt (p ^ 𝔐.R p) (p ^ 𝔐.R p)
    (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos) dvd_rfl (𝔐.tors p hpS) G.t₂.inj G.t₂.onto
  have hn0 : p ^ 𝔐.R p ≠ 0 := (pow_pos (Fact.out : p.Prime).pos _).ne'
  have hmem : ∀ z : Ω, z ^ (p ^ 𝔐.R p) = 1 → z ∈ CR O y c' := fun z hz => by
    have hi : IsIntegral ℤ z := IsIntegral.of_pow (Nat.pos_of_ne_zero hn0) (hz ▸ isIntegral_one)
    have h := IsIntegralClosure.algebraMap_mk' A z hi
    rw [← h, IsScalarTower.algebraMap_apply A O Ω]
    exact (CR O y c').algebraMap_mem _
  have hz1 : G.ζ ^ (p ^ 𝔐.R p) = 1 := G.ζ_prim.pow_eq_one
  have hz2 : (G.ζ⁻¹) ^ (p ^ 𝔐.R p) = 1 := by rw [inv_pow, hz1, inv_one]
  have hne : G.ζ ≠ 0 := G.ζ_prim.ne_zero hn0
  obtain ⟨ζ, hζ⟩ : ∃ u : (CR O y c')ˣ, ((u : CR O y c') : Ω) = G.ζ :=
    ⟨⟨⟨G.ζ, hmem _ hz1⟩, ⟨G.ζ⁻¹, hmem _ hz2⟩, Subtype.ext (mul_inv_cancel₀ hne), Subtype.ext (inv_mul_cancel₀ hne)⟩, rfl⟩
  haveI hfinT : Finite (TorsT E (D.p + D.q) (p ^ 𝔐.R p)) := finite_torsT E _ _ hn0
  have hsurj : Function.Surjective (qhom (E := E) (D.p + D.q) (p ^ 𝔐.R p)) := qhom_surjective E _ _
  have hker : ∀ y₁, qhom (E := E) (D.p + D.q) (p ^ 𝔐.R p) (Multiplicative.ofAdd y₁) = 1 ↔ ∃ y', y₁ = (p ^ 𝔐.R p) • y' :=
    qhom_eq_one_iff E _ _
  haveI hiso := isIso_spMap_fracToField (CR O y c')
  have hlin : ∀ (a : 𝓞 E) y₁, (Γ₂.pt (qhom _ _ (Multiplicative.ofAdd (a • y₁)))).left ≫ i₂' =
        (Γ₂.pt (qhom _ _ (Multiplicative.ofAdd y₁))).left ≫ i₂' ≫ (𝔐.t.act.act a).left := by
    intro a y₁
    rw [← cancel_epi (spMap (fracToField (CR O y c')))]
    have h1 := hp₂ (qhom _ _ (Multiplicative.ofAdd (a • y₁)))
    have h2 := hp₂ (qhom _ _ (Multiplicative.ofAdd y₁))
    have h3 : (G.t₂.pt (qhom _ _ (Multiplicative.ofAdd (a • y₁)))).left =
        (G.t₂.pt (qhom _ _ (Multiplicative.ofAdd y₁))).left ≫ (𝔐.t.act.act a).left :=
      congrArg (fun f => f.left) (G.t₂.lin a y₁)
    rw [← h1, h3, h2]
    simp only [Category.assoc]
  have hzpow : ζ ^ (p ^ 𝔐.R p) = 1 := by
    apply Units.ext
    apply Subtype.ext
    show (((ζ : CR O y c') ^ (p ^ 𝔐.R p) : CR O y c') : Ω) = 1
    rw [SubmonoidClass.coe_pow, hζ, hz1]
  have hbar : ∀ a : 𝓞 E, RingOfIntegers.mapRingEquiv (HT.cmConj E) a = H.bar a := fun a => by
    ext
    rw [H.bar_eq]
    rfl
  obtain ⟨Dh, hDe, hHT⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.ChartEx.htChartExists (CR O y c') Ω E (HT.cmConj E) p (𝔐.R p) (D.p + D.q) _ Γ₂ 𝔐.X 𝔐.t.G x i₂' ht₂ hsm
    𝔐.t.act.act 𝔐.t.act.hom L M ρ hact (Module.Dual Ω 𝔐.Li) j hjbc (qhom _ _) hsurj hker hlin ζ hzpow G.e G.alt
    (fun a y₁ z => by rw [hbar]; exact G.adj a y₁ z) G.e_surj G.e_inj
  have hform : ∀ (b : 𝓞 E) (w : Module.Dual (CR O y c') L), j (w ∘ₗ ρ b) = j w ∘ₗ 𝔐.ρ b := by
    intro b w
    ext e
    refine hbc.inductionOn e ?_ ?_ ?_
    · intro v
      simp only [LinearMap.comp_apply]
      rw [hj, ← hρ, hj]
      rfl
    · intro s n hn
      simp only [map_smul, hn]
    · intro n₁ n₂ h₁ h₂
      simp only [map_add (f := _), h₁, h₂]
  have hact' : ∀ (a : 𝓞 E) (u : Module.Dual Ω 𝔐.Li), Dh.ρΩ a u = u ∘ₗ 𝔐.ρ (H.bar a) := by
    intro a u
    refine hjbc.inductionOn u ?_ ?_ ?_
    · intro w
      rw [hHT.2.1, hbar, hform]
    · intro s n hn
      rw [map_smul, hn]
      rfl
    · intro n₁ n₂ h₁ h₂
      rw [map_add (f := _), h₁, h₂]
      rfl
  exact ⟨{ x := x, x_gen := hx, L := L, fin := hfin, proj := hproj, M := M, ρ := ρ, act := hact, toLi := toLi, toLi_bc := hbc,
           toLi_pt := hpt, j := j, j_bc := hjbc, j_apply := hj, Γ₁ := Γ₁, i₁ := i₁, tors₁ := ht₁, pts₁ := hp₁,
           Γ₂ := Γ₂, i₂ := i₂', tors₂ := ht₂, pts₂ := hp₂, ζ := ζ, ζ_eq := hζ, Dh := Dh, Dh_e := hDe, Dh_act := hact', isHT := hHT }⟩

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackEx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChowLemmaQuasiProjective
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_lift_of_isDominant {D Y V A : Scheme.{0}} [IsReduced Y] (σ : D ⟶ Y) [IsDominant σ]
    (r : Y ⟶ V) (k : A ⟶ V) [IsClosedImmersion k] (a : D ⟶ A) (h : σ ≫ r = a ≫ k) :
    ∃ φ : Y ⟶ A, φ ≫ k = r := by
  have hl : pullback.lift σ a h ≫ pullback.fst r k = σ := pullback.lift_fst _ _ _
  have : IsDominant (pullback.lift σ a h ≫ pullback.fst r k) := by rw [hl]; infer_instance
  have : IsDominant (pullback.fst r k) := IsDominant.of_comp (pullback.lift σ a h) _
  have : Surjective (pullback.fst r k) :=
    surjective_of_isDominant_of_isClosed_range _ (pullback.fst r k).isClosedEmbedding.isClosed_range
  have : IsIso (pullback.fst r k) := isIso_of_isClosedImmersion_of_surjective _
  exact ⟨inv (pullback.fst r k) ≫ pullback.snd r k, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem isClosedImmersion_morphismRestrict {S X B X' T D : Scheme.{0}} (f : X ⟶ S) [IsSeparated f]
    (u : B ⟶ S) [IsReduced X'] (π : X' ⟶ X) (b : X' ⟶ B) (hπb : π ≫ f = b ≫ u)
    [IsClosedImmersion (pullback.lift π b hπb)] (A : X.Opens) (O : B.Opens) (τ : T ⟶ S)
    (ρ : O.toScheme ⟶ T) (hρ : ρ ≫ τ = O.ι ≫ u) (k : A.toScheme ⟶ T) [IsClosedImmersion k]
    (hk : k ≫ τ = A.ι ≫ f) (σ : D ⟶ (b ⁻¹ᵁ O).toScheme) [IsDominant σ] (a : D ⟶ A.toScheme)
    (h₁ : σ ≫ b ∣_ O ≫ ρ = a ≫ k) (h₂ : a ≫ A.ι = σ ≫ (b ⁻¹ᵁ O).ι ≫ π) :
    IsClosedImmersion (b ∣_ O) := by
  obtain ⟨φ, hφ⟩ := exists_lift_of_isDominant σ (b ∣_ O ≫ ρ) k a h₁
  have hσφ : σ ≫ φ = a := by
    rw [← cancel_mono k, Category.assoc, hφ, h₁]
  have hφι : φ ≫ A.ι = (b ⁻¹ᵁ O).ι ≫ π := by
    refine ext_of_isDominant_of_isSeparated f ?_ σ ?_
    · rw [Category.assoc, Category.assoc, ← hk, reassoc_of% hφ, hρ, morphismRestrict_ι_assoc,
        hπb]
    · rw [reassoc_of% hσφ, h₂]
  have hc : (pullback.snd ρ k ≫ A.ι) ≫ f = (pullback.fst ρ k ≫ O.ι) ≫ u := by
    rw [Category.assoc, Category.assoc, ← hk, ← hρ, pullback.condition_assoc]
  let c : pullback ρ k ⟶ pullback f u := pullback.lift _ _ hc
  have c₁ : c ≫ pullback.fst f u = pullback.snd ρ k ≫ A.ι := pullback.lift_fst _ _ _
  have c₂ : c ≫ pullback.snd f u = pullback.fst ρ k ≫ O.ι := pullback.lift_snd _ _ _
  have : Mono c := by
    have : Mono (c ≫ pullback.snd f u) := by rw [c₂]; infer_instance
    exact mono_of_mono c (pullback.snd f u)
  let m : (b ⁻¹ᵁ O).toScheme ⟶ pullback ρ k := pullback.lift (b ∣_ O) φ hφ.symm
  have m₁ : m ≫ pullback.fst ρ k = b ∣_ O := pullback.lift_fst _ _ _
  have m₂ : m ≫ pullback.snd ρ k = φ := pullback.lift_snd _ _ _
  have hw : (b ⁻¹ᵁ O).ι ≫ pullback.lift π b hπb = m ≫ c := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, c₁, reassoc_of% m₂, hφι]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, c₂, reassoc_of% m₁,
        morphismRestrict_ι]
  have sq : IsPullback (b ⁻¹ᵁ O).ι m (pullback.lift π b hπb) c := by
    have hr : ∀ {Z : Scheme.{0}} (x : Z ⟶ X') (y : Z ⟶ pullback ρ k),
        x ≫ pullback.lift π b hπb = y ≫ c → Set.range x ⊆ Set.range (b ⁻¹ᵁ O).ι := by
      intro Z x y e
      have e' : x ≫ b = (y ≫ pullback.fst ρ k) ≫ O.ι := by
        have := congr($e ≫ pullback.snd f u)
        simpa only [Category.assoc, pullback.lift_snd, c₂] using this
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      change (x ≫ b) z ∈ O
      rw [e']
      exact ((y ≫ pullback.fst ρ k) z).2
    refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw
      (fun s ↦ IsOpenImmersion.lift (b ⁻¹ᵁ O).ι s.fst (hr _ _ s.condition)) (fun s ↦ ?_)
      (fun s ↦ ?_) (fun s n h₃ _ ↦ ?_)⟩⟩
    · exact IsOpenImmersion.lift_fac _ _ _
    · rw [← cancel_mono c, Category.assoc, ← hw, IsOpenImmersion.lift_fac_assoc, s.condition]
    · rw [← cancel_mono (b ⁻¹ᵁ O).ι, IsOpenImmersion.lift_fac, h₃]
  have : IsClosedImmersion m := MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq ‹_›
  rw [← m₁]
  infer_instance

theorem exists_isProper_surjective_isQProjOver : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), IsSeparated p → LocallyOfFiniteType p → QuasiCompact p → ∃ (X' : Scheme.{0}) (π : X' ⟶ X), IsProper π ∧ Surjective π ∧ IsQProjOver (π ≫ p) := by
  intro R _ _ X _ f _ _ _
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hA : ∀ y : X, ∃ A : X.Opens, IsAffineOpen A ∧ y ∈ A := fun y ↦ by
    obtain ⟨A, h₁, h₂, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
    exact ⟨A, h₁, h₂⟩
  choose A₀ hA₀ hyA using hA
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ (A₀ y : Set X))
    (fun y ↦ (A₀ y).isOpen) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyA y⟩)
  let A : T → X.Opens := fun i ↦ A₀ i
  have hcov : ∀ y : X, ∃ i : T, y ∈ A i := fun y ↦ by
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
    exact ⟨⟨i, hi⟩, h⟩
  have hP := fun i : T ↦ (have : IsAffine (A i).toScheme := hA₀ i
    (isAmpleLB_of_isAffine (LB.isLB_triv (A i).toScheme)).isQProjOver ((A i).ι ≫ f))
  choose N j hj _ hjt using hP
  let U : X.Opens := Finset.univ.inf A
  have hUA : ∀ i, U ≤ A i := fun i ↦ Finset.inf_le (Finset.mem_univ i)
  have hU : genericPoint X ∈ U := by
    have : ∀ i, genericPoint X ∈ A i := fun i ↦
      ((genericPoint_spec X).mem_open_set_iff (A i).isOpen).2 ⟨i, trivial, hyA i⟩
    refine Finset.inf_induction (p := fun V : X.Opens ↦ genericPoint X ∈ V) trivial
      (fun _ h _ h' ↦ ⟨h, h'⟩) fun i _ ↦ this i
  have hps : ∀ n, IsProjOver (PSpace.str R n) := fun n ↦ ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩
  obtain ⟨P, s, p, hP, hp, hu⟩ := ProjFinProd.exists_isProjOver_finite_prod R T (Sp R) (𝟙 _)
    (fun i ↦ PSpace R (N i)) (fun i ↦ PSpace.str R (N i))
    ((isAmpleLB_of_isAffine (LB.isLB_triv (Sp R))).isProjOver (𝟙 _)) (fun i ↦ hps _)
  rw [Category.comp_id] at hP hp
  obtain ⟨h, ⟨hs, hh⟩, -⟩ := hu U.toScheme (U.ι ≫ f) (fun i ↦ X.homOfLE (hUA i) ≫ j i)
    (fun i ↦ by rw [Category.assoc, hjt, X.homOfLE_ι_assoc, Category.comp_id])
  have : IsProper s := ((isProjOver_iff_isProper_and_exists_isAmpleLB s).1 hP).1
  let g : U.toScheme ⟶ pullback f s := pullback.lift U.ι h hs.symm
  have g₁ : g ≫ pullback.fst f s = U.ι := pullback.lift_fst _ _ _
  have g₂ : g ≫ pullback.snd f s = h := pullback.lift_snd _ _ _
  have : IsImmersion (g ≫ pullback.fst f s) := by rw [g₁]; infer_instance
  have : IsImmersion g := IsImmersion.of_comp g (pullback.fst f s)
  have : QuasiCompact (g ≫ pullback.fst f s) := by rw [g₁]; infer_instance
  have : QuasiCompact g := QuasiCompact.of_comp g (pullback.fst f s)
  have := isSchemeTheoreticallyDominant_toImage g
  have : IsReduced g.image := IsSchemeTheoreticallyDominant.isReduced g.toImage
  let π : g.image ⟶ X := g.imageι ≫ pullback.fst f s
  let q : g.image ⟶ P := g.imageι ≫ pullback.snd f s
  have hπ : g.toImage ≫ π = U.ι := by rw [g.toImage_imageι_assoc, g₁]
  have hq : g.toImage ≫ q = h := by rw [g.toImage_imageι_assoc, g₂]
  have hπq : π ≫ f = q ≫ s := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have key : ∀ i, (π ⁻¹ᵁ A i).ι ≫ q ≫ p i = π ∣_ A i ≫ j i := by
    intro i
    obtain ⟨σ, _, e₁, e₂⟩ := GlobalTheory.ChowLemma.exists_dominant_lift π (hUA i) g.toImage hπ
    have := isProper_str R (N i)
    refine ext_of_isDominant_of_isSeparated (PSpace.str R (N i)) ?_ σ ?_
    · rw [Category.assoc, Category.assoc, hp, ← hπq, Category.assoc (π ∣_ A i), hjt,
        morphismRestrict_ι_assoc]
    · rw [reassoc_of% e₁, reassoc_of% hq, hh, reassoc_of% e₂]
  have : ∀ i, IsImmersion (j i) := hj
  let V : ∀ i, (PSpace R (N i)).Opens := fun i ↦ (j i).coborderRange
  have hV : ∀ i (x : g.image), π x ∈ A i → (q ≫ p i) x ∈ V i := by
    intro i x hx
    have e : ((π ⁻¹ᵁ A i).ι ≫ q ≫ p i) ⟨x, hx⟩ = (π ∣_ A i ≫ j i) ⟨x, hx⟩ := by rw [key i]
    change ((π ⁻¹ᵁ A i).ι ≫ q ≫ p i) ⟨x, hx⟩ ∈ V i
    rw [e]
    exact subset_coborder ⟨_, rfl⟩
  let W : P.Opens := ⨆ i, p i ⁻¹ᵁ V i
  have hW : Set.range q ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨i, hi⟩ := hcov (π x)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hV i x hi⟩
  let q' : g.image ⟶ W.toScheme := IsOpenImmersion.lift W.ι q hW
  have hq' : q' ≫ W.ι = q := IsOpenImmersion.lift_fac _ _ _
  have hπq' : π ≫ f = q' ≫ W.ι ≫ s := by rw [reassoc_of% hq', hπq]
  have hcl : IsClosedImmersion (pullback.lift π q' hπq') := by
    let e : pullback f (W.ι ≫ s) ⟶ pullback f s :=
      pullback.lift (pullback.fst f (W.ι ≫ s)) (pullback.snd f (W.ι ≫ s) ≫ W.ι)
        (by rw [pullback.condition, Category.assoc])
    have e₁ : e ≫ pullback.fst f s = pullback.fst f (W.ι ≫ s) := pullback.lift_fst _ _ _
    have e₂ : e ≫ pullback.snd f s = pullback.snd f (W.ι ≫ s) ≫ W.ι := pullback.lift_snd _ _ _
    have : Mono e := by
      refine ⟨fun a b hab ↦ pullback.hom_ext ?_ ?_⟩
      · simpa only [Category.assoc, e₁] using congr($hab ≫ pullback.fst f s)
      · rw [← cancel_mono W.ι]
        simpa only [Category.assoc, e₂] using congr($hab ≫ pullback.snd f s)
    have he : pullback.lift π q' hπq' ≫ e = g.imageι := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, e₁, pullback.lift_fst]
      · rw [Category.assoc, e₂, pullback.lift_snd_assoc, hq']
    have : IsClosedImmersion (pullback.lift π q' hπq' ≫ e) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp _ e
  let O : T → W.toScheme.Opens := fun i ↦ (W.ι ≫ p i) ⁻¹ᵁ V i
  have hO : iSup O = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 y.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  have hloc : ∀ i, IsClosedImmersion (q' ∣_ O i) := by
    intro i
    have hr : Set.range g.toImage ⊆ Set.range (q' ⁻¹ᵁ O i).ι := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hx : (g.toImage ≫ π) x ∈ A i := by
        rw [hπ]
        exact hUA i x.2
      change (q' ≫ W.ι ≫ p i) (g.toImage x) ∈ V i
      rw [reassoc_of% hq']
      exact hV i _ hx
    have hσ := IsOpenImmersion.lift_fac (q' ⁻¹ᵁ O i).ι g.toImage hr
    have : IsDominant (IsOpenImmersion.lift (q' ⁻¹ᵁ O i).ι g.toImage hr ≫ (q' ⁻¹ᵁ O i).ι) := by
      rw [hσ]; infer_instance
    have : IsDominant (IsOpenImmersion.lift (q' ⁻¹ᵁ O i).ι g.toImage hr) :=
      IsDominant.of_comp_of_isOpenImmersion _ (q' ⁻¹ᵁ O i).ι
    refine isClosedImmersion_morphismRestrict f (W.ι ≫ s) π q' hπq' (A i) (O i)
      ((V i).ι ≫ PSpace.str R (N i)) ((W.ι ≫ p i) ∣_ V i) ?_ (j i).liftCoborder ?_
      (IsOpenImmersion.lift (q' ⁻¹ᵁ O i).ι g.toImage hr) (X.homOfLE (hUA i)) ?_ ?_
    · rw [morphismRestrict_ι_assoc, Category.assoc, hp]
    · rw [Scheme.Hom.liftCoborder_ι_assoc, hjt]
    · rw [← cancel_mono (V i).ι, Category.assoc, Category.assoc, Category.assoc,
        morphismRestrict_ι, Scheme.Hom.liftCoborder_ι, morphismRestrict_ι_assoc, reassoc_of% hσ,
        reassoc_of% hq', reassoc_of% hq, hh]
    · rw [X.homOfLE_ι, reassoc_of% hσ, hπ]
  have : IsClosedImmersion q' :=
    IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) O hO hloc
  have : IsImmersion q := by rw [← hq']; infer_instance
  have : IsProper π := by infer_instance
  have : IsDominant U.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact U.isOpen.dense ⟨_, hU⟩⟩
  have : IsDominant (g.toImage ≫ π) := by rw [hπ]; infer_instance
  have : IsDominant π := IsDominant.of_comp g.toImage π
  have : QuasiCompact (q ≫ s) := by rw [← hπq]; infer_instance
  have : QuasiCompact q := QuasiCompact.of_comp q s
  obtain ⟨n, i₀, hi₀, e₀⟩ := hP
  exact ⟨g.image, π, inferInstance,
    surjective_of_isDominant_of_isClosed_range π π.isClosedMap.isClosed_range, n, q ≫ i₀,
    inferInstance, inferInstance, by rw [Category.assoc, e₀, hπq]⟩

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagAtlasProjectiveEmbedding
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.CompanionTheory.FlagMod

theorem cells_smooth_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : GlobalTheory.FlagMod.LowRank.Proj (RingHom.id c.F)) (A : GlobalTheory.FlagMod.FieldFlag.Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : GlobalTheory.FlagEmb.En Dw.mult, Z ⟶ PSpace c.F (GlobalTheory.FlagEmb.plN A.N en.1)) (κ : ∀ b, GlobalTheory.FlagEmb.Pm Dw.mult → (Sp (GlobalTheory.FlagEmb.CR Dw.mult (A.V b)) ⟶ Z)), (∀ b w, IsOpenImmersion (κ b w)) → GlobalTheory.FlagMod.FieldFlag.Cells A π g κ → SmoothOfRelativeDimension Dw.dim Y.s → ∃ d : ℕ, SmoothOfRelativeDimension d (π ≫ Y.s) ∧ IsProjOver (π ≫ Y.s) :=
  @DifferentiableLines.flag_embedding_atlas_projective

end GlobalTheory.CompanionTheory.FlagMod
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTriangularRelay
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.generic_flag_triangular_relay : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (E₀ F : Type) [AddCommGroup E₀] [Module K E₀] [AddCommGroup F] [Module L F] (j : E₀ →+ F) (S : Type) [Finite S] (r : S → ℕ) (V : S → Submodule K E₀) (b : ∀ s, Fin (r s) → F) (d : ℕ), GlobalTheory.CompanionTheory.Ar.IsGenericFlag (Ω := K) (Ω' := L) j V b d → ∀ (e : ∀ s, Fin (r s) → E₀), (∀ s l, e s l ∈ V s) → (∀ s, LinearIndependent L fun l => j (e s l)) → ∃ v Tm : ∀ s, Matrix (Fin (r s)) (Fin (r s)) L, (∀ s k, v s k k = 1) ∧ (∀ s l k, l < k → v s l k = 0) ∧ AlgebraicIndependent K (fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) ∧ Module.finrank (IntermediateField.adjoin K (Set.range fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2)) L = d ∧ (∀ s i, b s i = ∑ m, Tm s i m • ∑ l, v s l m • j (e s l)) ∧ (∀ s i m, i < m → Tm s i m = 0) ∧ ∀ s i, Tm s i i ≠ 0 := by
  first | exact @ModelDimension.generic_flag_transition_matrices | exact ModelDimension.generic_flag_transition_matrices
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LemmaBTHolds
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT

open CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

theorem lemmaBT_holds : LemmaBT := by
  unfold GlobalTheory.CompanionTheory.Ar.BT.LemmaBT
  intro R _ _ _ _ T _ _ Γ S G _ _ x N i hi hG
  refine ⟨_root_.PositivityTheory.UnitarySelfGeneration.bt_hopf R T Γ, ?_,
    fun hN => _root_.GlobalTheory.CompanionTheory.Ar.BT.EtaleTop.btOrder_top_eq_top_of_etale R T Γ
      (_root_.GlobalTheory.CompanionTheory.Ar.BT.torsion_etale_of_isUnit R T Γ S G x N i hi hG hN), ?_, ?_,
    fun L _ _ M => _root_.GlobalTheory.CompanionTheory.Ar.BT.omega_isDerAtOne R T Γ S G x N i hi hG L M⟩
  · obtain ⟨j, hj, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.exists_unique_emb_btOrder_top R T Γ
    obtain ⟨hoi, htr⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.isOpenImmersion_emb_and_translatesCover R T Γ j hj
    refine ⟨j, hj, hoi, htr, fun hP => ?_⟩
    exact _root_.GlobalTheory.CompanionTheory.Ar.BT.FiniteIso.isIso_of_finite R T Γ j hj
      (_root_.GlobalTheory.CompanionTheory.Ar.BT.Tors.nTorsion_finite_of_isProper R T Γ S G x N i hi hP)
  · intro a _ α hα f hf
    obtain ⟨a', _, ha'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.TorsEnd.endomorphism_restricts_to_torsion R T Γ S G x N i hi a
    refine GlobalTheory.T.btOrder_comap_hom R T Γ T Γ a' α (fun t => ?_) f hf
    obtain ⟨_, _, hcancel, _⟩ := hi
    apply hcancel
    rw [Over.comp_left, Category.assoc, ha', hα t]
  · intro R' _ _ _ Γ' F hF
    obtain ⟨hd, hΓ'⟩ :=
      _root_.GlobalTheory.CompanionTheory.Ar.BT.btOrder_baseChange R T Γ R' Γ' F hF
    obtain ⟨-, e, he⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.ext_tensor_base_change R T R' _
      (_root_.PositivityTheory.UnitarySelfGeneration.bt_hopf R T Γ) hd
    rw [hΓ']
    exact ⟨e, he⟩

end GlobalTheory.CompanionTheory.Ar.BT
end
end

