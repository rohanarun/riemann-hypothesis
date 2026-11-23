module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2255
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2346
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedSectionExponentShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHomogeneousSecZGenFix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2349
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSplitClosedFibreRationalTwo
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem splitClosed_of_isGrpPullback_id {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' G₁ : Over (Sp R)}
    [GrpObj G'] [GrpObj G₁] {φ : G₁.left ⟶ G'.left} (hφ : IsGrpPullback G₁ G' (𝟙 _) φ) (h : SplitClosed G') :
    SplitClosed G₁ := by
  obtain ⟨X, _, _, _, ⟨Q⟩⟩ := h
  let t := thick R (maximalIdeal R) 0
  have h2 := (isGrpPullback_pullback G₁ t).comp hφ
  have h3 := isGrpPullback_pullback G' t
  let ψ : (thickObj R (maximalIdeal R) 0 G₁).left ⟶ (thickObj R (maximalIdeal R) 0 G').left :=
    pullback.lift (pullback.fst G₁.hom t ≫ φ) (pullback.snd G₁.hom t) (by
      rw [Category.assoc, hφ.1.w, Category.comp_id, pullback.condition])
  have hc : IsGrpPullback (thickObj R (maximalIdeal R) 0 G₁) (thickObj R (maximalIdeal R) 0 G') (𝟙 _) ψ :=
    IsGrpPullback.cancel h3 (h2.congr (by rw [Category.comp_id, Category.id_comp]) (pullback.lift_fst _ _ _).symm)
      (by
        rw [Category.comp_id]
        exact pullback.lift_snd _ _ _)
  obtain ⟨Q', -⟩ := GlobalTheory.UU.exists_tq_baseChange _ _ (𝟙 _) X _ _ ψ hc Q
  exact ⟨X, inferInstance, inferInstance, inferInstance, ⟨Q'⟩⟩

noncomputable section

theorem exists_finExt_splitClosed_twoTorsRat : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R'), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁] (β : G₁.left ⟶ G.left), IsGrpPullback G₁ G (spMap ρ) β → SplitClosed G₁ ∧ TwoTorsRat G₁ := by
  intro R _ _ _ hR G _ _ hG A gen hgen
  obtain ⟨K', _, _, hK'fin, H⟩ := _root_.GlobalTheory.TwoTorsPull.twoTorsRat_of_pullback R G A gen hgen
  haveI : IsDiscreteValuationRing R := hR.1
  haveI : IsAdicComplete (maximalIdeal R) R := hR.2.1
  haveI : CharZero R := hR.2.2
  haveI : CharZero (FractionRing R) := (algebraMap R (FractionRing R)).charZero_iff (IsFractionRing.injective R _) |>.1 inferInstance
  obtain ⟨W, _, _, _, hWc, _, _, _, hc, hWfin, hWinj, hWloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension R (FractionRing R) K'
  haveI : CharZero W := (algebraMap R W).charZero_iff hWinj |>.1 inferInstance
  have hWd : GlobalTheory.LN.CDvr W := ⟨inferInstance, hWc, inferInstance⟩
  have hGW : IsSemiAbelian ((Over.pullback (spMap (algebraMap R W))).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨R₂, _, _, _, ρ₂, G', _, _, β', X, _, _, _, hfin₂, hpb', ⟨Q⟩⟩ :=
    GlobalTheory.Mum.exists_finExt_tq_closedFibre W ⟨⟨inferInstance, inferInstance, inferInstance, hWc⟩, inferInstance⟩ _ hGW
  have hsp : spMap (ρ₂.comp (algebraMap R W)) = spMap ρ₂ ≫ spMap (algebraMap R W) := by
    rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ₂.comp (algebraMap R W), _root_.GlobalTheory.Mum.cDvr_of_finExt W R₂ ρ₂ hWd hfin₂,
    ⟨hfin₂.1, hfin₂.2.1.comp hWinj, hfin₂.2.2.comp (RingHom.finite_algebraMap.2 hWfin)⟩, ?_⟩
  intro G₁ _ _ β hβ
  have hGWp := isGrpPullback_pullback G (spMap (algebraMap R W))
  let gam : G₁.left ⟶ ((Over.pullback (spMap (algebraMap R W))).obj G).left :=
    pullback.lift β (G₁.hom ≫ spMap ρ₂) (by rw [hβ.1.w, hsp, Category.assoc])
  have hgam : IsGrpPullback G₁ _ (spMap ρ₂) gam :=
    IsGrpPullback.cancel hGWp (hβ.congr hsp (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  obtain ⟨e, he, -⟩ := grpPullback_iso hgam hpb'
  haveI := he
  have hsplit' : SplitClosed G' := ⟨X, inferInstance, inferInstance, inferInstance, ⟨Q⟩⟩
  refine ⟨splitClosed_of_isGrpPullback_id (isGrpPullback_of_iso e) hsplit', ?_⟩
  · let j : FractionRing W →+* FractionRing R₂ :=
      IsLocalization.map (M := nonZeroDivisors W) (T := nonZeroDivisors R₂) (FractionRing R₂) ρ₂
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective ρ₂ hfin₂.2.1)
    let i : K' →+* FractionRing R₂ := j.comp (FractionRing.algEquiv W K').symm.toRingHom
    refine H R₂ (ρ₂.comp (algebraMap R W)) i (fun r => ?_) G₁ β hβ
    have h1 := congrArg (fun f => f r) hc
    simp only [RingHom.comp_apply] at h1
    rw [← h1]
    show j ((FractionRing.algEquiv W K').symm (algebraMap W K' (algebraMap R W r))) = _
    rw [AlgEquiv.commutes]
    exact IsLocalization.map_eq _ _

end

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFlatCoverMSqTorsionSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.TorsionList

theorem pow_exp (n k : ℕ) (c : Multiplicative (Fin k → ZMod n)) : c ^ n = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap]

theorem pushHom_bij {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Bijective (pushHom h T) := by
  refine ⟨fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) ?_), fun y => ?_⟩
  · exact (Over.w x).trans (Over.w y).symm
  · exact ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem spMap_comp_assoc {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D] {X : Scheme.{0}}
    (f : A →+* B) (g : B →+* C) (h : C →+* D) (y : Sp A ⟶ X) :
    spMap (h.comp g) ≫ spMap f ≫ y = spMap h ≫ spMap (g.comp f) ≫ y := by
  simp only [spMap_comp, Category.assoc]

abbrev lft {S X : Scheme.{0}} {G : Over S} {a : X ⟶ S} (p : Over.mk a ⟶ G) : X ⟶ G.left := p.left

theorem pow_lft_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x : Over.mk a ⟶ G) (y : Over.mk b ⟶ G) (hx : lft x = lft y) (n : ℕ) : lft (x ^ n) = lft (y ^ n) := by
  subst h
  rw [Over.OverMorphism.ext hx]

theorem one_lft_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b) :
    lft (1 : Over.mk a ⟶ G) = lft (1 : Over.mk b ⟶ G) := by
  subst h
  rfl

theorem transport {S X : Scheme.{0}} {G : Over S} {a b : X ⟶ S} (h : a = b) (p : Over.mk b ⟶ G) :
    ∃ p' : Over.mk a ⟶ G, lft p' = lft p := by
  subst h
  exact ⟨p, rfl⟩

theorem lft_pushHom {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) {X : Scheme.{0}} (t : X ⟶ S') (y : Over.mk t ⟶ A') :
    lft (pushHom h (Over.mk t) y) = y.left ≫ φ := rfl

theorem toUnit_mk_left {X Y : Scheme.{0}} (f : Y ⟶ X) : (toUnit (Over.mk f)).left = f :=
  (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk f)))

theorem toUnit_left {X : Scheme.{0}} (T : Over X) : (toUnit T).left = T.hom :=
  (Category.comp_id _).symm.trans (Over.w (toUnit T))

theorem exists_cover_torsion_list : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (g m N : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (q : Fin N → (Over.mk (spMap (algebraMap R R₁) ≫ x) ⟶ G)), Module.Finite R R₁ ∧ Module.FaithfullyFlat R R₁ ∧ (∀ a, q a ^ (m ^ 2) = 1) ∧ ∀ (K : Type) [Field K] (i₁ : R₁ →+* K) (pt : Fin N → (Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G)), (∀ a, (pt a).left = spMap i₁ ≫ (q a).left) → Function.Injective pt ∧ ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (i' : K →+* K') (p : Over.mk (spMap i' ≫ spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G), p ^ (m ^ 2) = 1 → ∃ a, p.left = spMap i' ≫ (pt a).left := by
  intro S G _ _ L g m N R _ _ x hm hmu hN hP
  obtain ⟨P, α, hg, hp, -⟩ := hP
  haveI := P.isAb.comm
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
  haveI : NeZero (m ^ 2) := ⟨pow_ne_zero _ hm0⟩
  have hsm : SmoothOfRelativeDimension g P.A.hom := hg ▸ P.smoothDim
  have hu : IsUnit (((m ^ 2 : ℕ)) : R) := by rw [Nat.cast_pow]; exact hmu.pow 2
  obtain ⟨R₁, _, _, ⟨hfin, -, hff⟩, H⟩ :=
    GlobalTheory.TorsionCover.exists_torsion_basis_cover R P.A g (m ^ 2) P.isAb hsm hu
  let b := spMap (algebraMap R R₁)
  let A₁ := (Over.pullback b).obj P.A
  haveI : IsCommMonObj A₁ := Functor.isCommMonObj_obj
  have h₁ := isGrpPullback_pullback P.A b
  obtain ⟨ψ, hψ⟩ := H A₁ _ h₁
  have hc := h₁.comp hp
  have hcard : Fintype.card (Multiplicative (Fin (2 * g) → ZMod (m ^ 2))) = N := by
    rw [hN]
    simp [Fintype.card_fun, ZMod.card, ← pow_mul]
    ring_nf
  let e := (Fintype.equivFinOfCardEq hcard).symm
  let U : Over.mk (b ≫ x) ⟶ Over.mk ((𝟙_ (Over (Sp R₁))).hom ≫ b ≫ x) := Over.homMk (𝟙 _) (by simp)
  let Q := (preHom (G := G) U).comp ((pushHom hc (𝟙_ (Over (Sp R₁)))).comp ψ)
  have hQ : ∀ c, (Q c).left = (ψ c).left ≫ pullback.fst P.A.hom b ≫ α := fun c => by
    simp [Q, U, pushHom, pushPt, preHom]
  refine ⟨R₁, inferInstance, inferInstance, fun a => Q (e a), hfin, hff, fun a => by
    rw [← map_pow, pow_exp, map_one], ?_⟩
  intro K _ i₁ pt hpt
  have key : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R₁) c d,
      t ≫ (Q c).left = t ≫ (Q d).left → c = d := by
    intro k _ _ t c d h
    have hinj : Function.Injective ((preHom (G := A₁) (toUnit (Over.mk t))).comp ψ) := by
      rw [injective_iff_map_eq_one]
      exact fun c hc => (hψ k t).2 c hc
    apply hinj
    apply Over.OverMorphism.ext
    show (toUnit (Over.mk t) ≫ ψ c).left = (toUnit (Over.mk t) ≫ ψ d).left
    rw [Over.comp_left, Over.comp_left, toUnit_left]
    apply hc.1.hom_ext
    · rw [hQ, hQ] at h
      simpa [Category.assoc] using h
    · have e1 := Over.w (ψ c)
      have e2 := Over.w (ψ d)
      simp only [Category.assoc]
      erw [e1, e2]
  refine ⟨fun a a' h => ?_, ?_⟩
  · have h' := congrArg (fun z => z.left) h
    simp only [hpt] at h'
    let k := AlgebraicClosure K
    have := key k (spMap ((algebraMap K k).comp i₁)) (e a) (e a') (by
      rw [spMap_comp, Category.assoc, Category.assoc]; exact congrArg (spMap (algebraMap K k) ≫ ·) h')
    exact e.injective this
  · intro K' _ _ i' p hp2
    have ht : spMap i' ≫ spMap (i₁.comp (algebraMap R R₁)) ≫ x = spMap (i'.comp i₁) ≫ b ≫ x :=
      (spMap_comp_assoc (algebraMap R R₁) i₁ i' x).symm
    obtain ⟨p', hp'⟩ := transport ht.symm p
    obtain ⟨p₁, hp₁⟩ := (pushHom_bij hc (Over.mk (spMap (i'.comp i₁)))).2 p'
    have hk : p₁ ^ (m ^ 2) = 1 := by
      apply (pushHom_bij hc _).1
      rw [map_pow, hp₁, map_one]
      apply Over.OverMorphism.ext
      change lft _ = lft _
      rw [pow_lft_congr ht.symm p' p hp', hp2]
      exact one_lft_congr ht
    obtain ⟨c, rfl⟩ := ((hψ K' _).1 p₁).1 hk
    refine ⟨e.symm c, ?_⟩
    rw [hpt]
    simp only [Equiv.apply_symm_apply]
    change lft p = _
    have h2 := congrArg lft hp₁
    rw [← hp', ← h2, lft_pushHom, hQ, Over.comp_left, toUnit_mk_left, spMap_comp]
    simp only [Category.assoc]

end GlobalTheory.UMin.TorsionList
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetPowSmulMem
section
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FinitePowerAnnihilation

theorem exists_finset_pow_smul_mem {R A Rf Af : Type} [CommRing R] [CommRing A] [CommRing Rf] [CommRing Af]
    [IsNoetherianRing R] [Algebra R A] [Algebra R Rf] (f : R) [IsLocalization.Away f Rf]
    (ψ : Rf →+* Af) (ρ : A →+* Af) (hc : ∀ a, ρ (algebraMap R A a) = ψ (algebraMap R Rf a))
    (hk : ∀ x, ρ x = 0 → ∃ n : ℕ, f ^ n • x = 0) (T : Set Af) (hT : T.Finite)
    (hI : ∀ y ∈ T, ψ.IsIntegralElem y) (M : Set A)
    (hM : ∀ x ∈ M, ρ x ∈ Subring.closure (Set.range ψ ∪ T)) :
    ∃ s : Finset A, (s : Set A) ⊆ M ∧ ∀ x ∈ M, ∃ n : ℕ, f ^ n • x ∈ Submodule.span R (s : Set A) := by
  classical
  letI : Algebra Rf Af := ψ.toAlgebra
  haveI : IsNoetherianRing Rf := IsLocalization.isNoetherianRing (Submonoid.powers f) Rf inferInstance
  have hfg : (Algebra.adjoin Rf T).toSubmodule.FG := fg_adjoin_of_finite hT hI
  have hle : Submodule.span Rf (ρ '' M) ≤ (Algebra.adjoin Rf T).toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h := hM x hx
    have : Subring.closure (Set.range ψ ∪ T) ≤ (Algebra.adjoin Rf T).toSubring := by
      rw [Subring.closure_le]
      rintro y (⟨a, rfl⟩ | hy)
      · exact (Algebra.adjoin Rf T).algebraMap_mem a
      · exact Algebra.subset_adjoin hy
    exact this h
  have hfg2 : (Submodule.span Rf (ρ '' M)).FG := hfg.of_le hle
  obtain ⟨u, hu, hsp⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg2
  obtain ⟨s, hs, hsu⟩ := Finset.subset_set_image_iff.1 hu
  refine ⟨s, hs, fun x hx => ?_⟩
  have hx1 : ρ x ∈ Submodule.span Rf (u : Set Af) := hsp ▸ Submodule.subset_span ⟨x, hx, rfl⟩
  have key : ∀ z ∈ Submodule.span Rf (u : Set Af), ∃ n : ℕ, ∃ w ∈ Submodule.span R (s : Set A),
      ρ w = ρ (algebraMap R A f) ^ n * z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rw [← hsu, Finset.coe_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨0, w, Submodule.subset_span hw, by simp⟩
    | zero => exact ⟨0, 0, Submodule.zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨n, w, hw, e⟩ := ha
      obtain ⟨m, v, hv, e'⟩ := hb
      refine ⟨n + m, f ^ m • w + f ^ n • v,
        Submodule.add_mem _ (Submodule.smul_mem _ _ hw) (Submodule.smul_mem _ _ hv), ?_⟩
      simp only [Algebra.smul_def, map_add (f := _), map_mul, map_pow, e, e']
      ring
    | smul c a _ ha =>
      obtain ⟨n, w, hw, e⟩ := ha
      obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers f) c
      refine ⟨n + k, b • w, Submodule.smul_mem _ _ hw, ?_⟩
      have hb' : ψ c * ρ (algebraMap R A f) ^ k = ρ (algebraMap R A b) := by
        rw [hc, hc, ← map_pow, ← map_mul, ← map_pow]
        exact congrArg ψ hb
      have hs' : c • a = ψ c * a := rfl
      rw [Algebra.smul_def, map_mul, e, ← hb', hs']
      ring
  obtain ⟨n, w, hw, e⟩ := key _ hx1
  obtain ⟨m, hm⟩ := hk (f ^ n • x - w) (by rw [map_sub, e, Algebra.smul_def, map_mul, map_pow, map_pow, sub_self])
  refine ⟨m + n, ?_⟩
  rw [smul_sub, sub_eq_zero, ← mul_smul, ← pow_add] at hm
  rw [hm]
  exact Submodule.smul_mem _ _ hw

theorem pow_mul_eq_zero_of_res {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) (W : S.Opens) (f : Γ(S, W))
    (x : Γ(Sp K, gp ⁻¹ᵁ W)) (hx : resK gp (S.basicOpen_le f) x = 0) :
    ∃ n : ℕ, (gp.app W).hom f ^ n * x = 0 := by
  have hc : IsCompact ((gp ⁻¹ᵁ W : (Sp K).Opens) : Set (Sp K)) :=
    (Set.subsingleton_of_subsingleton (α := PrimeSpectrum K)).isCompact
  refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact (Sp K) hc x ((gp.app W).hom f) ?_
  have e : (Sp K).basicOpen ((gp.app W).hom f) ≤ gp ⁻¹ᵁ S.basicOpen f := (Scheme.preimage_basicOpen gp f).ge
  have h := congrArg ((Sp K).presheaf.map (homOfLE e).op).hom hx
  rw [map_zero, resK, ← CommRingCat.comp_apply, ← Functor.map_comp] at h
  exact h

theorem finFam_finite {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsLocallyNoetherian S] {r : ℕ}
    (V : Fin r → S.Opens) (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)) (hV : ⨆ i, V i = ⊤)
    (ht : ∀ i, ∀ y ∈ t i, (gp.app (V i)).hom.IsIntegralElem y) (W : S.Opens) (hW : IsAffineOpen W) :
    ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ W), (∀ y ∈ s, y ∈ finFam gp V t W) ∧
      ∀ x ∈ finFam gp V t W, ∃ c : Γ(Sp K, gp ⁻¹ᵁ W) → Γ(S, W), x = ∑ y ∈ s, (gp.app W).hom (c y) * y := by
  classical
  haveI : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  letI : Algebra Γ(S, W) Γ(Sp K, gp ⁻¹ᵁ W) := (gp.app W).hom.toAlgebra
  have loc : ∀ f : Γ(S, W), (∃ i, S.basicOpen f ≤ V i) → ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ W),
      (s : Set Γ(Sp K, gp ⁻¹ᵁ W)) ⊆ (finFam gp V t W : Set Γ(Sp K, gp ⁻¹ᵁ W)) ∧
      ∀ x ∈ (finFam gp V t W : Set Γ(Sp K, gp ⁻¹ᵁ W)), ∃ n : ℕ,
        f ^ n • x ∈ Submodule.span Γ(S, W) (s : Set Γ(Sp K, gp ⁻¹ᵁ W)) := by
    rintro f ⟨i, hi⟩
    haveI := hW.isLocalization_basicOpen f
    refine exists_finset_pow_smul_mem (Rf := Γ(S, S.basicOpen f)) f (gp.app (S.basicOpen f)).hom
      (resK gp (S.basicOpen_le f)) (fun a => resK_app gp _ a) ?_ (resK gp hi '' (t i : Set _))
      ((t i).finite_toSet.image _) ?_ _ ?_
    · intro x hx
      obtain ⟨n, hn⟩ := pow_mul_eq_zero_of_res gp W f x hx
      exact ⟨n, by rw [Algebra.smul_def, map_pow]; exact hn⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨p, hp, hp0⟩ := ht i y hy
      refine ⟨p.map (S.presheaf.map (homOfLE hi).op).hom, hp.map _, ?_⟩
      have e : (gp.app (S.basicOpen f)).hom.comp (S.presheaf.map (homOfLE hi).op).hom =
          (resK gp hi).comp (gp.app (V i)).hom := RingHom.ext fun a => (resK_app gp hi a).symm
      rw [Polynomial.eval₂_map, e, ← Polynomial.hom_eval₂, hp0, map_zero]
    · intro x hx
      have hii : S.basicOpen f ≤ W ⊓ V i := le_inf (S.basicOpen_le f) hi
      have h1 := (mem_finFam gp V t W x).1 hx i
      have hm : resK gp hii (resK gp (inf_le_left : W ⊓ V i ≤ W) x) ∈ (Subring.closure _).map (resK gp hii) :=
        ⟨_, h1, rfl⟩
      rw [RingHom.map_closure, resK_resK] at hm
      refine Subring.closure_mono ?_ hm
      rintro _ ⟨y, ⟨a, rfl⟩ | ⟨z, hz, rfl⟩, rfl⟩
      · exact Or.inl ⟨_, (resK_app gp hii a).symm⟩
      · exact Or.inr ⟨z, hz, by rw [resK_resK]⟩
  have hspan : Ideal.span {f : Γ(S, W) | ∃ i, S.basicOpen f ≤ V i} = ⊤ := by
    rw [← hW.self_le_iSup_basicOpen_iff]
    intro x hx
    have hx2 : x ∈ ⨆ i, V i := by rw [hV]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx2
    obtain ⟨f, hf, hxf⟩ := hW.exists_basicOpen_le ⟨x, hi⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, i, hf⟩, hxf⟩
  obtain ⟨F, hF, hFs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    {f : Γ(S, W) | ∃ i, S.basicOpen f ≤ V i}).1
    (IsNoetherian.noetherian (R := Γ(S, W)) _)
  have hF1 : Ideal.span (F : Set Γ(S, W)) = ⊤ := hFs.symm.trans hspan
  choose σ hσ using loc
  let s : Finset Γ(Sp K, gp ⁻¹ᵁ W) := F.attach.biUnion fun f => σ f.1 (hF f.2)
  refine ⟨s, fun y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨f, -, hf⟩ := Finset.mem_biUnion.1 hy
    exact (hσ f.1 (hF f.2)).1 hf
  · have hxs : x ∈ Submodule.span Γ(S, W) (s : Set Γ(Sp K, gp ⁻¹ᵁ W)) := by
      refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (F : Set Γ(S, W)) hF1 x fun f => ?_
      obtain ⟨n, hn⟩ := (hσ f.1 (hF f.2)).2 x hx
      refine ⟨n, Submodule.span_mono ?_ hn⟩
      intro y hy
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨⟨f.1, f.2⟩, Finset.mem_attach _ _, hy⟩)
    obtain ⟨c, hc⟩ := Submodule.mem_span_finset.1 hxs
    exact ⟨c, hc.2.symm⟩

end GlobalTheory.FinitePowerAnnihilation
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightPowerCm
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace _root_.CategoryTheory.Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic

namespace GlobalTheory.LatFull.CMInt

theorem exists_frame_denom_dominant_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ y : FrPt Xo c z.K, y.x = z.x → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ la : GlobalTheory.AllWt.Weight Dw, (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) (Dw.p - 1)) → ∀ m : ℕ, ∃ N : z.K, N ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw la m), (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) → IsIntegral ℤ (N * evR Xo c F y) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz y hy _hp _hq la _hanti _hgap m
  classical
  set e : Formalism.L2.Pj.Ix Dw → ℤ := GlobalTheory.AllWt.exOf Dw la m with he
  let k : (E →+* ℂ) → ℕ := fun b => ∑ i : Fin (Dw.mult b), (-(e (some ⟨b, i⟩))).toNat
  let a : ∀ b : E →+* ℂ, Fin (Dw.mult b) → ℕ := fun b i => (e (some ⟨b, i⟩) + (k b : ℤ)).toNat
  have hak : ∀ (b : E →+* ℂ) (i : Fin (Dw.mult b)), e (some ⟨b, i⟩) + (k b : ℤ) = (a b i : ℤ) := by
    intro b i
    have h1 : (-(e (some ⟨b, i⟩))).toNat ≤ k b :=
      Finset.single_le_sum (f := fun i : Fin (Dw.mult b) => (-(e (some ⟨b, i⟩))).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simp only [a]
    omega
  obtain ⟨t, ht0, ht⟩ := _root_.GlobalTheory.LatFull.CMIntZ.exists_coeff_denom_intWt_any E H Dw l Xo c z f La hz e k
  obtain ⟨g, s, hg, hgs⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c z.K z.y y).1 (hy.trans hz.2.2.2.1.symm)
  let Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K := fun b => (g b).transpose
  have hYd : ∀ b, (Y b).det ≠ 0 := fun b => by
    simp only [Y, Matrix.det_transpose]; exact (hg b).ne_zero
  have hgY : (fun b => (Y b).transpose) = g := funext fun b => Matrix.transpose_transpose _
  obtain ⟨w₀, hw₀, hsw⟩ := GlobalTheory.FieldPolyZ.exists_frChg_one_evR_eq E H Dw l Xo c z.K z.y y Y s hYd
    (by rw [hgY]; exact hgs)
  obtain ⟨N₀, hN₀, hint⟩ := GlobalTheory.LatFull.CMInt.exists_denom_eval
    (fun _ : Formalism.L2.LamCM.FrVar Dw.mult →₀ ℕ => FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 z.K)) ((t : z.K)⁻¹))
    (fun v : Formalism.L2.LamCM.FrVar Dw.mult => Y v.1 v.2.2 v.2.1) (∑ b, ∑ i, a b i)
  have hsu : (((s ^ e none : z.Kˣ)) : z.K) ≠ 0 := Units.ne_zero _
  refine ⟨N₀ * (∏ b, (Y b).det ^ k b) * ((((s ^ e none : z.Kˣ)) : z.K))⁻¹,
    mul_ne_zero (mul_ne_zero hN₀ (Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hYd b))) (inv_ne_zero hsu),
    fun F hF hv => ?_⟩
  obtain ⟨G, hGh, hG⟩ := GlobalTheory.FieldPolyZ.exists_isHomogeneous_secZ_genFix E H Dw l Xo c z.K z.y e k a hak F hF
  have h1 := hG w₀ Y hYd hw₀
  have h2 : N₀ * (∏ b, (Y b).det ^ k b) * ((((s ^ e none : z.Kˣ)) : z.K))⁻¹ * evR Xo c F y =
      N₀ * Formalism.L2.LamCM.evalFr G Y := by
    rw [hsw e F hF, ← h1]
    field_simp
  rw [h2]
  refine hint G hGh fun μ => ?_
  rw [FractionalIdeal.mem_spanSingleton]
  refine ⟨⟨_, ht F hF hv G (fun y' Y' hY' h' => hG y' Y' hY' h') μ⟩, ?_⟩
  have htK : (t : z.K) ≠ 0 := fun h => ht0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  change (t : z.K) * AddMonoidAlgebra.coeff G μ * (t : z.K)⁻¹ = _
  field_simp

end GlobalTheory.LatFull.CMInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentImaginaryQuadraticEigenCrystalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_imaginaryQuadratic_eigen_crystal : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] (ρ : D.O →+* Module.End C H) (φ : LinearMap.BilinForm C H), (∀ (c : D.O) x y, φ (ρ c x) y = φ x (ρ (D.star c).unop y)) → ∃ e : Module.End C H, e * e = e ∧ (∀ c, ρ c * e = e * ρ c) ∧ (∀ x y, φ (e x) y = φ x (y - e y)) ∧ (∀ x, ρ (algebraMap (𝓞 D.F) D.O D.ω) (e x) = tR b.ρ • e x) ∧ (∃ v : C, IsUnit v ∧ ∀ x, e x = 0 → ρ (algebraMap (𝓞 D.F) D.O D.ω) x - tR b.ρ • x = v • x) ∧ ∀ N : Submodule C H, (∀ (c : D.O), ∀ x ∈ N, ρ c x ∈ N) → ∀ x ∈ N, e x ∈ N := by
  first | (exact @GlobalTheory.UPel.HT.exists_idem_crys) | (exact GlobalTheory.UPel.HT.exists_idem_crys) | (intros; apply GlobalTheory.UPel.HT.exists_idem_crys  <;> assumption)
end

