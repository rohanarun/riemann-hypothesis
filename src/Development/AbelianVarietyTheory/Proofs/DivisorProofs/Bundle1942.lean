module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationValuesTransportFieldIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1894
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsFiniteType
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.AbelianLimit

theorem abelianScheme_descends_to_fg_subring_anyDim :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (F : Finset R), IsAbelianScheme A →
    ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧
      Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ := by
  intro R _ A _ F hA
  have := hA.comm
  have := hA.proper
  obtain ⟨k, A₀, _, _, φ₀, hF, hk, _, _, _, h₀⟩ :=
    smooth_grpScheme_descends_to_fg_subring R A F hA.smooth inferInstance inferInstance
  have : IsNoetherianRing k := Algebra.FiniteType.isNoetherianRing ℤ k
  have h₁ : IsPullback φ₀ A.hom A₀.hom (spMap (algebraMap k R)) := h₀.1
  have : UniversallyClosed (pullback.snd A₀.hom (spMap (algebraMap k R))) := by
    rw [← h₁.isoPullback_inv_snd]
    infer_instance
  obtain ⟨s, hs⟩ := ProperLimit.exists_finset_isProper k R A₀.hom
  let S : Subalgebra k R := Algebra.adjoin k (s : Set R)
  let t : Sp S.toSubring ⟶ Sp k := spMap (algebraMap k S)
  have e : spMap S.toSubring.subtype ≫ t = spMap k.subtype := Spread.spMap_algHom_comp S.val
  obtain ⟨φ, hφ⟩ := GoodVal.exists_isGrpPullback_of_comp A₀ t (spMap S.toSubring.subtype) (e ▸ h₀)
  have : Smooth ((Over.pullback t).obj A₀).hom := inferInstanceAs (Smooth (pullback.snd A₀.hom t))
  have : IsProper ((Over.pullback t).obj A₀).hom := hs
  have hd : IsDominant (spMap S.toSubring.subtype) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical S.toSubring.subtype).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]
      exact bot_le)⟩
  exact ⟨S.toSubring, (Over.pullback t).obj A₀, inferInstance, φ, fun x hx => S.algebraMap_mem ⟨x, hF hx⟩,
    SpreadGroup.finiteType_of_fg hk (Subalgebra.fg_adjoin_finset s), isAbelianScheme_of_isDominant hφ hA, hφ⟩

end GlobalTheory.AbelianLimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnitsLiftArtinPinch
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.PinchUnitLift

theorem unit_lift (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀)
    (h : IsPullback f₁ f₂ g₁ g₂) [IsLocalRing P] (h₁ : Function.Surjective g₁) (h₂ : Function.Surjective g₂)
    (r : R₀) (hr : IsUnit r) : ∃ s : R₁, IsUnit s ∧ g₁ s = r := by
  rcases subsingleton_or_nontrivial R₀ with h0 | h0
  · exact ⟨1, isUnit_one, Subsingleton.elim _ _⟩
  have hf : Function.Surjective f₁ := by
    intro a
    obtain ⟨b, hb⟩ := h₂ (g₁ a)
    obtain ⟨p, hp, -⟩ := Types.exists_of_isPullback (h.map (forget CommRingCat)) a b hb.symm
    exact ⟨p, hp⟩
  haveI : Nontrivial R₁ := g₁.hom.domain_nontrivial
  haveI : IsLocalRing R₁ := IsLocalRing.of_surjective' f₁.hom hf
  haveI : IsLocalHom g₁.hom := IsLocalHom.of_surjective g₁.hom h₁
  obtain ⟨s, rfl⟩ := h₁ r
  exact ⟨s, IsUnit.of_map g₁.hom s hr, rfl⟩

theorem main : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (B : Over (Spec R₀)) [GrpObj B], IsAbelianScheme B → ∀ (X₁ : Scheme.{0}) (q : X₁ ⟶ Spec R₁) (ρ : B.left ⟶ X₁), ρ ≫ q = B.hom ≫ Spec.map g₁ → ∀ u : Γ(B.left, ⊤)ˣ, ∃ v : Γ(X₁, ⊤)ˣ, ∀ x : B.left, gm ρ x ⊤ v = gm (𝟙 B.left) x ⊤ u := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ h hP _ h₁ h₂ B _ hB X₁ q ρ hρ u
  have hb := GlobalTheory.globalFns_holds _ B hB
  obtain ⟨t, ht⟩ := hb.2 u.val
  obtain ⟨t', ht'⟩ := hb.2 (u⁻¹).val
  have htu : IsUnit t := by
    refine IsUnit.of_mul_eq_one t' (hb.1 ?_)
    rw [map_mul, map_one, ht, ht']
    exact u.mul_inv
  obtain ⟨s, hs, hst⟩ := unit_lift P R₁ R₂ R₀ f₁ f₂ g₁ g₂ h h₁ h₂ ((Scheme.ΓSpecIso R₀).hom t)
    (htu.map (Scheme.ΓSpecIso R₀).hom.hom)
  have hv : IsUnit (q.appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s)) := (hs.map _).map _
  refine ⟨hv.unit, fun x => Units.ext ?_⟩
  rw [gm_val ρ x ⊤ trivial, gm_val (𝟙 B.left) x ⊤ trivial]
  have e : ρ.appTop.hom (q.appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s)) = u.val := by
    have e1 : ρ.appTop.hom (q.appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s)) =
        (ρ ≫ q).appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s) := by
      rw [Scheme.Hom.comp_appTop]; rfl
    have e2 : (Spec.map g₁).appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s) = t := by
      have := congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso_inv_naturality g₁)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [← this]
      have hst' : g₁.hom s = (Scheme.ΓSpecIso R₀).hom.hom t := hst
      rw [hst']
      exact (Scheme.ΓSpecIso R₀).hom_inv_id_apply t
    rw [e1, hρ, Scheme.Hom.comp_appTop, ← ht, ← e2]
    rfl
  exact congrArg (B.left.presheaf.germ ⊤ x trivial).hom e

end GlobalTheory.PinchUnitLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapCompStalkAlg
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def stalkAlg (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) : c.F →+* (X₀ TF.Y Z).presheaf.stalk x :=
  ((X₀ TF.Y Z).presheaf.germ ⊤ x trivial).hom.comp (algX (s₀ TF.Y Z) ⊤)

def stalkHom (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).presheaf.stalk x :=
  ((X₀ TF.Y Z).presheaf.germ ((barComp TF.Y Z).ι ⁻¹ᵁ U.1) x hx).hom.comp ((barComp TF.Y Z).ι.app U.1).hom

theorem algebraMap_comp_stalkAlg (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (x : X₀ TF.Y Z) :
    (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField).comp (stalkAlg TF Z x) =
      GlobalTheory.Cartier.constFn (s₀ TF.Y Z) :=
  RingHom.ext fun a => GlobalTheory.Cartier.algebraMap_germ (U := ⊤) trivial _

end GlobalTheory.LogKSDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraiseSystemInAlgebraisingClosedSubscheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem alg_of_closedSubscheme : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0})
    (f : W ⟶ Spec (CommRingCat.of R)) (a : W.IdealSheafData), Alg (a.subschemeι ≫ f) I →
    ∀ t : ℕ → W.IdealSheafData, IsSystem f I t → (∀ e, IsProper ((t e).subschemeι ≫ f)) →
    ∃ T : W.IdealSheafData, IsProper (T.subschemeι ≫ f) ∧ Reduces f I T (fun e => t e ⊔ a) := by
  intro R _ I W f a hA t ht hp
  set ι := a.subschemeι with hι
  have hbase : ∀ J : Ideal R, (baseIdeal f J).comap ι = baseIdeal (ι ≫ f) J :=
    fun J => _root_.GlobalTheory.FormalAlg.baseIdeal_calculus.1 R W a.subscheme f ι J
  have hms := _root_.GlobalTheory.ClosedImmIdeal.map_sup_comap_and_comap_map a.subscheme W ι inferInstance
  let s : ℕ → a.subscheme.IdealSheafData := fun e => (t e).comap ι
  have hs : IsSystem (ι ≫ f) I s := fun e => by
    simp only [s]
    rw [ht e, Scheme.IdealSheafData.comap_sup, hbase]
  have hsp : ∀ e, IsProper ((s e).subschemeι ≫ ι ≫ f) := fun e => by
    have H : t e ≤ (s e).map ι := Scheme.IdealSheafData.le_map_comap _ _
    rw [← Category.assoc, ← Scheme.IdealSheafData.subschemeMap_subschemeι (s e) (t e) ι H,
      Category.assoc]
    haveI := hp e
    haveI : IsClosedImmersion (Scheme.IdealSheafData.subschemeMap (s e) (t e) ι H) := by
      haveI : IsClosedImmersion (Scheme.IdealSheafData.subschemeMap (s e) (t e) ι H ≫
          (t e).subschemeι) := by
        rw [Scheme.IdealSheafData.subschemeMap_subschemeι]; infer_instance
      exact IsClosedImmersion.of_comp_isClosedImmersion _ (t e).subschemeι
    infer_instance
  obtain ⟨T₀, hT₀p, hT₀r⟩ := hA s hs hsp
  refine ⟨T₀.map ι, ?_, fun e => ?_⟩
  · let g := T₀.subschemeι ≫ ι
    have hk : (T₀.map ι).subschemeι.ker = g.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]; rfl
    haveI := IsClosedImmersion.isIso_lift _ _ hk
    have hfac : (T₀.map ι).subschemeι =
        inv (IsClosedImmersion.lift (T₀.map ι).subschemeι g hk.le) ≫ g := by
      rw [IsIso.eq_inv_comp, IsClosedImmersion.lift_fac]
    rw [hfac, Category.assoc]
    haveI : IsProper (g ≫ f) := by simpa [g, Category.assoc] using hT₀p
    infer_instance
  · calc T₀.map ι ⊔ baseIdeal f (I ^ (e + 1))
        = (T₀ ⊔ (baseIdeal f (I ^ (e + 1))).comap ι).map ι := (hms T₀ _).1.symm
      _ = (s e).map ι := by rw [hbase, hT₀r e]
      _ = ((⊥ : a.subscheme.IdealSheafData) ⊔ (t e).comap ι).map ι := by rw [bot_sup_eq]
      _ = t e ⊔ a := by
        rw [(hms ⊥ (t e)).1, Scheme.IdealSheafData.map_bot, hι,
          Scheme.IdealSheafData.ker_subschemeι, sup_comm]

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanExistenceOfComplexIsomorphicField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem archF_of_arch : ∀ κ : Rule, Funct κ → Arch κ → ArchF κ := by
  intro κ hF hA R _ _ _ _ D hP hT F _ _ _ e N ν g r m k hg hm hk β ζ q hq s hs vB bX σ gm hAd k₀ hK
  letI : Algebra (FractionRing R) ℂ := ((e : F →+* ℂ).comp (algebraMap (FractionRing R) F)).toAlgebra
  have he : ∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) ℂ x := fun _ => rfl
  obtain ⟨N', ν', I, hb, hh, hl, heX, hth, hrg, hvE, hfam⟩ := _root_.GlobalTheory.MBLow.FieldIso.transport_iso R D F ℂ e he N ν
  obtain ⟨hform, hlev⟩ := _root_.GlobalTheory.MBLow.TrNum.transport F ℂ e N N' I hb hh hl
  obtain ⟨β', hβ⟩ := hform k β
  obtain ⟨q', hq', hev⟩ := hlev m g hm ζ q hq
  obtain ⟨hBK, hadp⟩ := _root_.GlobalTheory.MBLow.bKey_adapted_map κ hF R D F ℂ e he N ν N' ν' I hh hl heX hth hvE vB
  obtain ⟨gm', hpull, hAd'⟩ := hadp r g bX σ gm hAd
  choose s' hs1 hs2 using fun a => hfam (m ^ 2) (s a)
  have hs' : ∀ a, ∃ f, ν'.FamV (s' a) f ∧ IsEvFam N' m (q' a) f := by
    intro a
    obtain ⟨f, hf, hf2⟩ := hs a
    obtain ⟨f', hf', hff⟩ := hs1 a f hf
    exact ⟨f', hf', hev a f f' hf2 hff⟩
  obtain ⟨ε, hε, H⟩ := hA R D hP hT N' ν' g r m k hg hm hk β' _ q' hq' s' hs' vB _ σ gm' hAd' _ (hBK k₀ hK)
  have h1 : ∀ a j α, (jc ν' (s' a) (gm' j) (I.e α)).fst = e (jc ν (s a) (gm j) α).fst := by
    intro a j α
    rw [hs2 a _ _ (hpull j) α]
    simp [dualMap]
  have h2 : ∀ a j α, (jc ν' (s' a) (gm' j) (I.e α)).snd = e (jc ν (s a) (gm j) α).snd := by
    intro a j α
    rw [hs2 a _ _ (hpull j) α]
    simp [dualMap]
  refine ⟨ε, hε, fun u hu hu' => ?_⟩
  obtain ⟨hsum, x₀, hg₀, lev₀, ϑ, hϑ, hJ, hκ⟩ := H u hu hu'
  refine ⟨fun a j => ⟨?_, ?_⟩, x₀, hg₀, lev₀, ϑ, fun a j => ?_, ?_, hκ⟩
  · have := ((I.e.toEquiv.summable_iff.2 (hsum a j).1)).mul_left ‖(e (ν.rg ^ (m ^ 2)))⁻¹‖
    refine this.congr fun α => ?_
    simp only [Function.comp, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h1, hβ]
    rw [← norm_mul, map_div₀, div_eq_inv_mul, _root_.mul_assoc]
  · have := ((I.e.toEquiv.summable_iff.2 (hsum a j).2)).mul_left ‖(e (ν.rg ^ (m ^ 2)))⁻¹‖
    refine this.congr fun α => ?_
    simp only [Function.comp, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h2, hβ]
    rw [← norm_mul, map_div₀, div_eq_inv_mul, _root_.mul_assoc]
  · rw [hϑ a j, ← I.e.toEquiv.tsum_eq]
    refine tsum_congr fun α => ?_
    simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h1, hβ, hrg, map_div₀, map_pow]
  · convert hJ using 3 with a j
    rw [← I.e.toEquiv.tsum_eq]
    refine tsum_congr fun α => ?_
    simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h2, hβ, hrg, map_div₀, map_pow]

end GlobalTheory.MBLow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeQuotientClosedImmersionIdealSheaf
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FormalAlg

theorem ker_specMap_quotientMk (R : Type) [CommRing R] (J : Ideal R) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).ker =
      baseIdeal (𝟙 (Spec (CommRingCat.of R))) J := by
  rw [Scheme.ker_of_isAffine, baseIdeal]
  congr 1
  have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have h1' : ∀ y, (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom.hom
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom y) =
        Ideal.Quotient.mk J ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y) := fun y => by
    rw [← CommRingCat.comp_apply, h1, CommRingCat.comp_apply]
    rfl
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom.hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  have hc : ∀ r : R, cst (𝟙 (Spec (CommRingCat.of R))) ⊤ r =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    intro r
    simp [cst, rs]
  ext x
  rw [RingHom.mem_ker, ← map_eq_zero_iff _ hinj, h1']
  constructor
  · intro hx
    have hm := Ideal.mem_map_of_mem (cst (𝟙 (Spec (CommRingCat.of R))) ⊤)
      (Ideal.Quotient.eq_zero_iff_mem.1 hx)
    rwa [hc, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at hm
  · intro hx
    have hle : J.map (cst (𝟙 (Spec (CommRingCat.of R))) ⊤) ≤
        RingHom.ker ((Ideal.Quotient.mk J).comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom) := by
      refine Ideal.map_le_iff_le_comap.2 fun j hj => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, hc, RingHom.comp_apply, ← CommRingCat.comp_apply,
        Iso.inv_hom_id, CommRingCat.id_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hj
    exact hle hx

theorem baseChange_quotient : ∀ (R : Type) [CommRing R] (J : Ideal R) (W Y : Scheme.{0})
    (f : W ⟶ Spec (CommRingCat.of R)) (b : Y ⟶ W) (q : Y ⟶ Spec (CommRingCat.of (R ⧸ J))),
    IsPullback b q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) →
      IsClosedImmersion b ∧ b.ker = baseIdeal f J ∧ ∀ V : W.Opens, IsAffineOpen V →
        Function.Surjective (b.app V).hom ∧ RingHom.ker (b.app V).hom = J.map (cst f V) := by
  intro R _ J W Y f b q h
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have e : h.isoPullback.hom ≫ pullback.fst _ _ = b := h.isoPullback_hom_fst
  haveI hb : IsClosedImmersion b := by
    rw [← e]
    infer_instance
  have hk : b.ker = baseIdeal f J := by
    rw [← e, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      ker_specMap_quotientMk, (_root_.GlobalTheory.FormalAlg.baseIdeal_calculus).1, Category.comp_id]
  refine ⟨hb, hk, fun V hV => ⟨b.app_surjective V hV, ?_⟩⟩
  rw [← Scheme.Hom.ker_apply b ⟨V, hV⟩, hk, baseIdeal_ideal]

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentTwistingSectionMulLe
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefTwist

theorem vAdd_natCast_pos {K : Type} [Field K] [NumberField K] {q : ℕ} (hq : q ≠ 0) {w : HeightOneSpectrum (𝓞 K)}
    (hw : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) : 0 < vAdd w (q : K) := by
  have h1 : w.valuation K (algebraMap (𝓞 K) K q) < 1 := (w.valuation_lt_one_iff_mem _).2 hw
  rw [map_natCast] at h1
  have h0 : w.valuation K (q : K) ≠ 0 := (w.valuation K).ne_zero_iff.2 (Nat.cast_ne_zero.2 hq)
  have h2 := (WithZero.log_lt_log h0 one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  unfold vAdd
  omega

theorem nval_le_add_of_mul {T : CDVR} {e n : ℕ} {m s k : ℝ} (he : 0 < e) (hm : 0 < m) (hn : (n : ℝ) = e * m)
    (hs : s ≤ k * m) {a b : T.Fr} (h : nval T.V e b ≤ nval T.V e a + (s : EReal)) :
    nval T.V n b ≤ nval T.V n a + (k : EReal) := by
  by_cases ha : a = 0
  · rw [ha, nval_zero, EReal.top_add_coe]; exact le_top
  rw [nval_of_ne ha, ← EReal.coe_add] at h ⊢
  by_cases hb : b = 0
  · rw [hb, nval_zero] at h; exact absurd h (not_le.2 (EReal.coe_lt_top _))
  rw [nval_of_ne hb, EReal.coe_le_coe_iff] at h ⊢
  have he' : (0 : ℝ) < e := Nat.cast_pos.2 he
  rw [hn, ← div_div, ← div_div, div_le_iff₀ hm, add_mul, div_mul_cancel₀ _ hm.ne']
  linarith

theorem refExp_vp_add_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (G G₀ : WTZ E), Even G.2 → ∀ (cst k : ℝ) (q : ℕ), q.Prime → ∀ t : ∀ Z : Comp Xo c, TwSec U x Z G₀, (∀ Z (w : HeightOneSpectrum (𝓞 c.F)), ((q : ℕ) : 𝓞 c.F) ∈ w.asIdeal → (t Z).hi w - (⌊(t Z).lo w⌋ : ℝ) ≤ k * (vAdd w (q : c.F) : ℝ)) → refExp_vp U cst (G + G₀) q ≤ refExp_vp U cst G q + (k : EReal) := by
  intro E _ _ _ H Dw l Xo c r U hU x G G₀ hG cst k q hq t ht
  refine (refExp_vp_le_iff U).2 fun la T io e ho y hy φ hφ => ?_
  have h0 := (refExp_vp_le_iff U).1 (le_refl (refExp_vp U cst G q)) la T io e ho y hy φ hφ
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.exists_component_integral_framedPoint_liesOn E H Dw l Xo c T io y
  have hv : (fun f => nval T.V e (evI y f)) ∈ valOn Z la.1 := ⟨PtV.mk la.1 ho y ⟨hy, hZ⟩ () trivial, rfl⟩
  have hm : 0 < vAdd la.1 (q : c.F) := vAdd_natCast_pos hq.ne_zero la.2
  have hq' : vV T.V (q : T.Fr) = (e : ℤ) * vAdd la.1 (q : c.F) := by
    rw [← map_natCast io q]; exact ho.2 _
  have hn : (((vV T.V (q : T.Fr)).toNat : ℕ) : ℝ) = e * (vAdd la.1 (q : c.F) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (hq' ▸ mul_nonneg (Int.natCast_nonneg e) hm.le), hq']
    push_cast; rfl
  have hd : depthAt_vp U (G + G₀) q y ≤ depthAt_vp U G q y + (k : EReal) := by
    rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    refine le_iInf₂ fun f hf => ?_
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    obtain ⟨g, hg, hle⟩ := _root_.GlobalTheory.TwMulOne.exists_latW_val_le E H Dw l Xo c r U hU x G G₀ hG Z (t Z) la.1 _ hv f hf
    exact (iInf₂_le g hg).trans (nval_le_add_of_mul ho.1 (Int.cast_pos.2 hm) hn (ht Z la.1 la.2) hle)
  rw [add_right_comm]
  exact hd.trans (add_le_add h0 le_rfl)

end GlobalTheory.RefTwist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisTorsionOfWeilPairingField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GeomBasis

theorem basis_of_weil : ∀ (h N : ℕ) (k : Type) [Field k] (S : Scheme.{0}) (x : Sp k ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (z : kˣ) (e₀ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ A)), L.IsLB → Odd N → IsPrimitiveRoot z N → (∀ a a', e₀ (a + a') = e₀ a * e₀ a') → (∀ a, e₀ a = 1 ↔ ∃ a', a = N • a') → (∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e₀ a = g) → (∀ a a', e (a + a') = e a * e a') → (∀ a, e a ^ N = 1) → (∀ a a', Out.WeilIs A L N (e a) (e a') (unitOn (z ^ (2 * omegaStd a a')))) → (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ ∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e a = g := by
  intro h N k _ S x A _ _ L z e₀ e hL hN hz add₀ ker₀ onto₀ add tors weil
  have hN0 : N ≠ 0 := by rintro rfl; exact (Nat.not_even_iff_odd.2 hN) (by decide)
  haveI : NeZero N := ⟨hN0⟩
  have e0 : e 0 = 1 := GlobalTheory.LevCover.add_map_zero add
  have kerE : ∀ a, e a = 1 ↔ ∃ a', a = N • a' := by
    intro a
    constructor
    · intro ha
      apply GlobalTheory.SiegelOfPolarised.exists_smul_of_dvd
      intro b
      have w1 := weil a b
      have w0 := weil 0 b
      rw [ha] at w1
      rw [e0] at w0
      have hu := GlobalTheory.weilIs_unique_fieldPoint S A L hL k x _ _ _ _ _ w1 w0
      have h0 : omegaStd (0 : Fin h ⊕ Fin h → ℤ) b = 0 := by simp [omegaStd]
      rw [h0, mul_zero, zpow_zero] at hu
      have hd : (N : ℤ) ∣ 2 * omegaStd a b := (hz.zpow_eq_one_iff_dvd _).1 hu
      obtain ⟨m, hm⟩ := hN
      have hc : IsCoprime (N : ℤ) 2 := ⟨1, -(m : ℤ), by rw [hm]; push_cast; ring⟩
      exact hc.dvd_of_dvd_mul_left hd
    · rintro ⟨b, rfl⟩
      rw [GlobalTheory.LevCover.add_map_nsmul add, tors]
  have tors₀ : ∀ a, e₀ a ^ N = 1 := fun a => by
    rw [← GlobalTheory.LevCover.add_map_nsmul add₀]; exact (ker₀ _).2 ⟨a, rfl⟩
  let F : (Fin h ⊕ Fin h → ZMod N) → {g : Over.mk x ⟶ A // g ^ N = 1} :=
    fun c => ⟨e₀ fun i => ((c i).val : ℤ), tors₀ _⟩
  have hF : Function.Injective F := fun c c' hcc => by
    have e₁ : e₀ (fun i => ((c i).val : ℤ)) = e₀ fun i => ((c' i).val : ℤ) := congrArg Subtype.val hcc
    have e₂ := add₀ ((fun i => ((c i).val : ℤ)) - fun i => ((c' i).val : ℤ)) fun i => ((c' i).val : ℤ)
    rw [sub_add_cancel, e₁] at e₂
    obtain ⟨b, hb⟩ := (ker₀ _).1 (mul_eq_right.1 e₂.symm)
    funext i
    have := congrArg (fun w : ℤ => (w : ZMod N)) (congrFun hb i)
    simpa [sub_eq_zero] using this
  have hF' : Function.Surjective F := by
    rintro ⟨g, hg⟩
    obtain ⟨a, rfl⟩ := onto₀ g hg
    refine ⟨fun i => (a i : ZMod N), Subtype.ext ?_⟩
    show e₀ (fun i => (((a i : ZMod N)).val : ℤ)) = e₀ a
    have d : ∀ i, (N : ℤ) ∣ a i - (((a i : ZMod N)).val : ℤ) := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (by simp)
    choose b hb using d
    have hab : a - (fun i => (((a i : ZMod N)).val : ℤ)) = N • b := funext fun i => by simpa using hb i
    have := add₀ (a - fun i => (((a i : ZMod N)).val : ℤ)) fun i => (((a i : ZMod N)).val : ℤ)
    rw [sub_add_cancel, hab, (ker₀ _).2 ⟨b, rfl⟩, _root_.one_mul] at this
    exact this.symm
  have card : Nat.card {g : Over.mk x ⟶ A // g ^ N = 1} = N ^ Fintype.card (Fin h ⊕ Fin h) := by
    rw [← Nat.card_congr (Equiv.ofBijective F ⟨hF, hF'⟩), Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card]
  exact ⟨kerE, GlobalTheory.SiegelOfPolarised.onto_torsion hN0 e add tors (fun a ha => (kerE a).1 ha) card⟩

end GlobalTheory.GeomBasis
end

