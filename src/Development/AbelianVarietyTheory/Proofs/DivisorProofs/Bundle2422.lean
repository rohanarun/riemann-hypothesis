module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2224
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantBijectionsFamiliesSectionsDifferBySca
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.UU

noncomputable section

namespace GlobalTheory.Mum

theorem eqv_eq_smul : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ lab E E', Eqv D.toPre A F N lab E → Eqv D.toPre A F N lab E' → ∃ c : Fˣ, ∀ s j, (E' s).f j = liftFun A.A _ (fnF F c.val) * (E s).f j := by
  intro R _ _ _ I D A F _ _ _ N hN lab E E' hE hE'
  have hN1 : 1 ≤ N := hN.pos
  have hNF : (N : F) ≠ 0 := by
    have h1 : (N : R) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have h2 : (N : FractionRing R) ≠ 0 := fun h =>
      h1 (IsFractionRing.injective R (FractionRing R) (by rw [map_natCast, map_zero]; exact h))
    intro h
    apply h2
    apply (algebraMap (FractionRing R) F).injective
    rw [map_zero, map_natCast]
    exact_mod_cast h
  let p : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (FractionRing R)) := jFK (R := R) F
  let mkE : ∀ G : Fam D.toPre F N → SecK A.L (snd (TFK (R := R) F) A.A).left N, Eqv D.toPre A F N lab G →
      (Fam D.toPre F N →ₗ[F] EA A p N) := fun G hG =>
    { toFun := fun s => SecMod.mk _ (G s)
      map_add' := fun s t => DVR.SecOps.sec_ext fun j => hG.add s t (s + t) (fun _ _ => rfl) j
      map_smul' := fun c s => DVR.SecOps.sec_ext fun j =>
        hG.smul c s (c • s) ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff c s _).2 rfl) j }
  have hbij : ∀ G hG, Function.Bijective (mkE G hG) := fun G hG => hG.bij
  let e := LinearEquiv.ofBijective (mkE E hE) (hbij E hE)
  let T : EA A p N →ₗ[F] EA A p N := (mkE E' hE').comp e.symm.toLinearMap
  have hTe : ∀ s, T (mkE E hE s) = mkE E' hE' s := fun s => by
    show mkE E' hE' (e.symm (e s)) = _
    rw [e.symm_apply_apply]
  obtain ⟨ρ, hact, -, -, -⟩ := GlobalTheory.thetaGrp_acts_linearly GlobalTheory.allSixLaws.1.globalFns _ A (N : ℤ) (TFK (R := R) F)
  have huniq : ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (a : EA A p N) (b b' : SecK A.L (snd (TFK (R := R) F) A.A).left N),
      IsActOf A.A A.L (N : ℤ) θ a.sec b → IsActOf A.A A.L (N : ℤ) θ a.sec b' → b = b' := fun θ a b b' h h' => by
    have := ((hact θ _ _).1 h).symm.trans ((hact θ _ _).1 h')
    exact DVR.SecOps.sec_ext fun j => congrFun (congrArg Subtype.val this) j
  have hT : ∀ x : Over.mk p ⟶ A.A, x ^ N = 1 → ∃ θ : ThetaGrp A.A A.L (N : ℤ) (Over.mk p), θ.pt = x ∧
      ∀ v v' : EA A p N, IsActOf A.A A.L (N : ℤ) θ v.sec v'.sec →
        IsActOf A.A A.L (N : ℤ) θ (T v).sec (T v').sec := by
    intro x hx
    obtain ⟨p₀, hp₀⟩ := (hE.onto x).1 hx
    obtain ⟨w, hw⟩ := hE.frame p₀
    obtain ⟨θ, hθ⟩ := hE.lift p₀
    obtain ⟨Φ, hΦ⟩ := ReciprocityTheory.ChartRestriction.G.DVR.phiFun_of GlobalTheory.allSixLaws.1 R I D F N hN1 p₀ w hw.1
    refine ⟨θ, hθ.pt_eq.trans hp₀, fun v v' hvv => ?_⟩
    obtain ⟨s, rfl⟩ := (hbij E hE).2 v
    have hPhi := (hΦ s (Φ s)).2 rfl
    have h₁ := hE.act p₀ w θ s (Φ s) hw hθ hPhi
    have h₂ := hE'.act p₀ w θ s (Φ s) hw hθ hPhi
    have e₁ : v' = mkE E hE (Φ s) := huniq θ _ _ _ hvv h₁
    rw [e₁, hTe, hTe]
    exact h₂
  obtain ⟨c, hc⟩ := GlobalTheory.ThetaCommutant.eq_smul_of_commute A F p N hNF T hT
  have hpos : 0 < Module.finrank F (EA A p N) := by
    rw [GlobalTheory.ThetaCommutant.finrank_eq A F p N hNF]; positivity
  have : Nontrivial (EA A p N) := Module.nontrivial_of_finrank_pos hpos
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := exists_ne (0 : EA A p N)
    obtain ⟨s, rfl⟩ := (hbij E hE).2 v
    have h0 : mkE E' hE' s = mkE E' hE' 0 := by rw [← hTe, hc, zero_smul, map_zero]
    have := (hbij E' hE').1 h0
    subst this
    exact hv (map_zero _)
  refine ⟨Units.mk0 c hc0, fun s j => ?_⟩
  have h := congrArg (fun v : EA A p N => v.sec.f j) ((hTe s).symm.trans (hc _))
  exact h

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNearPointOfEtaleOnFibreSmooth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem etale_basicOpen_comp_SpecMap_iff (S R : CommRingCat.{0}) (θ : S ⟶ R) (f : R) :
    Etale ((show (Spec R).Opens from PrimeSpectrum.basicOpen f).ι ≫ Spec.map θ) ↔
      ((algebraMap R (Localization.Away f)).comp θ.hom).Etale := by
  exact GlobalTheory.Mum.AffFib.etale_basicOpen_iff S R θ f

theorem etale_image_comp_of_etale (X Z X' Z' : Scheme.{0}) (h : X ⟶ Z) (h' : X' ⟶ Z') (iX : X' ⟶ X) (iZ : Z' ⟶ Z)
    [IsOpenImmersion iX] [IsOpenImmersion iZ] (sh : iX ≫ h = h' ≫ iZ) (U : X'.Opens) :
    Etale (U.ι ≫ h') → Etale ((iX ''ᵁ U).ι ≫ h) := by
  intro hE
  have e : (iX ''ᵁ U).ι ≫ h = (iX.isoImage U).inv ≫ (U.ι ≫ h') ≫ iZ := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Scheme.Hom.isoImage_hom_ι, Category.assoc, sh, Category.assoc]
  rw [e]
  infer_instance

end GlobalTheory.Mum

theorem GlobalTheory.Mum.etale_near_of_etale_fibre : ∀ (T X Z : Scheme.{0}) (p : X ⟶ T) (q : Z ⟶ T) (h : X ⟶ Z) (hh : h ≫ q = p), Smooth p → Smooth q → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ T) (W : (pullback p x).Opens) (w : ↥(pullback p x)), w ∈ W → Etale (W.ι ≫ pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)) → ∃ V : X.Opens, pullback.fst p x w ∈ V ∧ Etale (V.ι ≫ h) := by
  intro T X Z p q h hh hp hq Ω _ x W w hw hE
  subst hh
  obtain ⟨UA, hUA, hzA, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens)
    (show (h ≫ q) (pullback.fst (h ≫ q) x w) ∈ (⊤ : T.Opens) from trivial)
  obtain ⟨UC, hUC, hzC, hCA⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens)
    (show h (pullback.fst (h ≫ q) x w) ∈ q ⁻¹ᵁ UA by simpa using hzA)
  obtain ⟨UB, hUB, hzB, hBC⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show pullback.fst (h ≫ q) x w ∈ h ⁻¹ᵁ UC from hzC)
  have hUA' : IsAffineOpen UA := hUA
  have hUB' : IsAffineOpen UB := hUB
  have hUC' : IsAffineOpen UC := hUC
  haveI := hUA'.isOpenImmersion_fromSpec
  haveI := hUB'.isOpenImmersion_fromSpec
  haveI := hUC'.isOpenImmersion_fromSpec
  have hxr : Set.range x ⊆ Set.range hUA'.fromSpec := by
    rw [hUA'.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    have : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
    obtain rfl : y = pullback.snd (h ≫ q) x w := Subsingleton.elim _ _
    have := congrArg (fun g => g w) (pullback.condition (f := h ≫ q) (g := x))
    simp only [Scheme.Hom.comp_apply] at this
    show x (pullback.snd (h ≫ q) x w) ∈ UA
    rw [← this]; simpa using hzA
  set φ := q.appLE UA UC hCA
  set ψ := h.appLE UC UB hBC
  let x' := IsOpenImmersion.lift hUA'.fromSpec x hxr
  let ω : Γ(T, UA) ⟶ CommRingCat.of Ω := Spec.preimage x'
  have sx : Spec.map ω ≫ hUA'.fromSpec = x := by
    simp only [ω, Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨W', w', hw', hfst, hE'⟩ := _root_.GlobalTheory.fibre_etale_restrict_open T X Z _ _ _ (Sp Ω) (h ≫ q) q h rfl
    (Spec.map (φ ≫ ψ)) (Spec.map φ) (Spec.map ψ) (by rw [Spec.map_comp])
    hUA'.fromSpec hUB'.fromSpec hUC'.fromSpec (hUA'.SpecMap_appLE_fromSpec q hUC' hCA).symm
    (hUC'.SpecMap_appLE_fromSpec h hUB' hBC).symm x (Spec.map ω) sx W w hw
    (by rw [hUB'.range_fromSpec]; exact hzB) hE
  have hex := GlobalTheory.T.etale_localisation_of_etale_affine_fibre' _ _ _ φ ψ Ω ω W' w' hw' hE'
  dsimp only at hex
  obtain ⟨Q', hQ', f, hcomap, hf, hEt⟩ := hex
  letI := φ.hom.toAlgebra; letI := ψ.hom.toAlgebra; letI := (φ ≫ ψ).hom.toAlgebra; letI := ω.hom.toAlgebra
  letI : IsScalarTower Γ(T, UA) Γ(Z, UC) Γ(X, UB) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI := hQ'
  haveI hQprime : (pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w').asIdeal.IsPrime := PrimeSpectrum.isPrime _
  have hbij := _root_.GlobalTheory.Mum.mapBaseChange_residueField_bijective_of_etale_fibre Γ(T, UA) Γ(Z, UC) Γ(X, UB) Ω (pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w').asIdeal Q' f hcomap hf hEt
  haveI : Algebra.Smooth Γ(T, UA) Γ(Z, UC) := HasRingHomProperty.appLE @Smooth q hq ⟨UA, hUA'⟩ ⟨UC, hUC'⟩ hCA
  haveI : Algebra.Smooth Γ(T, UA) Γ(X, UB) := by
    have := HasRingHomProperty.appLE @Smooth (h ≫ q) hp ⟨UA, hUA'⟩ ⟨UB, hUB'⟩ (hBC.trans (h.preimage_mono hCA))
    rw [← Scheme.Hom.appLE_comp_appLE h q UA UC UB hCA hBC] at this
    exact this
  obtain ⟨g, hg, hgEt⟩ := _root_.GlobalTheory.Mum.exists_etale_away_of_bijective_mapBaseChange Γ(T, UA) Γ(Z, UC) Γ(X, UB) (pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w').asIdeal hbij
  have hR : ((algebraMap Γ(X, UB) (Localization.Away g)).comp ψ.hom).Etale := by
    have := RingHom.etale_algebraMap.mpr hgEt
    rwa [IsScalarTower.algebraMap_eq Γ(Z, UC) Γ(X, UB) (Localization.Away g)] at this
  have hV := (etale_basicOpen_comp_SpecMap_iff _ _ ψ g).mpr hR
  refine ⟨hUB'.fromSpec ''ᵁ (PrimeSpectrum.basicOpen g), ?_,
    etale_image_comp_of_etale X Z _ _ h (Spec.map ψ) hUB'.fromSpec hUC'.fromSpec
      (hUC'.SpecMap_appLE_fromSpec h hUB' hBC).symm _ hV⟩
  rw [← hfst]
  exact Set.mem_image_of_mem _ hg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTrivialisationOfTraitUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem evenOn_of_unifTrait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → UnifTrait D G P.L.L →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X],
    Nonempty (GlobalTheory.UU.TQ (thickObj R (maximalIdeal R) 0 G) X) → EvenOn P := by
  intro R _ _ _ _ D G _ _ P hG hU X _ _ _ hQ
  obtain ⟨W, _, _, _, φ, G', _, _, β, D', A', U', hW, -, hφ, hgp, hL, -⟩ := hU
  have hadm : AdmBase W (maximalIdeal W) := by
    haveI := hW.1
    exact ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hG' : IsSemiAbelian G' := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso hgp (isGrpPullback_pullback G (spMap φ))
    haveI := mbc
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (spMap φ) G hG)
  obtain ⟨P', hP', hE⟩ := unif_evenOn W hadm D' A' G' hG' U'
  have hpr : IsProper (pullback.snd G'.hom (jK W)) := by
    have := A'.isAb.proper
    haveI : IsIso U'.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U'.gen.hom))
    change IsProper ((Over.pullback (jK W)).obj G').hom
    rw [← Over.w U'.gen.hom]
    infer_instance
  have hL' : LBIso P'.L.L (P.L.L.pull β) := by rw [hP']; exact hL
  exact _root_.GlobalTheory.Mum.evenOn_of_local R W φ hφ G hG G' β hgp hpr P P' hL' hE X hQ

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianPartHomUniformisedGroups
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two


open GlobalTheory.EndData GlobalTheory.AbLaw in
theorem exists_hom_of_levels {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {I : Ideal R}
    (hC : IsAdicComplete I R) (Y Z : Over (Spec (CommRingCat.of R))) (sY : Smooth Y.hom) (sZ : Smooth Z.hom)
    (pY : IsProjBy Y.hom) (pZ : IsProjBy Z.hom) (s : Y ⟶ Z) (f : ∀ e, (thickObj R I e Y).left ⟶ Z.left)
    (hf : ∀ e, f e ≫ Z.hom = pullback.fst Y.hom (thick R I e) ≫ Y.hom)
    (hc : ∀ e, thickMap R I e Y ≫ f (e + 1) = f e) :
    ∃ g : Y ⟶ Z, ∀ e, pullback.fst Y.hom (thick R I e) ≫ g.left = f e := by
  have w₁ : (fst Y Z).left ≫ Y.hom = (Y ⊗ Z).hom := Over.w _
  have w₂ : (snd Y Z).left ≫ Z.hom = (Y ⊗ Z).hom := Over.w _
  have sm : Smooth (Y ⊗ Z).hom := by
    show Smooth (pullback.fst Y.hom Z.hom ≫ Y.hom)
    infer_instance
  let p : ∀ e, (thickObj R I e (Y ⊗ Z)).left ⟶ (thickObj R I e Y).left := fun e =>
    ((Over.pullback (thick R I e)).map (fst Y Z)).left
  have hp : ∀ e, p e ≫ pullback.fst Y.hom (thick R I e) = pullback.fst (Y ⊗ Z).hom (thick R I e) ≫ (fst Y Z).left :=
    fun e => map_fst e _
  let F : ∀ e, (thickObj R I e (Y ⊗ Z)).left ⟶ pullback Y.hom Z.hom := fun e =>
    pullback.lift (p e ≫ pullback.fst Y.hom (thick R I e)) (p e ≫ f e) (by
      rw [Category.assoc, Category.assoc, hf])
  have F₁ : ∀ e, F e ≫ pullback.fst _ _ = p e ≫ pullback.fst Y.hom (thick R I e) := fun e => pullback.lift_fst _ _ _
  have F₂ : ∀ e, F e ≫ pullback.snd _ _ = p e ≫ f e := fun e => pullback.lift_snd _ _ _
  have tp : ∀ e, thickMap R I e (Y ⊗ Z) ≫ p (e + 1) = p e ≫ thickMap R I e Y := fun e => trans_map e _
  obtain ⟨g, hg⟩ := EndAlg.exists_end_of_thickenings R I hC (Y ⊗ Z) sm (isProjBy_tensor R Y Z pY pZ) F
    (fun e => by
      show F e ≫ pullback.fst Y.hom Z.hom ≫ Y.hom = _
      rw [← Category.assoc, F₁, hp, Category.assoc, w₁])
    (fun e => by
      show (thickMap R I e (Y ⊗ Z) ≫ F (e + 1) : _ ⟶ pullback Y.hom Z.hom) = F e
      apply pullback.hom_ext
      · rw [Category.assoc, F₁, F₁, ← Category.assoc, tp, Category.assoc, trans_fst]
      · rw [Category.assoc, F₂, F₂, ← Category.assoc, tp, Category.assoc, hc])
  refine ⟨lift (𝟙 Y) s ≫ g ≫ snd Y Z, fun e => ?_⟩
  have hj : ((Over.pullback (thick R I e)).map (lift (𝟙 Y) s)).left ≫ p e = 𝟙 _ := by
    show ((Over.pullback (thick R I e)).map (lift (𝟙 Y) s) ≫ (Over.pullback (thick R I e)).map (fst Y Z)).left = _
    rw [← Functor.map_comp, lift_fst, CategoryTheory.Functor.map_id]
    rfl
  have k : F e ≫ (snd Y Z).left = p e ≫ f e := F₂ e
  rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← map_fst, Category.assoc,
    ← Category.assoc (pullback.fst _ _), hg]
  erw [k]
  rw [← Category.assoc]
  erw [hj]
  exact Category.id_comp _


open GlobalTheory.EndTorus in
theorem exists_abelian_level {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I)
    {D₁ D₂ : DegPre R} {e : ℕ} {G₁ G₂ : Over (Spec (CommRingCat.of R))} [GrpObj G₁] [IsCommMonObj G₁]
    [GrpObj G₂] [IsCommMonObj G₂] (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : thickObj R I e G₁ ⟶ thickObj R I e G₂) [IsMonHom a] :
    ∃ b : thickObj R I e D₁.P.A ⟶ thickObj R I e D₂.P.A, IsMonHom b ∧ g₁.q ≫ b = a ≫ g₂.q := by
  obtain ⟨hN, -, -, hC⟩ := hR
  have := g₁.q_hom
  have := g₂.q_hom
  have := g₁.i_hom
  have := g₁.q_flat
  have := g₁.q_surj
  have := g₁.q_affine
  have : IsProper D₂.P.A.hom := D₂.P.isAb.proper
  have hB : IsAbelianScheme (thickObj R I e D₂.P.A) :=
    { comm := inferInstance
      smooth := by have := D₂.P.isAb.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := D₂.P.isAb.geomConnected
        show GeometricallyConnected (pullback.snd _ _)
        infer_instance }
  have h1 : g₁.i ≫ a ≫ g₂.q = toUnit _ ≫ η[thickObj R I e D₂.P.A] :=
    (splitTorus_hom_abelian_eq_one _ D₁.X _ hB (g₁.i ≫ a ≫ g₂.q) inferInstance).trans (Hom.one_def)
  exact FlatQuotient.exists_desc g₁.q g₁.i (a ≫ g₂.q) g₁.isKernel h1


open GlobalTheory.EndData in
theorem exists_abelian_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), IsMonHom a → ∃ b : D₁.toPre.P.A ⟶ D₂.toPre.P.A, IsMonHom b ∧ Over₀ U₁ U₂ a b := by
  intro R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a ha
  have hN := hR.1
  have hC := hR.2.2.2
  choose b hb hq using fun e => exists_abelian_level hR (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map a)
  have hql : ∀ e, (U₁.gt e).q.left ≫ (b e).left = ((Over.pullback (thick R I e)).map a).left ≫ (U₂.gt e).q.left :=
    fun e => congrArg (·.left) (hq e)
  obtain ⟨aB, haB⟩ := exists_hom_of_levels hC D₁.toPre.P.A D₂.toPre.P.A D₁.toPre.P.isAb.smooth
    D₂.toPre.P.isAb.smooth (AbProj.isProjBy_of_isPullback D₁.toPre.P (IsPullback.id_horiz _))
    (AbProj.isProjBy_of_isPullback D₂.toPre.P (IsPullback.id_horiz _)) 1
    (fun e => (b e).left ≫ pullback.fst D₂.toPre.P.A.hom (thick R I e))
    (fun e => by
      have w : (b e).left ≫ pullback.snd D₂.toPre.P.A.hom (thick R I e) = pullback.snd _ _ := Over.w (b e)
      rw [Category.assoc, pullback.condition, ← Category.assoc, w, pullback.condition])
    (fun e => by
      have := (U₁.gt e).q_flat
      have := (U₁.gt e).q_surj
      have : Epi (U₁.gt e).q.left := Flat.epi_of_flat_of_surjective _
      rw [← cancel_epi (U₁.gt e).q.left, ← Category.assoc, ← UnifCompare.trans_comp_q, Category.assoc,
        ← Category.assoc (U₁.gt (e + 1)).q.left, hql, ← Category.assoc (U₁.gt e).q.left, hql, ← Category.assoc,
        ← Category.assoc, trans_map, Category.assoc _ (thickMap R I e G₂), UnifCompare.trans_comp_q,
        Category.assoc, Category.assoc, trans_fst, Category.assoc])
  have hm : ∀ e, (Over.pullback (thick R I e)).map aB = b e := fun e =>
    Over.OverMorphism.ext (pullback.hom_ext ((map_fst e aB).trans (haB e)) ((Over.w _).trans (Over.w (b e)).symm))
  refine ⟨aB, AbelianPartIso.isMonHom_of_thickenings (IsAdicComplete.le_jacobson_bot I) D₂.toPre.P.isAb
    D₁.toPre.P.isAb aB fun e => ?_, fun e => ?_⟩
  · rw [hm]; exact hb e
  · rw [hm]; exact (hq e).symm

end GlobalTheory.Mum.Two
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianVarietyOfHalvedPeriodMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HalvedPeriod

open GlobalTheory.CechPic GlobalTheory.Models GlobalTheory.ZM

theorem exists_abelian_of_isPeriod : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D' : PLat O bar) (Q : D'.La →+ (Fin g → ℂ)) (E₁ : LinearMap.BilinForm ℤ D'.La), IsPeriod D' ρ Q → D'.EF = (2 : ℤ) • E₁ → ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (_ : IsCommMonObj A) (act : OActN O A) (P : LB (G2 A).left) (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left) ∧ Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) ∧ IsExp (𝟙 (Sp ℂ)) e ∧ (∀ z, e z = 1 ↔ z ∈ Q.range) ∧ (∀ (a : O) z, e (ρ a *ᵥ z) = e z ≫ act.act a) ∧ (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) := by
  intro O _ bar g ρ D' Q E₁ hP hE
  obtain ⟨hlin, -, hdisc, hspan, Hm, hHm, hpos, him⟩ := hP
  let Λ : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Q.range
  have hmem : ∀ z, z ∈ Λ ↔ z ∈ Q.range := fun z => Iff.rfl
  have hΛd : DiscreteTopology Λ := hdisc
  have hΛs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ := by
    have e : (Λ : Set (Fin g → ℂ)) = Set.range Q := by
      ext z; exact AddMonoidHom.mem_range
    rw [e]; exact hspan
  let H₁ : Matrix (Fin g) (Fin g) ℂ := (2⁻¹ : ℂ) • Hm
  have hH₁ : H₁.IsHermitian := by
    unfold Matrix.IsHermitian at hHm ⊢
    simp only [H₁, Matrix.conjTranspose_smul, hHm, star_inv₀, star_ofNat]
  have hH₁v : ∀ z w : Fin g → ℂ, z ⬝ᵥ H₁ *ᵥ star w = 2⁻¹ * hermForm Hm z w := fun z w => by
    simp only [H₁, hermForm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hH₁pos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁ *ᵥ star z).re := fun z hz => by
    rw [hH₁v]
    have := hpos z hz
    have h2 : (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [h2, Complex.re_ofReal_mul]
    positivity
  have hH₁int : ∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ H₁ *ᵥ star l').im = n := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    refine ⟨E₁ x y, ?_⟩
    have h := him x y
    rw [hE] at h
    rw [hH₁v]
    have h2 : (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [h2, Complex.im_ofReal_mul, h]
    simp
  obtain ⟨A, _, hA, hdim, M, u, χ, hM, hu, hAH⟩ :=
    GlobalTheory.riemann_polarised_torus g Λ H₁ hΛd hΛs hH₁ hH₁pos hH₁int
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.proper
  have hker : ∀ z, u.ex z = 1 ↔ z ∈ Q.range := fun z => (u.ker z).trans (hu z)
  obtain ⟨u', χ', hex, hF'⟩ := GlobalTheory.TorusRM.exists_isFactorAH_lam_diag g A hA M u H₁ χ hM
    (GlobalTheory.TorusRM.isFactorAH_of_isAH hAH)
  have h2H : (2 : ℂ) • H₁ = Hm := by simp only [H₁, smul_smul]; norm_num
  rw [h2H] at hF'
  have hAH' : u'.IsAH Hm χ' := GlobalTheory.TorusRM.isAH_of_isFactorAH hF' (fun z hz => hpos z hz)
  have hker' : ∀ z, z ∈ u'.Λ ↔ z ∈ Q.range := fun z => by rw [← u'.ker, hex, hker]
  have hPLB := GlobalTheory.FullSiegel.isLB_lam hM
  have hΔLB := pull_isLB hPLB (lift (𝟙 A) (𝟙 A)).left

  have hid : IsGrpPullback A A (𝟙 _) (𝟙 A.left) :=
    @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl A) (inferInstanceAs (IsMonHom (𝟙 A)))
  have htb := GlobalTheory.TorusTransfer.tangent_bijective u hdim
  have hexp : IsExp (𝟙 (Sp ℂ)) u.ex :=
    GlobalTheory.PointUnif.isExp_push hid u htb.1 htb.2 (MulEquiv.refl _) (fun x => (Category.comp_id _).symm)

  have hρΛ : ∀ a, ∀ x ∈ u.Λ, Matrix.mulVecLin (ρ a) x ∈ u.Λ := by
    intro a x hx
    rw [hu, hmem] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    exact ⟨a • y, by rw [Matrix.mulVecLin_apply, hlin]⟩
  choose ψ hψ hlift using fun a =>
    GlobalTheory.HolUnifEnd.exists_isMonHom_of_map_lattice A g hA hdim M u (Matrix.mulVecLin (ρ a)) (hρΛ a)
  haveI : IsReduced A.left := isReduced_of_smooth_complex _ A.hom hA.smooth
  have hext : ∀ f f' : A ⟶ A, (∀ z, u.ex z ≫ f = u.ex z ≫ f') → f = f' := fun f f' h =>
    GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints fun x => by
      obtain ⟨z, rfl⟩ := u.ex_onto x
      exact h z
  let act : OActN O A :=
    { act := ψ
      hom := hψ
      one := hext _ _ fun z => by
        rw [← hlift, map_one, Matrix.mulVecLin_one, LinearMap.id_apply, Category.comp_id]
      mul := fun a b => hext _ _ fun z => by
        rw [← hlift, ← Category.assoc, ← hlift, ← hlift]
        congr 1
        simp only [Matrix.mulVecLin_apply, map_mul, Matrix.mulVec_mulVec]
      add := fun a b => hext _ _ fun z => by
        rw [← hlift, comp_mul, ← hlift, ← hlift, ← u.ex_add]
        congr 1
        simp [Matrix.add_mulVec] }
  refine ⟨A, inferInstance, inferInstance, act, abelian₂ A M, u.ex, hA, hdim, hPLB, ?_, ?_, GlobalTheory.FullSiegel.lam_symm hM,
    GlobalTheory.LefschetzAmple.relAmple_of_isAH g A hA _ u' Hm χ' hΔLB hAH', hexp, hker, fun a z => ?_, ?_⟩
  · exact (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hPLB _)).1
      ((GlobalTheory.FullSiegel.cls_lam_pull hM _ _).trans (lam_one_left _ _))
  · exact (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hPLB _)).1
      ((GlobalTheory.FullSiegel.cls_lam_pull hM _ _).trans (lam_one_right _ _))
  · rw [← Matrix.mulVecLin_apply]; exact hlift a z
  · intro k a b c hk hc
    have h := GlobalTheory.AHWeilAny.weilIs_exp_riemannForm A hA _ hΔLB g u' Hm χ' hAH' k (Q a) (Q b) c hk
      ((hker' _).2 ⟨a, rfl⟩) ((hker' _).2 ⟨b, rfl⟩) (by
        rw [hc]
        have e : (Q a ⬝ᵥ Hm *ᵥ star (Q b)).im = (D'.EF a b : ℝ) := him a b
        rw [e]; push_cast; rfl)
    rw [hex] at h
    exact h

end GlobalTheory.HalvedPeriod
end
end

