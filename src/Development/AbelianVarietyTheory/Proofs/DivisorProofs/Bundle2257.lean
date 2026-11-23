module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1328
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteGaloisDescentPrincipalPolarisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumDescent

theorem qc_qs_tensor {S : Scheme.{0}} (A : Over S) [IsProper A.hom] :
    QuasiCompact (A ⊗ A).hom ∧ QuasiSeparated (A ⊗ A).hom := by
  have e : (A ⊗ A).hom = pullback.fst A.hom A.hom ≫ A.hom := rfl
  rw [e]; exact ⟨inferInstance, inferInstance⟩

theorem exists_galois_polAV : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] (κ : (G2 ((Over.pullback (spMap (algebraMap K Ω))).obj A)).left ⟶ (G2 A).left), Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K Ω))) κ → ∀ L : LB ((Over.pullback (spMap (algebraMap K Ω))).obj A).left, L.IsLB → Out.Sym ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K Ω))).obj A) L) (PP.pull κ) → Out.RelAmple ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → Out.KTriv ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → ∃ (E : Type) (_ : Field E) (_ : Algebra K E), FiniteDimensional K E ∧ IsGalois K E ∧ ∃ (A₁ : PolAV (Sp E)) (gen : (Over.pullback (spMap (algebraMap K E))).obj A ≅ A₁.A), IsMonHom gen.hom ∧ ∀ κ : (G2 ((Over.pullback (spMap (algebraMap K E))).obj A)).left ⟶ (G2 A).left, Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K E))) κ → LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K E))).obj A) (A₁.L.pull gen.hom.left)) (PP.pull κ) := by
  intro K _ _ A _ _ hA PP hPP Ω _ _ _ _ κ hκ L hL hS hΛ hAmp hKT
  haveI := hA.proper
  haveI := hA.smooth
  let σΩ : K →+* Ω := algebraMap K Ω
  let AΩ := (Over.pullback (spMap σΩ)).obj A
  have hAΩ : IsAbelianScheme AΩ := isAbelianScheme_pullback_obj _ A hA
  have hpΩ : IsGrpPullback AΩ A (spMap σΩ) (pullback.fst A.hom (spMap σΩ)) := isGrpPullback_pullback A _

  obtain ⟨F, hF, H⟩ := GlobalTheory.LBDescent.exists_finite_subextension_cls K Ω A.left AΩ.left A.hom AΩ.hom
    (pullback.fst A.hom (spMap σΩ)) hpΩ.1 L hL
  let f : Sp F ⟶ Sp K := spMap (algebraMap K F)
  let AF := (Over.pullback f).obj A
  have hAF : IsAbelianScheme AF := isAbelianScheme_pullback_obj f A hA
  have hpF : IsGrpPullback AF A f (pullback.fst A.hom f) := isGrpPullback_pullback A f
  have hcomp : spMap (algebraMap F Ω) ≫ f = spMap σΩ := by
    simp only [f, σΩ, spMap]
    rw [← Spec.map_comp]
    congr 1
  have w : pullback.fst A.hom (spMap σΩ) ≫ A.hom = (AΩ.hom ≫ spMap (algebraMap F Ω)) ≫ f := by
    rw [Category.assoc, hcomp]
    exact hpΩ.1.w
  let jm : AΩ.left ⟶ AF.left := pullback.lift (pullback.fst A.hom (spMap σΩ)) (AΩ.hom ≫ spMap (algebraMap F Ω)) w
  have hjf : jm ≫ pullback.fst A.hom f = pullback.fst A.hom (spMap σΩ) := pullback.lift_fst _ _ _
  have hjs : jm ≫ AF.hom = AΩ.hom ≫ spMap (algebraMap F Ω) := pullback.lift_snd _ _ _
  have hj : IsGrpPullback AΩ AF (spMap (algebraMap F Ω)) jm :=
    IsGrpPullback.cancel hpF (hpΩ.congr hcomp.symm hjf.symm) hjs
  obtain ⟨x, hx⟩ := H AF.left AF.hom (pullback.fst A.hom f) (IsPullback.of_hasPullback _ _) jm hjf hjs
  obtain ⟨L₁, hL₁, rfl⟩ := CechPic.cls_surj x
  have hw : LBIso L (L₁.pull jm) := by
    rw [← CechPic.cls_eq_iff hL (pull_isLB hL₁ jm), CechPic.cls_pull hL₁ jm (pull_isLB hL₁ jm)]
    exact hx.symm

  have hPPlb : PP.IsLB := hPP
  obtain ⟨κF, hκF⟩ : ∃ κF : (G2 AF).left ⟶ (G2 A).left, IsSquare (pullback.fst A.hom f) κF :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare hpF.1.w⟩
  obtain ⟨jm₂, hjm₂⟩ : ∃ jm₂ : (G2 AΩ).left ⟶ (G2 AF).left, IsSquare jm jm₂ :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare hj.1.w⟩
  have hΛF : (abelian₂ AF L₁).IsLB := DVR.linComb_isLB _ hL₁ _ _
  have hΛΩ : (abelian₂ AΩ L).IsLB := DVR.linComb_isLB _ hL _ _
  have hNF : (PP.pull κF).IsLB := pull_isLB hPPlb κF
  have eΩ : κ = jm₂ ≫ κF := by
    have h := GlobalTheory.ZM.SiegPull.isSquare_comp hjm₂ hκF
    rw [hjf] at h
    exact GlobalTheory.LamPull.isSquare_unique hκ h
  have isoΩ : LBIso ((abelian₂ AF L₁).pull jm₂) ((PP.pull κF).pull jm₂) :=
    LBIso.trans (pull_isLB hΛF _) hΛΩ (pull_isLB hNF _)
      (GlobalTheory.LamPull.lbIso_lam_pull hj hL₁ hL hw hjm₂).symm
      (LBIso.trans hΛΩ (pull_isLB hPPlb _) (pull_isLB hNF _) hΛ
        (GlobalTheory.ArcDataDescent.lbIso_pull_pull hPPlb κF jm₂ eΩ).symm)
  haveI := hAF.proper
  haveI := hAF.smooth
  have hqq := qc_qs_tensor AF
  obtain ⟨s, hs⟩ := GlobalTheory.lbIso_descends_to_subfield_containing_finset F Ω (algebraMap F Ω) (G2 AF) (G2 AΩ) jm₂
    (abelian₂ AF L₁) (PP.pull κF) (GlobalTheory.SiegelDescent.isPullback_square hj.1 jm₂ hjm₂) hqq.1 hqq.2 hΛF hNF isoΩ

  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  let F' : IntermediateField K Ω := F ⊔ IntermediateField.adjoin K (s : Set Ω)
  haveI : FiniteDimensional K (IntermediateField.adjoin K (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin fun y _ => (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  haveI : FiniteDimensional K F' := IntermediateField.finiteDimensional_sup _ _
  let E : IntermediateField K Ω := IntermediateField.normalClosure K F' Ω
  haveI hEf : FiniteDimensional K E := normalClosure.is_finiteDimensional K F' Ω
  haveI hEg : IsGalois K E := by
    haveI : Normal K E := inferInstance
    exact IsGalois.mk
  have hFE : F ≤ E := le_sup_left.trans F'.le_normalClosure
  have hsE : (s : Set Ω) ⊆ E := fun y hy =>
    F'.le_normalClosure (le_sup_right (a := F) (IntermediateField.subset_adjoin K _ hy))
  let α : F →+* E := (IntermediateField.inclusion hFE).toRingHom
  let e : Sp E ⟶ Sp K := spMap (algebraMap K E)
  let AE := (Over.pullback e).obj A
  have hAE : IsAbelianScheme AE := isAbelianScheme_pullback_obj e A hA
  have hpE : IsGrpPullback AE A e (pullback.fst A.hom e) := isGrpPullback_pullback A e
  have hcα : spMap α ≫ f = e := by
    simp only [f, e, α, spMap]
    rw [← Spec.map_comp]
    congr 1
  have wE : pullback.fst A.hom e ≫ A.hom = (AE.hom ≫ spMap α) ≫ f := by
    rw [Category.assoc, hcα]
    exact hpE.1.w
  let χ : AE.left ⟶ AF.left := pullback.lift (pullback.fst A.hom e) (AE.hom ≫ spMap α) wE
  have hχf : χ ≫ pullback.fst A.hom f = pullback.fst A.hom e := pullback.lift_fst _ _ _
  have hχs : χ ≫ AF.hom = AE.hom ≫ spMap α := pullback.lift_snd _ _ _
  have hχ : IsGrpPullback AE AF (spMap α) χ := IsGrpPullback.cancel hpF (hpE.congr hcα.symm hχf.symm) hχs
  obtain ⟨χ₂, hχ₂⟩ : ∃ χ₂ : (G2 AE).left ⟶ (G2 AF).left, IsSquare χ χ₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hχ.1.w⟩
  have isoE : LBIso ((abelian₂ AF L₁).pull χ₂) ((PP.pull κF).pull χ₂) :=
    hs E α (algebraMap E Ω) (RingHom.ext fun _ => rfl) (fun y hy => ⟨⟨y, hsE hy⟩, rfl⟩) (G2 AE) χ₂
      (GlobalTheory.SiegelDescent.isPullback_square hχ.1 χ₂ hχ₂)

  let LE : LB AE.left := L₁.pull χ
  have hLE : LE.IsLB := pull_isLB hL₁ χ
  have hcE : spMap (algebraMap E Ω) ≫ e = spMap σΩ := by
    simp only [e, σΩ, spMap]
    rw [← Spec.map_comp]
    congr 1
  have wΩ : pullback.fst A.hom (spMap σΩ) ≫ A.hom = (AΩ.hom ≫ spMap (algebraMap E Ω)) ≫ e := by
    rw [Category.assoc, hcE]
    exact hpΩ.1.w
  let jE : AΩ.left ⟶ AE.left := pullback.lift (pullback.fst A.hom (spMap σΩ)) (AΩ.hom ≫ spMap (algebraMap E Ω)) wΩ
  have hjEf : jE ≫ pullback.fst A.hom e = pullback.fst A.hom (spMap σΩ) := pullback.lift_fst _ _ _
  have hjEs : jE ≫ AE.hom = AΩ.hom ≫ spMap (algebraMap E Ω) := pullback.lift_snd _ _ _
  have hjE : IsGrpPullback AΩ AE (spMap (algebraMap E Ω)) jE :=
    IsGrpPullback.cancel hpE (hpΩ.congr hcE.symm hjEf.symm) hjEs
  have hαΩ : spMap (algebraMap E Ω) ≫ spMap α = spMap (algebraMap F Ω) := by
    simp only [α, spMap]
    rw [← Spec.map_comp]
    congr 1
  have ejm : jm = jE ≫ χ := by
    apply pullback.hom_ext
    · rw [hjf, Category.assoc, hχf, hjEf]
    · show jm ≫ AF.hom = (jE ≫ χ) ≫ AF.hom
      rw [hjs, Category.assoc, hχs, ← Category.assoc, hjEs, Category.assoc, hαΩ]
  have hwE : LBIso L (LE.pull jE) :=
    LBIso.trans hL (pull_isLB hL₁ jm) (pull_isLB hLE jE) hw
      (GlobalTheory.ArcDataDescent.lbIso_pull_pull hL₁ χ jE ejm).symm
  have hd := GlobalTheory.PolDescent.rigidified_sym_kTriv_descend E Ω (algebraMap E Ω) AE AΩ jE LE L hAE hjE hLE hL hwE
  haveI := hAE.proper
  haveI := hAE.smooth
  have ha := GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension E Ω (algebraMap E Ω) AE AΩ jE hjE LE L hLE hL
    hwE hAΩ.proper hAmp hKT
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim E AE hAE
  have hrig : Out.Rigidified AE LE := by
    have : Subsingleton (𝟙_ (Over (Sp E))).left := inferInstanceAs (Subsingleton (PrimeSpectrum E))
    exact GlobalTheory.PolDescent.exists_gen_of_unique (default : PrimeSpectrum E) (pull_isLB hLE _)
  let A₁ : Out.PolAV (Sp E) :=
    { A := AE, isAb := hAE, g := g, smoothDim := hg, L := LE, isLB := hLE, rigid := hrig,
      sym := hd.2.1 hS, ample := ha.2.1, ktriv := ha.2.2 }
  refine ⟨E, inferInstance, inferInstance, hEf, hEg, A₁, Iso.refl _, ?_, fun κ' hκ' => ?_⟩
  · show IsMonHom (𝟙 AE); infer_instance
  have e' : κ' = χ₂ ≫ κF := by
    have h := GlobalTheory.ZM.SiegPull.isSquare_comp hχ₂ hκF
    rw [hχf] at h
    exact GlobalTheory.LamPull.isSquare_unique hκ' h
  have hLE' : (LE.pull (𝟙 AE.left)).IsLB := pull_isLB hLE _
  have k₁ : LBIso (abelian₂ AE (LE.pull (𝟙 AE.left))) ((abelian₂ AF L₁).pull χ₂) :=
    GlobalTheory.LamPull.lbIso_lam_pull hχ hL₁ hLE' (GlobalTheory.ArcDataDescent.lbIso_pull_pull hL₁ χ (𝟙 _) (Category.id_comp χ).symm) hχ₂
  have k₂ : LBIso ((PP.pull κF).pull χ₂) (PP.pull κ') := GlobalTheory.ArcDataDescent.lbIso_pull_pull hPPlb κF χ₂ e'
  exact LBIso.trans (DVR.linComb_isLB _ hLE' _ _) (pull_isLB hΛF _) (pull_isLB hPPlb _) k₁
    (LBIso.trans (pull_isLB hΛF _) (pull_isLB hNF _) (pull_isLB hPPlb _) isoE k₂)

end GlobalTheory.MumDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatProjectiveModelOverRingOfIntegers
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SpreadModel

open TopologicalSpace

theorem gen_specializes {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {p : X ⟶ Sp O} {j : Y ⟶ X} {q : Y ⟶ Sp K}
    (H : IsPullback j q p (spMap (algebraMap O K))) : j (genericPoint Y) ⤳ genericPoint X := by
  have hp (y : Y) : (p (j y)).asIdeal = ⊥ := by
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
    change Ideal.comap (algebraMap O K) (q y).asIdeal = ⊥
    rw [(Ideal.eq_bot_or_top _).resolve_right (q y).2.ne_top]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)
  have hx : (p (genericPoint X)).asIdeal = ⊥ :=
    eq_bot_iff.2 (((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2
      ((genericPoint_specializes (j (genericPoint Y))).map p.continuous))).trans (hp _).le)
  have hr : genericPoint X ∈ Set.range j := by
    rw [← H.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, H.isoPullback.hom.surjective.range_eq, Set.image_univ,
      Scheme.Pullback.range_fst]
    refine ⟨IsLocalRing.closedPoint K, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
    change Ideal.comap (algebraMap O K) (IsLocalRing.maximalIdeal K) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)
  obtain ⟨y, hy⟩ := hr
  exact hy ▸ (genericPoint_specializes y).map j.continuous

theorem app_algX {k k' : Type} [CommRing k] [CommRing k'] {σ : k →+* k'} {X Y : Scheme.{0}} {p : X ⟶ Sp k}
    {q : Y ⟶ Sp k'} {j : Y ⟶ X} (w : j ≫ p = q ≫ spMap σ) (a : k) :
    j.app ⊤ (algX p ⊤ a) = algX q ⊤ (σ a) := by
  have e₁ : j.app ⊤ (algX p ⊤ a) = algX (j ≫ p) ⊤ a := by
    simp only [algX, RingHom.comp_apply, Scheme.Hom.app_eq_appLE,
      ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    simp only [Opens.map_top]
    rfl
  rw [e₁, w]
  have e₂ := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e₂
  simp only [algX, RingHom.comp_apply]
  rw [e₂]
  simp [Scheme.Hom.appLE]
  rfl

theorem exists_spread : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (D m : ℕ) (y : Fin (m + 1) → Ω) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp K) (B : LB Y) (_ : B.IsLB) (t : Fin (m + 1) → B.Sec) (ψ : Ω →+* Y.functionField),
    IsProjOver q → topologicalKrullDim Y = D → (⨆ k, nonzeroLocus (t k) = ⊤) → Function.Bijective ψ →
    (∀ a : K, ψ (algebraMap K Ω a) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX q ⊤ a)) →
    (∀ (k l : Fin (m + 1)) (i : B.ι) (h : genericPoint Y ∈ B.U i), ψ (y k) * fnOf _ h ((t l).f i) = ψ (y l) * fnOf _ h ((t k).f i)) →
    ∃ (X : Scheme.{0}) (_ : IsIntegral X) (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (ψ' : Ω →+* X.functionField),
      g ≫ PSpace.str (𝓞 K) m = p ∧ IsArithVar p D ∧ Function.Bijective ψ' ∧
      (∀ a : 𝓞 K, ψ' (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ' (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) =
          ψ' (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i) := by
  intro K Ω _ _ _ _ D m y Y _ q B hB t ψ hq hD ht hψ hK hy
  let c := q ≫ spMap (algebraMap (𝓞 K) K)
  obtain ⟨X, π, j, hX, hπ, hfl, H, hg⟩ := IntModel.exists_flat_model (O := 𝓞 K) q hq
    (fun _ : Unit => PSpace (𝓞 K) m) (fun _ => PSpace.str (𝓞 K) m) (fun _ => ProjSpace.toProj c t ht)
    (fun _ => ⟨m, 𝟙 _, inferInstance, Category.id_comp _⟩) (fun _ => ProjSpace.toProj_str c t ht)
  obtain ⟨g, hg₁, hg₂⟩ := hg ()
  have := CommonModel.isProper_of_isProjOver hπ
  have hZ : Flat (spMap (Int.castRingHom (𝓞 K))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (RingHom.flat_algebraMap_iff (R := ℤ) (S := 𝓞 K)).2 inferInstance
  have har : IsArithVar π D := ⟨inferInstance, inferInstance, hX, hπ, inferInstance,
    IntModel.topologicalKrullDim_eq_succ (RingOfIntegers.not_isField K) H hD⟩
  have hη := gen_specializes H
  have hpre : IsPreimmersion j :=
    have := IsPreimmersion.of_isLocalization (R := 𝓞 K) (S := K) (nonZeroDivisors (𝓞 K))
    MorphismProperty.of_isPullback H.flip this
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (SmallSec.fnMap j hη)
    ⟨(SmallSec.fnMap j hη).injective, SmallSec.fnMap_surjective j hη⟩
  have he (u) : e u = SmallSec.fnMap j hη u := rfl
  have he' (a : Ω) : e ((e.symm.toRingHom.comp ψ) a) = ψ a := e.apply_symm_apply _
  refine ⟨X, hX, π, g, e.symm.toRingHom.comp ψ, hg₂, har, e.symm.bijective.comp hψ, fun a => ?_, fun k l i h => ?_⟩
  · apply e.injective
    rw [he', hK, he, SmallSec.fnMap_fnOf j hη _ (Opens.mem_top _), app_algX H.w]
    rfl
  · apply e.injective
    have h' : genericPoint Y ∈ j ⁻¹ᵁ ((ProjSpace.O1 (𝓞 K) m).pull g).U i := hη.mem_open (Opens.isOpen _) h
    have hU₀ : j ⁻¹ᵁ ((ProjSpace.O1 (𝓞 K) m).pull g).U i ≤ (j ≫ g) ⁻¹ᵁ ProjSpace.chart (𝓞 K) m (i PUnit.unit) :=
      fun x hx => (pull_U _ g i).le hx
    have hU : j ⁻¹ᵁ ((ProjSpace.O1 (𝓞 K) m).pull g).U i ≤
        ProjSpace.toProj c t ht ⁻¹ᵁ ProjSpace.chart (𝓞 K) m (i PUnit.unit) := hg₁ ▸ hU₀
    have hf (a) : j.app _ ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) g).f i) =
        ProjSpace.pullRatio (ProjSpace.toProj c t ht) _ (i PUnit.unit) hU a := by
      refine Eq.trans ?_ (ProjSpace.pullRatio_of_eq hg₁ hU₀ _)
      rw [Scheme.Hom.app_eq_appLE]
      exact congrArg (fun ψ => ψ.hom (ProjSpace.ratio (𝓞 K) m (i PUnit.unit) a))
        (Scheme.Hom.appLE_comp_appLE j g _ _ _ (pull_U _ g i).le le_rfl)
    obtain ⟨n, hn⟩ := exists_chart hB (genericPoint Y)
    have key (a) := congrArg (fnOf _ (memInf h' hn)) (ProjSpace.sec_eq_pullRatio_toProj_mul c t ht (i PUnit.unit) a n
      (W := _ ⊓ B.U n) (inf_le_left.trans hU) inf_le_right)
    have hne : fnOf _ hn ((t (i PUnit.unit)).f n) ≠ 0 := by
      have hu := (ProjSpace.isUnit_resG_sec (t (i PUnit.unit)) n (W := _ ⊓ B.U n)
        (inf_le_left.trans (hU.trans (ProjSpace.toProj_preimage_chart c t ht _).le)) inf_le_right).map
          (fnOf _ (memInf h' hn))
      rw [fnOf_resG] at hu
      exact hu.ne_zero
    have key' (a) : fnOf _ hn ((t a).f n) = e (fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) g).f i)) *
        fnOf _ hn ((t (i PUnit.unit)).f n) := by
      have e₁ := key a
      rw [map_mul, fnOf_resG, fnOf_resG, ← ProjSpace.resG_pullRatio (hi := hU) inf_le_left, fnOf_resG] at e₁
      rw [he, SmallSec.fnMap_fnOf j hη h h', hf]
      exact e₁
    have h₀ := hy k l n hn
    rw [key' k, key' l, ← mul_assoc, ← mul_assoc] at h₀
    rw [map_mul, map_mul, he', he']
    exact mul_right_cancel₀ hne h₀

end GlobalTheory.SpreadModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormsMapOfDividedPowerDerivation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section Lift

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)

theorem rel_isTwoSided (h : ∀ x ∈ rel R δ, ∀ y, x * y ∈ rel R δ) : (rel R δ).IsTwoSided :=
  ⟨fun b ha ↦ h _ ha b⟩

variable [(rel R δ).IsTwoSided]

def kq : K1 R δ →ₗ[B] DR R B ⧸ rel R δ :=
  (N1 R δ).liftQ ((Ideal.Quotient.mkₐ B (rel R δ)).toLinearMap ∘ₗ ι1) fun x hx ↦ by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hx

theorem kq_mk (ω : Ω[B⁄R]) : kq δ (Submodule.Quotient.mk ω) = Ideal.Quotient.mk (rel R δ) (ι1 ω) := rfl

end Lift

theorem exists_lift_of_pdDerivation (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B)
    (δ : DividedPowers J) (C : Type) [CommRing C] [Algebra R C] (JC : Ideal C) (δC : DividedPowers JC)
    (π : C →ₐ[R] B) (w : C →+ K1 R δ) (hw : ∀ x y, w (x * y) = π x • w y + π y • w x)
    (hw0 : ∀ r, w (algebraMap R C r) = 0)
    (hwd : ∀ n, ∀ a ∈ JC, w (δC.dpow (n + 1) a) = π (δC.dpow n a) • w a) :
    ∃ ρ : DR R C → DR R B, (∀ x y, ρ (x + y) - ρ x - ρ y ∈ rel R δ) ∧ (∀ x y, ρ (x * y) - ρ x * ρ y ∈ rel R δ) ∧
      (∀ c, ρ (algebraMap C (DR R C) c) - algebraMap B (DR R B) (π c) ∈ rel R δ) ∧
      (∀ c ω, Submodule.Quotient.mk ω = w c → ρ (ι1 (D R C c)) - ι1 ω ∈ rel R δ) ∧
      (∀ x ∈ rel R δC, ρ x ∈ rel R δ) ∧ (∀ x, ∃ ω, ρ (ι1 x) - ι1 ω ∈ rel R δ) ∧
      ∀ (j : ℕ), ∀ x ∈ ⋀[C]^j Ω[C⁄R], ∃ y ∈ ⋀[B]^j Ω[B⁄R], ρ x - y ∈ rel R δ := by
  haveI : (rel R δ).IsTwoSided := rel_isTwoSided δ ((_root_.GlobalTheory.PDForm.rel_two_sided_and_bot.1 R B J δ).1)
  letI algC : Algebra C (DR R B ⧸ rel R δ) :=
    ((algebraMap B (DR R B ⧸ rel R δ)).comp (π : C →+* B)).toAlgebra' fun c x ↦ Algebra.commutes (π c) x
  haveI : IsScalarTower R C (DR R B ⧸ rel R δ) := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change _ = algebraMap B _ (π (algebraMap R C r))
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have smulC : ∀ (c : C) (q : DR R B ⧸ rel R δ), c • q = π c • q := fun c q ↦ by
    rw [Algebra.smul_def, Algebra.smul_def]; rfl
  let v : Derivation R C (DR R B ⧸ rel R δ) := Derivation.mk'
    { toFun := fun c ↦ kq δ (w c)
      map_add' := fun a b ↦ by simp
      map_smul' := fun r c ↦ by
        rw [RingHom.id_apply, Algebra.smul_def r c, hw, hw0, smul_zero, add_zero, map_smul, AlgHom.commutes,
          algebraMap_smul] }
    fun a b ↦ by
      change kq δ (w (a * b)) = a • kq δ (w b) + b • kq δ (w a)
      rw [hw, map_add (f := _), map_smul, map_smul, smulC, smulC]
  have hv : ∀ c, v c = kq δ (w c) := fun _ ↦ rfl
  have key : ∀ ω : Ω[C⁄R], ∃ η : Ω[B⁄R], v.liftKaehlerDifferential ω = Ideal.Quotient.mk (rel R δ) (ι1 η) := by
    intro ω
    induction ω using ind1 with
    | h b c =>
      obtain ⟨η, hη⟩ := Submodule.Quotient.mk_surjective _ (w c)
      refine ⟨π b • η, ?_⟩
      rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, hv, ← hη, kq_mk, smulC, map_smul,
        Algebra.smul_def (π b) (ι1 η), map_mul, Ideal.Quotient.mk_algebraMap, Algebra.smul_def]
    | h0 => exact ⟨0, by simp⟩
    | ha x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]⟩
  let Φ : DR R C →ₐ[C] DR R B ⧸ rel R δ := ExteriorAlgebra.lift C ⟨v.liftKaehlerDifferential, fun m ↦ by
    obtain ⟨η, h⟩ := key m
    rw [h, ← map_mul, ExteriorAlgebra.ι_sq_zero, map_zero]⟩
  have hΦι : ∀ ω : Ω[C⁄R], Φ (ι1 ω) = v.liftKaehlerDifferential ω := fun ω ↦ ExteriorAlgebra.lift_ι_apply _ _ _ _
  have hΦD : ∀ c, Φ (ι1 (D R C c)) = kq δ (w c) := fun c ↦ by
    rw [hΦι, Derivation.liftKaehlerDifferential_comp_D, hv]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : DR R C → DR R B, ∀ x, Ideal.Quotient.mk (rel R δ) (ρ x) = Φ x :=
    ⟨_, fun x ↦ Function.surjInv_eq Ideal.Quotient.mk_surjective (Φ x)⟩
  have cv : ∀ x a, ρ x - a ∈ rel R δ ↔ Φ x = Ideal.Quotient.mk (rel R δ) a := fun x a ↦ by
    rw [← Ideal.Quotient.eq, hρ]
  refine ⟨ρ, fun x y ↦ ?_, fun x y ↦ ?_, fun c ↦ ?_, fun c ω h ↦ ?_, fun x hx ↦ ?_, fun x ↦ ?_, fun j x hx ↦ ?_⟩
  · rw [sub_sub]
    exact (cv _ _).2 (by rw [map_add (f := _), map_add (f := _), hρ, hρ])
  · exact (cv _ _).2 (by rw [map_mul, map_mul, hρ, hρ])
  · exact (cv _ _).2 (by rw [AlgHom.commutes, Ideal.Quotient.mk_algebraMap]; rfl)
  · exact (cv _ _).2 (by rw [hΦD, ← h, kq_mk])
  · rw [← Ideal.Quotient.eq_zero_iff_mem, hρ]
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, a, ha, rfl⟩ := hx
      rw [map_sub, map_smul, map_sub, map_smul, hΦD, hΦD, hwd n a ha, map_smul, smulC, sub_self]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
    | smul r x _ ih => rw [smul_eq_mul, map_mul, ih, mul_zero]
  · obtain ⟨η, h⟩ := key x
    exact ⟨η, (cv _ _).2 (by rw [hΦι, h])⟩
  · induction hx using Submodule.pow_induction_on_left' with
    | algebraMap c =>
      refine ⟨algebraMap B _ (π c), ?_, (cv _ _).2 (by rw [AlgHom.commutes, Ideal.Quotient.mk_algebraMap]; rfl)⟩
      change _ ∈ LinearMap.range _ ^ 0
      rw [pow_zero]; exact Submodule.algebraMap_mem _
    | add x y i _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      exact ⟨a + b, add_mem ha hb, (cv _ _).2 (by rw [map_add (f := _), (cv _ _).1 ha', (cv _ _).1 hb', map_add (f := _)])⟩
    | mem_mul m hm i x hx ih =>
      obtain ⟨ω, rfl⟩ := hm
      obtain ⟨η, hη⟩ := key ω
      obtain ⟨y, hy, hy'⟩ := ih
      refine ⟨ι1 η * y, ?_, (cv _ _).2 ?_⟩
      · have := GlobalTheory.CechDR.mul_mem (ι_mem η) hy
        rwa [add_comm] at this
      · rw [map_mul, (cv _ _).1 hy', map_mul, ← hη, ← hΦι]

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOnSmallerOpenOfNonvanishingSectio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GenRestrict

theorem exists_gen_restrict : ∀ (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (O O' : Z.Opens), O ≤ O' →
    ∀ u : LB.Sec (L.pull O'.ι), (∀ z : O'.toScheme, O'.ι z ∈ O → z ∈ nonzeroLocus u) →
    ∃ t : LB.Gen (L.pull O.ι), t.IsGen := by
  intro Z L _ O O' hle u hu
  have e : ∀ _k : PUnit, Z.homOfLE hle ≫ (fun _ : PUnit => O'.ι) _k = (fun _ : PUnit => O.ι) _k :=
    fun _ => Scheme.homOfLE_ι Z hle
  let v : LB.Sec (L.pull O.ι) := PullbackSections.pullSecLC L _ _ _ (Z.homOfLE hle) e u
  refine GlobalTheory.LocusPull.exists_gen_of_nonzeroLocus_eq_top v (top_unique fun z _ => ?_)
  have heq : O'.ι (Z.homOfLE hle z) = O.ι z := by
    exact congrArg (fun f : O.toScheme ⟶ Z => f z) (Scheme.homOfLE_ι Z hle)
  have hz : O'.ι (Z.homOfLE hle z) ∈ O := by
    rw [heq]
    exact (Scheme.Opens.ι_apply O z).symm ▸ z.2
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hu _ hz)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
  show z ∈ O.toScheme.basicOpen ((Scheme.Hom.appLE (Z.homOfLE hle) _ _ _).hom (u.f k))
  rw [Scheme.basicOpen_appLE]
  refine ⟨?_, hk⟩
  have h1 : Z.homOfLE hle z ∈ (L.pull O'.ι).U k := Scheme.basicOpen_le _ _ hk
  refine mem_pull.2 ?_
  rw [← heq]
  exact mem_pull.1 h1

end GlobalTheory.GenRestrict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectMapOfCommonPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylorObjectMap_of_common_pullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₀ : Scheme.{0}) (A₀ : Over S₀) [GrpObj A₀] (P₀ : LB (G2 A₀).left), P₀.IsLB → ∀ (T Z : Scheme.{0}) (t₁ : T ⟶ Sp R) (t₂ : Z ⟶ Sp R) (o : Obj b N t₁) (u : Obj b N t₂) (g : T ⟶ S₀) (πZ : Z ⟶ S₀) (z : T ⟶ Z) (φo : o.A.left ⟶ A₀.left) (φ₂o : (G2 o.A).left ⟶ (G2 A₀).left) (φu : u.A.left ⟶ A₀.left) (φ₂u : (G2 u.A).left ⟶ (G2 A₀).left) (ψ : o.A.left ⟶ u.A.left), IsGrpPullback o.A A₀ g φo → IsSquare φo φ₂o → LBIso o.P (P₀.pull φ₂o) → IsGrpPullback u.A A₀ πZ φu → IsSquare φu φ₂u → LBIso u.P (P₀.pull φ₂u) → z ≫ πZ = g → ψ ≫ φu = φo → ψ ≫ u.A.hom = o.A.hom ≫ z → (∀ a : D.O, (o.act.act a).left ≫ ψ = ψ ≫ (u.act.act a).left) → (∀ y, (o.eta y).left ≫ ψ = z ≫ (u.eta y).left) → ∃ m : ObjMap o u z, m.φ = ψ := by
  first | (exact @GlobalTheory.HTObjMap.exists_objMap_of_common_pullback) | (exact GlobalTheory.HTObjMap.exists_objMap_of_common_pullback) | (intros; apply GlobalTheory.HTObjMap.exists_objMap_of_common_pullback  <;> assumption)
end

