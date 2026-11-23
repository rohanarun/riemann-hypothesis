module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelNormalisationDedekind
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc


set_option maxHeartbeats 1000000 in
theorem exists_ratModel_normalization : ∀ (A o Ω : Type) [CommRing A] [IsDedekindDomain A] [CommRing o] [Field Ω]
    [Algebra o Ω] [ArithBase o Ω] (κ : A →+* o), κ.Finite → ∀ (Z : Scheme.{0}) (z : Z ⟶ Sp A), LocallyOfFiniteType z →
    QuasiCompact z → IsSeparated z → ∀ p : Sp Ω ⟶ Z, p ≫ z = spMap ((algebraMap o Ω).comp κ) →
    (p.stalkMap (genericPoint (Sp Ω))).hom.Finite → ∃ (M : RatModel o Ω) (π : M.Z ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z ∧
    IsFinite π ∧ M.pt ≫ π = p := by
  intro A o Ω _ _ _ _ _ _ κ hκ Z z _ _ _ p hp hfin
  haveI : CharZero Ω := ArithBase.char (o := o)
  haveI : CharZero (Sp Ω).functionField :=
    charZero_of_injective_ringHom (((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫
      (Sp Ω).germToFunctionField ⊤).hom).injective
  haveI : IsFinite p.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_genericallyFinite (o := CommRingCat.of A) p z hfin
  haveI : GlobalTheory.IsNormalScheme p.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral p
  haveI : IsFinite (spMap κ) := by rw [IsFinite.SpecMap_iff]; exact hκ
  have hl : p ≫ z = spMap (algebraMap o Ω) ≫ spMap κ := by
    rw [hp, ← Spec.map_comp]; rfl
  let l : Sp Ω ⟶ pullback z (spMap κ) := pullback.lift p (spMap (algebraMap o Ω)) hl
  have hl1 : p = l ≫ pullback.fst z (spMap κ) := (pullback.lift_fst _ _ _).symm
  let d := p.normalizationDesc l (pullback.fst z (spMap κ)) hl1
  let s : p.normalization ⟶ Sp o := d ≫ pullback.snd z (spMap κ)
  have hs : s ≫ spMap κ = p.fromNormalization ≫ z := by
    simp only [s, d, Category.assoc, ← pullback.condition]
    rw [Scheme.Hom.normalizationDesc_comp_assoc]
  have hfz : LocallyOfFiniteType (s ≫ spMap κ) ∧ IsSeparated (s ≫ spMap κ) ∧ QuasiCompact (s ≫ spMap κ) := by
    rw [hs]; exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨h1, h2, h3⟩ := hfz
  have hpt_s : p.toNormalization ≫ s = spMap (algebraMap o Ω) := by
    simp only [s, d]
    rw [Scheme.Hom.toNormalization_normalizationDesc_assoc, pullback.lift_snd]
  have hgen : Set.range p.toNormalization = {genericPoint p.normalization} := by
    have hr : ∀ w : Sp Ω, w = IsLocalRing.closedPoint Ω := fun w => Subsingleton.elim _ _
    have hrng : Set.range p.toNormalization = {p.toNormalization (IsLocalRing.closedPoint Ω)} :=
      Set.ext fun y => ⟨fun ⟨w, hw⟩ => hw ▸ congrArg p.toNormalization (hr w),
        fun hy => ⟨_, hy.symm⟩⟩
    have : IsGenericPoint (p.toNormalization (IsLocalRing.closedPoint Ω)) (⊤ : Set p.normalization) := by
      rw [isGenericPoint_def, ← hrng]
      exact p.toNormalization.denseRange.closure_range
    rw [hrng, this.eq (genericPoint_spec p.normalization)]
  have honto : ∀ x : Ω, ∃ (U : p.normalization.Opens) (f : Γ(p.normalization, U)), (U : Set p.normalization).Nonempty ∧
      valF p.toNormalization U f = x := by
    intro x
    set ξ : Sp Ω := genericPoint (Sp Ω) with hξ
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (x := p ξ) (U := ⊤) trivial
    have hsub : ∀ w : Sp Ω, w = ξ := fun w => Subsingleton.elim _ _
    have hpV : ⊤ ≤ p ⁻¹ᵁ V := fun w _ => by rw [hsub w]; exact hxV
    have hξB : ξ ∈ p ⁻¹ᵁ V := hxV
    letI := (p.app V).hom.toAlgebra

    let gB := (Sp Ω).presheaf.germ (p ⁻¹ᵁ V) ξ hξB
    let gR := Z.presheaf.germ V (p ξ) hxV
    have hsq : gR ≫ p.stalkMap ξ = p.app V ≫ gB := p.germ_stalkMap V ξ hxV
    letI alO : Algebra Γ(Z, V) (Z.presheaf.stalk (p ξ)) :=
      TopCat.Presheaf.algebra_section_stalk Z.presheaf ⟨p ξ, hxV⟩
    letI alS : Algebra (Z.presheaf.stalk (p ξ)) ((Sp Ω).presheaf.stalk ξ) := (p.stalkMap ξ).hom.toAlgebra
    letI alRS : Algebra Γ(Z, V) ((Sp Ω).presheaf.stalk ξ) := (gR ≫ p.stalkMap ξ).hom.toAlgebra
    haveI : IsScalarTower Γ(Z, V) (Z.presheaf.stalk (p ξ)) ((Sp Ω).presheaf.stalk ξ) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI hloc : IsLocalization.AtPrime (Z.presheaf.stalk (p ξ)) (hV.primeIdealOf ⟨p ξ, hxV⟩).asIdeal :=
      hV.isLocalization_stalk ⟨p ξ, hxV⟩

    have h1 : ⊤ ≤ (𝟙 (Sp Ω)) ⁻¹ᵁ (p ⁻¹ᵁ V) := hpV
    let E : Γ(Sp Ω, p ⁻¹ᵁ V) →+* Ω := (GlobalTheory.Points.valMap (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) h1).hom
    have hE : ∀ b, E b = valR (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) b := fun b => (GlobalTheory.Points.valR_eq _ _ h1 b).symm
    have hEinj : Function.Injective E := by
      have e1 : GlobalTheory.Points.valMap (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) h1 =
          (Sp Ω).presheaf.map (homOfLE h1).op ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
        rw [GlobalTheory.Points.valMap, Scheme.Hom.appLE]
        simp
        rfl
      haveI : Nonempty (⊤ : (Sp Ω).Opens) := ⟨⟨ξ, trivial⟩⟩
      show Function.Injective (GlobalTheory.Points.valMap (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) h1).hom
      rw [e1]
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).1.comp
        (map_injective_of_isIntegral (Sp Ω) (homOfLE h1))
    obtain ⟨y', hy'⟩ : ∃ y' : Γ(Sp Ω, p ⁻¹ᵁ V), E y' = x := by
      refine ⟨((Sp Ω).presheaf.map (homOfLE le_top).op).hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom x), ?_⟩
      rw [hE, GlobalTheory.Points.valR_res (𝟙 (Sp Ω)) le_top h1]
      have := GlobalTheory.Points.valR_specMap (𝟙 (CommRingCat.of Ω)) x
      rw [Spec.map_id] at this
      exact this

    let y := gB.hom y'
    have hy : IsIntegral (Z.presheaf.stalk (p ξ)) y := hfin.to_isIntegral y
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (hV.primeIdealOf ⟨p ξ, hxV⟩).asIdeal.primeCompl y hy
    have hcomm : ∀ r : Γ(Z, V), gB.hom (algebraMap Γ(Z, V) Γ(Sp Ω, p ⁻¹ᵁ V) r) =
        algebraMap Γ(Z, V) ((Sp Ω).presheaf.stalk ξ) r := fun r => by
      show gB.hom ((p.app V).hom r) = (gR ≫ p.stalkMap ξ).hom r
      rw [hsq]; rfl
    let gB' : Γ(Sp Ω, p ⁻¹ᵁ V) →ₐ[Γ(Z, V)] (Sp Ω).presheaf.stalk ξ := { gB.hom with commutes' := hcomm }
    have hgB : Function.Injective gB' := germ_injective_of_isIntegral (Sp Ω) ξ hξB
    let c' : Γ(Sp Ω, p ⁻¹ᵁ V) := algebraMap Γ(Z, V) _ (m : Γ(Z, V))
    let d' : Γ(Sp Ω, p ⁻¹ᵁ V) := c' * y'
    have hc : IsIntegral Γ(Z, V) c' := isIntegral_algebraMap
    have hd : IsIntegral Γ(Z, V) d' := by
      rw [← isIntegral_algHom_iff gB' hgB]
      have : gB' d' = (m : Γ(Z, V)) • y := by
        rw [Algebra.smul_def, map_mul]
        exact congrArg (· * y) (hcomm _)
      rw [this]
      exact hm
    have hc0 : c' ≠ 0 := by
      intro h0
      have h2 : IsUnit (gB.hom c') := by
        rw [hcomm]
        exact ((IsLocalization.map_units (Z.presheaf.stalk (p ξ)) m).map (p.stalkMap ξ).hom)
      rw [h0, map_zero] at h2
      exact not_isUnit_zero h2
    have hEc : E c' ≠ 0 := fun h0 => hc0 (hEinj (h0.trans (map_zero E).symm))

    let iso := p.normalizationObjIso hV
    have key := p.normalizationObjIso_hom_val hV
    let ac : Γ(p.normalization, p.fromNormalization ⁻¹ᵁ V) := iso.inv.hom ⟨c', hc⟩
    let ad : Γ(p.normalization, p.fromNormalization ⁻¹ᵁ V) := iso.inv.hom ⟨d', hd⟩
    have hle : p ⁻¹ᵁ V ≤ p.toNormalization ⁻¹ᵁ (p.fromNormalization ⁻¹ᵁ V) := by
      simp [← Scheme.Hom.comp_preimage]
    have hval : ∀ e : integralClosure Γ(Z, V) Γ(Sp Ω, p ⁻¹ᵁ V),
        valR p.toNormalization (p.fromNormalization ⁻¹ᵁ V) (iso.inv.hom e) = E e.1 := by
      intro e
      have h3 := congrArg (fun φ => φ.hom (iso.inv.hom e)) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply] at h3
      rw [hE, ← Category.id_comp p.toNormalization, ← GlobalTheory.Points.valR_appLE (𝟙 (Sp Ω)) p.toNormalization hle h1]
      congr 1
      exact h3.symm
    have hW : ⊤ ≤ p.toNormalization ⁻¹ᵁ (p.fromNormalization ⁻¹ᵁ V) := h1.trans hle
    have hU : ⊤ ≤ p.toNormalization ⁻¹ᵁ p.normalization.basicOpen ac := by
      rw [GlobalTheory.Points.le_preimage_basicOpen_iff _ hW ac]
      exact (show valR p.toNormalization _ ac ≠ 0 from (hval _).trans_ne hEc).isUnit
    have hu : IsUnit ((p.normalization.presheaf.map (homOfLE (p.normalization.basicOpen_le ac)).op).hom ac) :=
      p.normalization.toRingedSpace.isUnit_res_basicOpen ac
    refine ⟨p.normalization.basicOpen ac,
      (p.normalization.presheaf.map (homOfLE (p.normalization.basicOpen_le ac)).op).hom ad * ↑(hu.unit⁻¹),
      ⟨_, hU (x := ξ) trivial⟩, ?_⟩
    rw [GlobalTheory.Points.valF_eq_valR, GlobalTheory.Points.valR_mul _ _ hU, GlobalTheory.Points.valR_res _ _ hU, hval]
    have h4 : valR p.toNormalization _ ((p.normalization.presheaf.map (homOfLE (p.normalization.basicOpen_le ac)).op).hom ac) *
        valR p.toNormalization (p.normalization.basicOpen ac) ↑(hu.unit⁻¹) = 1 := by
      rw [← GlobalTheory.Points.valR_mul _ _ hU, ← GlobalTheory.Points.valR_one p.toNormalization _ hU]
      congr 1
      exact hu.mul_val_inv
    rw [GlobalTheory.Points.valR_res _ _ hU, hval] at h4
    rw [eq_inv_of_mul_eq_one_right h4]
    show E (c' * y') * (E c')⁻¹ = x
    rw [map_mul, mul_comm, ← mul_assoc, inv_mul_cancel₀ hEc, one_mul, hy']
  haveI := IsSeparated.of_comp s (spMap κ)
  haveI := locallyOfFiniteType_of_comp s (spMap κ)
  haveI := QuasiCompact.of_comp s (spMap κ)
  let M : RatModel o Ω :=
    { Z := p.normalization
      s := s
      sep := inferInstance
      lft := inferInstance
      qc := inferInstance
      pt := p.toNormalization
      pt_s := hpt_s
      gen := hgen
      onto := honto }
  exact ⟨M, p.fromNormalization, GlobalTheory.IsNormalScheme.pred _, inferInstance, p.toNormalization_fromNormalization⟩

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupCyclotomicAwayProjective
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.NormBlowupInt

theorem isFinite_fromNormalization_int_of_isReduced {X Y : Scheme.{0}} {o : CommRingCat.{0}}
    [Algebra.FiniteType ℤ o] (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : Y ⟶ Spec o)
    [LocallyOfFiniteType g] [IsReduced X] [IsLocallyNoetherian X]
    (hess : ∀ x ∈ genericPoints X, (f.residueFieldMap x).hom.EssFiniteType) :
    IsFinite f.fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  letI := (f.app U).hom.toAlgebra
  letI : Algebra o Γ(Y, U) := ((Scheme.ΓSpecIso o).inv ≫ g.appLE ⊤ U le_top).hom.toAlgebra
  haveI : Algebra.FiniteType o Γ(Y, U) :=
    (g.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso o).inv).2)
  haveI : Algebra.FiniteType ℤ Γ(Y, U) := .trans (S := o) inferInstance inferInstance
  haveI : IsNoetherianRing Γ(Y, U) := Algebra.FiniteType.isNoetherianRing ℤ _
  let D : Set X := genericPoints X
  have hD : Dense D := dense_iff_closure_eq.mpr genericPoints.closure
  let ι := ↥(D ∩ (f ⁻¹ᵁ U : X.Opens))
  haveI : Finite ι := (GlobalTheory.finite_genericPoints_inter _ (f.isCompact_preimage hU.isCompact)).to_subtype
  letI (x : ι) : Algebra Γ(Y, U) (X.residueField x.1) :=
    (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.toAlgebra
  haveI (x : ι) : Algebra.EssFiniteType Γ(Y, U) (X.residueField x.1) := by
    change (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.EssFiniteType
    rw [← Scheme.evaluation_naturality f (V := U) x.1 x.2.2]
    exact .comp (.comp (essFiniteType_germ hU (f x.1) x.2.2)
      (RingHom.FiniteType.of_surjective _ (Y.residue_surjective _)).essFiniteType) (hess _ x.2.1)
  haveI (x : ι) := GlobalTheory.ZMain.finite_integralClosure_field Γ(Y, U) (X.residueField x.1)
  haveI : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := by
    refine finite_integralClosure_of_family (L := fun x : ι => X.residueField x.1)
      (fun x => { (X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom with commutes' := fun _ => rfl })
      fun b hb => ?_
    rw [← basicOpen_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, hxD⟩ := hD.inter_open_nonempty _ (X.basicOpen b).isOpen ⟨y, hy⟩
    exact ((X.evaluation_eq_zero_iff_notMem_basicOpen x (X.basicOpen_le b hx) b).mp
      (hb ⟨x, hxD, X.basicOpen_le b hx⟩) hx).elim
  rw [f.fromNormalization_app hU]
  exact RingHom.Finite.comp
    (.of_surjective _ (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2)
    (RingHom.finite_algebraMap.mpr this)

theorem dense_preimage_of_blowup {Z X' : Scheme.{0}} (J : Z.IdealSheafData) (b : X' ⟶ Z)
    (hb : FinalTheorems.Blowup b J) (hiso : ∀ V : Z.Opens, (∀ x ∈ V, x ∉ J.support) → IsIso (b ∣_ V))
    (W : Z.Opens) (hWd : Dense (W : Set Z)) : Dense ((b ⁻¹ᵁ W : X'.Opens) : Set X') := by
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hb.1
  have hD' : Dense (((J.comap b).support : Set X')ᶜ) := by
    rw [← hD, ← D.coe_nonzeroLocus_canonical]
    exact D.dense_nonzeroLocus_canonical
  let Uc : Z.Opens := J.support.compl
  haveI : IsIso (b ∣_ Uc) := hiso Uc fun x hx => hx
  haveI hoi : IsOpenImmersion ((b ⁻¹ᵁ Uc).ι ≫ b) := by
    rw [← morphismRestrict_ι]; infer_instance
  rw [dense_iff_inter_open]
  intro O hO hne
  obtain ⟨y, hyO, hy⟩ := hD'.inter_open_nonempty O hO hne
  have hyU : y ∈ b ⁻¹ᵁ Uc := by
    change b y ∉ J.support
    intro h
    exact hy ((GlobalTheory.ProjBlowup.mem_support_comap J b y).2 h)
  let O' : (b ⁻¹ᵁ Uc).toScheme.Opens := (b ⁻¹ᵁ Uc).ι ⁻¹ᵁ ⟨O, hO⟩
  have hopen : IsOpen (((b ⁻¹ᵁ Uc).ι ≫ b) '' (O' : Set (b ⁻¹ᵁ Uc).toScheme)) :=
    ((b ⁻¹ᵁ Uc).ι ≫ b).isOpenEmbedding.isOpenMap _ O'.isOpen
  obtain ⟨w, ⟨t, htO, rfl⟩, hwW⟩ := hWd.inter_open_nonempty _ hopen ⟨_, ⟨⟨y, hyU⟩, hyO, rfl⟩⟩
  refine ⟨(b ⁻¹ᵁ Uc).ι t, htO, ?_⟩
  change b ((b ⁻¹ᵁ Uc).ι t) ∈ W
  rwa [← Scheme.Hom.comp_apply]

end GlobalTheory.NormBlowupInt

namespace GlobalTheory.NormBlowupInt

theorem exists_normBl : ∀ (n : ℕ) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)), IsProjOver z →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ (J : Z.IdealSheafData) (W : Z.Opens),
    Dense (W : Set Z) → (∀ x ∈ J.support, x ∉ W) → ∃ (S : Scheme.{0}) (π : S ⟶ Z)
    (BD : EffCartierData S), IsNormBl π J ∧ IsProjOver (π ≫ z) ∧ BD.idealSheaf = J.comap π ∧
    IsIso (π ∣_ W) ∧ Dense (π ⁻¹' W : Set S) := by
  intro n Z z hz hZ J W hWd hWJ
  haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  haveI : Algebra.FiniteType ℤ (CommRingCat.of (cycAway n)) := ‹Algebra.FiniteType ℤ (cycAway n)›
  haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨X', b, hb, hbs, hiso⟩ := GlobalTheory.ProjBlowup.exists_blowup z hz J
  haveI : LocallyOfFiniteType (b ≫ z) := by
    obtain ⟨m, i, hi, e⟩ := hbs
    have := isProper_str (cycAway n) m
    rw [← e]; infer_instance
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (b ≫ z)
  let V : X'.Opens := b ⁻¹ᵁ W
  haveI hbW : IsIso (b ∣_ W) := hiso W fun x hx hJ => hWJ x hJ hx
  haveI hoi : IsOpenImmersion (V.ι ≫ b) := by
    rw [← morphismRestrict_ι]; infer_instance
  haveI : GlobalTheory.IsNormalScheme Z := .of_pred hZ
  haveI hN : GlobalTheory.IsNormalScheme V.toScheme := .of_isOpenImmersion (V.ι ≫ b)
  haveI : IsReduced V.toScheme := by
    exact inferInstance
  haveI hfin : IsFinite V.ι.fromNormalization :=
    isFinite_fromNormalization_int_of_isReduced (o := CommRingCat.of (cycAway n)) V.ι (b ≫ z)
      fun x _ => (LocallyOfFiniteType.stalkMap V.ι x).residueFieldMap
  let ν := V.ι.fromNormalization
  have hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V.ι.normalization := IsNormalScheme.pred _
  have hν : IsIso (ν ∣_ V) := by
    have H := isPullback_toNormalization_of_mono (𝟙 _) V.ι V.ι (Category.id_comp _).symm
    have e := IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict V.ι.fromNormalization V) H.flip
    rw [← e]
    infer_instance
  have hd : Dense ((ν ⁻¹ᵁ V : V.ι.normalization.Opens) : Set V.ι.normalization) := by
    refine V.ι.toNormalization.denseRange.mono ?_
    rintro _ ⟨x, rfl⟩
    change V.ι.fromNormalization (V.ι.toNormalization x) ∈ V
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    exact x.2
  have hVd : Dense (V : Set X') := dense_preimage_of_blowup J b hb hiso W hWd
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hb.1
  have hK : D.KeepsRegular ν := by
    refine D.keepsRegular_of_dense ν (fun y => (hS y).1) (hd.mono fun t ht => ?_)
    show ν t ∉ D.idealSheaf.support
    rw [hD, GlobalTheory.ProjBlowup.mem_support_comap]
    exact fun h => hWJ _ h ht
  refine ⟨V.ι.normalization, ν ≫ b, D.pull ν hK,
    ⟨inferInstance, X', b, ν, V, hb, rfl, hfin, hVd, hd, hν⟩, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc]; exact isProjOver_comp_of_isFinite ν hbs
  · rw [EffCartierData.idealSheaf_pull, hD, Scheme.IdealSheafData.comap_comp]
  · rw [morphismRestrict_comp]; exact IsIso.comp_isIso' hν hbW
  · convert hd using 1
    ext t
    simp [V]

end GlobalTheory.NormBlowupInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointTranslatesInOpenSemiAbelianLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShearMeet

theorem exists_fst_mul_mem : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ V : G.left.Opens, (∃ y₀ ∈ V, G.hom y₀ = closedPoint R) → ∀ y : G.left, ∃ z : (G ⊗ G).left, (fst G G).left z = y ∧ (fst G G * snd G G).left z ∈ V ∧ (fst G G * (snd G G)⁻¹).left z ∈ V := by
  intro R _ _ G _ hG V ⟨y₀, hy₀, e₀⟩ y
  have := hG.smooth
  have : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_isSemiAbelian G

  obtain ⟨y₁, hy₁, e₁⟩ : ∃ y₁ ∈ V, G.hom y₁ = G.hom y := by
    have hs : G.hom y ⤳ G.hom y₀ := by rw [e₀]; exact IsLocalRing.specializes_closedPoint _
    obtain ⟨y₁, h₁, h₂⟩ := (Flat.generalizingMap G.hom) hs
    exact ⟨y₁, h₁.mem_open V.2 hy₀, h₂⟩
  let f := fst G G
  let g := snd G G
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := G.hom) y y₁ e₁.symm
  have hf : GeometricallyIrreducible f.left :=
    inferInstanceAs (GeometricallyIrreducible (pullback.fst G.hom G.hom))
  have hwf : f.left w = y := hw1
  have hwg : g.left w = y₁ := hw2

  let bp : G ⊗ G ⟶ G ⊗ G := lift f (f⁻¹ * g)
  let bm : G ⊗ G ⟶ G ⊗ G := lift f (g⁻¹ * f)
  have bp1 : bp ≫ (f * g) = g := by
    rw [MonObj.comp_mul, lift_fst, lift_snd, mul_inv_cancel_left]
  have bm1 : bm ≫ (f * g⁻¹) = g := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, mul_inv_rev, inv_inv, mul_inv_cancel_left]
  have bp2 : bp ≫ f = f := lift_fst _ _
  have bm2 : bm ≫ f = f := lift_fst _ _
  have hi : IsIrreducible (f.left ⁻¹' {y}) := by
    rw [← f.left.range_fiberι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (f.left.fiberι y).continuous.continuousOn
  have mp : (bp.left w) ∈ f.left ⁻¹' {y} ∩ (f * g).left ⁻¹ᵁ V := by
    refine ⟨?_, ?_⟩
    · show f.left (bp.left w) = y
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, bp2]; exact hwf
    · show (f * g).left (bp.left w) ∈ V
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, bp1, hwg]; exact hy₁
  have mm : (bm.left w) ∈ f.left ⁻¹' {y} ∩ (f * g⁻¹).left ⁻¹ᵁ V := by
    refine ⟨?_, ?_⟩
    · show f.left (bm.left w) = y
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, bm2]; exact hwf
    · show (f * g⁻¹).left (bm.left w) ∈ V
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, bm1, hwg]; exact hy₁
  obtain ⟨z, hz, k₁, k₂⟩ := hi.2 _ _ ((f * g).left ⁻¹ᵁ V).2 ((f * g⁻¹).left ⁻¹ᵁ V).2 ⟨_, mp⟩ ⟨_, mm⟩
  exact ⟨z, hz, k₁, k₂⟩

end GlobalTheory.ShearMeet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
section
noncomputable section

namespace GlobalTheory.UPel.HT.ES

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

def IsQuasiInv {Y : Scheme.{0}} {A B : Over Y} [GrpObj A] [GrpObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) : Prop :=
  IsMonHom ψ ∧ IsMonHom ψ' ∧ ψ ≫ ψ' = (𝟙 A) ^ k ∧ ψ' ≫ ψ = (𝟙 B) ^ k

def IsAxesTriv {Y : Scheme.{0}} (B : Over Y) [GrpObj B] [IsCommMonObj B] (Q : LB (G2 B).left) : Prop :=
  Q.IsLB ∧ (∃ t : (Q.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen) ∧
    ∃ t : (Q.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {Y : Scheme.{0}}
  {s : Y ⟶ Sp R}

theorem isAxesTriv_obj (o : Obj b N s) : IsAxesTriv o.A o.P := ⟨o.isLB, o.rig₁, o.rig₂⟩

def KerStableAt (o : Obj b N s) {B : Over Y} [GrpObj B] (ψ : o.A ⟶ B) {Tb : Scheme.{0}} (t : Tb ⟶ Y) : Prop :=
  ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ g : T ⟶ o.A, g ≫ ψ = 1 →
    ∀ a : D.O, g ≫ o.act.act a ≫ ψ = 1

def PullPolTriv (o : Obj b N s) {B : Over Y} (ψ' : B ⟶ o.A) {T : Over Y} (x : T ⟶ B) : Prop :=
  ∃ τ : (o.P.pull (lift (fst B T ≫ ψ') (snd B T ≫ x ≫ ψ')).left).Gen, τ.IsGen

def PolKerAt (o : Obj b N s) {B : Over Y} [GrpObj B] (ψ' : B ⟶ o.A) (c : ℕ) {Tb : Scheme.{0}} (t : Tb ⟶ Y) : Prop :=
  ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ x : T ⟶ B, x ^ (c ^ 3) = 1 →
    (PullPolTriv o ψ' x ↔ x ^ c = 1)

def TjAt (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ) (o : Obj b N s) {B : Over Y} [GrpObj B] (ψ : o.A ⟶ B)
    {Tb : Scheme.{0}} (t : Tb ⟶ Y) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ Y), (∃ σ : Sp k ⟶ Tb, σ ≫ t = x) →
    (∀ g : Over.mk x ⟶ o.A, g ≫ ψ = 1 → (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) → KilledBy o w g) ∧
    Nat.card {g : Over.mk x ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} = Ideal.absNorm w ^ (D.m * j)

theorem tjAt_id_iff (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) :
    TjAt r w j o ψ (𝟙 Y) ↔ IsTj r w j o o' ψ :=
  ⟨fun h k _ _ _ x => h k x ⟨x, Category.comp_id x⟩, fun h k _ _ _ x _ => h k x⟩

theorem IsPIsog.kerStableAt {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (h : IsPIsog c o o' ψ)
    {Tb : Scheme.{0}} (t : Tb ⟶ Y) : KerStableAt o ψ t := by
  intro T _ _ g hg a
  haveI := o'.act.hom a
  rw [h.2.2.1, ← Category.assoc, hg, one_comp]

theorem IsPIsog.exists_quasiInv {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (h : IsPIsog c o o' ψ) :
    ∃ ψ' : o'.A ⟶ o.A, IsQuasiInv c ψ ψ' := by
  obtain ⟨-, h1, -, -, -, ψ', h2, h3, h4⟩ := h
  exact ⟨ψ', h1, h2, h3, h4⟩

end GlobalTheory.UPel.HT.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelationsLiftVanishingConductor
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem relations_lift_vanishing : (∀ (R R' ν : Type) [CommRing R] [CommRing R'] [Algebra R R'] (c : Ideal R), (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ G ∈ (c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R'), ∃ H : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) H = 0 ∧ MvPolynomial.map (algebraMap R R') H = G) → ∀ (R R' C' D E ν : Type) [CommRing R] [CommRing R'] [CommRing C'] [CommRing D] [CommRing E] [Algebra R R'] [Algebra R' C'] (c : Ideal R) [Algebra (R ⧸ c) D], (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (π : C' →+* E) (ψ : D →+* E) (ζ : ν → D) (ξ : ν → C'), RingHom.ker π = c.map ((algebraMap R' C').comp (algebraMap R R')) → ψ.comp ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)) = (π.comp (algebraMap R' C')).comp (algebraMap R R') → (∀ s, π (ξ s) = ψ (ζ s)) → Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') → ∀ f : MvPolynomial ν (R ⧸ c), MvPolynomial.aeval ζ f = 0 → ∃ F : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) F = f ∧ MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F) = 0 := by
  intro hH R R' C' D E ν _ _ _ _ _ _ _ c _ hc π ψ ζ ξ hker hcomm hξ hsurj f hf
  obtain ⟨F₀, rfl⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk c) Ideal.Quotient.mk_surjective f
  have hπ : π (MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F₀)) = 0 := by
    have h1 : π (MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F₀))
        = ψ (MvPolynomial.aeval ζ (MvPolynomial.map (Ideal.Quotient.mk c) F₀)) := by
      rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_map,
        MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left, ← RingHom.comp_assoc, hcomm]
      congr 1
      funext s
      exact hξ s
    rw [h1, hf, map_zero]
  have hmem : MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F₀) ∈
      ((c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R')).map
        (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') := by
    rw [Ideal.map_map]
    change _ ∈ Ideal.map ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') : MvPolynomial ν R' →+* C') _
    rw [Ideal.map_map]
    have : ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') : MvPolynomial ν R' →+* C').comp
        ((MvPolynomial.C : R' →+* MvPolynomial ν R').comp (algebraMap R R'))
        = (algebraMap R' C').comp (algebraMap R R') := by
      ext x; simp
    rw [this, ← hker]
    exact hπ
  obtain ⟨G, hG, hGe⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 hmem
  obtain ⟨H, hH0, hHG⟩ := hH R R' ν c hc G hG
  refine ⟨F₀ - H, ?_, ?_⟩
  · rw [map_sub, hH0, sub_zero]
  · rw [map_sub, hHG, map_sub, hGe, sub_self]

end GlobalTheory.Pinch
end

