module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRanksDegreesAddWithMasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDvrFormallyUnramifiedOfEtale
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

namespace GlobalTheory

theorem formallyUnramified_of_dvr_of_essFiniteType : ∀ (R T V : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing T] [Algebra R T] [Algebra.FormallyUnramified R T] [Algebra.EssFiniteType R T] [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra R V] (μ : T →ₐ[R] V), (∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R V r ∈ IsLocalRing.maximalIdeal V) → Function.Injective (algebraMap R V) → (∀ v : V, ∃ a b : T, μ b ≠ 0 ∧ v * μ b = μ a) → Algebra.FormallyUnramified R V := by
  intro R T V _ _ _ _ _ _ _ _ _ _ _ μ hm hinj hfrac
  let Q : Ideal T := (IsLocalRing.maximalIdeal V).comap μ
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  let D := Localization.AtPrime Q
  haveI : Algebra.FormallyUnramified T D := .of_isLocalization Q.primeCompl
  haveI : Algebra.FormallyUnramified R D := .comp R T D
  haveI : Algebra.EssFiniteType T D := .of_isLocalization D Q.primeCompl
  haveI : Algebra.EssFiniteType R D := .comp R T D
  have hQ : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R T r ∈ Q := fun r hr => by
    show μ (algebraMap R T r) ∈ IsLocalRing.maximalIdeal V
    rw [μ.commutes]; exact hm r hr
  haveI : IsLocalHom (algebraMap R D) := ⟨fun r hr => by
    by_contra hnu
    rw [IsScalarTower.algebraMap_apply R T D, IsLocalization.AtPrime.isUnit_to_map_iff D Q] at hr
    exact hr (hQ r ((IsLocalRing.mem_maximalIdeal _).2 hnu))⟩
  have hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R D) = IsLocalRing.maximalIdeal D :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hunit : ∀ y : Q.primeCompl, IsUnit (μ y) := fun y => by
    by_contra h; exact y.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  let ν : D →ₐ[R] V := IsLocalization.liftAlgHom (M := Q.primeCompl) (f := μ) hunit
  have hν : ∀ t, ν (algebraMap T D t) = μ t := fun t => IsLocalization.lift_eq _ _
  have hνu : ∀ d, IsUnit (ν d) → IsUnit d := by
    intro d hd
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl d
    have e : IsLocalization.mk' D x s * algebraMap T D s = algebraMap T D x :=
      IsLocalization.mk'_spec D x s
    have hx : IsUnit (μ x) := by
      have := congrArg ν e
      rw [map_mul, hν, hν] at this
      rw [← this]; exact hd.mul (hunit s)
    have hxQ : x ∈ Q.primeCompl := fun h => (IsLocalRing.mem_maximalIdeal _).1 h hx
    have : IsUnit (algebraMap T D x) := IsLocalization.map_units D (⟨x, hxQ⟩ : Q.primeCompl)
    rw [← e] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmR : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hmD : IsLocalRing.maximalIdeal D = Ideal.span {algebraMap R D ϖ} := by
    rw [← hmax, hmR, Ideal.map_span, Set.image_singleton]
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have hS := GlobalTheory.T.subring_eq_univ_of_uniformizer_generates V (ν : D →+* V).range (algebraMap R V ϖ) ⟨algebraMap R D ϖ, ν.commutes ϖ⟩
    ((map_ne_zero_iff _ hinj).2 hϖ.ne_zero) (hm ϖ hϖm) ?_ ?_ ?_
  · refine Algebra.FormallyUnramified.of_surjective ν fun v => ?_
    have hv : v ∈ (ν : D →+* V).range := hS ▸ Subring.mem_top v
    obtain ⟨d, hd⟩ := hv
    exact ⟨d, hd⟩
  · rintro _ ⟨d, rfl⟩ hs
    have hu : IsUnit (ν d) := by
      by_contra h; exact hs ((IsLocalRing.mem_maximalIdeal _).2 h)
    obtain ⟨u, hu'⟩ := hνu d hu
    refine ⟨ν ↑u⁻¹, ⟨_, rfl⟩, ?_⟩
    change ν d * ν ↑u⁻¹ = 1
    rw [← map_mul, ← hu', Units.mul_inv, map_one]
  · rintro _ ⟨d, rfl⟩ hs
    have hd : d ∈ IsLocalRing.maximalIdeal D := (IsLocalRing.mem_maximalIdeal _).2 fun h =>
      (IsLocalRing.mem_maximalIdeal _).1 hs (h.map ν)
    rw [hmD] at hd
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hd
    refine ⟨ν a, ⟨a, rfl⟩, ?_⟩
    change ν (a * algebraMap R D ϖ) = _
    rw [map_mul, ν.commutes, mul_comm]
  · intro v
    obtain ⟨a, b, hb, hab⟩ := hfrac v
    exact ⟨μ a, ⟨_, hν a⟩, μ b, ⟨_, hν b⟩, hb, hab⟩

end GlobalTheory

namespace GlobalTheory

theorem trace_dvr_formallyUnramified_of_etale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (U : M.Opens), Etale (U.ι ≫ f) → ∀ z ∈ U, ∀ (V : ValuationSubring M.functionField) [IsDiscreteValuationRing V] [IsDiscreteValuationRing (V.comap (functionFieldMap f))], DominatesStalk V z → letI := ((functionFieldMap f).restrict (V.comap (functionFieldMap f)) V fun _ hx => hx).toAlgebra; Algebra.FormallyUnramified (V.comap (functionFieldMap f)) V := by
  intro M W _ _ f _ U hU z hz V _ _ hV
  obtain ⟨-, hfe, hess⟩ :=
    stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict M W f U hU z hz
  set φ := functionFieldMap f with hφ
  set R := V.comap φ
  let A := W.presheaf.stalk (f z)
  let B := M.presheaf.stalk z
  let g : A →+* B := (f.stalkMap z).hom
  letI : Algebra A B := g.toAlgebra
  haveI : Algebra.FormallyEtale A B := hfe
  haveI : Algebra.EssFiniteType A B := hess
  have hcomp : ∀ a : A, φ (algebraMap A W.functionField a) = algebraMap B M.functionField (g a) :=
    fun a => functionFieldMap_algebraMap f z a
  have hαR : ∀ a : A, algebraMap A W.functionField a ∈ R := fun a => by
    change φ _ ∈ V
    rw [hcomp]; exact hV.1 _
  let αR : A →+* R := (algebraMap A W.functionField).codRestrict R hαR
  let βV : B →+* V := (algebraMap B M.functionField).codRestrict V hV.1
  letI algRV : Algebra R V := (φ.restrict R V fun _ hx => hx).toAlgebra
  letI : Algebra A R := αR.toAlgebra
  letI : Algebra A V := (βV.comp g).toAlgebra
  haveI : IsScalarTower A R V := IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (hcomp a).symm
  let gV : B →ₐ[A] V := { βV with commutes' := fun _ => rfl }
  let μ : TensorProduct A R B →ₐ[R] V :=
    Algebra.TensorProduct.lift (Algebra.ofId R V) gV fun _ _ => Commute.all _ _
  haveI : Algebra.FormallyUnramified R (TensorProduct A R B) := Algebra.FormallyUnramified.base_change R
  haveI : Algebra.EssFiniteType R (TensorProduct A R B) := Algebra.EssFiniteType.baseChange A B R
  refine formallyUnramified_of_dvr_of_essFiniteType R (TensorProduct A R B) V μ ?_ ?_ ?_
  · intro r hr
    by_contra hnu
    have hu : IsUnit (algebraMap R V r) := by
      by_contra h; exact hnu ((IsLocalRing.mem_maximalIdeal _).2 h)
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
    have hw' : φ (r : W.functionField) * (w : M.functionField) = 1 := congrArg Subtype.val hw
    have hr0 : (r : W.functionField) ≠ 0 := by
      intro h0; rw [h0, map_zero, zero_mul] at hw'; exact zero_ne_one hw'
    have hinv : (r : W.functionField)⁻¹ ∈ R := by
      change φ _ ∈ V
      rw [map_inv₀, ← eq_inv_of_mul_eq_one_right hw']
      exact w.2
    exact (IsLocalRing.mem_maximalIdeal _).1 hr
      (isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hr0)⟩)
  · intro x y hxy
    exact Subtype.ext (φ.injective (congrArg Subtype.val hxy))
  · intro v
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := B) (v : M.functionField)
    have hμ : ∀ c : B, ((μ (1 ⊗ₜ c) : V) : M.functionField) = algebraMap B M.functionField c := by
      intro c
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
    refine ⟨1 ⊗ₜ a, 1 ⊗ₜ b, ?_, ?_⟩
    · intro h0
      apply nonZeroDivisors.ne_zero hb
      apply IsFractionRing.injective B M.functionField
      rw [map_zero]
      rw [← hμ, h0]; rfl
    · apply Subtype.ext
      rw [Subring.coe_mul, hμ, hμ]
      rw [← hab, div_mul_cancel₀]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialSquareZeroExtensionPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SqZeroPb

def liftHom {K : Type} [Field K] {V W₁ W₂ : Type} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] [AddCommGroup W₁] [Module K W₁] [Module Kᵐᵒᵖ W₁] [IsCentralScalar K W₁]
    [AddCommGroup W₂] [Module K W₂] [Module Kᵐᵒᵖ W₂] [IsCentralScalar K W₂]
    (e : V ≃ₗ[K] W₁ × W₂) {T : Type} [CommRing T]
    (a : T →+* TrivSqZeroExt K W₁) (b : T →+* TrivSqZeroExt K W₂)
    (h : ∀ t, (a t).fst = (b t).fst) : T →+* TrivSqZeroExt K V where
  toFun t := TrivSqZeroExt.inl (a t).fst + TrivSqZeroExt.inr (e.symm ((a t).snd, (b t).snd))
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp only [map_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero, zero_add, smul_eq_mul, op_smul_eq_smul, smul_zero]
      rw [← map_smul, ← map_smul, ← map_add (f := _)]
      congr 1
      ext <;> simp [h]
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_add' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp only [map_add (f := _), TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, zero_add]
      rw [show ((a x).snd + (a y).snd, (b x).snd + (b y).snd)
          = ((a x).snd, (b x).snd) + ((a y).snd, (b y).snd) from rfl, map_add]

end GlobalTheory.SqZeroPb

open GlobalTheory.SqZeroPb in
theorem GlobalTheory.SqZeroPb.isPullback_trivSqZeroExt : ∀ (K : Type) [Field K] (V W₁ W₂ : Type) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V] [AddCommGroup W₁] [Module K W₁] [Module Kᵐᵒᵖ W₁] [IsCentralScalar K W₁] [AddCommGroup W₂] [Module K W₂] [Module Kᵐᵒᵖ W₂] [IsCentralScalar K W₂] (p : V →ₗ[K] W₁) (q : V →ₗ[K] W₂), Function.Bijective (LinearMap.prod p q) → IsPullback (CommRingCat.ofHom (TrivSqZeroExt.map p).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.map q).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₁).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₂).toRingHom) := by
  intro K _ V W₁ W₂ _ _ _ _ _ _ _ _ _ _ _ _ p q hpq
  let e := LinearEquiv.ofBijective (LinearMap.prod p q) hpq
  have he : ∀ v, e v = (p v, q v) := fun v => rfl
  have hw : CommRingCat.ofHom (TrivSqZeroExt.map p).toRingHom ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₁).toRingHom =
      CommRingCat.ofHom (TrivSqZeroExt.map q).toRingHom ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₂).toRingHom := by
    ext x; simp
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => CommRingCat.ofHom (liftHom e s.fst.hom s.snd.hom ?_)) ?_ ?_ ?_)
  · intro t
    have := congrArg (fun φ => φ.hom t) s.condition
    simpa using this
  · intro s
    ext t : 2
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [liftHom]
    · simp [liftHom]
      exact congrArg Prod.fst (e.apply_symm_apply _)
  · intro s
    ext t : 2
    have hc := congrArg (fun φ => φ.hom t) s.condition
    simp at hc
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [liftHom, hc]
    · simp [liftHom]
      exact congrArg Prod.snd (e.apply_symm_apply _)
  · intro s m hm1 hm2
    ext t : 2
    have h1 := congrArg (fun φ => φ.hom t) hm1
    have h2 := congrArg (fun φ => φ.hom t) hm2
    simp at h1 h2
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [liftHom, ← h1]
    · simp [liftHom, ← h1, ← h2]
      rw [LinearEquiv.eq_symm_apply]
      rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrvEqSelf
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

namespace GlobalTheory.EqvTrans

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X Y : Scheme.{0}} {t : SAB H Y} {p : X ⟶ Y} {G' : Over X} [GrpObj G'] {ψ : G'.left ⟶ t.G.left}


open Classical in
def trv (hψ : IsPullback ψ G'.hom t.G.hom p) (g : G'.left ⟶ G'.left) {R : Type} [CommRing R] (q : Sp R ⟶ X)
    (v : Sp (DualNumber R) ⟶ t.G.left) : Sp (DualNumber R) ⟶ t.G.left :=
  if h : v ≫ t.G.hom = (spMap (algebraMap R (DualNumber R)) ≫ q) ≫ p then hψ.lift v _ h ≫ g ≫ ψ else v

variable (hψ : IsPullback ψ G'.hom t.G.hom p) {R R' : Type} [CommRing R] [CommRing R']

theorem trv_eq (g : G'.left ⟶ G'.left) (q : Sp R ⟶ X) {v : Sp (DualNumber R) ⟶ t.G.left}
    (w : Sp (DualNumber R) ⟶ G'.left) (hw : w ≫ ψ = v) (hw' : w ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ q) :
    trv hψ g q v = w ≫ g ≫ ψ := by
  have h : v ≫ t.G.hom = (spMap (algebraMap R (DualNumber R)) ≫ q) ≫ p := by
    rw [← hw, Category.assoc, hψ.w, ← Category.assoc, hw']
  rw [trv, dite_eq_left h]
  congr 1
  exact hψ.hom_ext (by rw [hψ.lift_fst, hw]) (by rw [hψ.lift_snd, hw'])


include hψ in
theorem exists_lift (q : Sp R ⟶ X) {v : Sp (DualNumber R) ⟶ t.G.left}
    (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    ∃ w : Sp (DualNumber R) ⟶ G'.left, w ≫ ψ = v ∧ w ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ q :=
  ⟨hψ.lift v _ (by rw [hv, Category.assoc]), hψ.lift_fst _ _ _, hψ.lift_snd _ _ _⟩

theorem trv_over (g : G'.left ⟶ G'.left) {b : X ⟶ X} (hg : g ≫ G'.hom = G'.hom ≫ b) (q : Sp R ⟶ X)
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ g q v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ (q ≫ b) ≫ p := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  rw [trv_eq hψ g q w hw hw', Category.assoc, Category.assoc, hψ.w, reassoc_of% hg, reassoc_of% hw']
  simp only [Category.assoc]

theorem trv_map (g : G'.left ⟶ G'.left) (σ : R →+* R') (q : Sp R ⟶ X) {v : Sp (DualNumber R) ⟶ t.G.left}
    (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ g (spMap σ ≫ q) (spMap (dualMap σ) ≫ v) = spMap (dualMap σ) ≫ trv hψ g q v := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  have e : spMap (dualMap σ) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R' (DualNumber R')) ≫ spMap σ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
  rw [trv_eq hψ g q w hw hw', trv_eq hψ g (spMap σ ≫ q) (spMap (dualMap σ) ≫ w) (by rw [Category.assoc, hw])
    (by rw [Category.assoc, hw', ← Category.assoc, e, Category.assoc])]
  simp only [Category.assoc]

theorem trv_comp (g₁ g₂ : G'.left ⟶ G'.left) {b₁ : X ⟶ X} (hg₁ : g₁ ≫ G'.hom = G'.hom ≫ b₁) (q : Sp R ⟶ X)
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ (g₁ ≫ g₂) q v = trv hψ g₂ (q ≫ b₁) (trv hψ g₁ q v) := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  rw [trv_eq hψ _ q w hw hw', trv_eq hψ g₁ q w hw hw', trv_eq hψ g₂ (q ≫ b₁) (w ≫ g₁) (Category.assoc _ _ _)
    (by rw [Category.assoc, hg₁, reassoc_of% hw'])]
  simp only [Category.assoc]

theorem trv_eq_self (g : G'.left ⟶ G'.left) (q : Sp R ⟶ X)
    (hg : ∀ w : Sp (DualNumber R) ⟶ G'.left, w ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ q → w ≫ g = w)
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ g q v = v := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  rw [trv_eq hψ g q w hw hw', ← Category.assoc, hg w hw', hw]

end GlobalTheory.EqvTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedWeightDegree
section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Proof.TwistedWeightDegree

theorem degW_twist : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ (G₀ G : WTZ D.host.E) (s : ∀ Z : Comp Xo c, TwSec U (xiR D) Z G₀) (B : Finset ℕ) (τ : ℝ), Even G.2 → (∀ p ∈ B, p.Prime) → (∀ Z, IntOff B (s Z).lo) → (∀ Z, τ ≤ (s Z).degLo) → GoodW U (xiR D) V dict G → GoodW U (xiR D) V dict (G + G₀) ∧ rankW U (G + G₀) = rankW U G ∧ degW U (xiR D) V dict G + (rankW U G : ℝ) * (τ - logSum B) ≤ degW U (xiR D) V dict (G + G₀) := by
  intro D H Dw l Xo c r U V dict hC G₀ G s B τ hev hB hint hτ hG
  have hU : ∀ σ, GoodEmb c σ → IsUnf (U σ) := fun σ hσ => (hC.2 σ hσ).1
  have hA : ∀ G' : WTZ D.host.E, Adds U V dict G' := fun G' =>
    _root_.GlobalTheory.CompAdds.adds D H Dw l Xo c r U V dict G' (_root_.GlobalTheory.CuspSplit.splits D H Dw l Xo c r U V dict hU G')
      ((_root_.GlobalTheory.CompPetOrth.orthogonal_mass_idem D H Dw l Xo c r U V dict hC G').1)
  have hOn : ∀ Z, GoodOn U (xiR D) V dict Z G := (hA G).1.1 hG
  have hgr : ∀ Z, GoodOn U (xiR D) V dict Z (G + G₀) ∧ rankOn U Z (G + G₀) = rankOn U Z G := fun Z =>
    _root_.GlobalTheory.FlatTw.Good.twist_goodOn D.host.E H Dw l Xo c r U (xiR D) D V dict Z G₀ (s Z) G hU hev (hOn Z)
  have hG' : GoodW U (xiR D) V dict (G + G₀) := (hA (G + G₀)).1.2 (fun Z => (hgr Z).1)
  obtain ⟨-, hr1, -, -, hd1⟩ := (hA G).2 hG
  obtain ⟨-, hr2, -, -, hd2⟩ := (hA (G + G₀)).2 hG'
  have hrank : rankW U (G + G₀) = rankW U G := by
    rw [hr1, hr2]; exact finsum_congr fun Z => (hgr Z).2
  refine ⟨hG', hrank, ?_⟩
  haveI : Finite (Comp Xo c) := finite_comp
  letI := Fintype.ofFinite (Comp Xo c)
  have hZ : ∀ Z, degOn U (xiR D) V dict Z G + (rankOn U Z G : ℝ) * (τ - logSum B) ≤
      degOn U (xiR D) V dict Z (G + G₀) := fun Z => by
    have h1 := _root_.GlobalTheory.FlatTw.degOn_add_rank_mul_degLo_le D.host.E H Dw l Xo c r U (xiR D) D V dict Z G₀ (s Z) G B hU hev hB (hint Z) (hOn Z)
    have h2 : (rankOn U Z G : ℝ) * (τ - logSum B) ≤ (rankOn U Z G : ℝ) * ((s Z).degLo - logSum B) :=
      mul_le_mul_of_nonneg_left (by linarith [hτ Z]) (Nat.cast_nonneg _)
    linarith
  rw [hd1, hd2, hr1]
  simp only [finsum_eq_sum_of_fintype, Nat.cast_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro Z _
  rw [(hgr Z).2]
  linarith [hZ Z]

end GlobalTheory.Proof.TwistedWeightDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

variable {S : Scheme.{0}}

def SiegKerBy {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B} (c : SiegPre h M ζ s) (d : ℕ) : Prop :=
  Out.RelAmple c.A c.diag ∧
    ∀ (T : Over S) (x : T ⟶ c.A),
      (∃ t : (c.P.pull (lift (snd c.A T ≫ x) (fst c.A T)).left).Gen, t.IsGen) → x ^ d = 1

def IsSympLev {A : Over S} [GrpObj A] (P : LB (G2 A).left) (h M : ℕ) {B : Type} [CommRing B] (ζ : B)
    (t₁ : S ⟶ Sp B) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) : Prop :=
  (∀ a b, lev (a + b) = lev a * lev b) ∧ (∀ a, lev a ^ M = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k) (z : kˣ), x ≫ t₁ = spMap β →
      (z : k) = β ζ →
      (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M • b)) ∧
      (∀ g : Over.mk x ⟶ A, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g) ∧
      ∀ a b, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) M (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b)
        (unitOn (z ^ (2 * omegaStd a b)))

theorem SiegPre.isSympLev {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B} (c : SiegPre h M ζ s) :
    IsSympLev c.P h M ζ s c.lev :=
  ⟨c.lev_add, c.lev_tors, c.geom⟩

def SDRep (h M d : ℕ) : Prop :=
  ∃ (X : Scheme.{0}) (s : X ⟶ Sp (cycAway M)) (u : SiegPre h M (zetaAway M) s),
    SiegKerBy u d ∧ IsUnit ((d : ℕ) : Γ(X, ⊤)) ∧ IsQProjOver s ∧
    ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t),
      IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃! f : S ⟶ X, f ≫ s = t ∧ SiegPB c u f

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def HasLevelStructureOfLevel (b : Base D R) (N h M : ℕ) : Prop :=
  ∃ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev ∧ IsQProjOver s ∧
    ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (t₁ : S ⟶ Sp (cycAway M)) (o : Obj b N t)
      (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)), IsSympLev o.P h M (zetaAway M) t₁ l →
      ∃! f : S ⟶ X, f ≫ s = t ∧ f ≫ s₁ = t₁ ∧ ∃ m : ObjMap o u f, ∀ a, (l a).left ≫ m.φ = f ≫ (lev a).left

theorem Datum.two_le_finrank_La {p : ℕ} [Fact p.Prime] (D : Datum p) : 2 ≤ Module.finrank ℤ D.La := by
  haveI := D.freeLa
  haveI := D.finLa
  have hF : 0 < Module.finrank ℚ D.F := Module.finrank_pos
  have hpos : 0 < Module.finrank ℤ D.La := by
    rw [D.rankLa]
    exact Nat.mul_pos (Nat.mul_pos D.m_pos D.n_pos) hF
  by_contra hlt
  have h1 : Module.finrank ℤ D.La = 1 := by omega
  let bs := Module.finBasisOfFinrankEq ℤ D.La h1
  have hzero : ∀ x y : D.La, D.EF x y = 0 := by
    intro x y
    have hx : x = bs.repr x 0 • bs 0 := by
      conv_lhs => rw [← bs.sum_repr x]
      simp
    have hy : y = bs.repr y 0 • bs 0 := by
      conv_lhs => rw [← bs.sum_repr y]
      simp
    rw [hx, hy, LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply, D.alt, smul_zero, smul_zero]
  have hsub : ∀ x : D.La, x = 0 := by
    intro x
    apply D.nondeg
    ext y
    simp [hzero]
  have : Module.finrank ℤ D.La = 0 := by
    haveI : Subsingleton D.La := ⟨fun a b => by rw [hsub a, hsub b]⟩
    exact Module.finrank_zero_of_subsingleton
  omega

end GlobalTheory.UPel.HT
end
end

