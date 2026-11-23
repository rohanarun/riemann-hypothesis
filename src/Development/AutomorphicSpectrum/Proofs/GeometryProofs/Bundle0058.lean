module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdeal
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.ConstClosure

section Chart

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω}

theorem exists_chart_div (h : CoordTie ℤ ξ x) :
    ∃ c, x c ≠ 0 ∧ ∀ ω : Ω, ∃ a b : Ω, a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧
      b ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧ b ≠ 0 ∧ ω = a / b := by
  let η : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  obtain ⟨c, hc⟩ := h.cover η
  refine ⟨c, hc.1, fun ω => ?_⟩
  obtain ⟨U, hU, hmem⟩ := h.affine c hc.1
  have hη : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, hc⟩
  have key : ∀ r : Γ(X, U), (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη r) ∈
      Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
    intro r
    refine (h.ring c hc.1 _).2 fun p hp => ?_
    have hpU : p.1 ∈ U := (hmem p.1).2 ⟨p.2, hp⟩
    exact ⟨X.presheaf.germ U p.1 hpU r, genMap_germ_eq_stalk_closed ξ p U hpU hη r⟩
  obtain ⟨b, rfl⟩ : ∃ b : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom b = ω := h.gen.bij.2 ω
  obtain ⟨r, t, hrt, hunit⟩ := stalk_eq_germ_div_of_affine hU ⟨genPt ξ, hη⟩ b
  replace hrt : b * X.presheaf.germ U (genPt ξ) hη t = X.presheaf.germ U (genPt ξ) hη r := hrt
  replace hunit : IsUnit (X.presheaf.germ U (genPt ξ) hη t) := hunit
  have hne : (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη t) ≠ 0 :=
    (hunit.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  refine ⟨_, _, key r, key t, hne, ?_⟩
  rw [eq_div_iff hne]
  exact ((Scheme.stalkClosedPointTo ξ).hom.map_mul _ _).symm.trans
    (congrArg (Scheme.stalkClosedPointTo ξ).hom hrt)

theorem adjoin_le_subfield (F : Subfield Ω) {c : κ} (h : ∀ j, x j / x c ∈ F) {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c)) : a ∈ F := by
  induction ha using Algebra.adjoin_induction with
  | mem t ht => obtain ⟨j, rfl⟩ := ht; exact h j
  | algebraMap n => simpa using intCast_mem F n
  | add s t _ _ hs ht => exact add_mem hs ht
  | mul s t _ _ hs ht => exact mul_mem hs ht

theorem subfield_eq_top {c : κ} (hc : ∀ ω : Ω, ∃ a b : Ω, a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧
      b ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧ b ≠ 0 ∧ ω = a / b)
    (F : Subfield Ω) (h : ∀ j, x j / x c ∈ F) : F = ⊤ := by
  refine eq_top_iff.2 fun ω _ => ?_
  obtain ⟨a, b, ha, hb, -, rfl⟩ := hc ω
  exact div_mem (adjoin_le_subfield F h ha) (adjoin_le_subfield F h hb)

end Chart

section Field

variable {Ω : Type} [Field Ω]

theorem charZero_of_isArithVar {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    {y : (Σ k, J k) → Ω} {n : ℕ} (h : IsArithVar (mCoordIdeal y) n) : CharZero Ω := by
  obtain ⟨-, -, hH, -⟩ := h
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing J) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]
    have e : mConeMap y (C (n : ℤ)) = C (n : Ω) := by
      simp [mConeMap, aeval_C]
    rw [e, hn, map_zero]
  rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing J) = ⊥ from hH] at hmem
  simpa using hmem

theorem dedekind_finite_of_finite [CharZero Ω] (hf : FiniteDimensional ℚ (algebraicClosure ℚ Ω))
    (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] :
    IsDedekindDomain A ∧ Module.Finite ℤ A := by
  let L := algebraicClosure ℚ Ω
  have hmem : ∀ a : A, algebraMap A Ω a ∈ L := fun a =>
    mem_algebraicClosure_iff'.2 ((IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).2 ⟨a, rfl⟩).tower_top
  letI : Algebra A L := ((algebraMap A Ω).codRestrict L.toSubalgebra.toSubring hmem).toAlgebra
  have hcoe : ∀ a : A, ((algebraMap A L a : L) : Ω) = algebraMap A Ω a := fun _ => rfl
  haveI : IsScalarTower ℤ A L := inferInstance
  haveI : NumberField L := ⟨⟩
  haveI : IsIntegralClosure A ℤ L := by
    refine ⟨fun a b hab => IsIntegralClosure.algebraMap_injective A ℤ Ω ?_, fun {v} => ?_⟩
    · rw [← hcoe, ← hcoe, hab]
    · rw [← isIntegral_algebraMap_iff (A := L) (B := Ω) (R := ℤ) ]
      rw [IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := Ω)]
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨a, Subtype.ext ha⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a, rfl⟩
  haveI : IsDomain A := (IsIntegralClosure.algebraMap_injective A ℤ Ω).isDomain _
  exact ⟨IsIntegralClosure.isDedekindDomain ℤ ℚ L A, IsIntegralClosure.finite ℤ ℚ L A⟩

end Field

section Local

variable {Ω : Type} [Field Ω]

theorem isIntegrallyClosedIn_of_atPrime (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω]
    (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω]
    [IsScalarTower A O Ω] : IsIntegrallyClosedIn O Ω := by
  have hA := IsIntegralClosure.algebraMap_injective A ℤ Ω
  have hs : ∀ s : m.primeCompl, algebraMap A Ω s ≠ 0 := fun s h0 =>
    s.2 (by rw [hA (h0.trans (map_zero _).symm)]; exact m.zero_mem)
  refine isIntegrallyClosedIn_iff.2 ⟨?_, fun {w} hw => ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun o ho => ?_
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj m.primeCompl o
    have e' := congrArg (algebraMap O Ω) e
    simp only [map_mul, ho, zero_mul, ← IsScalarTower.algebraMap_apply] at e'
    have ha : a = 0 := hA (e'.symm.trans (map_zero _).symm)
    rw [ha, map_zero] at e
    exact (IsLocalization.map_units O s).mul_left_eq_zero.1 e
  · obtain ⟨s, hsw⟩ := IsIntegral.exists_multiple_integral_of_isLocalization m.primeCompl w hw
    haveI : Algebra.IsIntegral ℤ A := IsIntegralClosure.isIntegral_algebra ℤ Ω
    have hz : IsIntegral ℤ (s • w) := isIntegral_trans _ hsw
    obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).1 hz
    refine ⟨IsLocalization.mk' O a s, ?_⟩
    have h1 : algebraMap O Ω (IsLocalization.mk' O a s) * algebraMap A Ω s = algebraMap A Ω a := by
      rw [IsScalarTower.algebraMap_apply A O Ω s, ← map_mul, IsLocalization.mk'_spec,
        ← IsScalarTower.algebraMap_apply]
    have h2 : algebraMap A Ω a = algebraMap A Ω s * w := by
      rw [ha, Submonoid.smul_def, Algebra.smul_def]
    exact mul_right_cancel₀ (hs s) (by rw [h1, h2, mul_comm])

end Local

theorem const_closure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω], IsDedekindDomain A ∧ Module.Finite ℤ A ∧ Function.Injective (algebraMap A Ω) ∧ HasConstants ℤ A y ∧ ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], IsIntegrallyClosedIn O Ω ∧ fnField O y = ⊤ := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV A _ _ _
  classical
  haveI : CharZero Ω := charZero_of_isArithVar hV
  obtain ⟨c₀, -, hdiv⟩ := exists_chart_div 𝔐.tie
  have hfin : FiniteDimensional ℚ (algebraicClosure ℚ Ω) := by
    refine GroundTheory.Heights₂.Heights.Inter.RelAlgClosureFinite.proof ℚ Ω
      (Finset.univ.image fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c₀ k⟩) ?_
    have htop := subfield_eq_top hdiv (IntermediateField.adjoin ℚ
      ((Finset.univ.image fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c₀ k⟩ : Finset Ω) : Set Ω)).toSubfield
      fun j => IntermediateField.subset_adjoin _ _ (by simp)
    refine eq_top_iff.2 fun ω _ => ?_
    have hω : ω ∈ (⊤ : Subfield Ω) := Subfield.mem_top ω
    rw [← htop] at hω
    exact hω
  have hconst : HasConstants ℤ A y := fun c' hc' a =>
    (𝔐.tie.ring c' hc' _).2 fun p _ =>
      IntReg.mem_regAt_of_isIntegral_of_stalk _ _ _ _ 𝔐.tie.gen (𝔐.normal p.1).2 _
        ((IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).2 ⟨a, rfl⟩)
  obtain ⟨hd, hfA⟩ := dedekind_finite_of_finite hfin A
  refine ⟨hd, hfA, IsIntegralClosure.algebraMap_injective A ℤ Ω, hconst, ?_⟩
  intro m _ O _ _ _ _ _ _ _
  refine ⟨isIntegrallyClosedIn_of_atPrime A m O, subfield_eq_top hdiv _ fun j => ?_⟩
  show (∏ k, y ⟨k, j k⟩) / (∏ k, y ⟨k, c₀ k⟩) ∈ fnField O y
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun k _ => Subfield.subset_closure (Or.inr ⟨⟨k, j k, c₀ k⟩, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Num.ConstClosure
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DivSuppArithHolds
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem divSuppArith_holds : ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.divSuppArith

end GlobalTheory.CompanionTheory.Ar.Link
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenvectorComplexPoint
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FramesEig

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology _root_.Metric
open LieTangent

section Germ

variable {X : Scheme.{0}} {O : Type} [CommRing O]

def germ (s : X ⟶ Sp O) (p : X) : O →+* X.presheaf.stalk p :=
  (Spec.preimage (X.fromSpecStalk p ≫ s)).hom

theorem spec_germ (s : X ⟶ Sp O) (p : X) :
    Spec.map (CommRingCat.ofHom (germ s p)) = X.fromSpecStalk p ≫ s := by
  simp only [germ, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem map_germ (s : X ⟶ Sp O) (p : X) {K : Type} [CommRing K] (φ : X.presheaf.stalk p →+* K) (i : O →+* K)
    (h : Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p ≫ s = spMap i) (n : O) :
    φ (germ s p n) = i n := by
  have h3 : Spec.map (CommRingCat.ofHom (φ.comp (germ s p))) = Spec.map (CommRingCat.ofHom i) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, spec_germ]
    exact h
  have h4 := Spec.map_injective h3
  exact congrArg (fun g => g.hom n) h4

end Germ

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {V : Type} [AddCommGroup V] [Module Ω V]

theorem valAt_comp (M : LieModel G ξ V) {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} (f : G ⟶ G) [IsMonHom f] {e e' : V} (he : M.pt e' = M.pt e ≫ f)
    {w : epsAt z ⟶ G} (h : M.ValAt z e w) : M.ValAt z e' (w ≫ f) := by
  obtain ⟨h1, v, hv, hw⟩ := h
  refine ⟨h1, v ≫ f, ⟨?_, ?_⟩, ?_⟩
  · have ht := (isTanAt_iff v).1 hv.1
    rw [isTanAt_iff, ← Category.assoc, ht, one_comp]
  · change (M.pt e').left = _
    rw [he]
    change (M.pt e).left ≫ f.left = _
    rw [hv.2, Category.assoc]
    rfl
  · change w.left ≫ f.left = _
    rw [hw, Category.assoc]
    rfl

end Val

theorem mem_eigSp_of_valAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (σ : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) (EC : Type) [AddCommGroup EC] [Module ℂ EC] (N : LieModel Y.t.G (y ≫ Y.j) EC) (ρ : 𝓞 E →+* Module.End ℂ EC) (t : 𝓞 E →+* c.F) (e : Z.V) (w : EC), (∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → y ≫ pullback.snd _ _ = spMap σ → N.IsActOf Y.t.act.act ρ → e ∈ eigSp Z.ρ (Z.inc.comp t) → Z.M.ValAt (y ≫ Y.j) e (N.pt w) → w ∈ eigSp ρ (σ.comp t) := by
  intro E _ _ _ H D l Xo c O _ β Y U Z σ y EC _ _ N ρ t e w hfr hy hN he hv
  have mem : ∀ {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (r : 𝓞 E →+* Module.End R V)
      (τ : 𝓞 E →+* R) (u : V), u ∈ eigSp r τ ↔ ∀ a, r a u = τ a • u := by
    intro R V _ _ _ r τ u
    simp [eigSp, Submodule.mem_iInf, sub_eq_zero]
  rw [mem] at he ⊢
  have h1 : Y.j ≫ Y.s = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ spMap β := by
    show (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have hh := hv
  obtain ⟨h0, -⟩ := hh
  have hgen : ∀ n, genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h0⟩ (germ Y.s (centre (y ≫ Y.j)) n) = Z.inc (β n) := by
    intro n
    refine map_germ Y.s _ _ (Z.inc.comp β) ?_ n
    rw [← Category.assoc, spec_genMap, Category.assoc, h1, ← Category.assoc, Z.over_inc]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hcl : ∀ n, (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom (germ Y.s (centre (y ≫ Y.j)) n) = σ (β n) := by
    intro n
    refine map_germ Y.s _ _ (σ.comp β) ?_ n
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Y.s) (spec_centre (y ≫ Y.j))).trans ?_)
    change (y ≫ Y.j) ≫ Y.s = _
    rw [Category.assoc, h1, ← Category.assoc, hy]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  intro a
  obtain ⟨n, d, hd, hnd⟩ := hfr (t a)
  have hva : Z.M.ValAt (y ≫ Y.j) (Z.ρ a e) (N.pt (ρ a w)) := by
    have := Y.t.act.hom a
    rw [hN a w]
    exact valAt_comp Z.M (Y.t.act.act a) (Z.act a e) hv
  have v1 := hva.smul h0 (germ Y.s (centre (y ≫ Y.j)) d)
  have v2 := hv.smul h0 (germ Y.s (centre (y ≫ Y.j)) n)
  rw [hgen, hcl, ← LieModel.pt_smul] at v1 v2
  have e1 : Z.inc (β d) • Z.ρ a e = Z.inc (β n) • e := by
    rw [he a, smul_smul, ← hnd]
    simp [mul_comm]
  rw [e1] at v1
  have e2 := N.inj (v1.unique Z.gen v2)
  rw [← hnd, map_mul, mul_comm, mul_smul] at e2
  have hσ : σ (β d) ≠ 0 := (map_ne_zero σ).2 hd
  exact smul_right_injective EC hσ e2

end GlobalTheory.CompanionTheory.Ar.FramesEig
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenvectorLinearCombination
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CombEig

theorem pt_sum {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x : Sp R ⟶ S} {V : Type}
    [AddCommGroup V] [Module R V] (M : LieModel G x V) :
    ∀ {n : ℕ} (e : Fin n → V), M.pt (∑ i, e i) = (List.ofFn fun i => M.pt (e i)).prod
  | 0, e => by simpa using M.pt_zero
  | n + 1, e => by
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons, M.add, pt_sum M]

theorem isEigVec_comb : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (P : Type) [CommRing P] (act : OAct P G) (σ : P →+* F) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (cf : Fin n → F) (w : epsAt x ⟶ G), (∀ i, IsEigVec act x σ (v i)) → IsComb cf v w → IsEigVec act x σ w := by
  intro S G _ _ F _ x P _ act σ n v cf w hv hc
  have key : ∀ y : epsAt x ⟶ G, IsEigVec act x σ y ↔
      (IsTanAt G x y ∧ ∀ a, y ≫ act.act a = LieTangent.epsScale x (σ a) ≫ y) := by
    intro y
    unfold IsEigVec
    refine and_congr_right fun _ => forall_congr' fun a => ?_
    constructor
    · intro h
      apply Over.OverMorphism.ext
      rw [h]
      rfl
    · intro h
      rw [h]
      rfl
  have hcomm : ∀ c d : F, LieTangent.epsScale x c ≫ LieTangent.epsScale x d =
      LieTangent.epsScale x d ≫ LieTangent.epsScale x c := by
    intro c d
    have hr : (epsMul c).comp (epsMul d) = (epsMul d).comp (epsMul c) := by
      refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
      · simp [LieTangent.epsMul_fst]
      · simp [LieTangent.epsMul_snd, mul_left_comm]
    apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom (epsMul c)) ≫ Spec.map (CommRingCat.ofHom (epsMul d)) =
      Spec.map (CommRingCat.ofHom (epsMul d)) ≫ Spec.map (CommRingCat.ofHom (epsMul c))
    rw [LieTangent.spec_comp, LieTangent.spec_comp, hr]
  obtain ⟨u, hu, rfl⟩ := hc
  have hu' : ∀ i, u i = LieTangent.epsScale x (cf i) ≫ v i := by
    intro i
    apply Over.OverMorphism.ext
    rw [hu i]
    rfl
  rw [key]
  apply List.prod_induction
    (fun y => IsTanAt G x y ∧ ∀ a, y ≫ act.act a = LieTangent.epsScale x (σ a) ≫ y)
  · rintro y z ⟨hy, hy'⟩ ⟨hz, hz'⟩
    refine ⟨LieTangent.isTanAt_mul hy hz, fun a => ?_⟩
    haveI := act.hom a
    rw [MonObj.mul_comp, hy', hz', MonObj.comp_mul]
  · refine ⟨LieTangent.isTanAt_one, fun a => ?_⟩
    haveI := act.hom a
    rw [MonObj.one_comp, MonObj.comp_one]
  · intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    rw [hu']
    obtain ⟨ht, he⟩ := (key (v i)).mp (hv i)
    refine ⟨LieTangent.isTanAt_scale (cf i) ht, fun a => ?_⟩
    rw [Category.assoc, he a, ← Category.assoc, ← Category.assoc, hcomm]

end GlobalTheory.CompanionTheory.Ar.CombEig
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConstantsGenericPoint
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem exists_open_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c), 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → ∃ (cst₀ : c.F →+* 𝔐.Ω₀) (y₁ : Sp 𝔐.Ω₀ ⟶ Xo.XF c), 𝔐.ξ₀ = y₁ ≫ Y.j ∧ 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) ∧ 𝔐.fn.comp cst₀ = 𝔐.cst := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 y₀ hy
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  haveI := Y.jQ_open
  have hd : 𝔐.ξ ≫ 𝔐.f = spMap 𝔐.fn ≫ 𝔐.ξ₀ := 𝔐.fn_over

  let b₀ : 𝓞 c.F →+* 𝔐.Ω₀ := (Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom
  have hb : 𝔐.ξ₀ ≫ Y.s = spMap b₀ := (Spec.map_preimage _).symm
  have hc : 𝔐.fn.comp b₀ = 𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    have hsp : spMap (𝔐.fn.comp b₀) = spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      have hm : spMap (𝔐.fn.comp b₀) = spMap 𝔐.fn ≫ spMap b₀ := by
        rw [← Spec.map_comp]; rfl
      rw [hm, ← hb, ← 𝔐.cst_over, ← Category.assoc, ← Category.assoc, hd]
    have := CommRingCat.hom_ext_iff.1 (Spec.map_injective hsp)
    simpa using this
  have hinj : Function.Injective b₀ := by
    intro u v huv
    have h := congrArg 𝔐.fn huv
    have hu : ∀ w, 𝔐.fn (b₀ w) = 𝔐.cst (algebraMap (𝓞 c.F) c.F w) := fun w => RingHom.congr_fun hc w
    rw [hu, hu] at h
    exact IsFractionRing.injective (𝓞 c.F) c.F (𝔐.cst.injective h)
  let cst₀ : c.F →+* 𝔐.Ω₀ := IsFractionRing.lift hinj
  have hl : cst₀.comp (algebraMap (𝓞 c.F) c.F) = b₀ := by
    ext w
    exact IsFractionRing.lift_algebraMap hinj w
  have hfn : 𝔐.fn.comp cst₀ = 𝔐.cst := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) ?_
    rw [RingHom.comp_assoc, hl, hc]
  have hs : 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) := by rw [hl, hb]
  have hcomp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap (g.comp f) = spMap g ≫ spMap f := by
    intro A B C _ _ _ f g
    rw [← Spec.map_comp]; rfl

  let w : Sp 𝔐.Ω₀ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) :=
    pullback.lift 𝔐.ξ₀ (spMap cst₀) (by rw [hs, hcomp])

  let u : c.F →+* Ω := (Spec.preimage (y₀ ≫ pullback.snd _ _)).hom
  have hu : y₀ ≫ pullback.snd _ _ = spMap u := (Spec.map_preimage _).symm
  have huc : u = 𝔐.cst := by
    have hsp : spMap (u.comp (algebraMap (𝓞 c.F) c.F)) = spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [hcomp, ← hu, ← 𝔐.cst_over, ← Category.assoc 𝔐.ξ, hy, Model.j]
      simp only [Category.assoc]
      rw [pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
    have h1 := CommRingCat.hom_ext_iff.1 (Spec.map_injective hsp)
    have h2 : u.comp (algebraMap (𝓞 c.F) c.F) = 𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by simpa using h1
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h2
  have hw : spMap 𝔐.fn ≫ w = y₀ ≫ Y.jQ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← hd, hy, Model.j, Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, ← hcomp, hfn, Category.assoc, Y.jQ_over, hu, huc]
  have hr : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ : ∃ a', (spMap 𝔐.fn) a' = a :=
      ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩
    refine ⟨y₀ a', ?_⟩
    have := congrArg (fun φ => φ a') hw
    simpa using this.symm
  refine ⟨cst₀, IsOpenImmersion.lift Y.jQ w hr, ?_, hs, hfn⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

end GlobalTheory.CompanionTheory.Ar.GenPoint
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExistsPosOfFamilyExists
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num

def FamilyExistsPos : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω]
    (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q →
    ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) →
    ∀ p ∈ S, HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E →
    ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ →
    ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω],
      AtPlacesOver A Ω p fun O _ _ _ _ => ∀ t₀, ∃ (Sg : Type) (_ : Fintype Sg) (e : Sg → CMType H ⊕ CMType H)
        (φ' : Equiv.Perm Sg) (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F p) (w : O)
        (σ : Sg → F →+* IsLocalRing.ResidueField O)
        (Df : (∀ k, J k) → LieLatticeData Ω F (D.p + D.q) Sg (fun τ => labelRk D (e τ)) fun τ => labelRk D (e τ).swap),
        t₀ ∈ Set.range e ∧ (∀ τ, e (φ' τ) = φ (e τ)) ∧ IsPreFamily O y p w σ φ' Df ∧
        IsFamilyOf O y Df (fun τ => 𝔐.dR (e τ)) (fun τ => 𝔐.HT p (e τ)) (fun τ => 𝔐.dR (e τ).swap)
          (fun τ => 𝔐.HT p (e τ).swap) (fun τ => b (e τ)) fun τ => b (e τ).swap

end GlobalTheory.CompanionTheory.Ar.Num
end

