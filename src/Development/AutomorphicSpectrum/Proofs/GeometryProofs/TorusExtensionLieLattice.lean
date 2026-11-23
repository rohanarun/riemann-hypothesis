module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0092
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0129
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianHomLieExtends
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianTorusLieSub
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0113

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ToricQuot

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.GlobalTheory.CompanionTheory.Ar

theorem exists_denominator {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (δ : X →+ K) :
    ∃ (a : O) (δ' : X →+ O), a ≠ 0 ∧ (algebraMap O K).toAddMonoidHom.comp δ' = algebraMap O K a • δ := by
  let b := Module.Free.chooseBasis ℤ X
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) (fun i => δ (b i))
  choose g hg using ha
  refine ⟨a, (b.constr ℤ g).toAddMonoidHom, nonZeroDivisors.coe_ne_zero a, ?_⟩
  apply AddMonoidHom.toIntLinearMap_injective
  refine b.ext fun i => ?_
  have := hg i
  simp only [Algebra.smul_def] at this
  simp [this, Algebra.smul_def]

theorem lattice_step {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {E E' T T' : Type} [AddCommGroup E] [Module O E] [AddCommGroup E'] [Module O E'] [Module.Projective O E']
    [AddCommGroup T] [Module K T] [Module O T] [IsScalarTower O K T]
    [AddCommGroup T'] [Module K T'] [Module O T'] [IsScalarTower O K T']
    (j : E →ₗ[O] T) (j' : E' →ₗ[O] T') (hj : IsBaseChange K j) (hj' : IsBaseChange K j')
    (I : (X →+ K) →ₗ[K] T) (A : T →ₗ[K] T') (hex : ∀ t, A t = 0 ↔ ∃ δ, I δ = t) (hA : Function.Surjective A)
    (io : (X →+ O) →ₗ[O] E) (f : E →ₗ[O] E')
    (hio : ∀ δ, j (io δ) = I ((algebraMap O K).toAddMonoidHom.comp δ)) (hf : ∀ e, j' (f e) = A (j e))
    (hsat : ∀ (a : O) (y : E), a ≠ 0 → a • y ∈ LinearMap.range io → y ∈ LinearMap.range io) :
    LinearMap.ker f = LinearMap.range io ∧ ∀ e' : E', ∃ (a : O) (e : E), a ≠ 0 ∧ f e = a • e' := by
  have : IsLocalizedModule (nonZeroDivisors O) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K j).2 hj
  have : IsLocalizedModule (nonZeroDivisors O) j' :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K j').2 hj'
  have hinj : Function.Injective j' := by
    intro x y hxy
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors O) (f := j') hxy
    exact smul_right_injective E' (nonZeroDivisors.coe_ne_zero c) hc
  refine ⟨le_antisymm ?_ ?_, fun e' => ?_⟩
  · intro e he
    have h0 : A (j e) = 0 := by rw [← hf, show f e = 0 from he, map_zero]
    obtain ⟨δ, hδ⟩ := (hex _).1 h0
    obtain ⟨a, δ', ha, hδ'⟩ := exists_denominator (O := O) δ
    have h1 : j (a • e) = j (io δ') := by
      rw [hio, hδ', map_smul, map_smul, hδ, algebraMap_smul]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors O) (f := j) h1
    refine hsat a e ha (hsat c _ (nonZeroDivisors.coe_ne_zero c) ⟨(c : O) • δ', ?_⟩)
    rw [map_smul]
    exact hc.symm
  · rintro _ ⟨δ, rfl⟩
    apply hinj
    rw [hf, hio, map_zero]
    exact (hex _).2 ⟨_, rfl⟩
  · obtain ⟨t, ht⟩ := hA (j' e')
    obtain ⟨⟨e, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors O) j t
    refine ⟨s, e, nonZeroDivisors.coe_ne_zero s, hinj ?_⟩
    have hs' : (s : O) • t = j e := hs
    rw [hf, ← hs', map_smul j', ← ht, ← algebraMap_smul K (s : O) t, map_smul, algebraMap_smul]

theorem exists_model_of_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x y : Sp R ⟶ S}
    (h : x = y) {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) :
    ∃ M' : LieModel G y E, ∀ e, (M'.pt e).left = (M.pt e).left := by
  subst h
  exact ⟨M, fun _ => rfl⟩

theorem exists_fibre_model {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] (G₁ : Over (Sp R')) [GrpObj G₁] (φ : G₁.left ⟶ G.left)
    (h : IsGrpPullback G₁ G (spMap (algebraMap R R')) φ) {V : Type} [AddCommGroup V] [Module R V]
    (M : LieModel G (𝟙 _) V) :
    ∃ (T : Type) (_ : AddCommGroup T) (_ : Module R' T) (_ : Module R T) (_ : IsScalarTower R R' T)
      (M₁ : LieModel G₁ (𝟙 _) T) (j : V →ₗ[R] T),
      (∀ e, ((M₁.pt (j e)).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left)) ∧ IsBaseChange R' j := by
  obtain ⟨T, iT, mT, ⟨M'⟩⟩ := lieModel_exists _ G R' (spMap (algebraMap R R') ≫ 𝟙 _)
  letI mR : Module R T := Module.compHom T (algebraMap R R')
  have hsm : ∀ (a : R) (t : T), a • t = algebraMap R R' a • t := fun _ _ => rfl
  have tower : IsScalarTower R R' T :=
    ⟨fun a b t => by rw [Algebra.smul_def, hsm, mul_smul]⟩
  let c := algebraMap R R'
  have halg : (dualMap c).comp (algebraMap R (DualNumber R)) =
      (algebraMap R' (DualNumber R')).comp c := by
    refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_
    all_goals simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hfst : (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap c) =
      c.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    refine RingHom.ext fun a => ?_
    simp [dualMap]
  have hscale (r : R) : (dualMap c).comp (epsMul r) = (epsMul (c r)).comp (dualMap c) := by
    refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
    all_goals simp [dualMap, epsMul, mul_comm]
  let base : epsAt (spMap c ≫ 𝟙 (Sp R)) ⟶ epsAt (𝟙 (Sp R)) :=
    Over.homMk (spMap (dualMap c)) (by
      change spMap (dualMap c) ≫ Spec.map _ ≫ 𝟙 (Sp R) = Spec.map _ ≫ spMap c ≫ 𝟙 (Sp R)
      simp only [spMap]
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, halg])
  have htan (v : epsAt (𝟙 (Sp R)) ⟶ G) (hv : IsTanAt G (𝟙 _) v) :
      IsTanAt G (spMap c ≫ 𝟙 _) (base ≫ v) := by
    have h1 : (Over.homMk (spMap c) rfl : Over.mk (spMap c ≫ 𝟙 (Sp R)) ⟶ Over.mk (𝟙 (Sp R))) ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G) = 1 := MonObj.comp_one _
    have h2 : spMap c ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left = (1 : Over.mk (spMap c ≫ 𝟙 (Sp R)) ⟶ G).left := by
      rw [← h1]; rfl
    unfold IsTanAt at hv ⊢
    rw [← h2, ← hv]
    change Spec.map _ ≫ spMap (dualMap c) ≫ v.left = spMap c ≫ Spec.map _ ≫ v.left
    simp only [spMap]
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hfst]
  have ex : ∀ e, ∃ t, M'.pt t = base ≫ M.pt e :=
    fun e => M'.onto _ (htan _ (M.tan e))
  choose f hf using ex
  have hleft : ∀ e, (M'.pt (f e)).left = spMap (dualMap c) ≫ (M.pt e).left := fun e => by
    rw [hf e]; rfl
  let j : V →ₗ[R] T :=
    { toFun := f
      map_add' := fun a b => M'.inj (by rw [M'.add, hf, hf, hf, M.add, comp_mul])
      map_smul' := fun r a => M'.inj (Over.OverMorphism.ext (by
        rw [RingHom.id_apply, hsm, M'.smul, hleft, hleft, M.smul]
        simp only [spMap]
        rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
          ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hscale])) }
  have hl : ∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left) := fun e => by
    change (M'.pt (f e)).left ≫ 𝟙 G.left = _
    rw [hf]
    exact Category.comp_id _
  obtain ⟨M'', h''⟩ := exists_model_of_eq (y := 𝟙 (Sp R') ≫ spMap (algebraMap R R'))
    (by rw [Category.comp_id, Category.id_comp]) M'
  obtain ⟨M₁, h₁⟩ := (LiePull.lieModel_pullback _ _ G G₁ _ φ h R' (𝟙 _) T).1 M''
  refine ⟨T, iT, mT, mR, tower, M₁, j, fun e => ?_, _root_.GlobalTheory.CompanionTheory.Ar.lieModel_isBaseChange _ G R R' _ V T M M' j hl⟩
  have := hl e
  rw [h₁, h'', ← this]
  exact (Category.comp_id _).symm

theorem lifts_unique {R R' : Type} [CommRing R] [CommRing R'] {c : R →+* R'} {G : Over (Sp R)} [GrpObj G]
    {G₁ : Over (Sp R')} [GrpObj G₁] {φ : G₁.left ⟶ G.left} (h : IsGrpPullback G₁ G (spMap c) φ)
    {V : Type} [AddCommGroup V] [Module R V] {M : LieModel G (𝟙 _) V} {e : V} {v w : epsAt (𝟙 (Sp R')) ⟶ G₁}
    (hv : (v.left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt e).left)) (hw : (w.left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt e).left)) : v = w := by
  apply Over.OverMorphism.ext
  refine h.1.hom_ext (hv.trans hw.symm) ?_
  rw [Over.w v, Over.w w]

theorem lie_quot_full : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (G G' : Over (Sp O)) [GrpObj G] [GrpObj G'] (GK : Over (Sp K)) [GrpObj GK] (τ : TorusExtension GK) (φ : GK.left ⟶ G.left) (φ' : τ.B.left ⟶ G'.left), letI := τ.addCommGroup; letI := τ.grpB; IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap O K)) φ → IsGrpPullback τ.B G' (spMap (algebraMap O K)) φ' → ∀ (MT : LieModel (splitTorus (Sp K) τ.X) (𝟙 _) (τ.X →+ K)), IsCocharLie MT → ∀ (E : Type) [AddCommGroup E] [Module O E] (E' : Type) [AddCommGroup E'] [Module O E'] (M : LieModel G (𝟙 _) E) (M' : LieModel G' (𝟙 _) E'), ∃ (io : (τ.X →+ O) →ₗ[O] E) (f : E →ₗ[O] E'), (∀ δ, ((MT.pt ((algebraMap O K).toAddMonoidHom.comp δ) ≫ τ.i).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M.pt (io δ)).left)) ∧ (∀ (e : E) (v : epsAt (𝟙 (Sp K)) ⟶ GK), (v.left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M.pt e).left) → ((v ≫ τ.q).left ≫ φ' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M'.pt (f e)).left)) ∧ Function.Injective io ∧ LinearMap.ker f = LinearMap.range io ∧ ∀ e' : E', ∃ (a : O) (e : E), a ≠ 0 ∧ f e = a • e' := by
  intro O K _ _ _ _ _ G G' _ _ GK _ τ φ φ'
  letI := τ.addCommGroup
  letI := τ.grpB
  intro hG hG' hφ hφ' MT hMT E _ _ E' _ _ M M'
  have := τ.free
  have := τ.finite
  have := τ.q_hom
  have := τ.i_hom
  have := hG.comm
  have := hG.smooth
  have := hG'.comm
  have := hG'.smooth
  have : Mono τ.i := ⟨fun a b hab => τ.isKernel.hom_ext hab (toUnit_unique _ _)⟩
  obtain ⟨io, hio, hinj, hsat⟩ := _root_.GlobalTheory.CompanionTheory.Ar.TsOk.saturated O K G GK φ hG hφ τ.X τ.i MT hMT E M
  obtain ⟨f, hf⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieHomOk.hom_maps_lie O K G G' GK τ.B φ φ' hG hG' hφ hφ' τ.q E E' M M'
  have := (_root_.GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective _ G' O _ E' M').2
  obtain ⟨T, _, _, _, _, MK, j, hj, hbc⟩ := exists_fibre_model G GK φ hφ M
  obtain ⟨T', _, _, _, _, MK', j', hj', hbc'⟩ := exists_fibre_model G' τ.B φ' hφ' M'
  obtain ⟨I, hI, -⟩ := lieModel_exists_unique_diff _ _ GK K _ _ T MT MK τ.i
  obtain ⟨A, hA, -⟩ := lieModel_exists_unique_diff _ GK τ.B K _ T T' MK MK' τ.q
  have hex := GlobalTheory.T.torus_extension_tangent_exact K GK τ K (RingHom.id K)
  have hid : spMap (RingHom.id K) = 𝟙 (Sp K) := Spec.map_id _
  rw [hid] at hex
  refine ⟨io, f, hio, hf, hinj, lattice_step j j' hbc hbc' I A (fun t => ?_) (fun t' => ?_) io f
    (fun δ => ?_) (fun e => ?_) hsat⟩
  · have h1 : A t = 0 ↔ MK.pt t ≫ τ.q = 1 := by
      rw [← hA, ← MK'.pt_zero]
      exact MK'.inj.eq_iff.symm
    rw [h1, hex.1 _ (MK.tan t)]
    constructor
    · rintro ⟨w, hw, e⟩
      obtain ⟨δ, rfl⟩ := MT.onto w hw
      exact ⟨δ, MK.inj (by rw [hI, e])⟩
    · rintro ⟨δ, rfl⟩
      exact ⟨_, MT.tan δ, (hI δ).symm⟩
  · obtain ⟨v, hv, e⟩ := hex.2 _ (MK'.tan t')
    obtain ⟨t, rfl⟩ := MK.onto v hv
    exact ⟨t, MK'.inj (by rw [hA, e])⟩
  · apply MK.inj
    rw [hI]
    exact lifts_unique hφ (hj _) (hio δ)
  · apply MK'.inj
    rw [hA]
    exact lifts_unique hφ' (hj' _) (hf e _ (hj e))

end GlobalTheory.CompanionTheory.Ar.ToricQuot
