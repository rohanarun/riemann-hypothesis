module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0076
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

section Rings

variable {S : Scheme.{0}} {A B D : Type} [CommRing A] [CommRing B] [CommRing D]

theorem dualMap_comp (f : A →+* B) (g : B →+* D) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap]

theorem spec_dualMap_comp (f : A →+* B) (g : B →+* D) :
    Spec.map (CommRingCat.ofHom (dualMap (g.comp f))) =
      Spec.map (CommRingCat.ofHom (dualMap g)) ≫ Spec.map (CommRingCat.ofHom (dualMap f)) := by
  rw [dualMap_comp]
  exact Spec.map_comp (CommRingCat.ofHom (dualMap f)) (CommRingCat.ofHom (dualMap g))

theorem isTanAt_epsHom {G : Over S} [GrpObj G] (φ : A →+* B) (x : Spec (CommRingCat.of A) ⟶ S)
    (x' : Spec (CommRingCat.of B) ⟶ S) (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x') (v : epsAt x ⟶ G)
    (hv : IsTanAt G x v) : IsTanAt G x' (LieCarrier.epsHom φ x x' h ≫ v) := by
  rw [LieEx.isTanAt_iff] at hv ⊢
  have key : (LieEx.zsec x' : _ ⟶ LieEx.ob x' B) ≫ LieCarrier.epsHom φ x x' h =
      (Over.homMk (Spec.map (CommRingCat.ofHom φ)) h : Over.mk x' ⟶ Over.mk x) ≫ LieEx.zsec x := by
    ext1
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a => ?_
    simp [dualMap, TrivSqZeroExt.fst_add]
  rw [← Category.assoc, key, Category.assoc, hv, MonObj.comp_one]

theorem stalk_hom_ext {X : Scheme.{0}} (c : X) (a b : X.presheaf.stalk c →+* B)
    (h : Spec.map (CommRingCat.ofHom a) ≫ X.fromSpecStalk c = Spec.map (CommRingCat.ofHom b) ≫ X.fromSpecStalk c) :
    a = b := by
  have h1 := (cancel_mono (X.fromSpecStalk c)).1 h
  have h2 := Spec.map_injective h1
  exact congrArg CommRingCat.Hom.hom h2

end Rings

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E] {R : Type} [CommRing R] [IsLocalRing R] {C : Type} [Field C] [Algebra R C]

theorem centre_specializes (z : Spec (CommRingCat.of R) ⟶ X) :
    centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) ⤳ centre z := by
  have h : (Spec.map (CommRingCat.ofHom (algebraMap R C))) (IsLocalRing.closedPoint C) ⤳
      IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint _
  exact h.map z.continuous

theorem valAt_base (M : LieModel G ξ E) (z : Spec (CommRingCat.of R) ⟶ X) {e : E} (hc : genPt ξ ⤳ centre z)
    (hc' : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z))
    (v : epsAt (R := X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) ⟶ G)
    (hv : M.Extends ⟨centre z, hc⟩ e v) (t : epsAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) ⟶ G)
    (u : epsAt z ⟶ G) (ht : t.left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) ≫ u.left)
    (hu : u.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫ v.left) :
    M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) e t := by
  set_option maxHeartbeats 0 in
  have hsp := centre_specializes (C := C) z
  have F1 : Spec.map (CommRingCat.ofHom (X.presheaf.stalkSpecializes hsp).hom) ≫ X.fromSpecStalk (centre z) =
      X.fromSpecStalk (centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have gen_eq : (genMap ξ ⟨_, hc'⟩).comp (X.presheaf.stalkSpecializes hsp).hom = genMap ξ ⟨_, hc⟩ := by
    apply stalk_hom_ext
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, F1]
    exact (LieCarrier.genMap_fromSpecStalk ⟨_, hc'⟩).trans (LieCarrier.genMap_fromSpecStalk ⟨_, hc⟩).symm
  have s_eq : (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)).hom.comp
      (X.presheaf.stalkSpecializes hsp).hom = (algebraMap R C).comp (Scheme.stalkClosedPointTo z).hom := by
    apply stalk_hom_ext
    have L : Spec.map (X.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo
        (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)) ≫ X.fromSpecStalk (centre z) =
        Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z :=
      (congrArg (· ≫ X.fromSpecStalk (centre z)) (Spec.map_comp _ _)).trans ((Category.assoc _ _ _).trans
        ((congrArg (Spec.map (Scheme.stalkClosedPointTo _) ≫ ·)
          (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp)).trans
            (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _)))
    have Rt : Spec.map (Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom (algebraMap R C)) ≫
        X.fromSpecStalk (centre z) = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z :=
      (congrArg (· ≫ X.fromSpecStalk (centre z)) (Spec.map_comp _ _)).trans ((Category.assoc _ _ _).trans
        (congrArg (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ ·)
          (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z)))
    exact L.trans Rt.symm
  refine ⟨hc', LieCarrier.epsHom (X.presheaf.stalkSpecializes hsp).hom _ _ F1 ≫ v,
    ⟨isTanAt_epsHom _ _ _ _ _ hv.1, ?_⟩, ?_⟩
  · change (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap (genMap ξ ⟨_, hc'⟩))) ≫
      Spec.map (CommRingCat.ofHom (dualMap (X.presheaf.stalkSpecializes hsp).hom)) ≫ v.left
    have e := spec_dualMap_comp (X.presheaf.stalkSpecializes hsp).hom (genMap ξ ⟨_, hc'⟩)
    rw [gen_eq] at e
    exact hv.2.trans ((congrArg (· ≫ v.left) e).trans (Category.assoc _ _ _))
  · change t.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo _).hom)) ≫
      Spec.map (CommRingCat.ofHom (dualMap (X.presheaf.stalkSpecializes hsp).hom)) ≫ v.left
    have e1 := spec_dualMap_comp (Scheme.stalkClosedPointTo z).hom (algebraMap R C)
    have e2 := spec_dualMap_comp (X.presheaf.stalkSpecializes hsp).hom
      (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)).hom
    have e3 := (congrArg (fun f : X.presheaf.stalk (centre z) →+* C => Spec.map (CommRingCat.ofHom (dualMap f)))
      s_eq).symm.trans e2
    exact ht.trans ((congrArg (_ ≫ ·) hu).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ v.left) (e1.symm.trans e3)).trans (Category.assoc _ _ _))))

end GlobalTheory.CompanionTheory.Ar.LieFib

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem lieLat_fibAt_iff : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (R : Type) [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (C : Type) [Field C] [Algebra R C] (EC : Type) [AddCommGroup EC] [Module C EC] [Module R EC] [IsScalarTower R C EC] (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) EC), IsCptGen ξ → Smooth G.hom → genPt ξ ⤳ centre z → genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) → ∀ w : EC, w ∈ M.fibAt M.lat z MC ↔ ∃ v : epsAt z ⟶ G, IsTanAt G z v ∧ (MC.pt w).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) ≫ v.left := by
  intro X G _ _ Ω _ ξ E _ _ M R _ _ z C _ _ EC _ _ _ _ MC hξ hG h h' w
  obtain ⟨ER, _, _, ⟨MR⟩⟩ := lieModel_exists X G R z
  obtain ⟨ev, hev, -, hspan⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieLat_val X G Ω ξ E M R z h ER MR hξ hG
  obtain ⟨evC, hevC, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieLat_val X G Ω ξ E M C _ h' EC MC hξ hG
  have hj : ∀ u : ER, ∃ w, MC.pt w = LieCarrier.epsHom (algebraMap R C) z _ rfl ≫ MR.pt u := fun u =>
    MC.onto _ (LieFib.isTanAt_epsHom _ _ _ _ _ (MR.tan u))
  choose j hj using hj
  have hjl : ∀ u, (MC.pt (j u)).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) ≫ (MR.pt u).left := fun u =>
    congrArg CommaMorphism.left (hj u)
  have hadd : ∀ u u', j (u + u') = j u + j u' := fun u u' => MC.inj (by
    rw [hj, MC.add, hj, hj, MR.add, MonObj.comp_mul])
  have hsmul : ∀ (r : R) u, j (r • u) = r • j u := fun r u => MC.inj (Over.OverMorphism.ext (by
    rw [← algebraMap_smul C r (j u), MC.smul, hjl, hjl, MR.smul]
    have e : Spec.map (CommRingCat.ofHom (epsMul (algebraMap R C r))) ≫
        Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) =
        Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) ≫ Spec.map (CommRingCat.ofHom (epsMul r)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        LieCarrier.dualMap_epsMul]
    rw [← Category.assoc, ← e, Category.assoc]))
  let jL : ER →ₗ[R] EC := { toFun := j, map_add' := hadd, map_smul' := hsmul }
  have hgen : ∀ (e : E) (he : e ∈ M.lat ⟨centre z, h⟩),
      M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) e (MC.pt (j (ev ⟨e, he⟩))) := by
    intro e he
    obtain ⟨h2, v, hv, hu⟩ := (hev e _).2 ⟨he, rfl⟩
    exact LieFib.valAt_base M z h h' v hv _ _ (hjl _) hu
  constructor
  · intro hw
    have hle : M.fibAt M.lat z MC ≤ LinearMap.range jL := by
      refine Submodule.span_le.2 ?_
      rintro w' ⟨h2, e, he, hval⟩
      obtain ⟨he', hw'⟩ := (hevC e _).1 hval
      obtain ⟨he'', hw''⟩ := (hevC e _).1 (hgen e he)
      exact ⟨ev ⟨e, he⟩, hw''.symm.trans hw'⟩
    obtain ⟨u, rfl⟩ := hle hw
    exact ⟨MR.pt u, MR.tan u, hjl u⟩
  · rintro ⟨v, hv, hw⟩
    obtain ⟨u, rfl⟩ := MR.onto v hv
    have hwu : w = j u := MC.inj (Over.OverMorphism.ext (hw.trans (hjl u).symm))
    subst hwu
    have hu : u ∈ Submodule.span R (Set.range ev) := hspan ▸ Submodule.mem_top
    have hle : (Submodule.span R (Set.range ev)).map jL ≤ M.fibAt M.lat z MC := by
      rw [Submodule.map_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨⟨e, he⟩, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨h, e, he, hgen e he⟩
    exact hle (Submodule.mem_map_of_mem hu)

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelActionSpecialize
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ValueSpan

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology _root_.Metric

theorem mem_eigSp_iff {R E O : Type} [CommRing R] [AddCommGroup E] [Module R E] [CommRing O]
    {ρ : O →+* Module.End R E} {σ : O →+* R} {v : E} : v ∈ eigSp ρ σ ↔ ∀ a, ρ a v = σ a • v := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem valAt_act {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {V : Type}
    [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) {F : Type} [Field F] {z : Sp F ⟶ X} {W : Type}
    [AddCommGroup W] [Module F W] (Mz : LieModel G z W) {A : Type} [CommRing A] (act : OAct A G)
    {ρ : A →+* Module.End Ω V} {ρz : A →+* Module.End F W} (hρ : M.IsActOf act.act ρ)
    (hρz : Mz.IsActOf act.act ρz) (a : A) {e : V} {w : W} (h : M.ValAt z e (Mz.pt w)) :
    M.ValAt z (ρ a e) (Mz.pt (ρz a w)) := by
  haveI : IsMonHom (act.act a) := act.hom a
  obtain ⟨h', v, ⟨ht, he⟩, hw⟩ := h
  refine ⟨h', v ≫ act.act a, ⟨?_, ?_⟩, ?_⟩
  · show _ ≫ (v ≫ act.act a).left = (1 : Over.mk _ ⟶ G).left
    have h1 : (1 : Over.mk (X.fromSpecStalk (centre z)) ⟶ G) ≫ act.act a = 1 := MonObj.one_comp _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (act.act a).left) ht).trans (congrArg CommaMorphism.left h1))
  · rw [hρ a e, Over.comp_left, he]
    exact Category.assoc _ _ _
  · rw [hρz a w, Over.comp_left, hw]
    exact Category.assoc _ _ _

theorem value_span : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (F : Type) [Field F] (z : Sp F ⟶ X) (h : genPt ξ ⤳ centre z) (W : Type) [AddCommGroup W] [Module F W] (Mz : LieModel G z W) (A : Type) [CommRing A] (act : OAct A G) (ρ : A →+* Module.End Ω V) (ρz : A →+* Module.End F W) (K : Type) [Field K] (inc : K →+* Ω) (βF : K →+* F) (σ : A →+* K) (n : ℕ) (e : Fin n → A) (cf : Fin n → K) (r : ℕ) (b : Fin r → V), IsCptGen ξ → Smooth G.hom → M.IsActOf act.act ρ → Mz.IsActOf act.act ρz → (∀ k : K, ValAt ξ z (inc k) (βF k)) → ∑ k, cf k * σ (e k) = 1 → (∀ (a : A) (w : V), ρ a (∑ k, inc (cf k) • ρ (e k) w) = inc (σ a) • ∑ k, inc (cf k) • ρ (e k) w) → (M.eigLat ρ (inc.comp σ)).IsFrameAt b ⟨centre z, h⟩ → ∃ u : Fin r → W, (∀ i, M.ValAt z (b i) (Mz.pt (u i))) ∧ Submodule.span F (Set.range u) = eigSp ρz (βF.comp σ) := by
  intro X G _ _ Ω _ ξ V _ _ M F _ z h W _ _ Mz A _ act ρ ρz K _ inc βF σ n e cf r b hgen hsm hρ hρz hinc hsum hπ hb
  obtain ⟨ev, hval, hsmul, hspan⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieLat_val X G Ω ξ V M F z h W Mz hgen hsm
  have hreg : ∀ k : K, inc k ∈ regAt ξ ⟨centre z, h⟩ := by
    intro k
    obtain ⟨_, s, hs, _⟩ := hinc k
    exact ⟨s, hs⟩
  have hvalr : ∀ c : regAt ξ ⟨centre z, h⟩, ∃ t : F, ValAt ξ z (c : Ω) t := by
    rintro ⟨_, s, rfl⟩
    exact ⟨_, h, s, rfl, rfl⟩
  have hself : ∀ l : M.lat ⟨centre z, h⟩, M.ValAt z l (Mz.pt (ev l)) :=
    fun l => (hval _ _).2 ⟨l.2, rfl⟩
  have hact : ∀ (a : A) (l : M.lat ⟨centre z, h⟩), ∃ he : ρ a l ∈ M.lat ⟨centre z, h⟩,
      ev ⟨ρ a l, he⟩ = ρz a (ev l) :=
    fun a l => (hval _ _).1 (valAt_act M Mz act hρ hρz a (hself l))
  have hbm : ∀ i, b i ∈ (M.eigLat ρ (inc.comp σ)) ⟨centre z, h⟩ := fun i => by
    rw [hb.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hbl : ∀ i, b i ∈ M.lat ⟨centre z, h⟩ := fun i => (hbm i).1
  have hbe : ∀ i, b i ∈ eigSp ρ (inc.comp σ) := fun i => (hbm i).2
  refine ⟨fun i => ev ⟨b i, hbl i⟩, fun i => hself ⟨b i, hbl i⟩, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine mem_eigSp_iff.2 fun a => ?_
    obtain ⟨he, h2⟩ := hact a ⟨b i, hbl i⟩
    have h3 : ρ a (b i) = inc (σ a) • b i := mem_eigSp_iff.1 (hbe i) a
    have h4 : (⟨ρ a (b i), he⟩ : M.lat ⟨centre z, h⟩) =
        (⟨inc (σ a), hreg _⟩ : regAt ξ ⟨centre z, h⟩) • (⟨b i, hbl i⟩ : M.lat ⟨centre z, h⟩) := Subtype.ext h3
    have h5 : ρz a (ev ⟨b i, hbl i⟩) = βF (σ a) • ev ⟨b i, hbl i⟩ := by
      rw [← h2]
      refine (congrArg ev h4).trans ?_
      exact hsmul _ _ _ (hinc _)
    exact h5
  · intro w hw
    have hw' := mem_eigSp_iff.1 hw
    let πW : W →ₗ[F] W := ∑ k, βF (cf k) • ρz (e k)
    have hπw : πW w = w := by
      have h1 : ∀ k, βF (cf k) • ρz (e k) w = βF (cf k * σ (e k)) • w := fun k => by
        rw [hw' (e k), map_mul, mul_smul]
        rfl
      simp only [πW, LinearMap.sum_apply, LinearMap.smul_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_congr rfl fun k _ => h1 k, ← Finset.sum_smul, ← map_sum, hsum, map_one, one_smul]
    have key : ∀ l : M.lat ⟨centre z, h⟩,
        πW (ev l) ∈ Submodule.span F (Set.range fun i => ev ⟨b i, hbl i⟩) := by
      intro l
      choose he hk using fun k => hact (e k) l
      let c : Fin n → regAt ξ ⟨centre z, h⟩ := fun k => ⟨inc (cf k), hreg _⟩
      let m : M.lat ⟨centre z, h⟩ := ∑ k, c k • (⟨ρ (e k) l, he k⟩ : M.lat ⟨centre z, h⟩)
      have hevm : ev m = πW (ev l) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [πW, LinearMap.sum_apply, LinearMap.smul_apply, m, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hsmul _ _ _ (hinc (cf k)), hk k]
      have hmv : (m : V) = ∑ k, inc (cf k) • ρ (e k) l := by
        simp only [m, AddSubmonoidClass.coe_finsetSum]
        exact Finset.sum_congr rfl fun _ _ => rfl
      have hme : (m : V) ∈ eigSp ρ (inc.comp σ) := mem_eigSp_iff.2 fun a => by
        rw [hmv]
        exact hπ a l
      have hmL : (m : V) ∈ (M.eigLat ρ (inc.comp σ)) ⟨centre z, h⟩ := ⟨m.2, hme⟩
      rw [hb.2] at hmL
      obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmL
      choose t ht using fun i => hvalr (d i)
      have hm : m = ∑ i, d i • (⟨b i, hbl i⟩ : M.lat ⟨centre z, h⟩) := by
        apply Subtype.ext
        rw [← hd, AddSubmonoidClass.coe_finsetSum]
        exact Finset.sum_congr rfl fun _ _ => rfl
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hevm, hm, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [hsmul _ _ _ (ht i)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hwt : w ∈ Submodule.span F (Set.range ev) := by
      rw [hspan]
      exact Submodule.mem_top
    rw [← hπw]
    refine Submodule.span_induction (p := fun y _ => πW y ∈
      Submodule.span F (Set.range fun i => ev ⟨b i, hbl i⟩)) ?_ ?_ ?_ ?_ hwt
    · rintro _ ⟨l, rfl⟩
      exact key l
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [map_smul]
      exact Submodule.smul_mem _ c hx

end GlobalTheory.CompanionTheory.Ar.ValueSpan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackSmooth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LiePull

section Lat

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {Ω : Type} [Field Ω]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem lat_eq_span (M : LieModel G ξ E) (p : Cpt ξ)
    (hx : Spec.map (CommRingCat.ofHom (genMap ξ p)) ≫ X.fromSpecStalk p.1 = ξ) {r : ℕ}
    (b : Fin r → ExtE hx M) (hsp : Submodule.span (X.presheaf.stalk p.1) (Set.range b) = ⊤) :
    M.lat p = Submodule.span (regAt ξ p) (Set.range fun k => val (b k)) := by
  have car := (lieLat_carrier X G Ω ξ E M p).1
  apply le_antisymm
  · intro e he
    obtain ⟨v, hv⟩ := (car e).1 he
    let y : ExtE hx M := ⟨e, v, hv⟩
    have hy : y ∈ Submodule.span (X.presheaf.stalk p.1) (Set.range b) := by
      rw [hsp]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy
    have he' : e = ∑ k, genMap ξ p (c k) • val (b k) := by
      have h1 : val y = e := rfl
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h1, ← hc, map_sum]
      rfl
    rw [he']
    refine Submodule.sum_mem _ fun k _ => ?_
    exact Submodule.smul_mem _ (⟨genMap ξ p (c k), c k, rfl⟩ : regAt ξ p) (Submodule.subset_span ⟨k, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact (car _).2 (val_spec (b k))

theorem ext_basis {A : Type} [CommRing A] [IsLocalRing A] {g : A →+* Ω} {x : Spec (CommRingCat.of A) ⟶ X}
    (hs : Smooth G.hom) (hg : Function.Injective g) (hx : Spec.map (CommRingCat.ofHom g) ≫ x = ξ)
    (M : LieModel G ξ E) : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) A (ExtE hx M)) :=
  _root_.GlobalTheory.CompanionTheory.Ar.LieFreeSmooth.lieModel_free_of_smooth X G hs A x (ExtE hx M) (extModel hg hx M)

end Lat

theorem frame : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X'), IsCptGen ξ → IsCptGen ξ' → ∀ (f : X' ⟶ X) (i : Ω →+* Ω') (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → Smooth G.hom → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (E' : Type) [AddCommGroup E'] [Module Ω' E'] (M' : LieModel G' ξ' E') (j : E →+ E'), (∀ v, (M'.pt (j v)).left ≫ φ = spMap (dualMap i) ≫ (M.pt v).left) → ∀ q' : Cpt ξ', ∃ (r : ℕ) (B : Module.Basis (Fin r) Ω E) (B' : Module.Basis (Fin r) Ω' E') (v : Fin r → (epsAt (X.fromSpecStalk (f q'.1)) ⟶ G)) (v' : Fin r → (epsAt (X'.fromSpecStalk q'.1) ⟶ G')), (∀ k, B' k = j (B k)) ∧ M.lat ⟨f q'.1, hd.specializes q'⟩ = Submodule.span (regAt ξ ⟨f q'.1, hd.specializes q'⟩) (Set.range B) ∧ M'.lat q' = Submodule.span (regAt ξ' q') (Set.range B') ∧ (∀ k, M.Extends ⟨f q'.1, hd.specializes q'⟩ (B k) (v k)) ∧ (∀ k, M'.Extends q' (B' k) (v' k)) ∧ ∀ k, (v' k).left ≫ φ = spMap (dualMap (f.stalkMap q'.1).hom) ≫ (v k).left := by
  intro X X' Ω Ω' _ _ ξ ξ' hξ hξ' f i hd G _ _ G' _ _ φ hG hs E _ _ M E' _ _ M' j hj q'
  have hp : genPt ξ ⤳ f q'.1 := hd.specializes q'
  have hx := LieCarrier.genMap_fromSpecStalk (ξ := ξ) ⟨f q'.1, hp⟩
  have hx' := LieCarrier.genMap_fromSpecStalk (ξ := ξ') q'
  have hρ : Spec.map (CommRingCat.ofHom (f.stalkMap q'.1).hom) ≫ X.fromSpecStalk (f q'.1) =
      X'.fromSpecStalk q'.1 ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hρ' : (genMap ξ' q').comp (f.stalkMap q'.1).hom = i.comp (genMap ξ ⟨f q'.1, hp⟩) :=
    RingHom.ext (RegAtDom.genMap_stalkMap hd q'.1 q'.2 hp)
  have hg := hξ.inj ⟨f q'.1, hp⟩
  have hg' := hξ'.inj q'
  obtain ⟨r, ⟨b⟩⟩ := ext_basis (A := X.presheaf.stalk (f q'.1)) hs hg hx M
  obtain ⟨hli, hsp⟩ := bc hs (genMap ξ ⟨f q'.1, hp⟩) (X.fromSpecStalk (f q'.1)) ξ hx (extModel hg hx M) M b
    (fun k => val (b k)) (fun k => (vec_spec (b k)).2)
  let B : Module.Basis (Fin r) Ω E := Module.Basis.mk hli hsp.ge
  have hB : ∀ k, B k = val (b k) := fun k => by simp [B]
  obtain ⟨hli', hsp'⟩ := bc hs i ξ (ξ' ≫ f) hd.symm M (LieMove.pushModel hG M') B (fun k => j (B k)) (fun k => hj _)
  let B' : Module.Basis (Fin r) Ω' E' := Module.Basis.mk hli' hsp'.ge
  have hB' : ∀ k, B' k = j (B k) := fun k => by simp [B']
  have up : ∀ k, ∃ u : epsAt (X'.fromSpecStalk q'.1) ⟶ G',
      Ext (genMap ξ' q') (X'.fromSpecStalk q'.1) M' (j (val (b k))) u ∧
      u.left ≫ φ = spMap (dualMap (f.stalkMap q'.1).hom) ≫ (vec (b k)).left :=
    fun k => ext_up hG hj hρ hρ' hx' (vec_spec (b k))
  choose u hu huφ using up
  let b' : Fin r → ExtE hx' M' := fun k => ⟨j (val (b k)), u k, hu k⟩
  obtain ⟨-, hsp''⟩ := bc hs (f.stalkMap q'.1).hom (X.fromSpecStalk (f q'.1)) (X'.fromSpecStalk q'.1 ≫ f) hρ
    (extModel hg hx M) (LieMove.pushModel hG (extModel hg' hx' M')) b b'
    (fun k => by
      have e₁ : vec (b' k) = u k := (vec_spec (b' k)).unique hg' (hu k)
      show (vec (b' k)).left ≫ φ = _
      rw [e₁]
      exact huφ k)
  refine ⟨r, B, B', fun k => vec (b k), u, hB', ?_, ?_, ?_, ?_, huφ⟩
  · rw [lat_eq_span M _ hx b b.span_eq]
    congr 2
    exact funext fun k => (hB k).symm
  · rw [lat_eq_span M' q' hx' b' hsp'']
    congr 2
    exact funext fun k => by rw [hB', hB]; rfl
  · intro k
    rw [hB]
    exact vec_spec (b k)
  · intro k
    rw [hB', hB]
    exact hu k

end GlobalTheory.CompanionTheory.Ar.LiePull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtTorPull

theorem spMap_comp_fields {A B C : Type} [Field A] [Field B] [Field C] (i : A →+* B) (τ : B →+* C) :
    spMap (τ.comp i) = spMap τ ≫ spMap i := by
  simp only [spMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem cancel_spMap {K K' : Type} [Field K] [Field K'] (τ : K →+* K') {Z : Scheme.{0}}
    (a b : Spec (CommRingCat.of K) ⟶ Z) (h : spMap τ ≫ a = spMap τ ≫ b) : a = b := by
  have hd : IsSchemeTheoreticallyDominant (spMap τ) :=
    LieEx.std_of_inj (CommRingCat.ofHom τ) τ.injective
  have hs : Function.Surjective (spMap τ) := by
    intro p
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of K')) := inferInstance
    exact ⟨x, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩
  exact LieEx.epi_of_surj (spMap τ) hs a b h

theorem secVal_eq_of_eq {B : Type} [CommRing B] {Z : Scheme.{0}} {x x' : Spec (CommRingCat.of B) ⟶ Z} (e : x = x')
    (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) (h' : ⊤ ≤ x' ⁻¹ᵁ W) (s : Γ(Z, W)) : secVal x W h s = secVal x' W h' s := by
  subst e
  rfl

theorem torsion_clause : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (n : ℕ) (e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ), GenWeil G L ξ n e → FullTorsion G ξ n → ∀ (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → FullTorsion G' ξ' n → ∀ (L' : LB G'.left) (e' : (Over.mk ξ' ⟶ G') → (Over.mk ξ' ⟶ G') → Ω'ˣ), GenWeil G' L' ξ' n e' → ∀ (y : Over.mk ξ ⟶ G) (y' : Over.mk ξ' ⟶ G'), y ^ n = 1 → y' ^ n = 1 → (∀ (g : Over.mk ξ ⟶ G) (g' : Over.mk ξ' ⟶ G'), g ^ n = 1 → g' ^ n = 1 → g'.left ≫ φ = spMap i ≫ g.left → (e' y' g' : Ω') = i (e y g)) → (∀ (g : Over.mk ξ ⟶ G), g ^ n = 1 → ∃ g' : Over.mk ξ' ⟶ G', g' ^ n = 1 ∧ g'.left ≫ φ = spMap i ≫ g.left) → (∀ (g' : Over.mk ξ' ⟶ G'), g' ^ n = 1 → ∃ g : Over.mk ξ ⟶ G, g ^ n = 1 ∧ g'.left ≫ φ = spMap i ≫ g.left) → ∀ (W : G.left.Opens) (s : Γ(G.left, W)),
  (∀ (k : Type) [Field k] [IsAlgClosed k] (τ : Ω →+* k) (xk g : Over.mk (spMap τ ≫ ξ) ⟶ G) (c : kˣ) (h : ⊤ ≤ g.left ⁻¹ᵁ W), xk.left = spMap τ ≫ y.left → g ^ n = 1 → Out.WeilIs G L n xk g (unitOn c) → secVal (B := k) g.left W h s = c) →
  (∀ (k : Type) [Field k] [IsAlgClosed k] (τ : Ω' →+* k) (xk g : Over.mk (spMap τ ≫ ξ') ⟶ G') (c : kˣ) (h : ⊤ ≤ g.left ⁻¹ᵁ (φ ⁻¹ᵁ W)), xk.left = spMap τ ≫ y'.left → g ^ n = 1 → Out.WeilIs G' L' n xk g (unitOn c) → secVal (B := k) g.left (φ ⁻¹ᵁ W) h (φ.app W s) = c) := by
  intro X X' Ω Ω' _ _ ξ ξ' f i hD G _ _ L n e hGW hFT G' _ _ φ hP hFT' L' e' hGW' y y' hy hy' hcomp hlift hdown W s hW
    k _ _ τ xk g c h hxk hgn hWeil
  obtain ⟨x', hx⟩ := hFT' k τ g hgn
  let U : Over.mk (spMap τ ≫ ξ') ⟶ Over.mk ξ' := Over.homMk (spMap τ) rfl
  have hgU : g = U ≫ x' := Over.OverMorphism.ext hx
  have hx'n : x' ^ n = 1 := by
    have e1 : preHom (G := G') U (x' ^ n) = preHom (G := G') U 1 := by
      rw [map_pow, map_one]
      show (U ≫ x') ^ n = 1
      rw [← hgU]
      exact hgn
    apply Over.OverMorphism.ext
    apply cancel_spMap τ
    exact congrArg (fun z => z.left) e1
  obtain ⟨g₀, hg₀, hxg⟩ := hdown x' hx'n
  have hc' : (c : k) = τ (e' y' x') := (hGW'.weil y' x' hy' hx'n k τ xk g c hxk hx).1 hWeil
  have hc : (c : k) = (τ.comp i) (e y g₀) := by
    rw [hc', hcomp g₀ x' hg₀ hx'n hxg]
    rfl
  let U₀ : Over.mk (spMap (τ.comp i) ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap (τ.comp i)) rfl
  have hW1 : Out.WeilIs G L n (U₀ ≫ y) (U₀ ≫ g₀) (unitOn c) :=
    (hGW.weil y g₀ hy hg₀ k (τ.comp i) (U₀ ≫ y) (U₀ ≫ g₀) c rfl rfl).2 hc
  have hg₁ : (U₀ ≫ g₀) ^ n = 1 := by
    have e1 : preHom (G := G) U₀ (g₀ ^ n) = (U₀ ≫ g₀) ^ n := map_pow _ _ _
    rw [← e1, hg₀, map_one]
  have hl : g.left ≫ φ = (U₀ ≫ g₀).left := by
    show g.left ≫ φ = spMap (τ.comp i) ≫ g₀.left
    rw [hx, Category.assoc, hxg, spMap_comp_fields, Category.assoc]
  have h' : ⊤ ≤ (g.left ≫ φ) ⁻¹ᵁ W := h
  have h₁ : ⊤ ≤ (U₀ ≫ g₀).left ⁻¹ᵁ W := hl ▸ h'
  rw [HtPull.seccomp k _ _ g.left φ W h h' s, secVal_eq_of_eq hl W h' h₁ s]
  exact hW k (τ.comp i) (U₀ ≫ y) (U₀ ≫ g₀) c h₁ rfl hg₁ hW1

end GlobalTheory.CompanionTheory.Ar.HtTorPull
end
end

