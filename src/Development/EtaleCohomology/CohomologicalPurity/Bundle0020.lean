module

public import Development.EtaleCohomology.CohomologicalPurity.LeafMonoPf
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0017
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0006
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0005
public import Development.EtaleCohomology.CohomologicalPurity.LeafExactPf
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0007
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0003
public import Development.EtaleCohomology.CohomologicalPurity.PresSheafify
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0016
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0015
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0012
public import Development.EtaleCohomology.TateTwists.Bundle0007
public import Development.EtaleCohomology.KummerTheory.Bundle0001

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.FinLeafBd
section
namespace LateralTheory.Fin.LeafBd
theorem etale_boundary_monomorphism_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafMono := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafMono_of
theorem etale_relative_boundary_pushout_property_holds : LateralTheory.CohomologicalPurity.Bd.LeafPush := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafPush_of
theorem etale_boundary_good_pair_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafGood := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafGood_of
theorem etale_boundary_connecting_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafDelta := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafDelta_of
theorem etale_boundary_exact_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafExact := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafExact_of
theorem etale_boundary_generator_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafGen := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafGen_of
theorem etale_boundary_image_hom_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafImgHom := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafImgHom_of <;> first | exact etale_boundary_generator_of_thom_isomorphism
theorem etale_boundary_image_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafImg := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafImg_of <;> first | exact etale_boundary_image_hom_of_thom_isomorphism
theorem etale_boundary_map_of_thom_isomorphism : LateralTheory.CohomologicalPurity.LeafBd := by
  apply LateralTheory.CohomologicalPurity.Bd.goal_of <;> first | exact etale_boundary_monomorphism_of_thom_isomorphism | exact etale_relative_boundary_pushout_property_holds | exact etale_boundary_good_pair_of_thom_isomorphism | exact etale_boundary_connecting_of_thom_isomorphism | exact etale_boundary_exact_of_thom_isomorphism | exact etale_boundary_generator_of_thom_isomorphism | exact etale_boundary_image_hom_of_thom_isomorphism | exact etale_boundary_image_of_thom_isomorphism
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafBd := etale_boundary_map_of_thom_isomorphism
end LateralTheory.Fin.LeafBd
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafAffEqvPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem affSieve_mem (U : Scheme.{0}) (S : Sieve U)
    (h : ∀ (A : Type) [CommRing A] (f : Spec (CommRingCat.of A) ⟶ U), S f) : S ∈ Scheme.etaleTopology U := by
  apply Scheme.zariskiTopology_le_etaleTopology
  refine GrothendieckTopology.superset_covering _ ?_ (Scheme.Cover.mem_grothendieckTopology U.affineCover)
  rintro _ _ ⟨_, k, _, ⟨i⟩, rfl⟩
  exact S.downward_closed (h _ (U.affineCover.f i)) k

theorem locBij {R : Type} [CommRing R] {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (φ : F ⟶ G)
    (h : ∀ (A : Type) [CommRing A], IsIso (φ.app (op (Spec (CommRingCat.of A))))) :
    Presheaf.IsLocallyInjective Scheme.etaleTopology φ ∧ Presheaf.IsLocallySurjective Scheme.etaleTopology φ := by
  have hb : ∀ (A : Type) [CommRing A], Function.Bijective (φ.app (op (Spec (CommRingCat.of A)))) :=
    fun A _ => ConcreteCategory.bijective_of_isIso _
  refine ⟨⟨fun {X} x y hxy => ?_⟩, ⟨fun {U} s => ?_⟩⟩
  · refine affSieve_mem _ _ fun A _ f => ?_
    apply (hb A).1
    change φ.app _ (F.map f.op x) = φ.app _ (F.map f.op y)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
  · refine affSieve_mem _ _ fun A _ f => ?_
    obtain ⟨t, ht⟩ := (hb A).2 (G.map f.op s)
    exact ⟨t, ht⟩

theorem freeIso (R : Type) [CommRing R] {P Q : PSh} (g : P ⟶ Q)
    (h : ∀ (A : Type) [CommRing A], Function.Bijective (g.app (op (Spec (CommRingCat.of A))))) :
    IsIso ((free R).map g) := by
  have h2 : ∀ (A : Type) [CommRing A], IsIso (((freeP R).map g).app (op (Spec (CommRingCat.of A)))) := by
    intro A _
    have : IsIso (g.app (op (Spec (CommRingCat.of A)))) := (isIso_iff_bijective _).2 (h A)
    change IsIso ((uliftFunctor.{1} ⋙ ModuleCat.free (ULift.{1} R)).map (g.app (op (Spec (CommRingCat.of A)))))
    infer_instance
  obtain ⟨h3, h4⟩ := locBij _ h2
  have hW : Scheme.etaleTopology.W ((freeP R).map g) := by
    rw [GrothendieckTopology.W_iff_isLocallyBijective]; exact ⟨h3, h4⟩
  exact (GrothendieckTopology.W_iff _ _).1 hW

theorem chainsIso (R : Type) [CommRing R] {E E' : Spc} (e : E ⟶ E')
    (h : ∀ (n : ℕ) (A : Type) [CommRing A], Function.Bijective
      (fun x : Sx E n (Spec (CommRingCat.of A)) => (e.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) x)) :
    IsIso ((chains R).map e) := by
  have : IsIso (((SimplicialObject.whiskering _ _).obj (free R)).map e) := by
    have hh : ∀ n, IsIso ((((SimplicialObject.whiskering _ _).obj (free R)).map e).app n) := by
      intro n
      induction n using Opposite.rec with | op n => ?_
      induction n using SimplexCategory.rec with | _ n => ?_
      exact freeIso R _ (h n)
    exact NatIso.isIso_of_isIso_app _
  change IsIso ((ComplexShape.embeddingDownNat.extendFunctor (Shv R)).map
    ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (((SimplicialObject.whiskering _ _).obj (free R)).map e)))
  infer_instance

theorem LeafAffEqv_of : LeafAffEqv := by
  intro hA1 q _ E E' e h i n
  have := chainsIso (ZMod q) e h
  exact hA1 (ZMod q) ((chains (ZMod q)).map e) (tw q i) n

end LateralTheory.CohomologicalPurity.Thom
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafAugLocalPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

abbrev PCx (R : Type) [CommRing R] := ChainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℕ

def Cyc {R : Type} [CommRing R] (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (x : (K.X n).obj T) : Prop :=
  ∀ m, ((K.d n m).app T).hom x = 0

def Bdy {R : Type} [CommRing R] (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (x : (K.X n).obj T) : Prop :=
  ∃ y, ((K.d (n + 1) n).app T).hom y = x

def InjC {R : Type} [CommRing R] {K L : PCx R} (φ : K ⟶ L) (n : ℕ) : Prop :=
  ∀ (T : Scheme.{0}ᵒᵖ) (x : (K.X n).obj T), Cyc K n T x → Bdy L n T ((φ.f n).app T |>.hom x) →
    ∃ S ∈ Scheme.etaleTopology.{0} T.unop, ∀ ⦃U : Scheme.{0}⦄ (f : U ⟶ T.unop), S f → Bdy K n (op U) (((K.X n).map f.op).hom x)

def SurjC {R : Type} [CommRing R] {K L : PCx R} (φ : K ⟶ L) (n : ℕ) : Prop :=
  ∀ (T : Scheme.{0}ᵒᵖ) (x : (L.X n).obj T), Cyc L n T x →
    ∃ S ∈ Scheme.etaleTopology.{0} T.unop, ∀ ⦃U : Scheme.{0}⦄ (f : U ⟶ T.unop), S f →
      ∃ x', Cyc K n (op U) x' ∧ Bdy L n (op U) (((φ.f n).app (op U)).hom x' - ((L.X n).map f.op).hom x)

def LeafHomLoc : Prop := ∀ (R : Type) [CommRing R] (K L : PCx R) (φ : K ⟶ L) (n : ℕ), InjC φ n → SurjC φ n →
  Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap φ n) ∧
  Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap φ n)

def LeafAugSurj : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R] (n : ℕ),
    SurjC ((chainsP R).map (aug _ hc)) n

def LeafAugInj : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R] (n : ℕ),
    InjC ((chainsP R).map (aug _ hc)) n

theorem LeafAugLocal_of (h1 : LeafHomLoc) (hs : LeafAugSurj) (hi : LeafAugInj) : LeafAugLocal := by
  intro J _ D X c ho hcov hdir hc R _ n
  exact h1 R _ _ _ n (hi J D X c ho hcov hdir hc R n) (hs J D X c ho hcov hc R n)

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafCmpPfAll
section
namespace LateralTheory.CohomologicalPurity.Cl

theorem LeafCmp_of_Mat (hMat : LeafMat) : LeafCmp := LeafCmp_of hMat LeafCmpNb_pf LeafCmpId_pf

end LateralTheory.CohomologicalPurity.Cl
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafDescOGluePfP
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl

def LeafResK : Prop := ∀ (q : ℕ) (i : ℤ),
  (∀ s, Injective ((res _ (tw q i)).X s)) ∧ ∀ s < 0, IsZero ((res _ (tw q i)).X s)

def LeafZcPull : Prop := ∀ {R : Type} [CommRing R] (K : Cx R) {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens)
  (U : X.Opens), U' ≤ f ⁻¹ᵁ U → ∀ (n : ℤ) (a : Sec (K.X n) X), a ∈ Zc K U n → Sec.res f a ∈ Zc K U' n

def LeafZcIn : Prop := ∀ {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U W V : X.Opens) (h : V ≤ W), V ≤ U →
  ∀ (n : ℤ) (a : Sec (K.X n) W.toScheme), a ∈ Zc K (W.ι ⁻¹ᵁ U) n → rs h a = 0

private theorem desc_sres_zero {R : Type} [CommRing R] {G : Shv R} {X Y : Scheme.{0}} (f : Y ⟶ X) :
    Sec.res f (0 : Sec G X) = 0 := by
  show (G.obj.map f.op).hom 0 = 0
  exact map_zero _

private theorem Bd_zero {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U : X.Opens) (n : ℤ) : Bd K U n 0 :=
  ⟨0, desc_sres_zero _, smap_zero _⟩

private theorem leι {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) (U : X.Opens) :
    V.ι ⁻¹ᵁ U ≤ X.homOfLE h ⁻¹ᵁ (W.ι ⁻¹ᵁ U) :=
  le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) le_rfl

private theorem descent_glue_of_residue_pullback_inclusion (hK : LeafResK) (hP : LeafZcPull) (hI : LeafZcIn) : LeafDescOGlue := by
  intro hD hF q X U m i hL A V s hcov H
  obtain ⟨cls, hon, hker, hnat⟩ := hD q m i
  have H1 : ∀ n < m, ∀ (W : X.Opens), ∀ a ∈ Zc (res _ (tw q i)) (W.ι ⁻¹ᵁ U) n, ∀ x ∈ W,
      ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ Bd (res _ (tw q i)) (V.ι ⁻¹ᵁ U) n (rs h a) := by
    intro n hn W a ha x hx
    by_cases hxU : x ∈ U
    · refine ⟨W ⊓ U, inf_le_left, ⟨hx, hxU⟩, ?_⟩
      rw [hI _ U W (W ⊓ U) _ inf_le_right n a ha]
      exact Bd_zero _ _ _
    · obtain ⟨V', hV'W, hxV', hsub⟩ := hL x W hx
      refine ⟨V', hV'W, hxV', ?_⟩
      obtain ⟨cn, -, hkern, -⟩ := hD q n i
      have hz := hP _ (X.homOfLE hV'W) (V'.ι ⁻¹ᵁ U) (W.ι ⁻¹ᵁ U) (leι hV'W U) n a ha
      have := hsub n hn
      exact (hkern (V'.ι ⁻¹ᵁ U) ⟨_, hz⟩).1 (Subsingleton.elim _ _)
  obtain ⟨-, hglue⟩ := hF _ (res _ (tw q i)) (hK q i).1 (hK q i).2 X U m H1
  choose l hl using fun a => hon ((V a).ι ⁻¹ᵁ U) (s a)
  let V' : Option A → X.Opens := fun o => Option.elim o U V
  let a' : ∀ k, Sec ((res _ (tw q i)).X m) (V' k).toScheme := fun
    | none => 0
    | some a => (l a).1
  have hmem : ∀ k, a' k ∈ Zc (res _ (tw q i)) ((V' k).ι ⁻¹ᵁ U) m := by
    rintro (_ | a)
    · exact zero_mem _
    · exact (l a).2
  have hcv : ∀ x : X, ∃ k, x ∈ V' k := by
    intro x
    by_cases hx : x ∈ U
    · exact ⟨none, hx⟩
    · obtain ⟨a, ha⟩ := hcov x hx
      exact ⟨some a, ha⟩
  have hcmp : ∀ k l', ∀ x ∈ V' k, x ∈ V' l' → ∃ (T : X.Opens) (hk : T ≤ V' k) (hl : T ≤ V' l'), x ∈ T ∧
      Bd (res _ (tw q i)) (T.ι ⁻¹ᵁ U) m (rs hk (a' k) - rs hl (a' l')) := by
    intro k l' x hk hl'
    by_cases hxU : x ∈ U
    · refine ⟨V' k ⊓ V' l' ⊓ U, inf_le_left.trans inf_le_left, inf_le_left.trans inf_le_right, ⟨⟨hk, hl'⟩, hxU⟩, ?_⟩
      rw [hI _ U (V' k) _ _ inf_le_right m (a' k) (hmem k), hI _ U (V' l') _ _ inf_le_right m (a' l') (hmem l'),
        sub_zero]
      exact Bd_zero _ _ _
    · rcases k with _ | a
      · exact absurd hk hxU
      rcases l' with _ | b
      · exact absurd hl' hxU
      obtain ⟨T, ha, hb, ha', hb', hxT, heq⟩ := H a b x hk hl' hxU
      refine ⟨T, ha, hb, hxT, ?_⟩
      have za := hP _ (X.homOfLE ha) (T.ι ⁻¹ᵁ U) ((V a).ι ⁻¹ᵁ U) ha' m (l a).1 (l a).2
      have zb := hP _ (X.homOfLE hb) (T.ι ⁻¹ᵁ U) ((V b).ι ⁻¹ᵁ U) hb' m (l b).1 (l b).2
      have e1 := hnat (X.homOfLE ha) (T.ι ⁻¹ᵁ U) ((V a).ι ⁻¹ᵁ U) ha' (l a) ⟨_, za⟩ rfl
      have e2 := hnat (X.homOfLE hb) (T.ι ⁻¹ᵁ U) ((V b).ι ⁻¹ᵁ U) hb' (l b) ⟨_, zb⟩ rfl
      rw [hl a] at e1
      rw [hl b] at e2
      have h0 : cls (T.ι ⁻¹ᵁ U) (⟨_, za⟩ - ⟨_, zb⟩) = 0 := by
        rw [map_sub, ← e1, ← e2, heq, sub_self]
      exact (hker _ _).1 h0
  obtain ⟨c, hc, hcb⟩ := hglue (Option A) V' a' hmem hcv hcmp
  refine ⟨cls U ⟨c, hc⟩, fun a => ?_⟩
  have zc := hP _ (V a).ι ((V a).ι ⁻¹ᵁ U) U le_rfl m c hc
  show Hs.pull q (opnMap (V a).ι ((V a).ι ⁻¹ᵁ U) U le_rfl) m i (cls U ⟨c, hc⟩) = s a
  rw [hnat (V a).ι ((V a).ι ⁻¹ᵁ U) U le_rfl ⟨c, hc⟩ ⟨_, zc⟩ rfl, ← hl a, ← sub_eq_zero, ← map_sub]
  exact (hker _ _).2 (hcb (some a))

private theorem desc_sres_comp {R : Type} [CommRing R] {G : Shv R} {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (a : Sec G X) :
    Sec.res g (Sec.res f a) = Sec.res (g ≫ f) a := by
  show (G.obj.map g.op).hom ((G.obj.map f.op).hom a) = (G.obj.map (g ≫ f).op).hom a
  rw [op_comp, Functor.map_comp]; rfl

private theorem sres_id {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (a : Sec G X) : Sec.res (𝟙 X) a = a := by
  show (G.obj.map (𝟙 X).op).hom a = a
  rw [op_id, CategoryTheory.Functor.map_id]; rfl

private theorem desc_smap_res {R : Type} [CommRing R] {G H : Shv R} (φ : G ⟶ H) {X Y : Scheme.{0}} (f : Y ⟶ X) (a : Sec G X) :
    Sec.map φ (Sec.res f a) = Sec.res f (Sec.map φ a) := by
  show (φ.hom.app (op Y)).hom ((G.obj.map f.op).hom a) = (H.obj.map f.op).hom ((φ.hom.app (op X)).hom a)
  have h := φ.hom.naturality f.op
  exact congrArg (fun t => t.hom a) h

private theorem LeafZcPull_pf : LeafZcPull := by
  intro R _ K X' X f U' U h n a ha
  obtain ⟨h1, h2⟩ := (mem_Zc a).1 ha
  refine (mem_Zc _).2 ⟨?_, ?_⟩
  · rw [desc_sres_comp, ← Scheme.Hom.resLE_comp_ι f h, ← desc_sres_comp, h1, desc_sres_zero]
  · rw [desc_smap_res, h2, desc_sres_zero]

private theorem LeafZcIn_pf : LeafZcIn := by
  intro R _ K X U W V h hU n a ha
  obtain ⟨h1, -⟩ := (mem_Zc a).1 ha
  have e : (⊤ : V.toScheme.Opens) ≤ X.homOfLE h ⁻¹ᵁ (W.ι ⁻¹ᵁ U) :=
    le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) ((Scheme.Opens.ι_preimage_self V).symm.le.trans (fun y hy => hU hy))
  have h0 : Sec.res (⊤ : V.toScheme.Opens).ι (rs h a) = 0 := by
    rw [desc_sres_comp, ← Scheme.Hom.resLE_comp_ι (X.homOfLE h) e, ← desc_sres_comp, h1, desc_sres_zero]
  rw [← sres_id (rs h a), ← Scheme.toIso_inv_ι, ← desc_sres_comp, h0, desc_sres_zero]

private theorem resK_inj (q : ℕ) (i : ℤ) (s : ℤ) : Injective ((res _ (tw q i)).X s) := by unfold GlobalTheory.EtC.res; infer_instance
private theorem LeafResK_pf : LeafResK := fun q i => ⟨resK_inj q i, fun s hs => by
  have : (res _ (tw q i)).IsStrictlyGE 0 := by unfold GlobalTheory.EtC.res; infer_instance
  exact CochainComplex.isZero_of_isStrictlyGE (res _ (tw q i)) 0 s hs⟩

theorem LeafDescOGlue_of : LeafDescOGlue := descent_glue_of_residue_pullback_inclusion LeafResK_pf LeafZcPull_pf LeafZcIn_pf

end LateralTheory.CohomologicalPurity.Cl
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafDiscNrmPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Cl.DiscNrmPf

def up {P : PSh} {U : Scheme.{0}} {p q : ℕ} (x : Sx (disc.obj P) p U) : Sx (disc.obj P) q U := x

theorem face_disc {P : PSh} {U : Scheme.{0}} {p : ℕ} (x : Sx (disc.obj P) (p + 1) U) (i : Fin (p + 2)) :
    ((disc.obj P).δ i).app (op U) x = up x := rfl

open LateralTheory.KummerTheory.AW in
theorem normal (R : Type) [CommRing R] (I : Cx R) (P : PSh) (n : ℤ) (α : Cocycle ((chains R).obj (disc.obj P)) I n) :
    ∃ β : Cochain ((chains R).obj (disc.obj P)) I (n - 1), ∀ p s h U y,
      ev (R := R) (α.1 - δ (n - 1) n β) (p + 1) s h U y = 0 := by
  have hα : δ n (n + 1) α.1 = 0 := (Cocycle.mem_iff n (n + 1) rfl α.1).1 α.2
  have hEval {k : ℤ} (γ : Cochain ((chains R).obj (disc.obj P)) I k) (p : ℕ) (s : ℤ)
      (h : -(p : ℤ) + k = s) (U : Scheme.{0}) (x : Sx (disc.obj P) p U) :
      ev (R := R) γ p s h U x = Sec.map ((chainsXIso R (disc.obj P) p).inv ≫ γ.v _ _ h) (freeGen R P U x) := rfl
  have hD {k l : ℤ} (hkl : k + 1 = l) (γ : Cochain ((chains R).obj (disc.obj P)) I k)
      (U : Scheme.{0}) (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + k = s)
      (ht : -((p + 1 : ℕ) : ℤ) + l = t) (x : Sx (disc.obj P) (p + 1) U) :
      ev (R := R) (δ k l γ) (p + 1) t ht U x = Sec.map (I.d s t) (ev (R := R) γ (p + 1) s hs U x) +
        l.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
          ev (R := R) γ p t (by omega) U (((disc.obj P).δ i).app (op U) x) := by
    rw [hEval, δ_v k l hkl γ _ _ ht s (-(p : ℤ)) (by omega) (by omega), Preadditive.comp_add,
      Linear.comp_units_smul, reassoc_of% (LateralTheory.KummerTheory.chains_d R (disc.obj P) p),
      Preadditive.sum_comp, sec_map_add]
    congr 1
    rw [Units.smul_def, Units.smul_def, sec_map_zsmul, sec_map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Preadditive.zsmul_comp, sec_map_zsmul, hEval]
    congr 1
    exact congrArg (Sec.map ((chainsXIso R (disc.obj P) p).inv ≫ γ.v (-(p : ℤ)) t (by omega)))
      (map_freeGen ((disc.obj P).δ i) U x)
  let a (p : ℕ) (s : ℤ) (h : -(p : ℤ) + (n - 1) = s) (U : Scheme.{0}) (x : Sx (disc.obj P) p U) : Sec (I.X s) U :=
    if Odd p then n.negOnePow • ev (R := R) α.1 (p + 1) s (by push_cast; omega) U (up x) else 0
  have hex (p : ℕ) (s : ℤ) (h : -(p : ℤ) + (n - 1) = s) :
      ∃ φ : (free R).obj P ⟶ I.X s, ∀ U x, Sec.map φ (freeGen R P U x) = a p s h U x :=
    LateralTheory.EtaleFoundations.EvMkPf.free_hom_exists R P (I.X s) (a p s h) (by
      intro V U g x
      dsimp only [a]
      split_ifs
      · rw [Units.smul_def, Units.smul_def]
        refine (map_zsmul ((I.X s).obj.map g.op).hom _ _).trans ?_
        congr 1
        change Sec.res g (ev (R := R) α.1 (p + 1) s _ U (up x)) =
          ev (R := R) α.1 (p + 1) s _ V (up (P.map g.op x))
        rw [hEval, hEval, sec_map_res, freeGen_res]
        rfl
      · exact map_zero _)
  choose φ hφ using hex
  let f (p : ℕ) (s : ℤ) (h : -(p : ℤ) + (n - 1) = s) : ((chains R).obj (disc.obj P)).X (-(p : ℤ)) ⟶ I.X s :=
    (chainsXIso R (disc.obj P) p).hom ≫ φ p s h
  let β : Cochain ((chains R).obj (disc.obj P)) I (n - 1) := Cochain.mk (fun i j hij =>
    if hi : 0 ≤ -i then
      (((chains R).obj (disc.obj P)).XIsoOfEq (show i = -(((-i).toNat : ℕ) : ℤ) by omega)).hom ≫
        f (-i).toNat j (by omega)
    else 0)
  have hβ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + (n - 1) = s) (U : Scheme.{0}) (x : Sx (disc.obj P) p U) :
      ev (R := R) β p s h U x = a p s h U x := by
    have hComponent (q : ℕ) (hq : q = p) (e : -(p : ℤ) = -(q : ℤ)) (h' : -(q : ℤ) + (n - 1) = s) :
        (((chains R).obj (disc.obj P)).XIsoOfEq e).hom ≫ f q s h' = f p s h := by
      subst q
      simp
    have hv : β.v (-(p : ℤ)) s h = f p s h := by
      simp only [β, Cochain.mk_v]
      rw [dite_eq_left (by omega)]
      exact hComponent _ (by omega) _ _
    rw [hEval, hv]
    simp only [f, Iso.inv_hom_id_assoc]
    exact hφ p s h U x
  refine ⟨β, ?_⟩
  intro p s h U y
  have hSub : ev (R := R) (α.1 - δ (n - 1) n β) (p + 1) s h U y =
      ev (R := R) α.1 (p + 1) s h U y - ev (R := R) (δ (n - 1) n β) (p + 1) s h U y := by
    rw [hEval, hEval, hEval, Cochain.sub_v, Preadditive.comp_sub]
    exact map_sub (AddMonoidHom.mk' (fun m => Sec.map m (freeGen R P U y)) (fun _ _ => sec_map_add _ _ _)) _ _
  rw [hSub, sub_eq_zero, hD (by omega) β U p (s - 1) s (by push_cast at h ⊢; omega) h y]
  simp only [face_disc, hβ, a]
  rcases Nat.even_or_odd p with hp | hp
  · have hp1 : Odd (p + 1) := hp.add_one
    have hp0 : ¬ Odd p := Nat.not_odd_iff_even.mpr hp
    simp only [hp1, hp0, ite_true, ite_false, smul_zero, Finset.sum_const_zero, add_zero]
    have hc := hD rfl α.1 U (p + 1) (s - 1) s (by push_cast at h ⊢; omega)
      (by push_cast at h ⊢; omega) (up y)
    rw [hα] at hc
    have hZero : ev (R := R) (0 : Cochain ((chains R).obj (disc.obj P)) I (n + 1))
        (p + 1 + 1) s (by push_cast at h ⊢; omega) U (up y) = 0 := by simp [ev]
    rw [hZero] at hc
    simp only [face_disc] at hc
    rw [← Finset.sum_smul, LateralTheory.KummerTheory.altsum] at hc
    have he : ¬ Even (p + 1 + 2) := by
      rw [Nat.not_even_iff_odd]; exact hp1.add_even even_two
    simp only [he, ite_false, one_smul] at hc
    rw [Int.negOnePow_succ, Units.neg_smul] at hc
    have key := add_neg_eq_zero.1 hc.symm
    rw [Units.smul_def]
    refine Eq.trans ?_ (map_zsmul ((I.d (s - 1) s).hom.app (op U)).hom _ _).symm
    rw [show (ModuleCat.Hom.hom ((I.d (s - 1) s).hom.app (op U))) (ev α.1 (p + 1 + 1) (s - 1) (by push_cast at h ⊢; omega) U (up y))
        = n.negOnePow • ev α.1 (p + 1) s (by push_cast at h ⊢; omega) U (up (up y)) from key]
    rw [← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]
    rfl
  · have hp1 : ¬ Odd (p + 1) := Nat.not_odd_iff_even.mpr hp.add_one
    simp only [hp1, hp, ite_true, ite_false, map_zero, zero_add]
    rw [← Finset.sum_smul, LateralTheory.KummerTheory.altsum]
    have he : ¬ Even (p + 2) := by
      rw [Nat.not_even_iff_odd]; exact hp.add_even even_two
    simp only [he, ite_false, one_smul, smul_smul, Int.units_mul_self]
    rfl

end LateralTheory.CohomologicalPurity.Cl.DiscNrmPf

namespace LateralTheory.CohomologicalPurity.Cl

open DiscNrmPf LateralTheory.KummerTheory.AW in
theorem etale_discrete_presheaf_cocycle_normalization_holds : LeafDiscNrm := by
  intro R _ K n P z
  obtain ⟨β, hβ⟩ := normal R K P n z
  refine ⟨(chainsXIso R (disc.obj P) 0).inv ≫ (z.1 - δ (n - 1) n β).v (-((0 : ℕ) : ℤ)) n (by omega), β, ?_⟩
  rw [← sub_eq_iff_eq_add]
  have hExt (a b : Cochain ((chains R).obj (disc.obj P)) K n)
      (hab : ∀ p s h U x, ev (R := R) a p s h U x = ev (R := R) b p s h U x) : a = b := by
    ext i j hij : 1
    by_cases hi : 0 < i
    · exact (isZero_pos (R := R) (disc.obj P) i hi).eq_of_src _ _
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R (disc.obj P) p).inv]
      exact free_ext _ _ (fun U x => hab p j hij U x)
  apply hExt
  intro p s h U x
  rcases p with _ | p
  · obtain rfl : s = n := by omega
    simp only [ev, Cochain.single_v, Iso.inv_hom_id_assoc]
  · rw [hβ]
    simp only [ev]
    rw [Cochain.single_v_eq_zero _ _ _ _ _ (by push_cast; omega), comp_zero]
    rfl

theorem LeafDisc_of' : LeafDisc := LeafDisc_of etale_discrete_presheaf_cocycle_normalization_holds

end LateralTheory.CohomologicalPurity.Cl
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafHensHPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem LeafHensH_of : LeafHensH := by
  intro hH q _ C _ K hK hq i
  exact hH.2.2.2.2.2.2.2.2.2.2.2 q C K hq i

end LateralTheory.CohomologicalPurity.TubeCut
end
end

