module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle0023
public import Development.EtaleCohomology.CohomologicalPurity.LeafChartFactPf

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafTailRep0OfVec
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def Vo (N k : ℕ) : PSh := vecCat N k ⋙ Cat.objects

def voTail (d : ℕ) : Vo (d + 1) 1 ⟶ Vo d 0 where
  app U := TypeCat.ofHom fun v => (Vec.tail d U.unop).obj v
  naturality _ _ _ := rfl

def nerve0 (N k : ℕ) : (Pj N k).obj (op (SimplexCategory.mk 0)) ≅ Vo N k :=
  NatIso.ofComponents (fun U =>
    { hom := TypeCat.ofHom fun (F : ComposableArrows (Vec N k U.unop) 0) => F.obj 0
      inv := TypeCat.ofHom fun v => ComposableArrows.mk₀ (C := Vec N k U.unop) v
      hom_inv_id := by
        ext F
        exact ComposableArrows.ext₀ rfl
      inv_hom_id := rfl })
    (fun _ => rfl)

def LeafRepVec : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (_ : R →+* A),
    I.FG ∧ ∃ (h : off (Polynomial A) (I.map Polynomial.C) ≤
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I)
      (e₁ : Vo (d + 1) 1 ⨯ yoneda.obj (Spec (CommRingCat.of R)) ≅ yoneda.obj (off (Polynomial A) (I.map Polynomial.C)).toScheme)
      (e₂ : Vo d 0 ⨯ yoneda.obj (Spec (CommRingCat.of R)) ≅ yoneda.obj (off A I).toScheme),
      prod.map (voTail d) (𝟙 _) ≫ e₂.hom =
        e₁.hom ≫ yoneda.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)

theorem LeafTailRep0_of_vec (hV : LeafRepVec) : LeafTailRep0 := by
  intro d R _
  obtain ⟨A, _, I, φ, hI, h, f₁, f₂, w⟩ := hV d R
  let E := (evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk 0))
  let sq : E.obj (sp R) ≅ yoneda.obj (Spec (CommRingCat.of R)) := Iso.refl _
  refine ⟨A, inferInstance, I, φ, hI, h,
    PreservesLimitPair.iso E _ _ ≪≫ prod.mapIso (nerve0 (d + 1) 1) sq ≪≫ f₁,
    PreservesLimitPair.iso E _ _ ≪≫ prod.mapIso (nerve0 d 0) sq ≪≫ f₂, ?_⟩
  simp only [Iso.trans_hom, PreservesLimitPair.iso_hom, prod.mapIso_hom, Category.assoc]
  change E.map (prod.map _ _) ≫ _ = _
  rw [prodComparison_natural_assoc, prod.map_map_assoc, ← w, prod.map_map_assoc]
  rfl

def LeafRepPt : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (_ : R →+* A),
    I.FG ∧ ∃ (h : off (Polynomial A) (I.map Polynomial.C) ≤
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I)
      (E₁ : ∀ U : Scheme.{0}, Vec (d + 1) 1 U × (U ⟶ Spec (CommRingCat.of R)) ≃
        (U ⟶ (off (Polynomial A) (I.map Polynomial.C)).toScheme))
      (E₂ : ∀ U : Scheme.{0}, Vec d 0 U × (U ⟶ Spec (CommRingCat.of R)) ≃ (U ⟶ (off A I).toScheme)),
      (∀ {V U : Scheme.{0}} (f : V ⟶ U) v g, E₁ V ((Vec.map _ _ f).obj v, f ≫ g) = f ≫ E₁ U (v, g)) ∧
      (∀ {V U : Scheme.{0}} (f : V ⟶ U) v g, E₂ V ((Vec.map _ _ f).obj v, f ≫ g) = f ≫ E₂ U (v, g)) ∧
      ∀ (U : Scheme.{0}) v g, E₂ U ((Vec.tail d U).obj v, g) =
        E₁ U (v, g) ≫ (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h

def isoOfPt {F G : PSh} {X : Scheme.{0}} (E : ∀ U : Scheme.{0}, F.obj (op U) × G.obj (op U) ≃ (U ⟶ X))
    (hE : ∀ {V U : Scheme.{0}} (f : V ⟶ U) a b, E V (F.map f.op a, G.map f.op b) = f ≫ E U (a, b)) :
    F ⨯ G ≅ yoneda.obj X :=
  FunctorToTypes.binaryProductIso F G ≪≫
    NatIso.ofComponents (fun U => (E U.unop).toIso) (fun f => by
      ext ⟨a, b⟩
      exact hE f.unop a b)

theorem LeafRepVec_of (hP : LeafRepPt) : LeafRepVec := by
  intro d R _
  obtain ⟨A, _, I, φ, hI, h, E₁, E₂, n₁, n₂, sq⟩ := hP d R
  refine ⟨A, inferInstance, I, φ, hI, h, isoOfPt (F := Vo (d + 1) 1) E₁ (fun f a b => n₁ f a b),
    isoOfPt (F := Vo d 0) E₂ (fun f a b => n₂ f a b), ?_⟩
  have key : prod.map (voTail d) (𝟙 (yoneda.obj (Spec (CommRingCat.of R)))) ≫
      (FunctorToTypes.binaryProductIso _ _).hom = (FunctorToTypes.binaryProductIso _ _).hom ≫
      FunctorToTypes.prod.lift (FunctorToTypes.prod.fst ≫ voTail d) FunctorToTypes.prod.snd := by
    apply (cancel_mono (FunctorToTypes.binaryProductIso _ _).inv).1
    apply Limits.prod.hom_ext <;> simp <;> rw [← Category.assoc, FunctorToTypes.binaryProductIso_hom_comp_fst]
  simp only [isoOfPt, Iso.trans_hom]
  rw [reassoc_of% key, Category.assoc]
  congr 1
  ext U ⟨v, g⟩
  exact sq U.unop v g

theorem LeafTailRep0_of (hP : LeafRepPt) : LeafTailRep0 := LeafTailRep0_of_vec (LeafRepVec_of hP)

end LateralTheory.CohomologicalPurity.Thom
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafTauOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ThomClassRestriction

theorem LeafTau_of (hBd : LeafBd) (hG : LeafGeo) (hPB : LeafPB) (hTl : LeafTail)
    (hU : LeafTauU) (hT : LeafTauTop) : LeafTau :=
  LeafTau_ofU hBd hG hPB hTl hU hT

end LateralTheory.CohomologicalPurity.Thom.ThomClassRestriction
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafWCovPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

theorem wincl_mono (d : ℕ) : Mono (Wincl d) := by
  have h : ∀ n, Mono ((Wincl d).app n) := by
    intro n
    have : ∀ U, Mono (((Wincl d).app n).app U) := by
      intro U
      rw [mono_iff_injective]
      intro F G hFG
      change (F : ComposableArrows (WVec d U.unop) _) ⋙ WVec.incl d U.unop = G ⋙ WVec.incl d U.unop at hFG
      exact CategoryTheory.Functor.hext (fun i => Subtype.ext (congrArg (fun K => K.obj i) hFG))
        (fun i j a => Functor.hcongr_hom hFG a)
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app _

theorem wb_mono (d : ℕ) (R : Type) [CommRing R] : Mono (wb d R) := by
  have := wincl_mono d
  unfold wb; infer_instance

def LocCov {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) : Prop :=
  ∀ (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}) (x : (E.obj n).obj (op X)), ∃ (ι : Type) (O : ι → X.Opens),
    iSup O = ⊤ ∧ ∀ i, (∃ y, (f.app n).app (op (O i : Scheme.{0})) y = (E.obj n).map (O i).ι.op x) ∨
      (∃ y, (g.app n).app (op (O i : Scheme.{0})) y = (E.obj n).map (O i).ι.op x)

def LeafCovLoc : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Mono f → Mono g →
  LocCov f g → Cover2 R f g

def LeafWLoc : Prop := ∀ (d : ℕ) (R : Type) [CommRing R], LocCov (wb d R) (pr d R).hom

theorem LeafWCov_of (hG : LeafGeo) (hC : LeafCovLoc) (hW : LeafWLoc) : LeafWCov := by
  intro _ q _ d R _ _
  exact hC (ZMod q) (wb d R) (pr d R).hom (wb_mono d R) (hG.1 d R) (hW d R)

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafWEqvLPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

abbrev Uo (d : ℕ) (R : Type) [CommRing R] (I : Ideal (MvPolynomial (Fin d) R)) : Scheme.{0} :=
  (off (MvPolynomial (Fin d) R) I).toScheme

abbrev Gm : Scheme.{0} := Spec (CommRingCat.of (LaurentPolynomial ℤ))

def gmU (d : ℕ) (R : Type) [CommRing R] (I : Ideal (MvPolynomial (Fin d) R)) : Uo d R I ⨯ Gm ⟶ Uo d R I := prod.fst

def LeafWGm : Prop := ∀ (d : ℕ) (R : Type) [CommRing R] (I : Ideal (MvPolynomial (Fin d) R)),
  Smooth (gmU d R I) ∧ Surjective (gmU d R I)

def LeafWTors : Prop := ∀ (d : ℕ) (R : Type) [CommRing R] (I : Ideal (MvPolynomial (Fin d) R)),
  Ideal.span (Set.range MvPolynomial.X) = I →
  ∃ e : pullback (wb d R) (pr d R).hom ≅ cech (gmU d R I),
  ∀ g : (opn (off (MvPolynomial (Fin d) R) I)).left ⟶ pullback (wb d R) (pr d R).hom,
  g ≫ pullback.fst _ _ = (opn (off (MvPolynomial (Fin d) R) I)).hom ≫ wa d R → g ≫ e.hom ≫ cechAug (gmU d R I) = 𝟙 _

theorem eqv_of_iso (R : Type) [CommRing R] {E E' : Spc} (e : E ≅ E') (F : Shv R) : Eqv R e.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem LeafWEqvL_of (hGm : LeafWGm) (hT : LeafWTors) : LeafWEqvL := by
  intro hH q _ d R _ I hI hq g hg i
  obtain ⟨e, he⟩ := hT d R I hI
  obtain ⟨hsm, hsu⟩ := hGm d R I
  have hA2 : Eqv _ (cechAug (gmU d R I)) (tw q i) := hH.2.1 _ (gmU d R I) (tw q i)
  exact eqv_of_section (he g hg) (eqv_comp (eqv_of_iso _ e _) hA2)

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

