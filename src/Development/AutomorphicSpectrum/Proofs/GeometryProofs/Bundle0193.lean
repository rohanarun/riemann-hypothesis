module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0183
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0145
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0187
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0189
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0049
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0042
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0076
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0079
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0086
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0082
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreCurveGermPowers
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationBoundedFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0191

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelEigenFrame
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem tanW_injective (Y : Model Xo c β) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    {w w' : Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left}
    (hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x)
    (hw' : w' ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x)
    (h : tanW Y y w hw = tanW Y y w' hw') : w = w' := by
  have a₁ : w ≫ Xo.univ.t.G.hom = (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) ≫ pullback.fst _ _ := by
    rw [hw, Category.assoc, Small.ptF_fst]
  have a₂ : w' ≫ Xo.univ.t.G.hom = (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) ≫ pullback.fst _ _ := by
    rw [hw', Category.assoc, Small.ptF_fst]
  have e : Y.m0.cart.1.lift w (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) a₁ =
      Y.m0.cart.1.lift w' (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) a₂ :=
    Y.m.cart.1.hom_ext h (by rw [IsPullback.lift_snd, IsPullback.lift_snd])
  rw [← Y.m0.cart.1.lift_fst w _ a₁, e, IsPullback.lift_fst]

theorem comp_unit {T : Scheme.{0}} {A B M : CategoryTheory.Over T} [GrpObj M] (u : B ⟶ A) : u ≫ (1 : A ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (u ≫ toUnit A) (toUnit B)]

theorem eps_alg {S : Type} [CommRing S] (a : S) :
    spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ spMap (algebraMap S (DualNumber S)) =
      spMap (algebraMap S (DualNumber S)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext b <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem eps_zero {S : Type} [CommRing S] :
    spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (0 : S)) =
      spMap (algebraMap S (DualNumber S)) ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext b <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_alg {S : Type} [CommRing S] :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 1

theorem isTanAt_one {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) :
    Formalism.L2.Pj.IsTanAt x (1 : tEps x ⟶ Xo.univ.t.G).left := by
  refine ⟨Over.w _, ?_⟩
  let k : Over.mk x ⟶ tEps x := Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
    change _ ≫ _ ≫ x = x
    rw [← Category.assoc, fst_alg, Category.id_comp])
  exact congrArg (fun z => z.left) (comp_unit (M := Xo.univ.t.G) k)

theorem eps_one {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) (a : S) :
    spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ (1 : tEps x ⟶ Xo.univ.t.G).left =
      (1 : tEps x ⟶ Xo.univ.t.G).left := by
  let k : tEps x ⟶ tEps x := Over.homMk (spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a)) (by
    change _ ≫ _ ≫ x = _ ≫ x
    rw [← Category.assoc, eps_alg])
  exact congrArg (fun z => z.left) (comp_unit (M := Xo.univ.t.G) k)

theorem isEigAt_one {S : Type} [CommRing S] [Algebra c.F S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) (τ : E →+* ℂ) :
    Formalism.L2.Pj.IsEigAt c τ (Xo := Xo) (1 : tEps x ⟶ Xo.univ.t.G).left := by
  intro a
  rw [eps_one]
  haveI := Xo.univ.t.act.hom a
  have h : (1 : tEps x ⟶ Xo.univ.t.G) ≫ Xo.univ.t.act.act a = 1 := by
    rw [Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]
  exact congrArg (fun z => z.left) h

theorem eps_zero_comp {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X)
    (v : Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left) (hv : Formalism.L2.Pj.IsTanAt x v) :
    spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (0 : S)) ≫ v = (1 : tEps x ⟶ Xo.univ.t.G).left := by
  rw [eps_zero, Category.assoc, hv.2]
  let k : tEps x ⟶ Over.mk x := Over.homMk (spMap (algebraMap S (DualNumber S))) rfl
  exact congrArg (fun z => z.left) (comp_unit (M := Xo.univ.t.G) k)

def combPt {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) {n : ℕ}
    (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left))
    (hv : ∀ j, Formalism.L2.Pj.IsTanAt x (v j)) (a : Fin n → S) (i : Fin n) : tEps x ⟶ Xo.univ.t.G :=
  Over.homMk (spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (a i)) ≫ v i) (by
    change (_ ≫ v i) ≫ _ = _ ≫ x
    rw [Category.assoc, (hv i).1, ← Category.assoc, eps_alg])

theorem exists_comb {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) {n : ℕ}
    (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left))
    (hv : ∀ j, Formalism.L2.Pj.IsTanAt x (v j)) (a : Fin n → S) : ∃ w, IsCombAt x v a w :=
  ⟨_, combPt x v hv a, fun _ => rfl, rfl⟩

theorem comb_zero {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) {n : ℕ}
    (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left))
    (hv : ∀ j, Formalism.L2.Pj.IsTanAt x (v j)) :
    IsCombAt x v (0 : Fin n → S) (1 : tEps x ⟶ Xo.univ.t.G).left :=
  ⟨fun _ => 1, fun i => (eps_zero_comp x (v i) (hv i)).symm, by
    simp [List.ofFn_const, List.prod_replicate]⟩

theorem coeff_zero_of_unit {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (τ : E →+* ℂ)
    (a : Fin (Dw.mult τ) → S) (h : IsCombAt y.x (y.u τ) a (1 : tEps y.x ⟶ Xo.univ.t.G).left) : a = 0 :=
  (y.basis τ _ (isTanAt_one y.x) (isEigAt_one y.x τ)).unique h (comb_zero y.x (y.u τ) (y.tan τ))

theorem coeff_zero_of_tanW {S : Type} [CommRing S] [Algebra c.F S] (Y : Model Xo c β) (y : FrPt Xo c S) (τ : E →+* ℂ)
    (a : Fin (Dw.mult τ) → S) {w w₁ : Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left}
    (h : IsCombAt y.x (y.u τ) a w) (h₁ : IsCombAt y.x (y.u τ) (0 : Fin (Dw.mult τ) → S) w₁)
    (hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x)
    (hw₁ : w₁ ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x)
    (e : tanW Y y w hw = tanW Y y w₁ hw₁) : a = 0 := by
  have e₁ : w₁ = (1 : tEps y.x ⟶ Xo.univ.t.G).left := by
    obtain ⟨U, hU, rfl⟩ := h₁
    have : U = fun _ => 1 := by
      funext i
      apply CategoryTheory.Over.OverMorphism.ext
      rw [hU i]
      exact eps_zero_comp y.x (y.u τ i) (y.tan τ i)
    subst this
    simp [List.ofFn_const, List.prod_replicate]
  have := tanW_injective Y y hw hw₁ e
  rw [this, e₁] at h
  exact coeff_zero_of_unit y τ a h

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

theorem GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.indep_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (g : Spec (CommRingCat.of F) ⟶ X) (EC : Type) [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC) (y : FrPt Xo c F), Small.ptY Y y = g ≫ f → ∀ (τ : E →+* ℂ) (r : ℕ) (hr : r = Dw.mult τ) (u : Fin r → EC), (∀ i, (MC.pt (u i)).left ≫ m.φ = Small.tanY Y y τ (Fin.cast hr i)) → LinearIndependent F u := by
  intro E _ _ _ H Dw l Xo c O _ β Y X tX f m F _ _ g EC _ _ MC y hy τ r hr u hu
  subst hr
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have comb := _root_.GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.comb_val E H Dw l Xo c O β Y X tX f m F g EC MC y hy (Dw.mult τ) (y.u τ) (y.tan τ) u hu
  obtain ⟨w, hc⟩ := FinRd.Roots.LieBasis.exists_comb y.x (y.u τ) (y.tan τ) a
  obtain ⟨w₁, h1⟩ := FinRd.Roots.LieBasis.exists_comb y.x (y.u τ) (y.tan τ) (0 : Fin (Dw.mult τ) → F)
  obtain ⟨hw, ew⟩ := comb a w hc
  obtain ⟨hw1, e1⟩ := comb 0 w₁ h1
  have hz := FinRd.Roots.LieBasis.coeff_zero_of_tanW Y y τ a hc h1 hw hw1 (by
    rw [← ew, ← e1, ha]
    simp)
  intro i
  exact congrFun hz i
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelLattice
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

theorem triIn_of_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (g : Spec (CommRingCat.of F) ⟶ X) (EC : Type) [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC) (y : FrPt Xo c F), Small.ptY Y y = g ≫ f → ∀ (y' : FrPt Xo c F) (t : Ix Dw → Fˣ), FrBor t y y' → ∀ (τ : E →+* ℂ) (r : ℕ) (hr : r = Dw.mult τ) (u yb : Fin r → EC), (∀ i, (MC.pt (u i)).left ≫ m.φ = Small.tanY Y y τ (Fin.cast hr i)) → (∀ i, (MC.pt (yb i)).left ≫ m.φ = Small.tanY Y y' τ (Fin.cast hr i)) → FinRd.Roots.TriIn u (fun i => (t (some ⟨τ, Fin.cast hr i⟩) : F)) yb := by
  intro E _ _ _ H Dw l Xo c O _ β Y X tX f m F _ _ g EC _ _ MC y hy y' t hb τ r hr u yb hu hyb
  subst hr
  intro i
  obtain ⟨hx, hcomb, -⟩ := hb
  obtain ⟨cf, h1, h2, h3⟩ := hcomb τ i
  refine ⟨cf, h1, h2, ?_⟩
  obtain ⟨hw, hval⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.comb_val E H Dw l Xo c O β Y X tX f m F g EC MC y hy (Dw.mult τ) (y.u τ)
    (fun j => y.tan τ j) u hu cf (y'.u τ i) h3
  have hF : Small.ptF y' = Small.ptF y := by
    apply Limits.pullback.hom_ext
    · rw [Small.ptF_fst, Small.ptF_fst, hx]
    · rw [Small.ptF_snd, Small.ptF_snd]
  have htan : FinRd.Roots.LieBasis.tanW Y y (y'.u τ i) hw = Small.tanY Y y' τ i := by
    unfold FinRd.Roots.LieBasis.tanW Small.tanY
    congr 1
    apply Small.eq_tanF
    · exact IsPullback.lift_fst _ _ _ _
    · rw [hF]
      exact IsPullback.lift_snd _ _ _ _
  have hleft : (MC.pt (yb i)).left = (MC.pt (∑ j, cf j • u j)).left := by
    apply m.cart.1.hom_ext
    · rw [hval, htan]
      exact hyb i
    · rw [Over.w (MC.pt (yb i)), Over.w (MC.pt (∑ j, cf j • u j))]
  exact MC.inj (Over.OverMorphism.ext hleft)

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeDvrDegree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat


open GlobalTheory.CompanionTheory.Ar.Flat.DegZ in
theorem toH_rhoH {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {X : Scheme.{0}}
    {t : SAB H X} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {d r : ℕ} {M : LieModel t.G ξ (Fin d → Ω)} (S : GermSys t ξ M)
    {ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)} {𝓗 : HodgeLat M.lat ρ H.bar r} (hg : S.Gives 𝓗) (p : Cpt ξ) (a : 𝓞 E)
    (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (rhoH (S.g p).B a y) = 𝓗.ρH a (toH S p y) := by
  have h1 := (_root_.GlobalTheory.CompanionTheory.Ar.Conj.Iso.rho_pairing _ _ _ _ _ _ _ _ (S.iso p)).2.2.2.2.1 a
  have h2 := hg.1 a (transH (S.φ p) (S.ψ p) (S.lam p) (vmap (genMap ξ p) y))
  have h3 := LinearMap.congr_fun h1 (vmap (genMap ξ p) y)
  simp only [LinearMap.comp_apply] at h3
  have h4 := vmap_rhoH (S.mapK p) a y
  refine (congrArg (fun z => toVec Ω d (transH (S.φ p) (S.ψ p) (S.lam p) z)) h4).trans ?_
  refine (congrArg (toVec Ω d) h3.symm).trans ?_
  exact h2.symm


open GlobalTheory.CompanionTheory.Ar.Flat.DegZ in
theorem eigProj_toH_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
    {X : Scheme.{0}} {t : SAB H X} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {d r : ℕ} {M : LieModel t.G ξ (Fin d → Ω)}
    (S : GermSys t ξ M) {ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)} {𝓗 : HodgeLat M.lat ρ H.bar r} (hg : S.Gives 𝓗)
    (σ : E →+* Ω) (p : Cpt ξ) (τ : 𝓞 E →+* X.presheaf.stalk p.1) (hτ : ∀ a, genMap ξ p (τ a) = σ (a : E))
    {w : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)} (hw : w ∈ eigW (S.g p).B τ) :
    HT.eigProj 𝓗.ρH σ (toH S p w) = 0 := by
  refine eigW_induction (P := fun w => HT.eigProj 𝓗.ρH σ (toH S p w) = 0) hw ?_ ?_ ?_
  · intro a y
    have hc : HT.eigProj 𝓗.ρH σ (𝓗.ρH a (toH S p y)) = 𝓗.ρH a (HT.eigProj 𝓗.ρH σ (toH S p y)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
    have hm := HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem 𝓗.ρH σ (toH S p y)) a
    have e1 : toH S p (rhoH (S.g p).B a y - τ a • y) = 𝓗.ρH a (toH S p y) - σ (a : E) • toH S p y :=
      (toH_sub S p _ _).trans (congrArg₂ (· - ·) (toH_rhoH S hg p a y)
        ((toH_smul S p _ _).trans (congrArg (· • toH S p y) (hτ a))))
    refine (congrArg _ e1).trans ?_
    generalize toH S p y = v at hc hm
    rw [map_sub, map_smul, hc, hm, sub_self]
  · exact (congrArg _ (toH_zero S p)).trans (map_zero _)
  · intro y y' h1 h2
    refine (congrArg _ (toH_add S p y y')).trans ?_
    exact (map_add _ _ _).trans (by rw [h1, h2, add_zero])

end GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat


open GlobalTheory.CompanionTheory.Ar.Flat.DegZ in
theorem exists_trans {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
    {X : Scheme.{0}} {t : SAB H X} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {d r : ℕ} {M : LieModel t.G ξ (Fin d → Ω)}
    (S : GermSys t ξ M) {ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)} {𝓗 : HodgeLat M.lat ρ H.bar r} (hg : S.Gives 𝓗)
    (σ : E →+* Ω) (p q : Cpt ξ) (h : q.1 ⤳ p.1) (τ : 𝓞 E →+* X.presheaf.stalk q.1)
    (hτ : ∀ a, genMap ξ q (τ a) = σ (a : E)) {φ' ψ' : Germ.Pt (X.presheaf.stalk q.1) 1 d}
    {lam' : Germ.PS (X.presheaf.stalk q.1) 2 d}
    (he : transH (S.φ p) (S.ψ p) (S.lam p) = transH (S.φ q) (S.ψ q) (S.lam q) ∘ₗ
      transH (fun i => MvPowerSeries.map (genMap ξ q) (φ' i)) (fun i => MvPowerSeries.map (genMap ξ q) (ψ' i))
        (MvPowerSeries.map (genMap ξ q) lam'))
    {xp : Fin r → (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)}
    {xq : Fin r → (Fin d → X.presheaf.stalk q.1) × (Fin d → X.presheaf.stalk q.1)}
    (hxq : IsHBasis (S.g q).B xq) {u : Fin r → (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)}
    (hu : LinearIndependent Ω u) {Ap Aq : Matrix (Fin r) (Fin r) Ω}
    (hAp : ∀ j, HT.eigProj 𝓗.ρH σ (toH S p (xp j)) = ∑ l, Ap j l • u l)
    (hAq : ∀ j, HT.eigProj 𝓗.ρH σ (toH S q (xq j)) = ∑ l, Aq j l • u l) :
    ∃ Mt : Matrix (Fin r) (Fin r) (X.presheaf.stalk q.1), Ap = Mt.map (genMap ξ q) * Aq ∧
      ∀ j, transH φ' ψ' lam' (vmap (X.presheaf.stalkSpecializes h).hom (xp j)) - ∑ l, Mt j l • xq l ∈
        eigW (S.g q).B τ := by
  choose m hm using fun j => exists_sub_mem_eigW hxq τ
    (transH φ' ψ' lam' (vmap (X.presheaf.stalkSpecializes h).hom (xp j)))
  refine ⟨Matrix.of m, ?_, hm⟩
  have key : ∀ j, ∑ k, Ap j k • u k = ∑ k, ((Matrix.of m).map (genMap ξ q) * Aq) j k • u k := by
    intro j
    have h0 := eigProj_toH_eq_zero S hg σ q τ hτ (hm j)
    have h1 : toH S q (transH φ' ψ' lam' (vmap (X.presheaf.stalkSpecializes h).hom (xp j)) - ∑ l, m j l • xq l) =
        toH S p (xp j) - ∑ l, genMap ξ q (m j l) • toH S q (xq l) := by
      refine (toH_sub S q _ _).trans (congrArg₂ (· - ·) (toH_spec S p q h he (xp j)).symm ?_)
      exact (toH_sum _ S q _).trans (Finset.sum_congr rfl fun l _ => toH_smul S q _ _)
    have h2 := (congrArg (HT.eigProj 𝓗.ρH σ) h1).symm.trans h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, sub_eq_zero, map_sum] at h2
    refine ((hAp j).symm.trans h2).trans ?_
    simp only [map_smul, hAq, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, Matrix.map_apply, Matrix.of_apply,
      smul_smul]
    exact Finset.sum_comm
  ext j k
  have := (Fintype.linearIndependent_iff.1 hu) (fun k => Ap j k - ((Matrix.of m).map (genMap ξ q) * Aq) j k)
    (by simp only [sub_smul, Finset.sum_sub_distrib, key j, sub_self]) k
  exact sub_eq_zero.1 this

end GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat


open GlobalTheory.CompanionTheory.Ar.Flat.DegZ in
theorem germ_degZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)) (𝓗 : HodgeLat M.lat ρ H.bar r) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Sp O) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : O) (p : ℕ) (σ : E →+* Ω), Irreducible ϖ → p.Prime → ϖ ∣ (p : O) → ξ ≫ s = spMap (algebraMap O Ω) → IsCptGen ξ → PowFns t → S.Gives 𝓗 → (∀ q : Cpt ξ, (p : X.residueField q.1) = 0 → FibPF t q.1) → Nat.card (E →+* Ω) = Module.finrank ℚ E → (∀ (s' : E →+* Ω) (a : 𝓞 E), s' (a : E) ∈ (algebraMap O Ω).range) → 𝓗.DegZero σ (algebraMap O Ω ϖ) := by
  intro E _ _ _ H _ hstar X t Ω _ _ ξ d r M S ρ 𝓗 O _ _ _ _ s _ _ ϖ p σ hϖ hp hdvd hs hξ hpow hgive hfib hcard hrange
    u hu hsp Γ
  haveI : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective (algebraMap O Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx0 hϖ
    have h1 : algebraMap O Ω ϖ ^ n = 0 := by rw [← map_pow, ← hw, map_mul, hx, zero_mul]
    have h0 : algebraMap O Ω ϖ = 0 := (pow_eq_zero_iff (fun hn => by simp [hn] at h1)).1 h1
    obtain ⟨c, hc⟩ := hdvd
    have h2 := congrArg (algebraMap O Ω) hc
    rw [map_natCast, map_mul, h0, zero_mul] at h2
    exact hp.ne_zero (by exact_mod_cast h2)
  have hreg := _root_.GlobalTheory.CompanionTheory.Ar.Flat.DegZ.RegBase.algebraMap_mem_regAt_of_base X Ω ξ O s hs
  have hσ : ∀ (q : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ q := fun q a => by
    obtain ⟨o, ho⟩ := hrange σ a
    exact ho ▸ hreg q o
  let τ : ∀ q : Cpt ξ, 𝓞 E →+* X.presheaf.stalk q.1 := fun q =>
    (GlobalTheory.CompanionTheory.Ar.ValHom.stalkEquiv ξ hξ q).symm.toRingHom.comp
      ((σ.comp (algebraMap (𝓞 E) E)).codRestrict (regAt ξ q) (hσ q))
  have hτ : ∀ (q : Cpt ξ) (a : 𝓞 E), genMap ξ q (τ q a) = σ (a : E) := fun q a => by
    have := GlobalTheory.CompanionTheory.Ar.ValHom.stalkEquiv_coe ξ hξ q (τ q a)
    rw [← this]
    simp [τ]
  let q0 : Cpt ξ := ⟨centre Γ.η, Γ.η_spec⟩
  let qi : Γ.C.I → Cpt ξ := fun i => ⟨centre (Γ.z i), FibreCurve.z_spec Γ i⟩
  let v0 : X.presheaf.stalk q0.1 →+* Γ.κ := (Scheme.stalkClosedPointTo Γ.η).hom
  let vi : ∀ i, X.presheaf.stalk (qi i).1 →+* (Γ.C.v i).valuationSubring :=
    fun i => (Scheme.stalkClosedPointTo (Γ.z i)).hom
  have hpκ : (p : Γ.κ) = 0 := by
    obtain ⟨hh, s0, hs0, hs1⟩ := Γ.η_zero
    obtain ⟨c, hc⟩ := hdvd
    obtain ⟨c', hc'⟩ := hreg q0 c
    have e : (p : X.presheaf.stalk q0.1) = s0 * c' := hξ.inj q0 (by
      have h2 := congrArg (algebraMap O Ω) hc
      rw [map_natCast, map_mul] at h2
      rw [map_natCast, map_mul, h2, hc']
      exact congrArg (· * algebraMap O Ω c) hs0.symm)
    have h3 := congrArg v0 e
    rw [map_natCast, map_mul] at h3
    rw [h3]
    have h4 : v0 s0 = 0 := hs1
    rw [h4, zero_mul]
  haveI : CharP Γ.κ p := (CharP.charP_iff_prime_eq_zero hp).2 hpκ
  obtain ⟨F, hF0, hFi⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.DegZ.GermFam.germ_family E H hstar X t Ω ξ d M S O s _ p Γ hξ hpow hfib
  choose hFB φ' ψ' lam' he hφ hψ hlam using hFi
  choose xs A hxs hfr hpr using _root_.GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame.exists_basis_frame E H X t Ω ξ d r M S ρ 𝓗 σ u hξ hgive hσ hu hsp
  have hdet := fun q => (_root_.GlobalTheory.CompanionTheory.Ar.Flat.HodgeLat.quot_det_bundle X Ω ξ E (Fin d → Ω) M.lat ρ H.bar r 𝓗 σ u hσ hu hsp).2.2 q (A q) (hfr q)
  choose Mt hAM hMt using fun i => exists_trans S hgive σ (qi i) q0 (FibreCurve.generic_centre_specializes Γ i) (τ q0) (hτ q0)
    (he i) (hxs q0) hu (hpr (qi i)) (hpr q0)
  let χ : 𝓞 E →+* Γ.κ := v0.comp (τ q0)
  have hsq : ∀ i, ((Γ.C.v i).valuationSubring.subtype).comp (vi i) =
      v0.comp (X.presheaf.stalkSpecializes (FibreCurve.generic_centre_specializes Γ i)).hom := fun i => by
    have key := ProjectiveLinePlaces.stalk_square (FibreCurve.generic_centre_specializes Γ i) (Scheme.stalkClosedPointTo (Γ.z i))
      (Scheme.stalkClosedPointTo Γ.η) (CommRingCat.ofHom (Γ.C.v i).valuationSubring.subtype)
      ((Scheme.Spec_stalkClosedPointTo_fromSpecStalk Γ.η).trans ((Γ.z_gen i).symm.trans
        (congrArg (Spec.map (CommRingCat.ofHom (Γ.C.v i).valuationSubring.subtype) ≫ ·)
          (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (Γ.z i))).symm))
    exact RingHom.ext fun s => (congrArg (fun g => g.hom s) key).symm
  have hτs : ∀ i a, (X.presheaf.stalkSpecializes (FibreCurve.generic_centre_specializes Γ i)).hom (τ (qi i) a) = τ q0 a :=
    fun i a => hξ.inj q0 ((ProjectiveLinePlaces.genMap_specializes (FibreCurve.generic_centre_specializes Γ i) q0.2 (qi i).2 _).trans
      ((hτ (qi i) a).trans (hτ q0 a).symm))
  have hχ : ∀ i a, Γ.C.v i (χ a) ≤ 1 := fun i a => by
    have e : χ a = ((vi i (τ (qi i) a) : (Γ.C.v i).valuationSubring) : Γ.κ) :=
      (congrArg v0 (hτs i a).symm).trans (RingHom.congr_fun (hsq i) (τ (qi i) a)).symm
    rw [e]
    exact (vi i (τ (qi i) a)).2
  let x₀ : Fin r → (Fin d → Γ.κ) × (Fin d → Γ.κ) := fun l => vmap v0 (xs q0 l)
  let x : ∀ i : Γ.C.I, Fin r → (Fin d → (Γ.C.v i).valuationSubring) × (Fin d → (Γ.C.v i).valuationSubring) :=
    fun i j => vmap (vi i) (xs (qi i) j)
  let N : Γ.C.I → Matrix (Fin r) (Fin r) Γ.κ := fun i => (Mt i).map v0
  have hx₀ : IsHBasis F.B x₀ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isHBasis_map E _ _ v0 d r _ _ _ hF0 (hxs q0)
  have hx : ∀ i, IsHBasis (F.Bi i) (x i) := fun i => _root_.GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isHBasis_map E _ _ (vi i) d r _ _ _ (hFB i) (hxs (qi i))
  have hrel : ∀ i j, transH (F.φ i) (F.ψ i) (F.lam i) (vmap (Γ.C.v i).valuationSubring.subtype (x i j)) -
      ∑ l, N i j l • x₀ l ∈ eigW F.B χ := fun i j => by
    have h1 := vmap_mem_eigW hF0 (τ q0) (hMt i j)
    have h2 := vmap_rel v0 (vi i) (Γ.C.v i).valuationSubring.subtype _ (hsq i) (φ' i) (ψ' i) (lam' i)
      (xs (qi i) j) (Mt i j) (xs q0)
    rw [hφ i, hψ i, hlam i]
    exact h2 ▸ h1
  obtain ⟨hne, hfin, hsum⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.DegProd.curve_deg E Γ.κ Γ.C p d r F χ
    (GlobalTheory.T.charpoly_splits_of_embeddings E Ω O Γ.κ (v0.comp ((GlobalTheory.CompanionTheory.Ar.ValHom.stalkEquiv ξ hξ q0).symm.toRingHom.comp
      ((algebraMap O Ω).codRestrict (regAt ξ q0) (hreg q0)))) hinj hcard hrange) hχ x₀ x N hx₀ hx hrel
  have hNdet : ∀ i, (N i).det = v0 (Mt i).det := fun i => (RingHom.map_det v0 (Mt i)).symm
  have hAdet : ∀ i, (A (qi i)).det = genMap ξ q0 (Mt i).det * (A q0).det := fun i => by
    rw [hAM i, Matrix.det_mul]
    exact congrArg (· * (A q0).det) (RingHom.map_det (genMap ξ q0) (Mt i)).symm
  have hunit : ∀ i, IsUnit (Mt i).det := fun i => by
    have h1 : IsUnit (v0 (Mt i).det) := isUnit_iff_ne_zero.2 (hNdet i ▸ hne i)
    haveI : IsLocalHom v0 := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo Γ.η).hom)
    exact (isUnit_map_iff v0 _).1 h1
  refine ⟨(A q0).det, fun i => (A (qi i)).det, fun i => ((N i).det)⁻¹, hdet q0,
    fun i => ⟨FibreCurve.z_spec Γ i, hdet (qi i)⟩, fun i => ⟨inv_ne_zero (hne i), ?_⟩, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hunit i
    have hw0 : genMap ξ q0 (w : X.presheaf.stalk q0.1) * genMap ξ q0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hv0 : v0 (w : X.presheaf.stalk q0.1) * v0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    refine ⟨Γ.η_spec, ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1), ?_, ?_⟩
    · have e0 := (hdet q0).1
      have e1 : (A (qi i)).det = genMap ξ q0 (w : X.presheaf.stalk q0.1) * (A q0).det :=
        (hAdet i).trans (congrArg (fun z => genMap ξ q0 z * (A q0).det) hw.symm)
      have e2 : genMap ξ q0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) =
          (A q0).det / (genMap ξ q0 (w : X.presheaf.stalk q0.1) * (A q0).det) := by
        generalize genMap ξ q0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) = b at hw0
        generalize genMap ξ q0 (w : X.presheaf.stalk q0.1) = a at hw0
        have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one hw0
        rw [eq_div_iff (mul_ne_zero ha e0)]
        linear_combination (A q0).det * hw0
      exact e2.trans (congrArg ((A q0).det / ·) e1.symm)
    · have e3 : (N i).det = v0 (w : X.presheaf.stalk q0.1) := (hNdet i).trans (congrArg v0 hw.symm)
      exact (eq_inv_of_mul_eq_one_right hv0).trans (congrArg (·⁻¹) e3.symm)
  · refine hfin.subset fun i hi h1 => hi ?_
    rw [map_inv₀, h1, inv_one]
  · have : ∀ i, (Γ.C.w i : ℤ) * (-WithZero.log (Γ.C.v i ((N i).det)⁻¹)) =
        (Γ.C.w i : ℤ) * WithZero.log (Γ.C.v i (N i).det) := fun i => by
      rw [map_inv₀, WithZero.log_inv, neg_neg]
    simp only [this]
    exact hsum

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrameFinalStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_generic_frame_final : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → (letI := io.toAlgebra; Small.ptY Y zT = FinRd.Roots.gen T zV ≫ Or.𝔐.f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.ptY_eq_gen | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.ptY_eq_gen | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.ptY_eq_gen <;> assumption)
end

