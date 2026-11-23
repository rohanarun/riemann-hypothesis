module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0183
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0145
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0187
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.WeilBound.CoreStatements.HodgeTatePoints.FamilyEx
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FamilyGivesConjugateLieData
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0158
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0186
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0184

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelFieldPoint
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

namespace CombVal

section General

variable {S S' : Scheme.{0}} {G : CategoryTheory.Over S} {G' : CategoryTheory.Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

theorem push_mul (h : IsGrpPullback G' G f φ) {A : Scheme.{0}} {a : A ⟶ S'} {b : A ⟶ S} (hab : a ≫ f = b)
    (x y : CategoryTheory.Over.mk a ⟶ G') (x₀ y₀ : CategoryTheory.Over.mk b ⟶ G) (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hab
  exact h.2 (CategoryTheory.Over.mk a) x y x₀ y₀ hx hy

theorem push_one (h : IsGrpPullback G' G f φ) {A : Scheme.{0}} {a : A ⟶ S'} {b : A ⟶ S} (hab : a ≫ f = b) :
    (1 : CategoryTheory.Over.mk b ⟶ G).left = (1 : CategoryTheory.Over.mk a ⟶ G').left ≫ φ := by
  subst hab
  exact (congrArg (fun z => z.left) (map_one (pushHom h (CategoryTheory.Over.mk a)))).symm

theorem one_left_congr {A : Scheme.{0}} {a b : A ⟶ S} (h : a = b) :
    (1 : CategoryTheory.Over.mk a ⟶ G).left = (1 : CategoryTheory.Over.mk b ⟶ G).left := by
  subst h
  rfl

theorem push_mul₂ {S₂ : Scheme.{0}} {G₂ : CategoryTheory.Over S₂} [GrpObj G₂] {f₂ : S₂ ⟶ S} {φ₂ : G₂.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (h₂ : IsGrpPullback G₂ G f₂ φ₂) {A : Scheme.{0}} {a : A ⟶ S'} {a₂ : A ⟶ S₂}
    (hab : a ≫ f = a₂ ≫ f₂) (x y : CategoryTheory.Over.mk a ⟶ G') (x' y' : CategoryTheory.Over.mk a₂ ⟶ G₂)
    (hx : x.left ≫ φ = x'.left ≫ φ₂) (hy : y.left ≫ φ = y'.left ≫ φ₂) :
    (x * y).left ≫ φ = (x' * y').left ≫ φ₂ := by
  have wx : (x.left ≫ φ) ≫ G.hom = a ≫ f := by
    rw [Category.assoc, h.1.w, ← Category.assoc, CategoryTheory.Over.w x]
    rfl
  have wy : (y.left ≫ φ) ≫ G.hom = a ≫ f := by
    rw [Category.assoc, h.1.w, ← Category.assoc, CategoryTheory.Over.w y]
    rfl
  let W : CategoryTheory.Over.mk (a ≫ f) ⟶ G := CategoryTheory.Over.homMk (x.left ≫ φ) wx
  let W' : CategoryTheory.Over.mk (a ≫ f) ⟶ G := CategoryTheory.Over.homMk (y.left ≫ φ) wy
  exact (push_mul h rfl x y W W' rfl rfl).symm.trans (push_mul h₂ hab.symm x' y' W W' hx hy)

theorem push_one₂ {S₂ : Scheme.{0}} {G₂ : CategoryTheory.Over S₂} [GrpObj G₂] {f₂ : S₂ ⟶ S} {φ₂ : G₂.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (h₂ : IsGrpPullback G₂ G f₂ φ₂) {A : Scheme.{0}} {a : A ⟶ S'} {a₂ : A ⟶ S₂}
    (hab : a ≫ f = a₂ ≫ f₂) :
    (1 : CategoryTheory.Over.mk a ⟶ G').left ≫ φ = (1 : CategoryTheory.Over.mk a₂ ⟶ G₂).left ≫ φ₂ :=
  (push_one h hab).symm.trans (push_one h₂ rfl)

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {F : Type} [Field F] [Algebra c.F F]

abbrev qe (y : FrPt Xo c F) : Spec (CommRingCat.of (DualNumber F)) ⟶ Xo.XF c :=
  spMap (algebraMap F (DualNumber F)) ≫ Small.ptF y

theorem qe_fst (y : FrPt Xo c F) : qe y ≫ pullback.fst _ _ = spMap (algebraMap F (DualNumber F)) ≫ y.x := by
  rw [Category.assoc, Small.ptF_fst]

def liftP (Y : Model Xo c β) (y : FrPt Xo c F) (p : tEps y.x ⟶ Xo.univ.t.G) : CategoryTheory.Over.mk (qe y) ⟶ Y.oF.t.G :=
  CategoryTheory.Over.homMk (Y.m0.cart.1.lift p.left (qe y) ((CategoryTheory.Over.w p).trans (qe_fst y).symm)) (Y.m0.cart.1.lift_snd _ _ _)

theorem pointLift_fst (Y : Model Xo c β) (y : FrPt Xo c F) (p : tEps y.x ⟶ Xo.univ.t.G) :
    (liftP Y y p).left ≫ Y.m0.toSABMap.φ = p.left :=
  Y.m0.cart.1.lift_fst _ _ _

theorem pointLift_eq (Y : Model Xo c β) (y : FrPt Xo c F) (p : tEps y.x ⟶ Xo.univ.t.G) (P : CategoryTheory.Over.mk (qe y) ⟶ Y.oF.t.G)
    (h : P.left ≫ Y.m0.toSABMap.φ = p.left) : (liftP Y y p).left = P.left := by
  apply Y.m0.cart.1.hom_ext
  · exact (pointLift_fst Y y p).trans h.symm
  · exact (CategoryTheory.Over.w (liftP Y y p)).trans (CategoryTheory.Over.w P).symm

variable {Y : Model Xo c β} {X : Scheme.{0}} {tX : SAB H X} {f : X ⟶ Y.X} (m : SABMap tX Y.t f)
  {g : Spec (CommRingCat.of F) ⟶ X} {EC : Type} [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC)
  (y : FrPt Xo c F)

def Rd (p : tEps y.x ⟶ Xo.univ.t.G) (e : EC) : Prop :=
  (MC.pt e).left ≫ m.φ = (liftP Y y p).left ≫ Y.m.φ

variable {y}

theorem base_eq (hY : Small.ptY Y y = g ≫ f) :
    (spMap (algebraMap F (DualNumber F)) ≫ g) ≫ f = qe y ≫ Y.jQ ≫ pullback.fst _ _ := by
  rw [Category.assoc, Category.assoc, ← hY]
  rfl

theorem pt_zero : MC.pt 0 = 1 := by
  have h := MC.add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)

theorem rd_one (hY : Small.ptY Y y = g ≫ f) : Rd m MC y 1 0 := by
  have h1 : (liftP Y y 1).left = (1 : CategoryTheory.Over.mk (qe y) ⟶ Y.oF.t.G).left := by
    refine pointLift_eq Y y 1 1 ?_
    exact ((push_one Y.m0.cart (qe_fst y)).symm).trans (one_left_congr rfl)
  unfold Rd
  rw [h1, pt_zero]
  exact push_one₂ m.cart Y.m.cart (base_eq hY)

theorem rd_mul (hY : Small.ptY Y y = g ≫ f) {p p' : tEps y.x ⟶ Xo.univ.t.G} {e e' : EC}
    (h : Rd m MC y p e) (h' : Rd m MC y p' e') : Rd m MC y (p * p') (e + e') := by
  have h1 : (liftP Y y (p * p')).left = (liftP Y y p * liftP Y y p').left := by
    refine pointLift_eq Y y _ _ ?_
    exact (push_mul Y.m0.cart (qe_fst y) (liftP Y y p) (liftP Y y p') p p'
      (pointLift_fst Y y p).symm (pointLift_fst Y y p').symm).symm
  unfold Rd
  rw [h1, MC.add]
  exact push_mul₂ m.cart Y.m.cart (base_eq hY) (MC.pt e) (MC.pt e') (liftP Y y p) (liftP Y y p') h h'

theorem scale_base (a : F) : spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ spMap (algebraMap F (DualNumber F)) =
    spMap (algebraMap F (DualNumber F)) := by
  rw [← spMap_comp]
  congr 1
  ext r <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem rd_smul {p p₂ : tEps y.x ⟶ Xo.univ.t.G} {e : EC} (a : F)
    (hp : p₂.left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ p.left) (h : Rd m MC y p e) :
    Rd m MC y p₂ (a • e) := by
  have h1 : (liftP Y y p₂).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ (liftP Y y p).left := by
    apply Y.m0.cart.1.hom_ext
    · rw [pointLift_fst, Category.assoc, pointLift_fst, hp]
    · have e₁ := CategoryTheory.Over.w (liftP Y y p)
      have e₂ := CategoryTheory.Over.w (liftP Y y p₂)
      refine e₂.trans ?_
      rw [Category.assoc, e₁]
      show qe y = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ qe y
      rw [qe, ← Category.assoc, scale_base]
  unfold Rd at h ⊢
  rw [h1, MC.smul, Category.assoc, Category.assoc, h]
  rfl

theorem rd_prod (hY : Small.ptY Y y = g ≫ f) :
    ∀ (n : ℕ) (u : Fin n → (tEps y.x ⟶ Xo.univ.t.G)) (e : Fin n → EC), (∀ i, Rd m MC y (u i) (e i)) →
      Rd m MC y (List.ofFn u).prod (∑ i, e i)
  | 0, u, e, _ => by
    simpa using rd_one m MC hY
  | n + 1, u, e, h => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact rd_mul m MC hY (h 0) (rd_prod hY n _ _ fun i => h i.succ)

end CombVal

theorem comb_val : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (g : Spec (CommRingCat.of F) ⟶ X) (EC : Type) [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC) (y : FrPt Xo c F), Small.ptY Y y = g ≫ f → ∀ (n : ℕ) (v : Fin n → (Spec (CommRingCat.of (DualNumber F)) ⟶ Xo.univ.t.G.left)) (hv : ∀ j, Formalism.L2.Pj.IsTanAt y.x (v j)) (e : Fin n → EC), (∀ j, (MC.pt (e j)).left ≫ m.φ = FinRd.Roots.LieBasis.tanW Y y (v j) (hv j).1) → ∀ (cf : Fin n → F) (w : Spec (CommRingCat.of (DualNumber F)) ⟶ Xo.univ.t.G.left), IsCombAt y.x v cf w → ∃ hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap F (DualNumber F)) ≫ y.x, (MC.pt (∑ j, cf j • e j)).left ≫ m.φ = FinRd.Roots.LieBasis.tanW Y y w hw := by
  intro E _ _ _ H Dw l Xo c O _ β Y X tX f m F _ _ g EC _ _ MC y hY n v hv e he cf w hc
  obtain ⟨u, hu, rfl⟩ := hc
  refine ⟨CategoryTheory.Over.w ((List.ofFn u).prod), ?_⟩
  have h0 : ∀ j, CombVal.Rd m MC y (CategoryTheory.Over.homMk (v j) (hv j).1 : tEps y.x ⟶ Xo.univ.t.G) (e j) := he
  have h1 : ∀ j, CombVal.Rd m MC y (u j) (cf j • e j) := fun j => CombVal.rd_smul m MC (cf j) (hu j) (h0 j)
  exact CombVal.rd_prod m MC hY n u (fun j => cf j • e j) h1

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrPullbackSemiabelian
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open scoped CategoryTheory.Obj

theorem exists_extended_identification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (t' : SAB H (Spec (CommRingCat.of T.Fr))) (m2 : SABMap t' G (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)))) (b : t'.G.left ⟶ tX.G.left), IsGrpPullback t'.G tX.G (FinRd.Roots.gen T zV) b → (∀ a, (t'.act.act a).left ≫ b = b ≫ (tX.act.act a).left) → ∃ Ψ : G.G.left ⟶ tX.G.left, IsGrpPullback G.G tX.G zV Ψ ∧ m2.φ ≫ Ψ = b ∧ ∀ a, (G.act.act a).left ≫ Ψ = Ψ ≫ (tX.act.act a).left := by
  intro E _ _ _ H hE X tX T zV G t' m2 b hb hact
  have hp : IsGrpPullback ((Over.pullback zV).obj tX.G) tX.G zV (Limits.pullback.fst tX.G.hom zV) :=
    isGrpPullback_pullback tX.G zV
  let ψ : t'.G.left ⟶ ((Over.pullback zV).obj tX.G).left :=
    Limits.pullback.lift b (t'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)))
      (by rw [hb.1.w, Category.assoc])
  have hψf : ψ ≫ Limits.pullback.fst tX.G.hom zV = b := Limits.pullback.lift_fst _ _ _
  have hψs : ψ ≫ ((Over.pullback zV).obj tX.G).hom =
      t'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) := Limits.pullback.lift_snd _ _ _
  have hψ : IsGrpPullback t'.G ((Over.pullback zV).obj tX.G)
      (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) ψ :=
    hp.cancel (hb.congr rfl hψf.symm) hψs
  have hj : GlobalTheory.IsGenericPointHom (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) :=
    GlobalTheory.IsGenericPointHom.fractionField T.V T.Fr
  have hS := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec T.V
  have hH' : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian ((Over.pullback zV).obj tX.G) := by
    have h := tX.semi
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := h.comm; infer_instance
    · have := h.smooth; show Smooth (Limits.pullback.snd tX.G.hom zV); infer_instance
    · have := h.separated; show IsSeparated (Limits.pullback.snd tX.G.hom zV); infer_instance
    · have := h.quasiCompact; show QuasiCompact (Limits.pullback.snd tX.G.hom zV); infer_instance
    · have := h.geomConnected; show GeometricallyConnected (Limits.pullback.snd tX.G.hom zV); infer_instance
    · intro Ω _ _ q
      obtain ⟨F⟩ := h.fibres Ω (q ≫ zV)
      exact ⟨torusExtOfIso (pullCompIso q zV tX.G) F⟩
  obtain ⟨e, ⟨hmon, heq⟩, -⟩ := hE.generic_existsUnique_iso_of_extensions hS hj G.semi hH' m2.cart hψ
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G.G G.semi
  obtain ⟨-, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ hH'
  refine ⟨e.hom.left ≫ Limits.pullback.fst tX.G.hom zV,
    ((isGrpPullback_of_iso e).comp hp).congr (Category.id_comp _) rfl, ?_, fun a => ?_⟩
  · rw [← Category.assoc, heq, hψf]
  · have hB : ((Over.pullback zV).map (tX.act.act a)).left ≫ Limits.pullback.fst tX.G.hom zV =
        Limits.pullback.fst tX.G.hom zV ≫ (tX.act.act a).left := Limits.pullback.lift_fst _ _ _
    have hψa : (t'.act.act a).left ≫ ψ = ψ ≫ ((Over.pullback zV).map (tX.act.act a)).left := by
      apply Limits.pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hB, hψf, ← Category.assoc ψ, hψf, hact]
      · have h₁ := hψs
        have h₂ := Over.w ((Over.pullback zV).map (tX.act.act a))
        have h₃ := Over.w (t'.act.act a)
        change _ ≫ ((Over.pullback zV).obj tX.G).hom = _ ≫ ((Over.pullback zV).obj tX.G).hom
        rw [Category.assoc, Category.assoc, h₂, h₁, ← Category.assoc, h₃]
    have key : G.act.act a ≫ e.hom = e.hom ≫ (Over.pullback zV).map (tX.act.act a) := by
      refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback m2.cart.1 ?_
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← m2.act a, Category.assoc, heq, hψa,
        ← Category.assoc, heq]
    have key' := congrArg (fun f => f.left ≫ Limits.pullback.fst tX.G.hom zV) key
    simp only [Over.comp_left, Category.assoc, hB] at key'
    simpa only [Category.assoc] using key'

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieEigenDegree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.TopH2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem comp_one_over {G T T' : Over X0} [GrpObj G] (f : T' ⟶ T) : f ≫ (1 : T ⟶ G) = 1 := by
  show f ≫ (toUnit T ≫ η[G]) = toUnit T' ≫ η[G]
  rw [← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

theorem comp_prod_ofFn {G T T' : Over X0} [GrpObj G] (f : T' ⟶ T) :
    ∀ {m : ℕ} (u : Fin m → (T ⟶ G)), f ≫ (List.ofFn u).prod = (List.ofFn fun l => f ≫ u l).prod
  | 0, u => by simp only [List.ofFn_zero, List.prod_nil]; exact comp_one_over f
  | m + 1, u => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul,
      comp_prod_ofFn f (fun l => u l.succ)]

theorem spMap_comp_eq {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (a : B →+* C) (b : A →+* B) (c : D →+* C) (d : A →+* D) (h : a.comp b = c.comp d) :
    spMap a ≫ spMap b = spMap c ≫ spMap d := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

section Rings

variable {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')

theorem dualMap_comp_algebraMap :
    (GlobalTheory.CompanionTheory.Ar.dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_epsMul (c : R) :
    (GlobalTheory.CompanionTheory.Ar.dualMap f).comp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul c) =
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (f c)).comp (GlobalTheory.CompanionTheory.Ar.dualMap f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, mul_comm]

theorem fst_comp_dualMap :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (GlobalTheory.CompanionTheory.Ar.dualMap f) =
      f.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [GlobalTheory.CompanionTheory.Ar.dualMap]

end Rings

variable (t : SAB H X0)

theorem isTanAt_iff {S : Type} [CommRing S] (x : Sp S ⟶ X0) (w : GlobalTheory.CompanionTheory.Ar.epsAt x ⟶ t.G) :
    GlobalTheory.CompanionTheory.Ar.IsTanAt t.G x w ↔ IsTanAtG t x w.left :=
  ⟨fun h => ⟨Over.w w, h⟩, fun h => h.2⟩

theorem isTanAtG_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {x : Sp R ⟶ X0}
    {v : Sp (DualNumber R) ⟶ t.G.left} (h : IsTanAtG t x v) :
    IsTanAtG t (spMap f ≫ x) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ v) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h.1, ← Category.assoc, ← Category.assoc,
      spMap_comp_eq _ _ _ _ (dualMap_comp_algebraMap f)]
  · rw [← Category.assoc, spMap_comp_eq _ _ _ _ (fst_comp_dualMap f), Category.assoc, h.2]
    have := comp_one_over (G := t.G) (Over.homMk (U := Over.mk (spMap f ≫ x)) (V := Over.mk x) (spMap f) rfl)
    rw [← this, Over.comp_left]
    rfl

theorem isCombAtG_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {x : Sp R ⟶ X0} {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {cf : Fin m → R} {w : Sp (DualNumber R) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) :
    IsCombAtG t (spMap f ≫ x) (fun l => spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ v l) (fun l => f (cf l))
      (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ w) := by
  obtain ⟨u, hu, hw⟩ := h
  let k : tEpsG (spMap f ≫ x) ⟶ tEpsG x := Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f)) (by
    simp only [Over.mk_hom]
    rw [← Category.assoc, ← Category.assoc, spMap_comp_eq _ _ _ _ (dualMap_comp_algebraMap f)])
  refine ⟨fun l => k ≫ u l, fun l => ?_, ?_⟩
  · show spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ (u l).left = _
    rw [hu l, ← Category.assoc, ← Category.assoc,
      spMap_comp_eq _ _ _ _ (dualMap_comp_epsMul f (cf l))]
  · rw [← comp_prod_ofFn, Over.comp_left, hw]
    rfl

theorem pt_sum {S : Type} [CommRing S] {x : Sp S ⟶ X0} {V : Type} [AddCommGroup V] [Module S V]
    (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V) :
    ∀ {m : ℕ} (c : Fin m → V), (List.ofFn fun l => M.pt (c l)).prod = M.pt (∑ l, c l)
  | 0, c => by
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    have h := M.add 0 0
    rw [add_zero] at h
    exact (mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)).symm
  | m + 1, c => by
    rw [List.ofFn_succ, List.prod_cons, pt_sum M (fun l => c l.succ), Fin.sum_univ_succ, M.add]

theorem isCombAtG_iff_lie {S : Type} [CommRing S] {x : Sp S ⟶ X0} {V : Type} [AddCommGroup V] [Module S V]
    (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V) {m : ℕ} (b : Fin m → V) (cf : Fin m → S)
    (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x (fun l => (M.pt (b l)).left) cf w ↔ w = (M.pt (∑ l, cf l • b l)).left := by
  constructor
  · rintro ⟨u, hu, hw⟩
    have hu' : u = fun l => M.pt (cf l • b l) :=
      funext fun l => Over.OverMorphism.ext (by rw [hu l, M.smul]; rfl)
    rw [← hw, hu', pt_sum]
  · intro hw
    exact ⟨fun l => M.pt (cf l • b l), fun l => by rw [M.smul]; rfl, by rw [pt_sum, hw]⟩

theorem lieLat_conjData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), Nonempty C.I → (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∀ (V : Type) [AddCommGroup V] [Module K V] (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G z V) (r : 𝓞 E →+* Module.End K V), M.IsActOf t.act.act r → ∃ (d : ℕ) (D : ConjData C p (𝓞 E) d) (e : V ≃ₗ[K] (Fin d → K)), (∀ i v, v ∈ Y.lieLat M i ↔ e v ∈ D.lie i) ∧ ∀ a v, e (r a v) = (D.ρ a).mulVec (e v) := by
  intro E _ _ _ H _ hbar X0 t hPow K _ p _ _ C z Y hne hFib V _ _ M r hr
  obtain ⟨d, F, g, hgB, hfam⟩ := _root_.PositivityTheory.HtPt.Cf.family_ex E H hbar X0 t hPow K p C z Y hFib
  obtain ⟨D, hDρ, hDlie⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Conj.Fam.family_conj K C p d (𝓞 E) F hne
  obtain ⟨e, hecomb, heact⟩ := _root_.GlobalTheory.CompanionTheory.Ar.GermLie.germ_lie E H hbar X0 t K z d g V M
  refine ⟨d, D, e, fun i v => ?_, fun a v => by rw [heact r hr a v, hDρ a, hgB]⟩
  obtain ⟨gi, hgi⟩ := hfam i
  obtain ⟨hΦΨ, hΨΦ, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Conj.Iso.rho_pairing K d (𝓞 E) F.B (F.BK i) (F.φ i) (F.ψ i) (F.lam i) (F.iso i)
  have hgen : spMap (C.v i).valuationSubring.subtype ≫ Y.x i = z := Y.gen i
  have htan : ∀ l, IsTanAtG t z (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) :=
    fun l => by
      have h0 := isTanAtG_map t (C.v i).valuationSubring.subtype (gi.tan l)
      rwa [hgen] at h0
  choose c hc using fun l => M.onto (Over.homMk _ (htan l).1) ((isTanAt_iff t z _).2 (htan l))
  have hcl : ∀ l, (M.pt (c l)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l :=
    fun l => by rw [hc l]; rfl
  have hec : ∀ l j, e (c l) j = lin (F.φ i) 1 j l := by
    intro l
    have hw : IsTanAtG t z (M.pt (c l)).left := (isTanAt_iff t z _).1 (M.tan _)
    have := (g.basis _ hw).unique (hecomb (c l)) (by rw [hcl]; exact hgi l)
    exact fun j => congrFun this j
  have key : ∀ (a : Fin d → (C.v i).valuationSubring)
      (w : Sp (DualNumber (C.v i).valuationSubring) ⟶ t.G.left), IsCombAtG t (Y.x i) gi.tg a w →
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ w = (M.pt (∑ l, (a l : K) • c l)).left ∧
        e (∑ l, (a l : K) • c l) = (lin (F.φ i) 1).mulVec (fun l => (a l : K)) := by
    intro a w hw
    refine ⟨?_, ?_⟩
    · have h1 := isCombAtG_map t (C.v i).valuationSubring.subtype hw
      rw [hgen] at h1
      have h2 : (fun l => spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) =
          fun l => (M.pt (c l)).left := funext fun l => (hcl l).symm
      rw [h2] at h1
      exact (isCombAtG_iff_lie t M c _ _).1 h1
    · funext j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, Matrix.mulVec, dotProduct, hec, mul_comm]
  constructor
  · intro hv
    have hsub : Y.lieLat M i ≤ (D.lie i).comap e.toLinearMap.toAddMonoidHom := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro v ⟨w, hw, hvw⟩
      obtain ⟨a, ha, -⟩ := gi.basis w.left ((isTanAt_iff t (Y.x i) w).1 hw)
      obtain ⟨hbc, hea⟩ := key a w.left ha
      have hv' : v = ∑ l, (a l : K) • c l := M.inj (Over.OverMorphism.ext (hvw.trans hbc))
      show e v ∈ D.lie i
      rw [hDlie, hv', hea, Matrix.mulVec_mulVec, hΨΦ, Matrix.one_mulVec]
      intro j
      exact (a j).2
    exact hsub hv
  · intro hv
    have hint : ∀ j, C.v i ((lin (F.ψ i) 1).mulVec (e v) j) ≤ 1 := (hDlie i (e v)).1 hv
    let a : Fin d → (C.v i).valuationSubring := fun j => ⟨_, hint j⟩
    obtain ⟨Vi, _, _, ⟨Mi⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists X0 t.G (C.v i).valuationSubring (Y.x i)
    choose b hb using fun l =>
      Mi.onto (Over.homMk (gi.tg l) (gi.tan l).1) ((isTanAt_iff t (Y.x i) _).2 (gi.tan l))
    have hbl : ∀ l, (Mi.pt (b l)).left = gi.tg l := fun l => by rw [hb l]; rfl
    have hcomb : IsCombAtG t (Y.x i) gi.tg a (Mi.pt (∑ l, a l • b l)).left := by
      have h3 := (isCombAtG_iff_lie t Mi b a (Mi.pt (∑ l, a l • b l)).left).2 rfl
      have h2 : (fun l => (Mi.pt (b l)).left) = gi.tg := funext hbl
      rwa [h2] at h3
    obtain ⟨hbc, hea⟩ := key a _ hcomb
    have hsum : ∑ l, (a l : K) • c l = v := by
      apply e.injective
      rw [hea]
      show (lin (F.φ i) 1).mulVec ((lin (F.ψ i) 1).mulVec (e v)) = e v
      rw [Matrix.mulVec_mulVec, hΦΨ, Matrix.one_mulVec]
    refine AddSubgroup.subset_closure ⟨Mi.pt (∑ l, a l • b l), Mi.tan _, ?_⟩
    rw [← hsum]
    exact hbc.symm

end GlobalTheory.CompanionTheory.Ar.Conj.TopH2
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelAndHeckeOfZeroSignatureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_and_hecke_of_zero_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), D.p + D.q = 0 → ToroidalLevelCompatibility (H := H) (D := D) ∧ ToroidalHeckeCompatibility (H := H) (D := D) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.LevelZero.main | exact GlobalTheory.CompanionTheory.Ar.Top.LevelZero.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.LevelZero.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerMapLocallyQuasiFinite
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem locallyQuasiFinite_pow_semiAbelian :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ N : ℕ, 1 ≤ N →
      LocallyQuasiFinite ((𝟙 G) ^ N).left := by
  intro S G _ hG N hN
  have := hG.comm
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have hm : IsMonHom ((𝟙 G) ^ N) := GlobalTheory.AbLaw.MulN.isMonHom_mulA G N
  have : LocallyOfFiniteType (((𝟙 G) ^ N).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType ((𝟙 G) ^ N).left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact (((𝟙 G) ^ N).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact ((𝟙 G) ^ N).left := QuasiCompact.of_comp _ G.hom
  refine GlobalTheory.locallyQuasiFinite_of_finite_geometric_ker S G G _ hm inferInstance inferInstance
    fun Ω _ _ t => ?_
  simp only [MonObj.comp_pow, Category.comp_id]
  exact GlobalTheory.HomExt.finite_torsion_points hG t hN

end GlobalTheory.CompanionTheory.Ar.BT
end

