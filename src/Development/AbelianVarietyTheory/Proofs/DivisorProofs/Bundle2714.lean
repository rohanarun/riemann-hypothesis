module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0453
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0425
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2705
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2701
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFormsRestrictionAffineLiftBijective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.LevLift

variable (D : Data) (Λ : Lift D) (n : ℕ)

abbrev CC : Type 1 := (LevE D.κ D.t D.i (n + 1)).FullSubcategory

variable {D n}

theorem hom_ext' {T T' : CC D n} {f g : T ⟶ T'} (h : f.hom.hom.1 = g.hom.hom.1) : f = g :=
  ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ (Subtype.ext h))

def opn (T : CC D n) : AffOp D.X := Opposite.op ⟨T.obj.obj.U, T.obj.property⟩


variable (D n) in
def qq : CC D n ⥤ AffOp D.X where
  obj T := opn T
  map f := (homOfLE (show (⟨_, _⟩ : D.X.affineOpens) ≤ ⟨_, _⟩ from f.hom.hom.2)).op
  map_id _ := rfl
  map_comp _ _ := rfl

theorem mem_of_hom {T T' : Thick D.κ D.t} (f : T ⟶ T') {U : D.X.Opens} (h : ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U) :
    ⊤ ≤ (T'.x ≫ D.i) ⁻¹ᵁ U := by
  rw [← f.pt, Category.assoc, Scheme.Hom.comp_preimage, top_le_iff.1 h, Scheme.Hom.preimage_top]

theorem cop_ex (T : CC D n) : ∃ (G : Thick D.κ D.t) (l : T.obj.obj.T ⟶ G) (r : Λ.L.obj ((qq D n).obj T) ⟶ G),
    IsCop (n + 1) l r ∧ (KK D.κ D.t).QAt l :=
  _root_.GlobalTheory.PDForm.CopPoincare.exists_cop_qAt D Λ n ((qq D n).obj T) T.obj.obj.T T.property T.obj.obj.mem

def GG (T : CC D n) : Thick D.κ D.t := (cop_ex Λ T).choose

def ll (T : CC D n) : T.obj.obj.T ⟶ GG Λ T := (cop_ex Λ T).choose_spec.choose

def rr (T : CC D n) : Λ.L.obj ((qq D n).obj T) ⟶ GG Λ T := (cop_ex Λ T).choose_spec.choose_spec.choose

theorem isCop (T : CC D n) : IsCop (n + 1) (ll Λ T) (rr Λ T) :=
  (cop_ex Λ T).choose_spec.choose_spec.choose_spec.1

theorem qat_ll (T : CC D n) : (KK D.κ D.t).QAt (ll Λ T) :=
  (cop_ex Λ T).choose_spec.choose_spec.choose_spec.2

def SObj (T : CC D n) : CC D n :=
  ⟨⟨⟨GG Λ T, T.obj.obj.U, T.obj.obj.hU, mem_of_hom (ll Λ T) T.obj.obj.mem⟩, T.obj.property⟩, (isCop Λ T).1⟩

theorem smap_ex {T T' : CC D n} (f : T ⟶ T') : ∃! c : GG Λ T ⟶ GG Λ T',
    ll Λ T ≫ c = f.hom.hom.1 ≫ ll Λ T' ∧ rr Λ T ≫ c = Λ.L.map ((qq D n).map f) ≫ rr Λ T' :=
  (isCop Λ T).2 (GG Λ T') (isCop Λ T').1 _ _

def smap {T T' : CC D n} (f : T ⟶ T') : GG Λ T ⟶ GG Λ T' := (smap_ex Λ f).exists.choose

theorem smap_spec {T T' : CC D n} (f : T ⟶ T') :
    ll Λ T ≫ smap Λ f = f.hom.hom.1 ≫ ll Λ T' ∧ rr Λ T ≫ smap Λ f = Λ.L.map ((qq D n).map f) ≫ rr Λ T' :=
  (smap_ex Λ f).exists.choose_spec

theorem smap_uniq {T T' : CC D n} (f : T ⟶ T') (c : GG Λ T ⟶ GG Λ T')
    (h1 : ll Λ T ≫ c = f.hom.hom.1 ≫ ll Λ T') (h2 : rr Λ T ≫ c = Λ.L.map ((qq D n).map f) ≫ rr Λ T') :
    c = smap Λ f :=
  (smap_ex Λ f).unique ⟨h1, h2⟩ (smap_spec Λ f)

def SS : CC D n ⥤ CC D n where
  obj := SObj Λ
  map f := ObjectProperty.homMk (ObjectProperty.homMk ⟨smap Λ f, f.hom.hom.2⟩)
  map_id T := hom_ext' (smap_uniq Λ (𝟙 T) (𝟙 _) (by simp; rfl)
    (by rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]; simp)).symm
  map_comp {T T' T''} f g := hom_ext' (smap_uniq Λ (f ≫ g) (smap Λ f ≫ smap Λ g)
    (by rw [← Category.assoc, (smap_spec Λ f).1, Category.assoc, (smap_spec Λ g).1, ← Category.assoc]; rfl)
    (by rw [← Category.assoc, (smap_spec Λ f).2, Category.assoc, (smap_spec Λ g).2, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp])).symm

def uu : 𝟭 (CC D n) ⟶ SS Λ where
  app T := ObjectProperty.homMk (ObjectProperty.homMk ⟨ll Λ T, le_rfl⟩)
  naturality {T T'} f := hom_ext' (smap_spec Λ f).1.symm

variable (h : ∀ U, LevE D.κ D.t D.i (n + 1) (Λ.toE.obj U))

abbrev ell : AffOp D.X ⥤ CC D n := (LevE D.κ D.t D.i (n + 1)).lift Λ.toE h

def ww : qq D n ⋙ ell Λ h ⟶ SS Λ where
  app T := ObjectProperty.homMk (ObjectProperty.homMk ⟨rr Λ T, le_rfl⟩)
  naturality {T T'} f := hom_ext' (smap_spec Λ f).2.symm

def eps : 𝟭 (AffOp D.X) ⟶ ell Λ h ⋙ qq D n where
  app U := 𝟙 U
  naturality _ _ _ := rfl

abbrev KL : Cx (CC D n) := (((KK D.κ D.t).res (pE D.κ D.t D.i)).res (LevE D.κ D.t D.i (n + 1)).ι)

theorem qat_iff {T T' : CC D n} (φ : T ⟶ T') : (KL (D := D) (n := n)).QAt φ ↔ (KK D.κ D.t).QAt φ.hom.hom.1 :=
  Iff.rfl

theorem qat_rr (U : AffOp D.X) : (KK D.κ D.t).QAt (rr Λ ((ell Λ h).obj U)) := by
  set T := (ell Λ h).obj U
  have hc := isCop Λ T
  obtain ⟨σ, ⟨h1, h2⟩, -⟩ := hc.2 (GG Λ T) hc.1 (rr Λ T) (ll Λ T)
  have hσ : σ ≫ σ = 𝟙 _ := by
    obtain ⟨c, -, hu⟩ := hc.2 (GG Λ T) hc.1 (ll Λ T) (rr Λ T)
    exact (hu (σ ≫ σ) ⟨(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ σ) h1).trans h2),
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ σ) h2).trans h1)⟩).trans
      (hu (𝟙 _) ⟨Category.comp_id _, Category.comp_id _⟩).symm
  have hi : IsIso σ := ⟨σ, hσ, hσ⟩
  obtain ⟨hiso, hcomp, -⟩ := _root_.GlobalTheory.CxCoh.QAtFormal.qAt_formal (Thick D.κ D.t) (KK D.κ D.t)
  exact h1 ▸ hcomp _ _ _ _ _ (qat_ll Λ T) (hiso _ _ σ)

theorem qat_map_id (U : AffOp D.X) {B : Thick D.κ D.t} (f : Λ.L.obj U ⟶ B) (hf : (KK D.κ D.t).QAt f) :
    (KK D.κ D.t).QAt (Λ.L.map (𝟙 U) ≫ f) := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact hf

theorem resMap_bij : (KL (D := D) (n := n)).resMap (ell Λ h) |>.Bij := by
  refine _root_.GlobalTheory.CxCoh.collapse_resMap_bij (CC D n) (AffOp D.X) KL (ell Λ h) (qq D n) (SS Λ) (uu Λ) (ww Λ h) (eps Λ h)
    (fun T ↦ qat_ll Λ T) (fun U ↦ ?_)
  rw [qat_iff]
  exact qat_map_id Λ U _ (qat_rr Λ h U)

end GlobalTheory.PDForm.LevLift

theorem GlobalTheory.PDForm.levLift_resMap_bij : ∀ (D : Data) (Λ : Lift D) (n : ℕ) (h : ∀ U, LevE D.κ D.t D.i (n + 1) (Λ.toE.obj U)),
    ((((KK D.κ D.t).res (pE D.κ D.t D.i)).res (LevE D.κ D.t D.i (n + 1)).ι).resMap
      ((LevE D.κ D.t D.i (n + 1)).lift Λ.toE h)).Bij :=
  fun _ Λ _ h ↦ GlobalTheory.PDForm.LevLift.resMap_bij Λ h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsExtendVanishCompactifiedFlagSpace
section
noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace _root_.CategoryTheory.Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)

theorem ext_of_arcZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (σ : c.F →+* ℂ),
    IsVariety₀ TF.X Z → ∀ m : H0 (str₀ TF.X Z) (L₀ TF.X Z la) (U₀ TF.X Z), ArcZero TF.X Z la σ m →
      ∃ s ∈ vanBd TF.X Z la, H0.restr le_top s = m := by
  intro E _ _ _ H Dw l Xo c TF Z la σ hv m hm
  obtain ⟨s, hs, hz⟩ := _root_.GlobalTheory.CompHS.exists_ext_of_dense_local (str₀ TF.X Z) (L₀ TF.X Z la) (isLB_L₀ TF.X Z la) (U₀ TF.X Z) (dense_U₀ TF.X Z) m
    fun y _ => by
      obtain ⟨W, hW, i, p, hyW, hi, hd, hsm, hp, hb⟩ := _root_.GlobalTheory.CompHS.ChartBd.exists_chart_bd E H Dw l Xo c TF Z la hv y
      obtain ⟨b, h1, h2⟩ := _root_.GlobalTheory.CompHS.exists_extension_of_arcZero E H Dw l Xo c TF.Y TF.X Z la σ m hm W hW i p hi hd hsm hp hb
      exact ⟨W, i, hi, b, hyW, h1, fun y' h h' => h2 y' h h'⟩
  exact ⟨s, fun y hy i hi => hz y hy i hi, hs⟩

end GlobalTheory.CompHS

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal GlobalTheory.KoecherArc

theorem arcZero_cusp : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)), ∀ σ : Y.d.c₂.F →+* ℂ, GoodEmb Y.d.c₂ σ → ∀ f : Cusp Z Y.U la, ArcZero TF.X Z la σ (cuspSec TF.X Z Y.U la f) := by
  intro D T j Y e o hY Z TF la σ hσ f
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  have hU := hY.unf σ hσ
  obtain ⟨hfW, -⟩ := Submodule.mem_inf.1 f.2
  obtain ⟨-, hhol⟩ := AllWt.mem_cuspW.1 hfW
  have hS := GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ (hhol σ hσ)
  have hχ := AllWt.Model.chi_modelWt (Y.U σ) (hY.chiTriv σ hσ) (AllWt.wtOf _ la 0) (AllWt.even_wtOf la 0)
  have he : AllWt.exOf (T.Q.Dw j) la 0 none = 0 := by
    show (AllWt.wtOf (T.Q.Dw j) la 0).2 = 0
    rw [AllWt.wtOf_snd, mul_zero]
  intro W hW i hWi ψ r hψ hs hin hout ε hε
  obtain ⟨φ, x, fr, y, hb, hm, hval⟩ := _root_.GlobalTheory.CompHS.ArcBridge.arc_bridge TF Z la σ hσ W hW i hWi ψ r hψ hs hin hout
  obtain ⟨ρ, p, q, hρ, hρr, hpq⟩ := _root_.GlobalTheory.Vanishing.exists_quot_along_arc (cuspSec TF.X Z Y.U la f) W hW i hWi ψ r hψ hout
  have hi : ∀ u, ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ
      (L₀ TF.X Z la).U i := fun u s _ => hWi (hW.range_fromSpec.le ⟨_, rfl⟩)
  let g : AllWt.secZ Y.d.Xo₂ Y.d.c₂ (AllWt.exOf (T.Q.Dw j) la 0) := ⟨f.1, cusp_le_secZ Z Y.U la f.2⟩
  have hv : ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → ψ u q ≠ 0 ∧ toC (evR _ _ g.1 (y u)) * ψ u q = ψ u p :=
    fun u hu h => by
      have hur : u ∈ Metric.ball (0 : ℂ) r := Metric.ball_subset_ball hρr hu
      refine ⟨(hpq u hu h).1, ?_⟩
      rw [← hval g u hur h (hout u hur h) (hi u)]
      exact (hpq u hu h).2 _ _
  have ht := tendsto_val TF.Y hσ hU _ hχ he g.2 hS fr (isBdArc_mono hb hρ hρr)
    (fun u hu h => hm u (Metric.ball_subset_ball hρr hu) h) p q hv
  have h2 : Tendsto (fun u => ‖toC (evR _ _ g.1 (y u))‖) (𝓝[≠] 0) (𝓝 0) := by simpa using ht.norm
  filter_upwards [h2.eventually (gt_mem_nhds hε), self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) hρ)] with u h1 h3 h4 hO hi'
  rw [show cuspSec TF.X Z Y.U la f = sec₀ TF.X Z _ g from rfl,
    hval g u (Metric.ball_subset_ball hρr h4) h3 hO hi']
  exact h1

end GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem GlobalTheory.CompHS.cusp_extends_comp : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)), Extends TF.X Z Y.U la := by
  intro D T j Y e o hG hE Z TF la
  have hσ : GoodEmb Y.d.c₂ Y.d.c₂.F.val.toRingHom := rfl
  intro f
  exact ext_of_arcZero _ _ _ _ _ _ TF Z la _ (GlobalTheory.T.flagSpace_component_smooth_projective_connected _ _ _ _ _ _ TF Z hG.geo) _
    (arcZero_cusp D T j Y e o hG Z TF la _ hσ f)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarCohomologousEvenFormsAlgebraClosed
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem dbarCoh_algebra : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) , DbarCoh A 1 1 ∧ (∀ w : A.Pt → Ev n, A.IsForm (fld A w) → A.dbar (fld A w) = 0 → DbarCoh A w w) ∧ ∀ (c : ℂ) (w w' z z' : A.Pt → Ev n), DbarCoh A w w' → DbarCoh A z z' → DbarCoh A (c • w) (c • w') ∧ DbarCoh A (w + z) (w' + z') ∧ DbarCoh A (w * z) (w' * z') := by
  intro M _ n A
  obtain ⟨h1, hc, hl, -, -⟩ := GlobalTheory.formCalculus M n A
  have h0 : A.IsForm 0 := by simpa using (hc 0 1 1 h1 h1).2.2.1
  have d0 : A.dbar 0 = 0 := by simpa using (hc 0 1 1 h1 h1).2.2.2.2.2.2.2.2
  have e1 : fld A 1 = 1 := rfl
  have d1 : A.dbar 1 = 0 := by
    have h := (hl 1 1 h1 h1).2
    rw [e1, mul_one, mul_one, one_mul] at h
    simpa using h
  have diag : ∀ w : A.Pt → Ev n, A.IsForm (fld A w) → A.dbar (fld A w) = 0 → DbarCoh A w w :=
    fun w hw dw => ⟨hw, hw, dw, dw, 0, h0, by rw [d0, sub_self]⟩
  refine ⟨diag 1 h1 d1, diag, ?_⟩
  rintro c w w' z z' ⟨hw, hw', dw, dw', u, hu, eu⟩ ⟨hz, hz', dz, dz', v, hv, ev⟩
  have es (x : A.Pt → Ev n) : fld A (c • x) = c • fld A x := rfl
  have ea (x y : A.Pt → Ev n) : fld A (x + y) = fld A x + fld A y := rfl
  have em (x y : A.Pt → Ev n) : fld A (x * y) = fld A x * fld A y := rfl
  have ecomm (x y : A.Pt → Ev n) : fld A x * fld A y = fld A y * fld A x := by rw [← em, ← em, mul_comm]
  have hs (α : A.Fld) (h : A.IsForm α) := (hc c α α h h).2.2.1
  have ds (α : A.Fld) (h : A.IsForm α) := (hc c α α h h).2.2.2.2.2.2.2.2
  have ha (α β : A.Fld) (h : A.IsForm α) (h' : A.IsForm β) := (hc c α β h h').1
  have hm (α β : A.Fld) (h : A.IsForm α) (h' : A.IsForm β) := (hc c α β h h').2.1
  have da (α β : A.Fld) (h : A.IsForm α) (h' : A.IsForm β) := (hc c α β h h').2.2.2.2.2.2.1
  refine ⟨⟨hs _ hw, hs _ hw', ?_, ?_, c • u, hs _ hu, ?_⟩,
    ⟨ha _ _ hw hz, ha _ _ hw' hz', ?_, ?_, u + v, ha _ _ hu hv, ?_⟩,
    ⟨hm _ _ hw hz, hm _ _ hw' hz', ?_, ?_, fld A w * v + fld A z' * u, ha _ _ (hm _ _ hw hv) (hm _ _ hz' hu), ?_⟩⟩
  · rw [es, ds _ hw, dw, smul_zero]
  · rw [es, ds _ hw', dw', smul_zero]
  · rw [es, es, ds _ hu, ← eu, smul_sub]
  · rw [ea, da _ _ hw hz, dw, dz, add_zero]
  · rw [ea, da _ _ hw' hz', dw', dz', add_zero]
  · rw [ea, ea, da _ _ hu hv, ← eu, ← ev]
    abel
  · rw [em, (hl w _ hw hz).2, dw, dz, zero_mul, mul_zero, add_zero]
  · rw [em, (hl w' _ hw' hz').2, dw', dz', zero_mul, mul_zero, add_zero]
  · rw [em, em, da _ _ (hm _ _ hw hv) (hm _ _ hz' hu), (hl w _ hw hv).2, (hl z' _ hz' hu).2, dw, dz', ← eu, ← ev,
      zero_mul, zero_mul, zero_add, zero_add, mul_sub, mul_sub, ecomm z' w, ecomm z' w']
    abel

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalSiegelHeisenbergInvariantFormUnique
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section

namespace GlobalTheory.DiagSiegelUniq

open GlobalTheory.WeilM

theorem diagMat_eq_mul {A : Type} [CommRing A] {m n : ℕ} (w : Matrix (Fin m) (Fin n) A) :
    GlobalTheory.DiagSiegel.diagMat w =
      w * ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) A).submatrix finSumFinEquiv.symm id)ᵀ := by
  ext i j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases j with j | j <;>
    simp only [GlobalTheory.DiagSiegel.diagMat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, id] <;>
    simp [diagCols, Matrix.one_apply]

theorem transpose_transport (D : D7) (S T : HSp D) (ν : Measure (Formalism.IndefR.Datum.WO T S))
    (𝓕 : Set (Formalism.IndefR.Datum.WO T S)) (h : Formalism.IndefR.Datum.IsCovolOne (ratL S T) ν 𝓕) :
    ∃ (ν' : Measure (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank))
      (𝓕' : Set (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank)),
      ν'.IsAddHaarMeasure ∧ IsAddFundamentalDomain (Formalism.IndefR.DatumF.ratLF D.host.F D.host.E S.rank T.rank) 𝓕' ν' ∧
      ∀ f : Matrix (Fin T.rank) (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E) → ℂ,
        ∫ u in 𝓕', f u ∂ν' = ∫ w in 𝓕, f wᵀ ∂ν := by
  classical
  haveI : BorelSpace (Formalism.IndefR.Datum.WO T S) := ⟨rfl⟩
  haveI : BorelSpace (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank) := ⟨rfl⟩
  obtain ⟨hH, hF, -⟩ := h
  let e : Formalism.IndefR.Datum.WO T S ≃+ Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank :=
    Matrix.transposeAddEquiv _ _ _
  have hc : Continuous e := Continuous.matrix_transpose continuous_id
  have hcs : Continuous e.symm := Continuous.matrix_transpose continuous_id
  let E' : Formalism.IndefR.Datum.WO T S ≃ᵐ Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank :=
    (Homeomorph.mk e.toEquiv hc hcs).toMeasurableEquiv
  have hE' : ∀ w, E' w = wᵀ := fun _ => rfl
  let eG : Formalism.IndefR.DatumF.ratLF D.host.F D.host.E S.rank T.rank ≃ ratL S T :=
    { toFun := fun g => ⟨(g : Matrix (Fin T.rank) (Fin S.rank) _)ᵀ, by
        obtain ⟨γ, hγ⟩ := g.2
        exact ⟨γᵀ, by rw [← hγ]; rfl⟩⟩
      invFun := fun g => ⟨(g : Matrix (Fin S.rank) (Fin T.rank) _)ᵀ, by
        obtain ⟨γ, hγ⟩ := g.2
        exact ⟨γᵀ, by rw [← hγ]; rfl⟩⟩
      left_inv := fun g => Subtype.ext (Matrix.transpose_transpose _)
      right_inv := fun g => Subtype.ext (Matrix.transpose_transpose _) }
  refine ⟨ν.map E', E' '' 𝓕, ?_, ?_, fun f => ?_⟩
  · exact AddEquiv.isAddHaarMeasure_map ν e hc hcs
  · refine hF.image_of_equiv E'.toEquiv (E'.quasiMeasurePreserving_symm ν) eG fun g x => ?_
    show (((eG g : ratL S T) : Matrix (Fin S.rank) (Fin T.rank) _) + x)ᵀ = (g : Matrix (Fin T.rank) (Fin S.rank) _) + xᵀ
    rw [Matrix.transpose_add]
    exact congrArg (· + xᵀ) (Matrix.transpose_transpose _)
  · rw [E'.restrict_map, E'.preimage_image, MeasureTheory.integral_map_equiv]
    rfl

theorem lubinTateSeries_eq_of_coeff_one_eq (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E)
    (hξ : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (κ : Type) [Fintype κ]
    (J' : Matrix (Fin (T.rank + T.rank)) (Fin (T.rank + T.rank)) (AF D.host.F ⊗[D.host.F] D.host.E))
    (hJ : incM D.host.F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG T.gram)ᵀ = J')
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ J' (incM D.host.F JB)) κ)
    (hrat : ∀ x : Matrix (Fin (T.rank + T.rank)) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
        fun i => algebraMap D.host.F (AF D.host.F) (z i)))
    (ν' : Measure (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank))
    (𝓕' : Set (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank)) (hν' : ν'.IsAddHaarMeasure)
    (h𝓕' : IsAddFundamentalDomain (Formalism.IndefR.DatumF.ratLF D.host.F D.host.E S.rank T.rank) 𝓕' ν')
    (l : ((κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ) (hl : l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ)
    (hinv : ∀ z : Matrix (Fin S.rank) (Fin T.rank) (AF D.host.F ⊗[D.host.F] D.host.E),
      ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        l ((GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co).rho ψ
          (GlobalTheory.DiagSiegel.diagMat z) Φ) = l Φ) :
    ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, l Φ = c * GlobalTheory.LagrTheta.lagrInt ν' 𝓕'
      ((diagCols (Fin T.rank) : Matrix (Fin T.rank ⊕ Fin T.rank) (Fin T.rank)
        (AF D.host.F ⊗[D.host.F] D.host.E)).submatrix finSumFinEquiv.symm id)
      (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) := by
  subst hJ
  classical
  obtain ⟨v₁, -, -, ⟨τ₁⟩⟩ := GlobalTheory.TripleDarboux.exists_good_place D ∅
  let B : Base D.host.F D.host.E :=
    { ψ := ψ, emb := fun _ => Classical.arbitrary _, mα := 0, mβ := 0, P := ∅,
      τ := fun v => absurd v.2 (Finset.notMem_empty _), v₁ := v₁, τ₁ := τ₁ }
  have hB : B.IsGood D.sp.cm.sig :=
    GlobalTheory.TripleDarboux.base_isGood B hψ fun v hv => absurd hv (Finset.notMem_empty _)
  exact _root_.GlobalTheory.LagrUniq.lagr_invariant_unique D.host.F D.host.E D.sp.cm.sig B hB S.rank T.rank S.gram T.gram
    (GlobalTheory.Doubling.isHermND_gram S) (GlobalTheory.Doubling.isHermND_gram T) D.host.xi0 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
    (Formalism.L2.Pj.conj_xi0_alt D) JB ξ hξ κ co hrat ν' 𝓕' hν' h𝓕' l hl fun z Φ hΦ => by
      rw [← diagMat_eq_mul]
      exact hinv z Φ hΦ

theorem uniq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
            (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin (GlobalTheory.Doubling.dblSp T).rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
              fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO T S)) (𝓕 : Set (Formalism.IndefR.Datum.WO T S)),
            Formalism.IndefR.Datum.IsCovolOne (ratL S T) ν 𝓕 →
          ∀ l : ((κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ →
            (∀ z : Matrix (Fin S.rank) (Fin T.rank) (AF D.host.F ⊗[D.host.F] D.host.E),
              ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                l ((GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co).rho ψ
                  (GlobalTheory.DiagSiegel.diagMat z) Φ) = l Φ) →
            ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, l Φ = c * GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕
              (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) ψ Φ) := by
  intro D ψ hψ S T JB ξ hξ κ _ co hrat ν 𝓕 hcov l hl hinv
  obtain ⟨ν', 𝓕', hν', h𝓕', hint⟩ := transpose_transport D S T ν 𝓕 hcov
  have hJ : incM D.host.F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG T.gram)ᵀ =
      incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ) := by
    rw [← GlobalTheory.WeilSchrodinger.DblTargetF.reindex_dbl_incM (F := D.host.F) (J := T.gram) rfl,
      GlobalTheory.WeilSchrodinger.DblTarget.reindex_dbl_incM T rfl]
  obtain ⟨c, hc⟩ := lubinTateSeries_eq_of_coeff_one_eq D ψ hψ S T JB ξ hξ κ _ hJ co hrat ν' 𝓕' hν' h𝓕' l hl hinv
  refine ⟨c, fun Φ hΦ => ?_⟩
  rw [hc Φ hΦ, GlobalTheory.LagrTheta.lagrInt, hint, GlobalTheory.DiagSiegel.thetaDiagInt]
  congr 2
  funext w
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilSchrodinger.transD_rho,
    diagMat_eq_mul, Matrix.transpose_mul, Matrix.transpose_transpose]

end GlobalTheory.DiagSiegelUniq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenlatticeSlopeLowerBoundDefiniteCaseStatement
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.eigenlattice_slope_lower_bound_definite_case : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (G : Type) [Group G] [Finite G] (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) (χ : G →* (c.F)ˣ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ : ℝ), DefCase U ξ → Finite (Comp Xo c) → Nonempty (Comp Xo c) → (∀ σ, GoodEmb c σ → ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom) → ActLev (Xo := Xo) c lev → FreePt Xo c lev → Dom a n → GoodW U ξ V dict (wtZ a n) → FlatExistsAt U ξ c₁ → eigLat U lev χ (wtZ a n) ≠ ⊥ ∧ defBound Dw a n c₁ ≤ slope_sq (normW U ξ V dict (wtZ a n)) (eigLat U lev χ (wtZ a n)) / 2 := by
  intro D H Dw l Xo c r U ξ V dict G _ _ lev χ a n c₁ hD hF hN hdom hA hfree hDom hW hflat
  have hFibre := _root_.GlobalTheory.DefFibre.fibreAt_defCase
    D.host.E H Dw l Xo c r U ξ a n c₁ hD hDom hflat
  exact GlobalTheory.DefPt.OrbitGeo.eigLat_slope
    D H Dw l Xo c r U ξ V dict G lev χ a n (defBound Dw a n c₁) hD hF hN hdom hA hfree hDom hW hFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfPairingVanishes
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_pairing_vanishes : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (z : AfP p ⊗[ℚ] VQ D), (∀ v, (D.EF.baseChange ℚ).baseChange (AfP p) v z = 0) → z = 0 := by
  first | (exact @GlobalTheory.LKGeo.nondeg_afP) | (exact GlobalTheory.LKGeo.nondeg_afP) | (intros; apply GlobalTheory.LKGeo.nondeg_afP  <;> assumption)
end

