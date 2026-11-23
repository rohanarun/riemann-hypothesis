module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieMultIffExistsFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0113
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0112
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0086
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmTypeEigenMultiplicityOfDensePrimes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0116
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0090
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsSecNeObj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartLieMultShift
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.AbMult

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi _root_.GlobalTheory.CompanionTheory.Ar

theorem lieMult_iff_family {S : Scheme.{0}} {k : Type} [Field k] {G : Over S} [GrpObj G] {O : Type} [CommRing O]
    {V : Type} [AddCommGroup V] [Module k V] {x : Sp k ⟶ S} (M : LieModel G x V) (act : OAct O G)
    (ρ : O →+* Module.End k V) (h : M.IsActOf act.act ρ) (τ : O →+* k) (n : ℕ) :
    LieMult act x τ n ↔ ∃ b : Fin n → V, LinearIndependent k b ∧ Submodule.span k (Set.range b) = eigSp ρ τ := by
  rw [Fl.Test.lieMult_iff_exists_frame]
  constructor
  · rintro ⟨v, hv⟩
    choose e he using fun i => M.onto (v i) (hv.1 i).1
    obtain rfl : v = fun i => M.pt (e i) := funext fun i => (he i).symm
    exact ⟨e, (Fl.Test.isEigFrame_iff M act ρ h τ e).1 hv⟩
  · rintro ⟨b, hb⟩
    exact ⟨fun i => M.pt (b i), (Fl.Test.isEigFrame_iff M act ρ h τ b).2 hb⟩

theorem lieMult_abPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S) (P : AbPart t z), ∃ r : ℕ, ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k) (n : ℕ), LieMult P.tK.act (spMap g) τ n → r ≤ n ∧ LieMult P.tB.act (spMap g) τ (n - r) := by
  intro E _ _ _ H S t L _ _ z P
  letI := P.τ.addCommGroup
  letI := P.τ.grpB
  haveI := P.τ.free
  haveI := P.τ.finite
  haveI := P.τ.q_hom
  haveI := P.τ.i_hom
  haveI := P.e_hom
  haveI heinv : IsMonHom P.e.inv := inferInstance
  obtain ⟨m, hm⟩ := GlobalTheory.T.torus_extension_module_structure L P.tK.G P.τ (𝓞 E) P.tK.act (fun a => by
    haveI := P.tB.act.hom a
    refine ⟨P.e.hom ≫ P.tB.act.act a ≫ P.e.inv, inferInstance, ?_⟩
    refine (cancel_mono P.e.hom).1 ?_
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using P.act a)
  letI := m
  refine ⟨Module.finrank ℤ P.τ.X / Module.finrank ℚ E, ?_⟩
  intro k _ _ g τ n hn
  haveI : CharZero k := charZero_of_injective_ringHom g.injective
  obtain ⟨V₂, _, _, ⟨M₂⟩⟩ := lieModel_exists (Sp L) P.tK.G k (spMap g)
  obtain ⟨V₃, _, _, ⟨M₃⟩⟩ := lieModel_exists (Sp L) P.tB.G k (spMap g)
  let D := GlobalTheory.Diag.diagAct (Sp L) (𝓞 E) P.τ.X
  let M₁ := Fl.Test.torusModel (spMap g) P.τ.X
  obtain ⟨ρ₁, hρ₁, -⟩ := lieModel_exists_unique_act _ _ k (spMap g) _ M₁ (𝓞 E) D.act D.hom D.one D.mul D.add
  obtain ⟨ρ₂, hρ₂, -⟩ := lieModel_exists_unique_act _ _ k (spMap g) _ M₂ (𝓞 E) P.tK.act.act P.tK.act.hom
    P.tK.act.one P.tK.act.mul P.tK.act.add
  obtain ⟨ρ₃, hρ₃, -⟩ := lieModel_exists_unique_act _ _ k (spMap g) _ M₃ (𝓞 E) P.tB.act.act P.tB.act.hom
    P.tB.act.one P.tB.act.mul P.tB.act.add
  obtain ⟨f, hf, -⟩ := lieModel_exists_unique_diff _ _ _ k (spMap g) _ _ M₁ M₂ P.τ.i
  obtain ⟨h, hh, -⟩ := lieModel_exists_unique_diff _ _ _ k (spMap g) _ _ M₂ M₃ (P.τ.q ≫ P.e.hom)
  obtain ⟨hker, hsurj⟩ := GlobalTheory.T.torus_extension_tangent_exact L P.tK.G P.τ k g
  haveI hmono : Mono P.τ.i := ⟨fun a b hab => P.τ.isKernel.hom_ext hab (toUnit_unique _ _)⟩
  have finj : Function.Injective f := fun a b hab => M₁.inj ((cancel_mono P.τ.i).1 (by
    rw [← hf, ← hf, hab]))
  have hsur : Function.Surjective h := fun y => by
    obtain ⟨v, hv, hvq⟩ := hsurj (M₃.pt y ≫ P.e.inv) ((M₃.tan y).comp_monHom P.e.inv)
    obtain ⟨a, rfl⟩ := M₂.onto v hv
    refine ⟨a, M₃.inj ?_⟩
    rw [hh, ← Category.assoc, hvq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hex : LinearMap.range f = LinearMap.ker h := by
    ext a
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    have h1 : h a = 0 ↔ M₂.pt a ≫ P.τ.q = 1 := by
      constructor
      · intro h0
        have := hh a
        rw [h0, Fl.Test.pt_zero, ← Category.assoc] at this
        refine (cancel_mono P.e.hom).1 ?_
        rw [← this, MonObj.one_comp]
      · intro h0
        refine M₃.inj ?_
        rw [hh, ← Category.assoc, h0, MonObj.one_comp, Fl.Test.pt_zero]
    rw [h1, hker _ (M₂.tan a)]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨M₁.pt c, M₁.tan c, (hf c).symm⟩
    · rintro ⟨w, hw, hwa⟩
      obtain ⟨c, rfl⟩ := M₁.onto w hw
      exact ⟨c, M₂.inj ((hf c).trans hwa)⟩
  have eqf : ∀ a c, f (ρ₁ a c) = ρ₂ a (f c) := fun a c => M₂.inj (by
    rw [hf, hρ₂ a (f c), hρ₁ a c, hf, Category.assoc, Category.assoc]
    exact congrArg (M₁.pt c ≫ ·) (hm a))
  have eqh : ∀ a c, h (ρ₂ a c) = ρ₃ a (h c) := fun a c => M₃.inj (by
    rw [hh, hρ₃ a (h c), hρ₂ a c, hh, Category.assoc, Category.assoc, Category.assoc]
    exact congrArg (M₂.pt c ≫ ·) (P.act a))
  obtain ⟨bas⟩ := GlobalTheory.T.eigenspace_basis_exists E P.τ.X k τ
  obtain ⟨b₁, hb₁, hb₁'⟩ := (lieMult_iff_family M₁ D ρ₁ hρ₁ τ _).1
    ((GlobalTheory.Diag.lieMult_iff (spMap g) τ _).2 ⟨bas⟩)
  obtain ⟨b₂, hb₂, hb₂'⟩ := (lieMult_iff_family M₂ P.tK.act ρ₂ hρ₂ τ n).1 hn
  obtain ⟨hle, b₃, hb₃⟩ := _root_.GlobalTheory.CompanionTheory.Ar.EigExact.exists_basis_eigSp_quot E k _ _ _ ρ₁ ρ₂ ρ₃ f h finj hsur hex eqf eqh τ _ n b₁ b₂ hb₁ hb₁' hb₂ hb₂'
  exact ⟨hle, (lieMult_iff_family M₃ P.tB.act ρ₃ hρ₃ τ _).2 ⟨b₃, hb₃⟩⟩

end GlobalTheory.CompanionTheory.Ar.AbMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CubicalTripleTrivial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.CubeUnit

open GlobalTheory.CubicUnit

theorem eq_one_at_rational_points : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → TorusExtension G → ∀ (v : Γ((G ⊗ G ⊗ G).left, ⊤)ˣ), (∀ (T : Over (Sp K)) (x y : T ⟶ G), (lift (1 : T ⟶ G) (lift x y)).left.appTop.hom v.val = 1 ∧ (lift x (lift (1 : T ⟶ G) y)).left.appTop.hom v.val = 1 ∧ (lift x (lift y (1 : T ⟶ G))).left.appTop.hom v.val = 1) → ∀ x y w : 𝟙_ (Over (Sp K)) ⟶ G, (lift x (lift y w)).left.appTop.hom v.val = 1 := by
  intro K _ G _ _ hs τ v hv x₀ y₀ w₀
  letI := τ.addCommGroup
  haveI := τ.free
  letI := τ.grpB
  haveI := τ.q_hom
  haveI := τ.i_hom
  haveI := τ.q_flat
  haveI := τ.q_surjective
  haveI := τ.q_quasiCompact
  haveI := hs.smooth
  haveI := hs.geomConnected
  haveI hGc : ConnectedSpace G.left := (GlobalTheory.GroupConn.connectedSpace_group (Sp K) G).1
  haveI hYc : ConnectedSpace (G ⊗ G).left := GlobalTheory.GroupConn.connectedSpace_tensor G G
  haveI hsn : Smooth (snd G G).left := by
    show Smooth (pullback.snd G.hom G.hom)
    infer_instance
  haveI hsm : Smooth (G ⊗ G).hom := by
    rw [← Over.w (snd G G)]
    infer_instance
  haveI hYr : IsReduced (G ⊗ G).left := GlobalTheory.isReduced_of_smooth_of_isReduced (G ⊗ G).hom
  have hf1 : ∀ (T : Over (Sp K)) (x y : T ⟶ G), ev (lift (1 : T ⟶ G) (lift x y)) v = 1 :=
    fun T x y => Units.ext (hv T x y).1
  have hf2 : ∀ (T : Over (Sp K)) (x y : T ⟶ G), ev (lift x (lift (1 : T ⟶ G) y)) v = 1 :=
    fun T x y => Units.ext (hv T x y).2.1
  let m : splitTorus (Sp K) τ.X ⊗ (G ⊗ G) ⟶ G ⊗ (G ⊗ G) :=
    lift ((fst _ _ ≫ τ.i) * (snd _ _ ≫ fst _ _)) (lift (snd _ _ ≫ snd _ _) (toUnit _ ≫ w₀))
  have hm : ∀ (Z : Over (Sp K)) (t : Z ⟶ splitTorus (Sp K) τ.X) (x y : Z ⟶ G),
      lift t (lift x y) ≫ m = lift ((t ≫ τ.i) * x) (lift y (toUnit Z ≫ w₀)) := fun Z t x y => by
    simp [m, comp_lift, MonObj.comp_mul]
  obtain ⟨χ, hχ⟩ := GlobalTheory.CompanionTheory.TorusMono.torus_unit_eq_char_mul (Sp K) τ.X (G ⊗ G) (ev m v)
  have h1 : ∀ (Z : Over (Sp K)) (t : Z ⟶ splitTorus (Sp K) τ.X) (x y : Z ⟶ G),
      ev (lift ((t ≫ τ.i) * x) (lift y (toUnit Z ≫ w₀))) v =
        chV t χ * ev (lift x (lift y (toUnit Z ≫ w₀))) v := fun Z t x y => by
    have e : ev (lift t (lift x y)) (ev m v) =
        chV t χ * ev (lift (1 : Z ⟶ splitTorus (Sp K) τ.X) (lift x y)) (ev m v) :=
      Units.ext (hχ Z t (lift x y))
    rw [ev_comp, ev_comp, hm, hm, MonObj.one_comp, _root_.one_mul] at e
    exact e
  have h2 : ∀ (Z : Over (Sp K)) (t : Z ⟶ splitTorus (Sp K) τ.X), chV t χ = 1 := fun Z t => by
    have e := h1 Z t 1 1
    rw [hf2, hf2, _root_.mul_one] at e
    exact e.symm
  have h3 : ∀ (Z : Over (Sp K)) (t : Z ⟶ splitTorus (Sp K) τ.X) (x y : Z ⟶ G),
      ev (lift ((t ≫ τ.i) * x) (lift y (toUnit Z ≫ w₀))) v =
        ev (lift x (lift y (toUnit Z ≫ w₀))) v := fun Z t x y => by
    rw [h1, h2, _root_.one_mul]
  let s : G ⟶ G ⊗ (G ⊗ G) := lift (𝟙 G) (lift (toUnit G ≫ y₀) (toUnit G ≫ w₀))
  have hs' : ∀ (Z : Over (Sp K)) (g : Z ⟶ G),
      g ≫ s = lift g (lift (toUnit Z ≫ y₀) (toUnit Z ≫ w₀)) := fun Z g => by
    simp [s, comp_lift]
  have h8 : IsWt τ.i ⊤ (ev s v).val 0 := isWt_top_iff.2 fun Z t g => by
    rw [← ev_val, ← ev_val, ev_comp, ev_comp, hs', hs', h3, chV_zero, Units.val_one, _root_.one_mul]
  obtain ⟨c, hc⟩ := (invariant_functions_descend (Sp K) G τ.B _ τ.q τ.i τ.q_hom τ.i_hom τ.q_flat
    τ.q_surjective τ.q_quasiCompact τ.isKernel ⊤).2.2 (ev s v).val fun Z t g h₁ h₂ => by
      refine (h8 Z t g h₁ h₂).trans ?_
      rw [← chV_val, chV_zero, Units.val_one, _root_.one_mul]
      rfl
  obtain ⟨d, hd⟩ := (GlobalTheory.globalFns_holds (Sp K) τ.B τ.isAbelian).2 c
  have hud : (ev s v).val = G.hom.appTop.hom d := by
    rw [← Over.w τ.q, FunDescent.comp_appTop_apply, hd]
    exact hc.symm
  have hd1 : d = 1 := by
    have e : ev (1 : 𝟙_ (Over (Sp K)) ⟶ G) (ev s v) = 1 := by
      rw [ev_comp, hs', toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, Category.id_comp]
      exact hf1 _ y₀ w₀
    have e := congrArg Units.val e
    rw [ev_val, hud, ← FunDescent.comp_appTop_apply, Over.w] at e
    simpa using e
  have hu : ev s v = 1 := by
    apply Units.ext
    rw [hud, hd1, map_one, Units.val_one]
  have e : ev x₀ (ev s v) = 1 := by
    rw [hu]
    exact map_one _
  rw [ev_comp, hs', toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, Category.id_comp] at e
  exact congrArg Units.val e

end GlobalTheory.CompanionTheory.Ar.CubeUnit
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNonzeroSectionPpData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg


open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 in
theorem exists_sec_ne_zero_int : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), ∃ t : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), t ≠ 0 := by
  intro E _ _ _ H L _ _ D
  have hS : SecBaseChangeAnySt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have := D.tK.semi.smooth
  have := D.tK.semi.geomConnected
  have : ConnectedSpace D.tK.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := D.tK.G.hom) (𝟙 _) (𝟙 _) D.tK.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected D.tK.G.hom (eSec D.tK.G (default : PrimeSpectrum L))
  obtain ⟨-, ws, gs', -⟩ := D.tK.sym
  obtain ⟨hprop, hamp, hkt⟩ := D.princ
  have eid : spMap (RingHom.id L) = 𝟙 (Sp L) := by
    simp [spMap]
  have hpb : IsPullback (𝟙 D.tK.G.left) D.tK.G.hom D.tK.G.hom (spMap (RingHom.id L)) := by
    rw [eid]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨β, hβ⟩ : ∃ β : LB.Sec D.tK.PP.L, ¬ ∀ y j, (𝟙 D.tK.G.left : D.tK.G.left ⟶ D.tK.G.left) y ∈ D.tK.PP.L.U j →
      gs (𝟙 D.tK.G.left) y _ (β.f j) = 0 := exists_sec_ne hS
    { A := D.tK.G, g := d, smoothDim := hd, L := D.tK.PP.L, isLB := D.tK.PP.isLB
      ample := hamp
      ktriv := hkt
      isAb := ⟨inferInstance, inferInstance, hprop, ‹_›⟩
      rigid := ⟨D.tK.PP.rig, D.tK.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ } (RingHom.id L) hpb
  obtain ⟨w, gw', -⟩ := D.m.lin
  have := D.t.semi.separated
  have := D.t.semi.quasiCompact
  have : CompactSpace D.t.G.left := QuasiCompact.compactSpace_of_compactSpace D.t.G.hom
  obtain ⟨a, ha, σ, hσ⟩ := exists_extend (nonZeroDivisors (𝓞 L)) D.m.cart.1 D.t.PP.isLB D.tK.PP.isLB
    ((isGen_iff w).1 gw') β
  obtain ⟨w₁, hw₁⟩ := exists_iso_linComb (F := 𝟙 D.t.G.left) D.t.PP.isLB (K := Fin 1) (fun _ => 𝟙 _)
    (fun _ => ((1 : ℕ) : ℤ)) (fun U _ k => by simp)
  have hM := linComb_isLB D.t.PP.L D.t.PP.isLB (K := Fin 1) (fun _ => 𝟙 D.t.G.left) (fun _ => ((1 : ℕ) : ℤ))
  obtain ⟨τ, hτ⟩ := sec_pull_down ((isGen_iff w₁).1 hw₁) D.t.PP.isLB hM σ
  refine ⟨τ, fun h0 => hβ fun y k hk => ?_⟩
  obtain ⟨j, hj⟩ := exists_chart D.t.PP.isLB (D.m.φ y)
  obtain ⟨k', hk'⟩ := exists_chart hM (D.m.φ y)
  have hz : LB.Sec.f τ k' = 0 := congrArg (fun s : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _)
    (fun _ => ((1 : ℕ) : ℤ))) => LB.Sec.f s k') h0
  have e₁ := hτ _ D.m.φ y j k' hj hk'
  rw [hz, gs_zero _ y _ hk', mul_zero, Category.comp_id] at e₁
  have e₂ := hσ y j k hj hk
  rw [e₁, D.m.cart.1.w, cst_comp] at e₂
  have ha' : algebraMap (𝓞 L) L a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).2 (nonZeroDivisors.ne_zero ha)
  have u₁ : IsUnit (cst D.tK.G.hom y (algebraMap (𝓞 L) L a)) :=
    IsUnit.of_mul_eq_one (cst D.tK.G.hom y (algebraMap (𝓞 L) L a)⁻¹) (by
      rw [← cst_mul, mul_inv_cancel₀ ha', cst_one])
  exact (Units.isUnit _).mul_right_eq_zero.1 (u₁.mul_right_eq_zero.1 e₂.symm)

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPeriodRiemannLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FibreAtPeriod

section Reparam

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left}

theorem exists_reparam_isAH {g g' : ℕ} (u : HolUnif A L g') (X : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ))
    (Hm : Matrix (Fin g') (Fin g') ℂ) (Hf : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (hAH : u.IsAH Hm χ)
    (hHf : Hf.IsHermitian) (hf : ∀ x y, hermForm Hf x y = hermForm Hm (X x) (X y)) :
    ∃ (u₂ : HolUnif A L g) (χ₂ : u₂.Λ → ℂ), (∀ z, u₂.ex z = u.ex (X z)) ∧ (∀ z, z ∈ u₂.Λ ↔ X z ∈ u.Λ) ∧
      u₂.IsAH Hf χ₂ ∧ ∀ w v, u.IsDiff (X w) v → u₂.IsDiff w v := by
  have hg : g = g' := by simpa using X.finrank_eq
  subst hg
  refine ⟨GlobalTheory.holUnifReparam u X (fun _ => 1) (differentiable_const _) (fun _ => one_ne_zero),
    fun l => χ ⟨X l, l.2⟩, fun _ => rfl, fun _ => Iff.rfl, ⟨hHf, ?_, fun l => hAH.2.2.1 _, ?_⟩, ?_⟩
  · intro z hz
    have h := hAH.2.1 (X z) ((LinearEquiv.map_ne_zero_iff X).2 hz)
    have e := hf z z
    unfold hermForm at e
    rw [e]
    exact h
  · intro l i z hz
    have h := hAH.2.2.2 ⟨X l, l.2⟩ i (X z) hz
    have e1 := hf z l
    have e2 := hf l l
    unfold hermForm at e1 e2
    show u.fr i (X z) / 1 = χ ⟨X l, l.2⟩ * Complex.exp (Real.pi * (z ⬝ᵥ Hf.mulVec (star (l : Fin g → ℂ))) +
      Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hf.mulVec (star (l : Fin g → ℂ)))) * (u.fr i (X (z + l)) / 1)
    rw [div_one, div_one, map_add (f := _), h, e1, e2]
  · intro w v hv U h f
    rw [hv U h f]
    have key := X.toContinuousLinearEquiv.comp_right_fderiv
      (f := fun z => valAt' (u.ex z).left U f) (x := 0)
    have h2 := congrArg (fun T => T w) key
    simp only [map_zero] at h2
    exact h2.symm

end Reparam

theorem fibreLatVec_of_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (R : RiemLat E g (FU.Di i).La) (P : (FU.Di i).La →+ (Fin g → ℂ)) (h : Matrix (Fin g) (Fin g) ℂ), IsPeriod (FU.Di i) ty P → R.form = (FU.Di i).EF → IsUnit h.det → (∀ x, P x = h *ᵥ R.P x) → ∀ (A₀ : Type) (x : A₀ → Fin g → ℂ) (v : A₀ → (epsAt (FU.u i P) ⟶ Xo.univ.t.G)), (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (h *ᵥ x a) (v a).left) → FibreLatVec Xo.univ.t (FU.u i P) R x v := by
  intro E _ _ _ H D l Xo σ g ty FU i R P h hP hRf hdet hPh A₀ x v hd
  let hl : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := h.toLinearEquiv' (h.invertibleOfIsUnitDet hdet)
  have hla : ∀ z, hl z = h *ᵥ z := fun z => by
    show Matrix.toLin' h z = h *ᵥ z
    exact Matrix.toLin'_apply h z
  have hlP : ∀ a, hl (R.P a) = P a := fun a => by rw [hla, hPh]
  have hlP' : ∀ a, hl.symm (P a) = R.P a := fun a => by rw [← hlP, hl.symm_apply_apply]
  obtain ⟨Q, ψ, -, hQ, hQL, -⟩ := GlobalTheory.exists_polAV_pullback_of_isLocalRing E H _ Xo.univ.t Xo.univ.proper
    Xo.univ.ample Xo.univ.ktriv ℂ (FU.u i P)
  obtain ⟨u, H₂, χ, F, hAH, -, d₂, -, hF, hΛ, hE⟩ :=
    GlobalTheory.familyUnif_fibre_theta GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1.weil E H D l Xo σ g ty FU i P hP
      Q ψ hQ hQL
  obtain ⟨w, hw⟩ := hQL

  have hLB : (Xo.univ.t.PP.L.pull ψ).IsLB := LB.isLB_pull Xo.univ.t.PP.isLB ψ
  let ub : HolUnif Q.A (Xo.univ.t.PP.L.pull ψ) Q.g := GlobalTheory.ArchMetricCompare.carry u Q.isLB hLB hw
  have hAHb : ub.IsAH H₂ χ := GlobalTheory.ArchMetricCompare.carry_isAH Q.isLB hLB hw hAH
  let T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin Q.g → ℂ) := hl.trans F
  have hf : ∀ x y, hermForm R.Hm x y = hermForm H₂ (T x) (T y) := fun x y => by
    have key := GlobalTheory.KeyFam.SamePeriod.hermForm_eq_of_im H₂ F.toLinearMap R.Hm hl.symm.toLinearMap hP.2.2.2.1 (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      have h1 := hE a b
      have h2 := R.im a b
      rw [hRf] at h2
      show (hermForm H₂ (F (P a)) (F (P b))).im = (hermForm R.Hm (hl.symm (P a)) (hl.symm (P b))).im
      rw [hlP', hlP', h1]
      exact h2.symm) (hl x) (hl y)
    show _ = hermForm H₂ (F (hl x)) (F (hl y))
    simpa using key.symm
  obtain ⟨u', χ', hue, huΛ, huAH, hud⟩ := exists_reparam_isAH ub T H₂ R.Hm χ hAHb R.herm hf
  have hex : ∀ q, (u'.ex q).left ≫ ψ = (FU.ex i P (hl q)).left := fun q => by
    rw [hue]
    exact hF (hl q)

  have hB : ∀ (a : 𝓞 E) (p : Fin g → ℂ), hl (R.B a p) = fun k => ty k (a : E) * hl p k := fun a p => by
    let Da : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      { toFun := fun z k => ty k (a : E) * z k
        map_add' := fun z z' => by
          ext k
          simp [mul_add]
        map_smul' := fun c z => by
          ext k
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          ring }
    let N : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      hl.toLinearMap.comp ((R.B a).comp hl.symm.toLinearMap) - Da
    have hN : N.restrictScalars ℝ = 0 := LinearMap.ext_on hP.2.2.2.1 (by
      rintro _ ⟨y, rfl⟩
      show hl (R.B a (hl.symm (P y))) - (fun k => ty k (a : E) * P y k) = 0
      rw [hlP', ← R.act, hlP, sub_eq_zero]
      exact funext (hP.1 a y))
    have h0 : N (hl p) = 0 := congrArg (fun f => f (hl p)) hN
    have h1 : hl (R.B a (hl.symm (hl p))) - (fun k => ty k (a : E) * hl p k) = 0 := h0
    rw [hl.symm_apply_apply] at h1
    exact sub_eq_zero.1 h1
  refine ⟨Q.A, inferInstance, ψ, u', χ', hQ, huAH, fun a p => ?_, fun y y' hy => ?_, fun p => ?_, fun a => ?_⟩
  · rw [hex, hB, FU.ex_lin i P hP a (hl p), Over.comp_left, ← Category.assoc, hex]
  · exact hP.2.1 (by rw [hPh, hPh, hy])
  · rw [huΛ]
    show F (hl p) ∈ u.Λ ↔ _
    rw [hΛ]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, hl.injective (by rw [hlP, hy])⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, (hlP y).symm⟩
  · have hd' : IsDerivAt0 (fun z => (FU.ex i P z).left) (hl (x a)) (v a).left := by
      rw [hla]
      exact hd a
    obtain ⟨t, ⟨h₁, h₂⟩, -⟩ := d₂ (F (hl (x a)))
    refine ⟨t, GlobalTheory.VerticalDeriv.isDerivAt0_unique
      (Flat.PerGram.isDerivAt0_of_fibre ψ u F.toLinearMap hF h₁ h₂) hd', hud (x a) t h₂⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.FibreAtPeriod
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMultLabelRank
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgeCpt

theorem lieMult_label_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (s : CMType H ⊕ CMType H), LieMult 𝔐.t.act 𝔐.ξ (𝔐.emb s) (labelRk D s) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J y 𝔐 s
  letI := 𝔐.acg
  letI := 𝔐.mod
  obtain ⟨U, hU, b, hspan, hfr⟩ := 𝔐.vb s ⟨genPt 𝔐.ξ, specializes_refl _⟩ (Set.mem_univ _)
  exact (Fl.Test.lieMult_iff_exists_frame _ _ _ _).2
    ⟨_, (Fl.Test.isEigFrame_iff 𝔐.M 𝔐.t.act 𝔐.ρ 𝔐.act (𝔐.emb s) b).2
      ⟨(hfr _ (Set.mem_univ _) hU).1, hspan⟩⟩

end GlobalTheory.CompanionTheory.Ar.HodgeCpt
end

