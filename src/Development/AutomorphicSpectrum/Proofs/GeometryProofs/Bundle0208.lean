module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
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
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0203
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0090
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0142
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0055
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CubicalWeilPairingIsoInvariant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.CubIso

section Local
variable {X Y Z : Scheme.{0}} {A B : LB X}

def isoGerm (w : LB.Iso A B) (f : Y ⟶ X) (y : Y) (j : B.ι) (k : A.ι) : (Y.presheaf.stalk y)ˣ :=
  gm f y (B.U j ⊓ A.U k) (w.s (j, k))

theorem isoGerm_trans {w : LB.Iso A B} (hw : w.IsGen) (f : Y ⟶ X) (y : Y) {j j' : B.ι} {k k' : A.ι}
    (hj : f y ∈ B.U j) (hj' : f y ∈ B.U j') (hk : f y ∈ A.U k) (hk' : f y ∈ A.U k') :
    isoGerm w f y j k = gm f y _ (B.g j j') * (gm f y _ (A.g k k'))⁻¹ * isoGerm w f y j' k' := by
  have hm : f y ∈ B.U j ⊓ A.U k ⊓ (B.U j' ⊓ A.U k') := ⟨⟨hj, hk⟩, hj', hk'⟩
  have h := congrArg (gm f y (B.U j ⊓ A.U k ⊓ (B.U j' ⊓ A.U k'))) (hw (j, k) (j', k'))
  have e : gm f y (B.U j ⊓ A.U k ⊓ (B.U j' ⊓ A.U k')) ((LB.div B A).g (j, k) (j', k')) =
      gm f y _ (B.g j j') * (gm f y _ (A.g k k'))⁻¹ := by
    show gm f y _ (res _ (B.g j j') * (res _ (A.g k k'))⁻¹) = _
    rw [map_mul, map_inv, gm_res f y _ hm, gm_res f y _ hm]
  exact (gm_res f y _ hm _).symm.trans (h.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) e (gm_res f y _ hm _))))

variable {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem prod_isoGerm_trans {w : LB.Iso A B} (hw : w.IsGen) (r : Z ⟶ Y) (z : Z) {p p' : K → B.ι} {q q' : K → A.ι}
    (hp : r z ∈ LB.wchart B φ p) (hp' : r z ∈ LB.wchart B φ p') (hq : r z ∈ LB.wchart A φ q)
    (hq' : r z ∈ LB.wchart A φ q') :
    ∏ k, isoGerm w (r ≫ φ k) z (p k) (q k) ^ ε k =
      trF (L := B) φ ε r z p p' * (trF (L := A) φ ε r z q q')⁻¹ * ∏ k, isoGerm w (r ≫ φ k) z (p' k) (q' k) ^ ε k := by
  rw [trF, trF, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [isoGerm_trans hw (r ≫ φ k) z (Set.mem_iInter.1 hp k) (Set.mem_iInter.1 hp' k) (Set.mem_iInter.1 hq k)
    (Set.mem_iInter.1 hq' k), mul_zpow, mul_zpow, _root_.inv_zpow]

theorem exists_ratio (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} (hw : w.IsGen) {a : LB.Gen (LB.LinComb A φ ε)}
    {b : LB.Gen (LB.LinComb B φ ε)} (ha : a.IsGen) (hb : b.IsGen) :
    ∃ v : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → B.ι) (q : K → A.ι),
      r z ∈ LB.wchart B φ p → r z ∈ LB.wchart A φ q →
      gm r z (LB.wchart B φ p) (b.s p) = gm r z ⊤ v * (∏ k, isoGerm w (r ≫ φ k) z (p k) (q k) ^ ε k) *
        gm r z (LB.wchart A φ q) (a.s q) := by
  let Wc : (K → B.ι) × (K → A.ι) → Y.Opens := fun P => LB.wchart B φ P.1 ⊓ LB.wchart A φ P.2
  have le : ∀ P k, Wc P ≤ φ k ⁻¹ᵁ (B.U (P.1 k) ⊓ A.U (P.2 k)) := fun P k =>
    le_inf (inf_le_left.trans (LB.wchart_le B φ P.1 k)) (inf_le_right.trans (LB.wchart_le A φ P.2 k))
  let I : ∀ P, Γ(Y, Wc P)ˣ := fun P => res (inf_le_left : Wc P ≤ LB.wchart B φ P.1) (b.s P.1) *
    (res (inf_le_right : Wc P ≤ LB.wchart A φ P.2) (a.s P.2))⁻¹ *
    (∏ k, res (le P k) (pullU (φ k) _ (w.s (P.1 k, P.2 k))) ^ ε k)⁻¹
  have hI : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) P, r z ∈ Wc P → gm r z (Wc P) (I P) =
      gm r z (LB.wchart B φ P.1) (b.s P.1) * (gm r z (LB.wchart A φ P.2) (a.s P.2))⁻¹ *
        (∏ k, isoGerm w (r ≫ φ k) z (P.1 k) (P.2 k) ^ ε k)⁻¹ := by
    intro Z r z P hz
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _)
      ((map_inv _ _ ).trans (congrArg _ (gm_res r z _ hz _))))) ((map_inv _ _).trans (congrArg _ ?_)))
    refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
    exact (gm_res r z (le P k) hz _).trans (gm_pull r (φ k) z _ (le P k hz) _)
  obtain ⟨v, hv⟩ := glue_unit ⊤ Wc (fun _ => le_top) (fun x _ => by
      choose p hp using fun k => exists_chart hB (φ k x)
      choose q hq using fun k => exists_chart hA (φ k x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(p, q), Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩) I (fun P Q x hx => by
      rw [hI _ _ x P hx.1, hI _ _ x Q hx.2, gen_trans hb (𝟙 Y) x hx.1.1 hx.2.1, gen_trans ha (𝟙 Y) x hx.1.2 hx.2.2,
        prod_isoGerm_trans hw (𝟙 Y) x hx.1.1 hx.2.1 hx.1.2 hx.2.2]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨v, fun Z r z p q hp hq => ?_⟩
  have hz : r z ∈ Wc (p, q) := ⟨hp, hq⟩
  have e := (gm_res r z (le_top : Wc (p, q) ≤ ⊤) hz v).symm.trans ((congrArg (gm r z (Wc (p, q))) (hv (p, q))).trans
    (hI Z r z (p, q) hz))
  rw [e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem appTop_eq_one (r : Z ⟶ Y) (v : Γ(Y, ⊤)ˣ) (h : ∀ z, gm r z ⊤ v = 1) : r.appTop.hom v.val = 1 := by
  have e : Units.map r.appTop.hom.toMonoidHom v = 1 :=
    unit_ext fun z _ => by rw [← gm_top r z v, h z, map_one]
  exact congrArg Units.val e

end Local

section Cube
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L₁ L₂ : RigLB G}

theorem exists_cube_ratio {w : LB.Iso L₁.L L₂.L} (hw : w.IsGen) (c₁ : CubicalStr G L₁) (c₂ : CubicalStr G L₂) :
    ∃ v : Γ((G ⊗ G ⊗ G).left, ⊤)ˣ, ∀ (T : Over S) (z : T.left) (J₁ : (T.left ⟶ G.left) → L₁.L.ι)
      (J₂ : (T.left ⟶ G.left) → L₂.L.ι), Good L₁.L z J₁ → Good L₂.L z J₂ →
      ∀ (W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ), (∀ x, W x = isoGerm w x.left z (J₂ x.left) (J₁ x.left)) →
      ∀ a b d : T ⟶ G, cubV c₂ z J₂ a b d * W (a * b) * W (a * d) * W (b * d) * W 1 =
        gm (lift a (lift b d)).left z ⊤ v * (W (a * b * d) * W a * W b * W d) * cubV c₁ z J₁ a b d := by
  obtain ⟨v, hv⟩ := exists_ratio (φ := thφ G (x3 G)) (ε := thε) (a := c₁.t) (b := c₂.t) L₁.isLB L₂.isLB hw
    c₁.isGen c₂.isGen
  refine ⟨v, fun T z J₁ J₂ h₁ h₂ W hW a b d => ?_⟩
  have e := hv T.left (lift a (lift b d)).left z (fun I => J₂ ((lift a (lift b d)).left ≫ thφ G (x3 G) I))
    (fun I => J₁ ((lift a (lift b d)).left ≫ thφ G (x3 G) I)) (h₂.mem _ _) (h₁.mem _ _)
  have f := prod_cub a b d (fun q => isoGerm w q z (J₂ q) (J₁ q))
  have e' : cubV c₂ z J₂ a b d = gm (lift a (lift b d)).left z ⊤ v *
      (∏ I : thK.{0}, isoGerm w ((lift a (lift b d)).left ≫ thφ G (x3 G) I) z
        (J₂ ((lift a (lift b d)).left ≫ thφ G (x3 G) I)) (J₁ ((lift a (lift b d)).left ≫ thφ G (x3 G) I)) ^ thε I) *
      cubV c₁ z J₁ a b d := e
  rw [e', f, hW, hW, hW, hW, hW, hW, hW, hW]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem cube_ratio_faces {w : LB.Iso L₁.L L₂.L} (c₁ : CubicalStr G L₁) (c₂ : CubicalStr G L₂)
    {v : Γ((G ⊗ G ⊗ G).left, ⊤)ˣ}
    (hv : ∀ (T : Over S) (z : T.left) (J₁ : (T.left ⟶ G.left) → L₁.L.ι)
      (J₂ : (T.left ⟶ G.left) → L₂.L.ι), Good L₁.L z J₁ → Good L₂.L z J₂ →
      ∀ (W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ), (∀ x, W x = isoGerm w x.left z (J₂ x.left) (J₁ x.left)) →
      ∀ a b d : T ⟶ G, cubV c₂ z J₂ a b d * W (a * b) * W (a * d) * W (b * d) * W 1 =
        gm (lift a (lift b d)).left z ⊤ v * (W (a * b * d) * W a * W b * W d) * cubV c₁ z J₁ a b d)
    (T : Over S) (x y : T ⟶ G) :
    (lift (1 : T ⟶ G) (lift x y)).left.appTop.hom v.val = 1 ∧
      (lift x (lift (1 : T ⟶ G) y)).left.appTop.hom v.val = 1 ∧
      (lift x (lift y (1 : T ⟶ G))).left.appTop.hom v.val = 1 := by
  refine ⟨appTop_eq_one _ v fun z => ?_, appTop_eq_one _ v fun z => ?_, appTop_eq_one _ v fun z => ?_⟩
  all_goals
    obtain ⟨J₁, h₁⟩ := exists_good_pt L₁.isLB z
    obtain ⟨J₂, h₂⟩ := exists_good_pt L₂.isLB z
  · have e := hv T z J₁ J₂ h₁ h₂ _ (fun _ => rfl) 1 x y
    rw [(isCub_cubV c₁ (T := T) h₁).face x y, (isCub_cubV c₂ (T := T) h₂).face x y] at e
    simp only [_root_.one_mul, _root_.mul_one] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · have e := hv T z J₁ J₂ h₁ h₂ _ (fun _ => rfl) x 1 y
    rw [(isCub_cubV c₁ (T := T) h₁).face₂ x y, (isCub_cubV c₂ (T := T) h₂).face₂ x y] at e
    simp only [_root_.one_mul, _root_.mul_one] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · have e := hv T z J₁ J₂ h₁ h₂ _ (fun _ => rfl) x y 1
    rw [(isCub_cubV c₁ (T := T) h₁).face₃ x y, (isCub_cubV c₂ (T := T) h₂).face₃ x y] at e
    simp only [_root_.one_mul, _root_.mul_one] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'

end Cube

theorem cubWeil_of_lbIso : ∀ (G : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → TorusExtension G → ∀ (L₁ L₂ : RigLB G) (c₁ : CubicalStr G L₁) (c₂ : CubicalStr G L₂), LBIso L₁.L L₂.L → ∀ (N : ℕ) (x y : 𝟙_ (Over (Sp ℂ)) ⟶ G) (ζ : Γ(Sp ℂ, ⊤)ˣ), CubWeil c₁ N x y ζ → CubWeil c₂ N x y ζ := by
  intro G _ _ hs te L₁ L₂ c₁ c₂ hiso N x y ζ h
  obtain ⟨w, hw⟩ := hiso
  obtain ⟨v, hv⟩ := exists_cube_ratio hw c₁ c₂
  have hone := _root_.GlobalTheory.CompanionTheory.Ar.CubeUnit.eq_one_at_rational_points ℂ G hs te v (cube_ratio_faces c₁ c₂ hv)
  refine ⟨h.1, h.2.1, fun z J₂ h₂ => ?_⟩
  obtain ⟨J₁, h₁⟩ := exists_good_pt L₁.isLB z
  let W : (𝟙_ (Over (Sp ℂ)) ⟶ G) → _ := fun a => isoGerm w a.left z (J₂ a.left) (J₁ a.left)
  refine cubN_ratio_twist (MonoidHom.id _) W (fun a b d => ?_) h.1 h.2.1 (h.2.2 z J₁ h₁)
  have e := hv _ z J₁ J₂ h₁ h₂ W (fun _ => rfl) a b d
  have g : gm (lift a (lift b d)).left z ⊤ v = 1 := by
    rw [gm_top]
    have : Units.map (lift a (lift b d)).left.appTop.hom.toMonoidHom v = 1 := Units.ext (hone a b d)
    rw [this, map_one]
  rw [g, _root_.one_mul] at e
  exact e

end GlobalTheory.CompanionTheory.Ar.CubIso
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNonzeroSectionPpDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_section_pp_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), ∃ t : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), t ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_sec_ne_zero_int | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_sec_ne_zero_int | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_sec_ne_zero_int <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPPowerLevelFromPrimesAboveP
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SplitEx

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi _root_.GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem isPreimmersion_fst (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) :
    IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
  have b₁ : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  exact MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip b₁

theorem mem_of_dense_of_isOpen {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    [T0Space X] {U : Set X} (hU : IsOpen U) (hd : Dense U) {x : X} (hx : ∀ z, z ⤳ x → z = x) : x ∈ U := by
  have hfin : (irreducibleComponents X).Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hgen : ∀ C ∈ irreducibleComponents X, x ∈ C → C = closure {x} := by
    intro C hC hxC
    have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    have e := hx _ (hg.specializes hxC)
    rw [← e]
    exact hg.def.symm
  let T : Set X := ⋃ C ∈ irreducibleComponents X \ {closure {x}}, C
  have hT : IsClosed T := Set.Finite.isClosed_biUnion (hfin.subset Set.diff_subset)
    fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  have hxT : x ∈ Tᶜ := by
    intro h
    obtain ⟨C, ⟨hC, hne⟩, hxC⟩ := Set.mem_iUnion₂.1 h
    exact hne (hgen C hC hxC)
  obtain ⟨w, hwT, hwU⟩ := hd.inter_open_nonempty _ hT.isOpen_compl ⟨x, hxT⟩
  have hwC : w ∈ closure {x} := by
    by_contra hn
    refine hwT (Set.mem_iUnion₂.2 ⟨irreducibleComponent w,
      ⟨irreducibleComponent_mem_irreducibleComponents w, fun e => hn ?_⟩, mem_irreducibleComponent⟩)
    rw [← (show irreducibleComponent w = closure {x} from e)]
    exact mem_irreducibleComponent
  exact (specializes_iff_mem_closure.2 hwC).mem_open hU hwU

theorem injective_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) : Function.Injective Y.j := by
  have := isPreimmersion_fst Y
  have := Y.jQ_open
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  exact Y.j.isEmbedding.injective

theorem genPt_comp {X X' : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (g : X ⟶ X') :
    genPt (ξ ≫ g) = g (genPt ξ) :=
  Scheme.Hom.comp_apply ξ g (IsLocalRing.closedPoint Ω : Spec (CommRingCat.of Ω))

theorem mem_range_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ Y.X) (cst : c.F →+* Ω) (hmax : ∀ y, y ⤳ genPt ξ → y = genPt ξ)
    (hs : ξ ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F))) : genPt ξ ∈ Set.range Y.j := by
  have hpr := projProper _ _ _ Y.proj
  have sq : ξ ≫ Y.s = spMap cst ≫ spMap (algebraMap (𝓞 c.F) c.F) := by rw [hs, spMap_comp']
  let P := pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))
  let ξ₁ : Spec (CommRingCat.of Ω) ⟶ P := pullback.lift ξ (spMap cst) sq
  have hf : ξ₁ ≫ pullback.fst _ _ = ξ := pullback.lift_fst _ _ _
  let pt : Spec (CommRingCat.of Ω) := IsLocalRing.closedPoint Ω
  let x₁ : P := ξ₁ pt
  have h1 : pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) x₁ = genPt ξ := by
    have e := Scheme.Hom.comp_apply ξ₁ (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) pt
    rw [hf] at e
    exact e.symm
  have a₁ := isPreimmersion_fst Y
  have hx₁ : ∀ z : P, z ⤳ x₁ → z = x₁ := by
    intro z hz
    apply (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.injective
    rw [h1]
    exact hmax _ (h1 ▸ hz.map (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).continuous)
  have : LocallyOfFiniteType (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := inferInstance
  have : QuasiCompact (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := inferInstance
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
  have : IsNoetherian P := {}
  have := Y.jQ_open
  obtain ⟨v', hv'⟩ := mem_of_dense_of_isOpen Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hx₁
  exact ⟨v', by rw [Model.j, Scheme.Hom.comp_apply, hv', h1]⟩

theorem splitComps_of_fnAlgClosed (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (hc : Formalism.L2.Pj.FnAlgClosed (Xo := Xo) (c := c)) : SplitComps Y := by
  intro Ω _ ξ cst hξ hs a ha
  have hmax := CptInh.nogen ξ hξ
  obtain ⟨w₀, hw₀⟩ := mem_range_j Y ξ cst hmax hs
  have hwmax : ∀ y, y ⤳ w₀ → y = w₀ := by
    intro y hy
    have h1 : Y.j y ⤳ genPt ξ := hw₀ ▸ hy.map Y.j.continuous
    exact injective_j Y ((hmax _ h1).trans hw₀.symm)
  let Z : Formalism.L2.Pj.Comp Xo c := ⟨irreducibleComponent w₀, irreducibleComponent_mem_irreducibleComponents w₀⟩
  have hZ : Formalism.L2.Pj.genPt Z = w₀ := by
    have hC := irreducibleComponent_mem_irreducibleComponents w₀
    have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    exact hwmax _ (hg.specializes mem_irreducibleComponent)
  have e : genPt (Formalism.L2.Pj.genSp Z ≫ Y.j) = genPt ξ := by
    refine (genPt_comp (Ω := Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.genSp Z) Y.j).trans ?_
    rw [← hw₀, ← hZ]
    exact congrArg Y.j (Scheme.fromSpecResidueField_apply _ _)
  obtain ⟨i, hi⟩ := TowerOfTest.factor ξ hξ (Formalism.L2.Pj.genSp Z ≫ Y.j) e
  have hcomp : i.comp cst = algebraMap c.F (Formalism.L2.Pj.kap Z) := by
    have hsY : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
      rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
    have h1 : Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) :=
      (Spec.map_preimage _).symm
    have h2 : spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) ≫ spMap (algebraMap (𝓞 c.F) c.F) =
        spMap i ≫ spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [← h1, ← hs]
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans (congrArg (Formalism.L2.Pj.genSp Z ≫ ·) hsY.symm) ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact (congrArg (· ≫ Y.s) hi).trans (Category.assoc _ _ _)
    have e0 : (i.comp cst).comp (algebraMap (𝓞 c.F) c.F) =
        (algebraMap c.F (Formalism.L2.Pj.kap Z)).comp (algebraMap (𝓞 c.F) c.F) := by
      apply TowerOfTest.spec_inj
      have : spMap ((i.comp cst).comp (algebraMap (𝓞 c.F) c.F)) =
          spMap i ≫ spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
        rw [RingHom.comp_assoc, spMap_comp']
      exact this.trans (h2.symm.trans (spMap_comp' _ _).symm)
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) e0
  have hb : IsAlgebraic c.F (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z) (i a)) := by
    obtain ⟨p, hp0, hp⟩ := ha
    refine ⟨p.map (Int.castRingHom c.F), (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hp0, ?_⟩
    have h3 := Polynomial.hom_eval₂ p (algebraMap ℤ Ω) ((algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).comp i) a
    rw [← Polynomial.aeval_def, hp, map_zero] at h3
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    refine Eq.trans ?_ h3.symm
    exact congrArg (fun φ => Polynomial.eval₂ φ _ p) (Subsingleton.elim _ _)
  obtain ⟨k, hk⟩ := hc Z _ hb
  refine ⟨k, i.injective ?_⟩
  have h2 : algebraMap c.F (Formalism.L2.Pj.kap Z) k = i a := by
    apply (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).injective
    rw [← hk, ← IsScalarTower.algebraMap_apply]
  rw [← h2, ← hcomp]
  rfl

end GlobalTheory.CompanionTheory.Ar.SplitEx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSqrtNegDiscPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.PointDet

theorem isReduced_of_isNormalScheme {X : Scheme.{0}} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (h x).1
    infer_instance
  exact isReduced_of_isReduced_stalk X

theorem connectedSpace_of_specializes {X : Scheme.{0}} (x : X) (h : ∀ q : X, x ⤳ q) : ConnectedSpace X := by
  have hcl : closure {x} = (Set.univ : Set X) :=
    Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.1 (h q)
  have hp : PreconnectedSpace X := ⟨by rw [← hcl]; exact isPreconnected_singleton.closure⟩
  exact { toPreconnectedSpace := hp, toNonempty := ⟨x⟩ }

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

noncomputable def rtF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) : c.F :=
  ⟨H.rt0, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩

theorem rtF_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    rtF c ^ 2 = -(H.d : c.F) := by
  apply Subtype.ext
  simpa [rtF] using H.sqrt_neg_disc_sq

theorem isIntegral_rtF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    IsIntegral ℤ (rtF c) := by
  refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
  rw [rtF_sq]
  have := isIntegral_algebraMap (R := ℤ) (A := c.F) (x := -(H.d : ℤ))
  simpa using this

noncomputable def rtO {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) : 𝓞 c.F :=
  IsIntegralClosure.mk' (𝓞 c.F) (rtF c) (isIntegral_rtF c)

theorem algebraMap_rtO {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    algebraMap (𝓞 c.F) c.F (rtO c) = rtF c :=
  IsIntegralClosure.algebraMap_mk' _ _ _

theorem rtO_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    rtO c ^ 2 = -(H.d : 𝓞 c.F) := by
  apply RingOfIntegers.ext
  have := rtF_sq c
  rw [← algebraMap_rtO] at this
  simpa using this

theorem detCond_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ 𝔐.X), ∃ ρ : L, ρ ^ 2 = -(H.d : L) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k), DetCond D 𝔐.t.act (spMap g ≫ z) (g ρ) := by
  intro E _ _ _ H D l Xo c Y S Ω _ Kf _ J _ y 𝔐 L _ _ z
  haveI : IsReduced 𝔐.X := isReduced_of_isNormalScheme 𝔐.normal
  haveI : ConnectedSpace 𝔐.X := connectedSpace_of_specializes _ 𝔐.all
  haveI : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨n, hn⟩ := GlobalTheory.CompanionTheory.Ggeo.exists_smoothOfRelativeDimension_of_geometricallyConnected 𝔐.X 𝔐.t.G 𝔐.t.semi.smooth 𝔐.t.semi.geomConnected
  let s : 𝔐.X ⟶ Sp (𝓞 c.F) := 𝔐.f ≫ Y.s
  have hd : Dense {p : 𝔐.X | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ 𝔐.X)
      (β : 𝓞 c.F →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D 𝔐.t.act x (β (rtO c))} := by
    intro q
    refine closure_mono (Set.singleton_subset_iff.2 ?_) (specializes_iff_mem_closure.1 (𝔐.all q))
    let i : Ω →+* AlgebraicClosure Ω := algebraMap Ω (AlgebraicClosure Ω)
    haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
    haveI : CharZero (AlgebraicClosure Ω) := charZero_of_injective_ringHom i.injective
    refine ⟨AlgebraicClosure Ω, inferInstance, inferInstance, inferInstance, spMap i ≫ 𝔐.ξ,
      i.comp (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)), ?_, ?_, ?_⟩
    · let y₀ : Sp (AlgebraicClosure Ω) := (default : PrimeSpectrum (AlgebraicClosure Ω))
      refine ⟨y₀, ?_⟩
      rw [Scheme.Hom.comp_apply]
      exact congrArg 𝔐.ξ (Subsingleton.elim _ _)
    · have h := 𝔐.cst_over
      change (spMap i ≫ 𝔐.ξ) ≫ 𝔐.f ≫ Y.s = _
      rw [Category.assoc, h, spMap_comp_spMap]
    · intro τ
      have hβ : (i.comp (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))) (rtO c) = (i.comp 𝔐.cst) (rtF c) := by
        simp only [RingHom.comp_apply, algebraMap_rtO]
      rw [hβ]
      obtain ⟨h₁, h₂⟩ := GlobalTheory.CompanionTheory.Ar.LabelCover.exists_label E H l c (rtF c) rfl (AlgebraicClosure Ω) (i.comp 𝔐.cst) τ
      constructor
      · intro h
        obtain ⟨t, rfl⟩ := h₁ h
        exact (GlobalTheory.DetExtend.lieMult_extend i 𝔐.ξ 𝔐.t.act (𝔐.emb (.inl t)) D.p).2
          (GlobalTheory.CompanionTheory.Ar.HodgeCpt.lieMult_label_generic E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S Ω Kf J y 𝔐 (.inl t))
      · intro h
        obtain ⟨t, rfl⟩ := h₂ h
        exact (GlobalTheory.DetExtend.lieMult_extend i 𝔐.ξ 𝔐.t.act (𝔐.emb (.inr t)) D.q).2
          (GlobalTheory.CompanionTheory.Ar.HodgeCpt.lieMult_label_generic E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S Ω Kf J y 𝔐 (.inr t))
  obtain ⟨b, hb⟩ := Spec.map_surjective (z ≫ s)
  refine ⟨b.hom (rtO c), ?_, ?_⟩
  · have := congrArg b.hom (rtO_sq c)
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  · intro k _ _ g
    haveI : CharZero k := charZero_of_injective_ringHom g.injective
    refine GlobalTheory.DetSpread.detCond_of_dense E H D 𝔐.X 𝔐.t.G n 𝔐.t.act (𝓞 c.F) s (rtO c) hn (rtO_sq c) hd k
      (spMap g ≫ z) (g.comp b.hom) ?_
    rw [Category.assoc, ← hb]
    exact spMap_comp_spMap b.hom g

end GlobalTheory.CompanionTheory.Ar.PointDet
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPurePeriodsSpan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ggeo

theorem point_numberField_of_finiteIndex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (n : ℕ), 0 < n → (∀ y : (FU.Di i).La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → ∃ (K₁ : IntermediateField ℚ ℂ) (hk : KA l ≤ K₁) (y : Sp K₁ ⟶ Xo.X), FiniteDimensional ℚ K₁ ∧ y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i P :=
  @PositivityTheory.Xgf.family_pure_periods_span

end GlobalTheory.CompanionTheory.Ggeo
end

