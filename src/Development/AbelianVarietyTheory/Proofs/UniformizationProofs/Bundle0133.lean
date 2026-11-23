module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationNonnegIffSpanMultiplicationTranslates
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.firstFiveLaws : _root_.GlobalTheory.UT.LL := by
  unfold _root_.GlobalTheory.UT.LL
  obtain ⟨h₁, h₂, h₃, h₄, h₅, -⟩ := _root_.GlobalTheory.allSixLaws
  exact ⟨h₁, h₂, h₃, h₄, h₅⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcClauseClosed
section
namespace GlobalTheory

theorem arcClause_closed : ReciprocityTheory.ChartRestriction.G.Geo.Tor.ToroidalArchimedeanCondition :=
  _root_.GlobalTheory.HolomorphicArc.main _root_.GlobalTheory.abelianSchemeLaws_all.1 _root_.GlobalTheory.abelianSchemeLaws_all.2 _root_.GlobalTheory.thetaUnifAV_all

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CmPointClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PureType
open scoped CategoryTheory.Obj

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
private theorem weil_pairing_properties : _root_.ReciprocityTheory.ChartRestriction.G.Out.WeilSt :=
  (_root_.GlobalTheory.AbLaw.FromCube.all_of_cubeGen
    (fun S P M a ↦ _root_.GlobalTheory.AbLaw.CubeAssembly.cube_gen S P M a)).2.2.2.2.1


open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.cmPoint_closed : _root_.GlobalTheory.CMPoint :=
  _root_.GlobalTheory.cmPoint _root_.GlobalTheory.thetaUnifAV_all weil_pairing_properties

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCmEllipticCurveWithPeriod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane in
theorem _root_.GlobalTheory.cmCurve_closed : _root_.GlobalTheory.CMCurve :=
  _root_.GlobalTheory.cmCurve_of_uniformisation _root_.GlobalTheory.thetaUnifAV_all
    _root_.GlobalTheory.polBaseChange_holds _root_.GlobalTheory.homExtension_semiAbelian_dvr_unconditional

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointRepresentingWeightMumfordQuotient
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WtPoint

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}
  {Y : Scheme.{0}} {f : G.left ⟶ Y}

theorem gm_gen_pull {Z W : Scheme.{0}} {F : Z ⟶ Y} {M : LB Y} {t : LB.Gen (M.pull F)} (ht : t.IsGen) (r : W ⟶ Z) (y : W)
    {j j' : M.ι} (hj : F (r y) ∈ M.U j) (hj' : F (r y) ∈ M.U j') :
    gm r y ((M.pull F).U fun _ => j) (t.s fun _ => j) =
      gm (r ≫ F) y (M.U j ⊓ M.U j') (M.g j j') * gm r y ((M.pull F).U fun _ => j') (t.s fun _ => j') := by
  have hm : r y ∈ (M.pull F).U (fun _ => j) ⊓ (M.pull F).U (fun _ => j') := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  have e := congrArg (gm r y _) (ht (fun _ => j) (fun _ => j'))
  rw [map_mul, gm_res _ y _ hm, gm_res _ y _ hm, gm_pull_g M F r y _ _ hm.1 hm.2] at e
  exact e

theorem gm_iso {W : Scheme.{0}} {O N : LB Y} {w : LB.Iso O N} (hw : w.IsGen) (r : W ⟶ Y) (y : W)
    {j j' : N.ι} {k k' : O.ι} (h : r y ∈ N.U j ⊓ O.U k) (h' : r y ∈ N.U j' ⊓ O.U k') :
    gm r y (N.U j ⊓ O.U k) (w.s (j, k)) =
      gm r y (N.U j ⊓ N.U j') (N.g j j') * (gm r y (O.U k ⊓ O.U k') (O.g k k'))⁻¹ *
        gm r y (N.U j' ⊓ O.U k') (w.s (j', k')) := by
  have hm : r y ∈ N.U j ⊓ O.U k ⊓ (N.U j' ⊓ O.U k') := ⟨h, h'⟩
  exact (gm_res r y _ hm _).symm.trans ((congrArg (gm r y _) (hw (j, k) (j', k'))).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div O N r y (j, k) (j', k') hm) (gm_res r y _ hm _))))

theorem exists_gen_of_iso
    (hf : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ((t ≫ i) * g).left ≫ f = g.left ≫ f)
    {O N : LB Y} (hO : O.IsLB) (hN : N.IsLB) (h : LBIso O N) {χ : X} (u : LB.Gen (O.pull f)) (hu : u.IsGen)
    (hχ : ∀ k, IsWt i _ (u.s k).val χ) :
    ∃ v : LB.Gen (N.pull f), v.IsGen ∧ ∀ j, IsWt i _ (v.s j).val χ := by
  obtain ⟨w, hw⟩ := h
  have tr : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (j j' : N.ι) (k k' : O.ι), f (r z) ∈ N.U j ⊓ O.U k →
      f (r z) ∈ N.U j' ⊓ O.U k' →
      gm (r ≫ f) z (N.U j ⊓ O.U k) (w.s (j, k)) * gm r z ((O.pull f).U fun _ => k) (u.s fun _ => k) =
        gm (r ≫ f) z (N.U j ⊓ N.U j') (N.g j j') *
          (gm (r ≫ f) z (N.U j' ⊓ O.U k') (w.s (j', k')) * gm r z ((O.pull f).U fun _ => k') (u.s fun _ => k')) := by
    intro Z r z j j' k k' h h'
    rw [gm_iso hw (r ≫ f) z h h', gm_gen_pull hu r z h.2 h'.2, _root_.mul_assoc, _root_.mul_assoc,
      mul_left_comm (gm (r ≫ f) z (N.U j' ⊓ O.U k') (w.s (j', k'))), inv_mul_cancel_left]
  have glue : ∀ j : N.ι, ∃ s : Γ(G.left, (N.pull f).U fun _ => j)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (k : O.ι),
      f (r z) ∈ N.U j ⊓ O.U k → gm r z _ s =
        gm (r ≫ f) z (N.U j ⊓ O.U k) (w.s (j, k)) * gm r z ((O.pull f).U fun _ => k) (u.s fun _ => k) := by
    intro j
    have l₀ : ∀ k, f ⁻¹ᵁ (N.U j ⊓ O.U k) ≤ (N.pull f).U fun _ => j := fun k x hx => mem_pull.2 hx.1
    have l₁ : ∀ k, f ⁻¹ᵁ (N.U j ⊓ O.U k) ≤ (O.pull f).U fun _ => k := fun k x hx => mem_pull.2 hx.2
    obtain ⟨a, ha⟩ : ∃ a : ∀ k, Γ(G.left, f ⁻¹ᵁ (N.U j ⊓ O.U k))ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (k : O.ι),
        f (r z) ∈ N.U j ⊓ O.U k → gm r z _ (a k) =
          gm (r ≫ f) z (N.U j ⊓ O.U k) (w.s (j, k)) * gm r z ((O.pull f).U fun _ => k) (u.s fun _ => k) :=
      ⟨fun k => pullU f (N.U j ⊓ O.U k) (w.s (j, k)) * res (l₁ k) (u.s fun _ => k), fun Z r z k hz =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull r f z _ hz _) (gm_res r z (l₁ k) hz _))⟩
    obtain ⟨s, hs⟩ := glue_unit _ _ l₀ (fun x hx => by
        obtain ⟨k, hk⟩ := exists_chart hO (f x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, mem_pull.1 hx, hk⟩) a (fun k k' x hx => by
        rw [ha _ (𝟙 _) x k hx.1, ha _ (𝟙 _) x k' hx.2, tr _ (𝟙 _) x j j k k' hx.1 hx.2,
          gm_self hN (𝟙 _ ≫ f) x hx.1.1, _root_.one_mul])
    exact ⟨s, fun Z r z k hz => (gm_res r z (l₀ k) hz s).symm.trans
      ((congrArg (gm r z (f ⁻¹ᵁ (N.U j ⊓ O.U k))) (hs k)).trans (ha Z r z k hz))⟩
  choose s hs using glue
  refine ⟨⟨fun J => s (J PUnit.unit)⟩, fun J J' => unit_ext fun y hy => ?_, fun J => isWt_of_gm _ _ ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hO (f y)
    have h₁ := mem_pull.1 hy.1
    have h₂ := mem_pull.1 hy.2
    exact ((gm_res _ y _ hy _).trans ((hs _ _ (𝟙 _) y k ⟨h₁, hk⟩).trans
      (tr _ (𝟙 _) y _ _ k k ⟨h₁, hk⟩ ⟨h₂, hk⟩))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        (gm_pull_g N f (𝟙 _) y J J' hy.1 hy.2) ((gm_res _ y _ hy _).trans (hs _ _ (𝟙 _) y k ⟨h₂, hk⟩)))).symm
  · intro Z t g z hz
    obtain ⟨k, hk⟩ := exists_chart hO (f (g.left z))
    have h₂ : f (g.left z) ∈ N.U (J PUnit.unit) ⊓ O.U k := ⟨mem_pull.1 hz, hk⟩
    have h₁ : f (((t ≫ i) * g).left z) ∈ N.U (J PUnit.unit) ⊓ O.U k :=
      (congrArg (fun m : Z.left ⟶ Y => m z ∈ N.U (J PUnit.unit) ⊓ O.U k) (hf Z t g)).mpr h₂
    refine (hs _ _ _ z k h₁).trans (Eq.trans ?_ (congrArg (_ * ·) (hs _ _ _ z k h₂)).symm)
    rw [hf, WtBundle.gm_of_isWt (hχ fun _ => k) t g z (mem_pull.2 h₁.2) (mem_pull.2 h₂.2), gm_charUnit,
      mul_left_comm]

theorem exists_gen_neg {B : Scheme.{0}} {L : LB B} {K : Type} [Fintype K] {φ : K → (Y ⟶ B)} {ε ε' : K → ℤ}
    (hε : ∀ k, ε' k = - ε k) {χ : X} (u : LB.Gen ((LB.LinComb L φ ε).pull f)) (hu : u.IsGen)
    (hχ : ∀ k, IsWt i _ (u.s k).val (-χ)) :
    ∃ v : LB.Gen ((LB.LinComb L φ ε').pull f), v.IsGen ∧ ∀ j, IsWt i _ (v.s j).val χ := by
  refine ⟨⟨fun J => (u.s J)⁻¹⟩, fun J J' => ?_, fun J => ?_⟩
  · refine unit_ext fun y hy => ?_
    have h₁ : f y ∈ LB.wchart L φ (J PUnit.unit) := mem_pull.1 hy.1
    have h₂ : f y ∈ LB.wchart L φ (J' PUnit.unit) := mem_pull.1 hy.2
    have e : gm (𝟙 _ ≫ f) y _ ((LB.LinComb L φ ε').g (J PUnit.unit) (J' PUnit.unit)) =
        (gm (𝟙 _ ≫ f) y _ ((LB.LinComb L φ ε).g (J PUnit.unit) (J' PUnit.unit)))⁻¹ := by
      refine (gm_linComb L φ ε' (𝟙 _ ≫ f) y _ _ h₁ h₂).trans (Eq.trans ?_
        (congrArg (·⁻¹) (gm_linComb L φ ε (𝟙 _ ≫ f) y _ _ h₁ h₂)).symm)
      simp only [hε, zpow_neg, Finset.prod_inv_distrib]
    exact ((gm_res _ y _ hy _).trans ((map_inv _ _).trans ((congrArg (·⁻¹) (gm_gen_pull hu (𝟙 _) y h₁ h₂)).trans
      (mul_inv _ _)))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((gm_pull_g (LB.LinComb L φ ε') f (𝟙 _) y J J' hy.1 hy.2).trans e)
        ((gm_res _ y _ hy _).trans (map_inv _ _)))).symm
  · have := (hχ J).inv
    rwa [neg_neg] at this

theorem sym_of_cp [IsCommMonObj G] (P : CP G) : Out.Sym G P.L.L := fun _ => by
  obtain ⟨t, ht, -⟩ := exists_gen P.L.isLB (K' := Fin 2)
    (φ' := ![(G.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : G ⟶ G).left, (G.hom ⁻¹ᵁ ⊤).ι]) (ε' := ![1, -1])
    (fun U _ h => by simp [Fin.prod_univ_two]) (LB.pullGen _ _ _ P.sym (G.hom ⁻¹ᵁ ⊤).ι)
    (LB.isGen_pullGen _ _ _ _ P.sym_gen _)
  exact ⟨⊤, trivial, t, ht⟩

end GlobalTheory.WtPoint

namespace GlobalTheory

theorem exists_point_repWt : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L → ∀ χ : s.X, ∃ c : 𝟙_ _ ⟶ a.B, ∀ e, a.RepWt c χ e := by
  intro hL V _ _ _ A G _ _ s t a hK χ
  have : IsDiscreteValuationRing V := s.cdvr.1
  obtain ⟨g, hg⟩ := AbelianDim.exists_relDim V a.B a.isAb
  obtain ⟨O, hO, hΛ, hu⟩ := _root_.GlobalTheory.WtTower.exists_weight_bundle_alg hL V A G s t a (-χ)
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.PrimitiveOverValuationRing.exists_section_translate hL V
    { A := a.B, isAb := a.isAb, g := g, smoothDim := hg, L := a.M.L.L, isLB := a.M.L.isLB,
      rigid := ⟨a.M.L.rig, a.M.L.rigGen⟩, sym := WtPoint.sym_of_cp a.M, ample := a.ample, ktriv := hK } O hO hΛ
  refine ⟨c, fun e => ?_⟩
  obtain ⟨u, hu, hw⟩ := hu e
  obtain ⟨v, hv, hw'⟩ := WtPoint.exists_gen_of_iso (fun Z τ x => by
    rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, WtBundle.act_comp])
    hO (LB.isLB_linComb a.M.L.isLB _ _) hc u hu hw
  exact WtPoint.exists_gen_neg (fun k => by fin_cases k <;> rfl) v hv hw'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SixthLawsAndUnifUniq
section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem sixthLaws_and_unifUniq : Laws6 ∧ UnifUniqSt :=
  ⟨GlobalTheory.allSixLaws.2.2.2.2.2, GlobalTheory.allSixLaws.2.2.2.2.2.unifUniq⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem uTors_closed : GlobalTheory.ZH.UTorsSt :=
  _root_.GlobalTheory.ZH.uTors_of_laws _root_.GlobalTheory.allSixLaws.1 _root_.GlobalTheory.allSixLaws.2.1 _root_.GlobalTheory.allSixLaws.2.2.1 _root_.GlobalTheory.allSixLaws.2.2.2.1 _root_.GlobalTheory.allSixLaws.2.2.2.2.1

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationNonnegIffSpanMultiplicationTranslatesStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_nonneg_iff_span_multiplicationTranslates : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ (m : ℕ), Odd m → IsUnit (m : V) → 3 ≤ m → ∀ s : Fam D.toPre F (m ^ 2), NuGe D Q F v (m ^ 2) s 0 ↔ ∃ (n : ℕ) (a : Fin n → F) (x : Fin n → (TFK (R := V) F ⟶ A.A)) (t : Fin n → SecA A F (m ^ 2)) (c : Fin n → F) (r : Fin n → Fam D.toPre F (m ^ 2)), (∀ i, 0 ≤ v (a i) ∧ x i ^ (m ^ 2) = 1 ∧ ThC A ρ m th (x i) (t i) (c i) ∧ U.ExpandsF F (m ^ 2) w₀ (t i) (r i)) ∧ s = ∑ i, a i • r i := by
  first | exact @GlobalTheory.UT.nuGe_zero_iff_span_translates | exact GlobalTheory.UT.nuGe_zero_iff_span_translates | (intros; apply GlobalTheory.UT.nuGe_zero_iff_span_translates <;> assumption)
end

