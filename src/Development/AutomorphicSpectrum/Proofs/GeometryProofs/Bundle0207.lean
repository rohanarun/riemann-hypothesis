module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QQuasiCompact
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0205
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0010
public import Development.WeilBound.CoreStatements.SesquilinearFractions.GDerivLin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0204
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientOfPowerFns
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.AbQ

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open GlobalTheory.CechPic
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_desc {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] (T : TorusExtension G)
    {Y : Over (Sp k)} [GrpObj Y] (f : G ⟶ Y) [IsMonHom f] (hf : T.i ≫ f = 1) :
    ∃ f' : T.B ⟶ Y, T.q ≫ f' = f := by
  letI := T.grpB
  have := T.q_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have : EffectiveEpi T.q := GlobalTheory.CosetQuotient.effectiveEpi_of_left T.q
  refine ⟨EffectiveEpi.desc T.q f fun {Z} g₁ g₂ e => ?_, EffectiveEpi.fac _ _ _⟩
  have h : (g₁ * g₂⁻¹) ≫ T.q = toUnit Z ≫ η[T.B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]
    rfl
  have h₁ : T.isKernel.lift _ _ h ≫ T.i = g₁ * g₂⁻¹ := T.isKernel.lift_fst _ _ h
  have h₂ : g₁ = (T.isKernel.lift _ _ h ≫ T.i) * g₂ := by rw [h₁, inv_mul_cancel_right]
  rw [h₂, MonObj.mul_comp, Category.assoc, hf, MonObj.comp_one, _root_.one_mul]

theorem i_comp_eq_one {k : Type} [Field k] [IsAlgClosed k] {G : Over (Sp k)} [GrpObj G] (T : TorusExtension G)
    {B : Over (Sp k)} [GrpObj B] (hB : IsAbelianScheme B) (f : G ⟶ B) [IsMonHom f] : T.i ≫ f = 1 := by
  letI := T.addCommGroup
  have := T.free
  have := T.finite
  have := T.i_hom
  obtain ⟨b, hb⟩ := GlobalTheory.splitTorus_to_abelian_const k T.X B hB (T.i ≫ f)
  have e : (η[splitTorus (Sp k) T.X]) ≫ T.i ≫ f = η[B] := IsMonHom.one_hom _
  rw [hb] at e
  have e' : b = η[B] := by
    rw [← e, ← Category.assoc, toUnit_unique (η[splitTorus (Sp k) T.X] ≫ toUnit _) (𝟙 _), Category.id_comp]
  rw [hb, e']
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_act {k : Type} [Field k] [IsAlgClosed k] {G : Over (Sp k)} [GrpObj G] {O : Type} [CommRing O]
    (a : OAct O G) (T : TorusExtension G) :
    letI := T.grpB
    ∃ b : OAct O T.B, ∀ r, a.act r ≫ T.q = T.q ≫ b.act r := by
  letI := T.grpB
  have hB := T.isAbelian
  have := T.q_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have : EffectiveEpi T.q := GlobalTheory.CosetQuotient.effectiveEpi_of_left T.q
  have canc : ∀ {Y : Over (Sp k)} (f f' : T.B ⟶ Y), T.q ≫ f = T.q ≫ f' → f = f' := fun f f' h =>
    (cancel_epi T.q).1 h
  have hact : ∀ r, ∃ f' : T.B ⟶ T.B, T.q ≫ f' = a.act r ≫ T.q := fun r => by
    have := a.hom r
    exact exists_desc T _ (i_comp_eq_one T hB _)
  choose α hα using hact
  refine ⟨{ act := α, hom := fun r => GlobalTheory.abelianSchemeLaws_all.1.rigidity _ T.B T.B hB hB _ ?_,
            one := canc _ _ (by rw [hα, a.one, Category.id_comp, Category.comp_id]),
            mul := fun r s => canc _ _ (by
              rw [hα, a.mul, ← Category.assoc T.q, hα, Category.assoc, Category.assoc, hα]),
            add := fun r s => canc _ _ (by rw [hα, a.add, MonObj.mul_comp, MonObj.comp_mul, hα, hα]) },
    fun r => (hα r).symm⟩
  have := a.hom r
  rw [← IsMonHom.one_hom T.q, Category.assoc, hα, ← Category.assoc, IsMonHom.one_hom]

theorem adj_quot {k : Type} [Field k] [IsAlgClosed k] {H : Host E} (tK : SAB H (Sp k)) (T : TorusExtension tK.G)
    (M : LB T.B.left) (hM : M.IsLB) (hbun : LBIso tK.PP.L (M.pull T.q.left)) :
    letI := T.grpB
    ∀ (act : OAct (𝓞 E) T.B), (∀ r, tK.act.act r ≫ T.q = T.q ≫ act.act r) → ∀ a,
      LBIso (cubeLB T.B ![fst T.B T.B ≫ act.act a, snd T.B T.B] M)
        (cubeLB T.B ![fst T.B T.B, snd T.B T.B ≫ act.act (H.bar a)] M) := by
  letI := T.grpB
  have hB := T.isAbelian
  haveI := hB.comm
  have := T.q_hom
  intro act hact a
  have := act.hom a
  have := act.hom (H.bar a)
  have hL := tK.PP.isLB
  set l := cls tK.PP.L hL with hl
  set m := cls M hM with hm
  have hqm : pull T.q.left m = l := ((cls_eq_iff hL (pull_isLB hM _)).2 hbun).symm
  have lamq : ∀ {Z : Over (Sp k)} (u v : Z ⟶ tK.G), lam m (u ≫ T.q) (v ≫ T.q) = lam l u v := fun u v => by
    rw [← lam_pull, hqm]
  have adjG : ∀ {Z : Over (Sp k)} (u v : Z ⟶ tK.G),
      lam l (u ≫ tK.act.act a) v = lam l u (v ≫ tK.act.act (H.bar a)) := by
    intro Z u v
    have h := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (tK.adj a)
    have h' := congrArg (pull (lift u v).left)
      ((cls_cube_two hL _ _ _).symm.trans (h.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
  let D : ∀ {Z : Over (Sp k)}, (Z ⟶ T.B) → (Z ⟶ T.B) → Pic Z.left := fun x y =>
    lam m (x ≫ act.act a) y - lam m x (y ≫ act.act (H.bar a))
  have Dpull : ∀ {Z Z' : Over (Sp k)} (h : Z' ⟶ Z) (x y : Z ⟶ T.B), pull h.left (D x y) = D (h ≫ x) (h ≫ y) := by
    intro Z Z' h x y
    simp only [D, map_sub, pull_lam, Category.assoc]
  have Dq : ∀ {Z : Over (Sp k)} (u v : Z ⟶ tK.G), D (u ≫ T.q) (v ≫ T.q) = 0 := by
    intro Z u v
    have e₁ : (u ≫ T.q) ≫ act.act a = (u ≫ tK.act.act a) ≫ T.q := by
      rw [Category.assoc, Category.assoc, hact]
    have e₂ : (v ≫ T.q) ≫ act.act (H.bar a) = (v ≫ tK.act.act (H.bar a)) ≫ T.q := by
      rw [Category.assoc, Category.assoc, hact]
    simp only [D]
    rw [e₁, e₂, lamq, lamq, adjG, sub_self]
  have D1l : ∀ {Z : Over (Sp k)} (y : Z ⟶ T.B), D 1 y = 0 := by
    intro Z y
    simp only [D]
    rw [MonObj.one_comp, lam_one_left, lam_one_left, sub_self]
  have D1r : ∀ {Z : Over (Sp k)} (x : Z ⟶ T.B), D x 1 = 0 := by
    intro Z x
    simp only [D]
    rw [MonObj.one_comp, lam_one_right, lam_one_right, sub_self]
  have hGs := tK.semi
  have one_q : ∀ {Z : Over (Sp k)}, (1 : Z ⟶ tK.G) ≫ T.q = 1 := fun {Z} => MonObj.one_comp _
  have c₁ : D (fst T.B tK.G) (snd T.B tK.G ≫ T.q) = 0 := by
    refine _root_.GlobalTheory.CompanionTheory.TorusPic.pic_inj k tK.G hGs T tK.G hGs.smooth hGs.geomConnected η[tK.G] _ ?_ ?_
    · have e₁ : lift (fst tK.G tK.G ≫ T.q) (snd tK.G tK.G) ≫ fst T.B tK.G = fst tK.G tK.G ≫ T.q := lift_fst _ _
      have e₂ : lift (fst tK.G tK.G ≫ T.q) (snd tK.G tK.G) ≫ snd T.B tK.G ≫ T.q = snd tK.G tK.G ≫ T.q := by
        rw [← Category.assoc, lift_snd]
      rw [Dpull, e₁, e₂]
      exact Dq _ _
    · have e₁ : lift (𝟙 T.B) (toUnit T.B ≫ η[tK.G]) ≫ fst T.B tK.G = 𝟙 T.B := lift_fst _ _
      have e₂ : lift (𝟙 T.B) (toUnit T.B ≫ η[tK.G]) ≫ snd T.B tK.G ≫ T.q = 1 := by
        rw [← Category.assoc, lift_snd]
        exact one_q
      rw [Dpull, e₁, e₂]
      exact D1r _
  have Dr : ∀ {Z : Over (Sp k)} (x : Z ⟶ T.B) (v : Z ⟶ tK.G), D x (v ≫ T.q) = 0 := by
    intro Z x v
    have h := congrArg (pull (lift x v).left) c₁
    have e₂ : lift x v ≫ snd T.B tK.G ≫ T.q = v ≫ T.q := by rw [← Category.assoc, lift_snd]
    rw [Dpull, map_zero, lift_fst, e₂] at h
    exact h
  have c₂ : D (snd T.B T.B) (fst T.B T.B) = 0 := by
    refine _root_.GlobalTheory.CompanionTheory.TorusPic.pic_inj k tK.G hGs T T.B hB.smooth hB.geomConnected η[T.B] _ ?_ ?_
    · have e₁ : lift (fst tK.G T.B ≫ T.q) (snd tK.G T.B) ≫ fst T.B T.B = fst tK.G T.B ≫ T.q := lift_fst _ _
      have e₂ : lift (fst tK.G T.B ≫ T.q) (snd tK.G T.B) ≫ snd T.B T.B = snd tK.G T.B := lift_snd _ _
      rw [Dpull, e₁, e₂]
      exact Dr _ _
    · have e₁ : lift (𝟙 T.B) (toUnit T.B ≫ η[T.B]) ≫ fst T.B T.B = 𝟙 T.B := lift_fst _ _
      have e₂ : lift (𝟙 T.B) (toUnit T.B ≫ η[T.B]) ≫ snd T.B T.B = 1 := lift_snd _ _
      rw [Dpull, e₁, e₂]
      exact D1l _
  have c₃ : D (fst T.B T.B) (snd T.B T.B) = 0 := by
    have h := congrArg (pull (lift (snd T.B T.B) (fst T.B T.B)).left) c₂
    rw [Dpull, map_zero, lift_fst, lift_snd] at h
    exact h
  have h₁ : (cubeLB T.B ![fst T.B T.B ≫ act.act a, snd T.B T.B] M).IsLB := LB.isLB_linComb hM _ _
  have h₂ : (cubeLB T.B ![fst T.B T.B, snd T.B T.B ≫ act.act (H.bar a)] M).IsLB := LB.isLB_linComb hM _ _
  refine (cls_eq_iff h₁ h₂).1 ?_
  rw [cls_cube_two hM, cls_cube_two hM]
  exact sub_eq_zero.1 c₃

theorem exists_abQuot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X),
    PowFns t → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X),
    GeomPF t x → Nonempty (AbQuot t x) := by
  intro E _ _ _ H X t _ k _ _ p _ _ x ⟨T, M, hM, hK, hbun⟩
  obtain ⟨PP', cub', sym', adj', prim', m, hm⟩ := sabPull Out.CubePf.cubePull x t
  let tK : SAB H (Sp k) := ⟨_, IsSemiAbelian.pullback x t.G t.semi, OAct.pullback x t.G t.act, PP', cub', sym', adj', prim'⟩
  obtain ⟨w, hw, -, -⟩ := m.lin
  have hiso : LBIso PP'.L (t.PP.L.pull (pullback.fst t.G.hom x)) := by
    rw [← hm]
    exact ⟨w, hw⟩
  letI := T.grpB
  have hB := T.isAbelian
  haveI := hB.comm
  have hq := T.q_hom
  have hP₀ := pull_isLB t.PP.isLB (pullback.fst t.G.hom x)
  have hqL := pull_isLB hM T.q.left
  have hbun' : LBIso tK.PP.L (M.pull T.q.left) := LBIso.trans PP'.isLB hP₀ hqL hiso hbun
  obtain ⟨act, hact⟩ := exists_act tK.act T
  have hadj := adj_quot tK T M hM hbun' act hact
  obtain ⟨PP, cub, hsym, hPP, hlam, hprim, hadjP⟩ := GlobalTheory.PrimNorm.exists_primitive_normalisation GlobalTheory.globalFns_holds
    E H _ T.B act M hB hM (GlobalTheory.exists_gen_theta_of_isAbelianScheme k T.B hB M hM) hadj
  have hP' := PP.isLB
  have hL : tK.PP.L.IsLB := PP'.isLB
  have hqm : pull T.q.left (cls M hM) = cls tK.PP.L hL := ((cls_eq_iff hL hqL).2 hbun').symm
  have hpull : pull T.q.left (cls PP.L hP') = cls tK.PP.L hL := by
    have h := (cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 tK.prim
    have h' := (cls_eq_iff hP' (LB.isLB_linComb hM _ _)).2 hPP
    have e : cls tK.PP.L hL = lam (cls tK.PP.L hL) (𝟙 _) (tK.act.act H.w0) := h.trans (cls_cube_two hL _ _ _)
    have e' : cls PP.L hP' = lam (cls M hM) (𝟙 _) (act.act H.w0) := h'.trans (cls_cube_two hM _ _ _)
    rw [e', pull_lam, ← hact, Category.comp_id, ← Category.id_comp T.q, ← Category.assoc, Category.comp_id,
      ← lam_pull, hqm, ← e]
  have hfin : LBIso tK.PP.L (PP.L.pull T.q.left) := by
    rw [← cls_eq_iff hL (pull_isLB hP' _), cls_pull hP', hpull]
  have hK' : Out.KTriv T.B PP.L := GlobalTheory.CM.kTriv_of_lamEq _ T.B M PP.L hM hP'
    (by simp only [GlobalTheory.CM.LamEq, Category.comp_id]; exact hlam) hK
  exact ⟨{ tB := ⟨T.B, GlobalTheory.isSemiAbelian_of_isAbelianScheme T.B hB, act, PP, cub, hsym, hadjP, hprim⟩
           proper := hB.proper
           ktriv := hK'
           Ch := T.X
           acg := T.addCommGroup
           free := T.free
           fin := T.finite
           q := T.q
           q_hom := hq
           q_flat := T.q_flat
           q_surjective := T.q_surjective
           q_quasiCompact := T.q_quasiCompact
           i := T.i
           i_hom := T.i_hom
           isKernel := T.isKernel
           act_q := hact
           bun := LBIso.trans hP₀ hL (pull_isLB hP' _) (LBIso.symm hiso) hfin }⟩

end GlobalTheory.CompanionTheory.Ar.AbQ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHolomorphic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isOpen_punct (n a : ℕ) (ρ : ℝ) : IsOpen (punct n a ρ) := by
  have h : punct n a ρ = Metric.ball 0 ρ ∩ ⋂ i : Fin n, {z : Fin n → ℂ | (i : ℕ) < a → z i ≠ 0} := by
    ext z
    simp only [punct, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [h]
  refine Metric.isOpen_ball.inter (isOpen_iInter_of_finite fun i => ?_)
  by_cases hi : (i : ℕ) < a
  · simp only [hi, true_implies]
    exact isOpen_ne_fun (continuous_apply i) continuous_const
  · simp [hi]

theorem isHolTo_of_comp_openImmersion {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {X Y : Scheme.{0}}
    (j : X ⟶ Y) [IsOpenImmersion j] {B : Set W} {y : W → (Sp ℂ ⟶ X)}
    (h : IsHolTo B fun b => y b ≫ j) : IsHolTo B y := by
  intro U f
  have hpre : ∀ x : Sp ℂ ⟶ X, (x ≫ j) ⁻¹ᵁ (j ''ᵁ U) = x ⁻¹ᵁ U := by
    intro x
    ext p
    simp
  have key : ∀ (x : Sp ℂ ⟶ X) (h1 : ⊤ ≤ (x ≫ j) ⁻¹ᵁ (j ''ᵁ U)) (h2 : ⊤ ≤ x ⁻¹ᵁ U),
      valAt (x ≫ j) (j ''ᵁ U) h1 ((j.appIso U).inv f) = valAt x U h2 f := by
    intro x h1 h2
    have e : (j.appIso U).inv ≫ (x ≫ j).appLE (j ''ᵁ U) ⊤ h1 = x.appLE U ⊤ h2 := by
      rw [← Scheme.Hom.appLE_comp_appLE x j (j ''ᵁ U) U ⊤ (j.preimage_image_eq U).ge h2]
      rw [← Category.assoc, Scheme.Hom.appIso_inv_appLE]
      simp
    unfold valAt
    rw [← e]
    rfl
  have hval : ∀ b, valAt' (y b ≫ j) (j ''ᵁ U) ((j.appIso U).inv f) = valAt' (y b) U f := by
    intro b
    unfold valAt'
    by_cases hb : ⊤ ≤ y b ⁻¹ᵁ U
    · have hb' : ⊤ ≤ (y b ≫ j) ⁻¹ᵁ (j ''ᵁ U) := by rw [hpre]; exact hb
      rw [dite_eq_left hb, dite_eq_left hb']
      exact key _ hb' hb
    · have hb' : ¬ ⊤ ≤ (y b ≫ j) ⁻¹ᵁ (j ''ᵁ U) := by rw [hpre]; exact hb
      rw [dite_eq_right hb, dite_eq_right hb']
  obtain ⟨ho, hd⟩ := h (j ''ᵁ U) ((j.appIso U).inv f)
  simp only [hpre] at ho hd
  exact ⟨ho, by simpa only [hval] using hd⟩

theorem isHolTo_pt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : BdryChart Xo σ n a), IsHolTo (punct n a 1) C.pt := by
  intro E _ _ _ H D l Xo σ n a C
  haveI := C.j_open
  apply isHolTo_of_comp_openImmersion C.j
  have hB : IsOpen (punct n a 1) := isOpen_punct n a 1
  have hsub : punct n a 1 ⊆ Metric.ball 0 1 := fun z hz => hz.1
  have h0 : IsHolTo (punct n a 1) fun z => ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (C.ψ z) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_spMap hB fun r => (C.hol.2 r).mono hsub
  exact GlobalTheory.FiniteOrderConst.isHolTo_of_eqOn h0 fun z hz => (C.pt_eq z hz).1

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackEigenPeriod
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.CoordPart

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix _root_.GlobalTheory GlobalTheory.CM _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

section Comb

variable {S : Scheme.{0}} {K C : Type} [CommRing K] [CommRing C]

theorem dualMap_comp_algebraMap' (φ : K →+* C) :
    (GlobalTheory.CompanionTheory.Ar.dualMap φ).comp (algebraMap K (DualNumber K)) = (algebraMap C (DualNumber C)).comp φ := by
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

def bcHom (φ : K →+* C) (x : Sp K ⟶ S) : epsAt (spMap φ ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ)) (by
    show spMap _ ≫ spMap _ ≫ x = spMap _ ≫ spMap _ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_algebraMap'])

theorem dual_epsMul (φ : K →+* C) (a : K) :
    spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ spMap (GlobalTheory.CompanionTheory.Ar.epsMul a) =
      spMap (GlobalTheory.CompanionTheory.Ar.epsMul (φ a)) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) := by
  rw [spMap_comp_spMap, spMap_comp_spMap]
  congr 1
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, mul_comm]

theorem comp_list_prod {G : Over S} [GrpObj G] {T T' : Over S} (f : T' ⟶ T) (l : List (T ⟶ G)) :
    f ≫ l.prod = (l.map (f ≫ ·)).prod := by
  induction l with
  | nil => simp [MonObj.comp_one]
  | cons a l ih => simp [MonObj.comp_mul, ih]

theorem comb_eq_pt {G : Over S} [GrpObj G] (φ : K →+* C) {x : Sp K ⟶ S} {x' : Sp C ⟶ S} (hx : spMap φ ≫ x = x')
    {U : Type} [AddCommGroup U] [Module C U] (M : LieModel G x' U) {n : ℕ} (c : Fin n → K)
    (u : Fin n → (epsAt x ⟶ G)) (w : epsAt x ⟶ G) (hc : IsComb c u w) (e : Fin n → U)
    (he : ∀ k, spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ (u k).left = (M.pt (e k)).left) :
    spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ w.left = (M.pt (∑ k, φ (c k) • e k)).left := by
  subst hx
  obtain ⟨u', hu', rfl⟩ := hc
  have key : IsComb (fun k => φ (c k)) (fun k => M.pt (e k)) (bcHom φ x ≫ (List.ofFn u').prod) := by
    refine ⟨fun k => bcHom φ x ≫ u' k, fun k => ?_, ?_⟩
    · show spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ (u' k).left = _
      rw [hu' k, ← Category.assoc, dual_epsMul, Category.assoc, he k]
    · rw [comp_list_prod, List.map_ofFn]
      rfl
  have := ((_root_.GlobalTheory.CompanionTheory.Ar.Fl.Bridge.comb_eig_frame S C G _ U M).1 n _ _ _).1 key
  exact congrArg (fun q => q.left) this

end Comb

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sum_eq_tyPart {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty P) (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ))
    (hρ : ∀ a w, ρ a w = fun k => ty k (a : E) * w k) (τ : E →+* ℂ)
    (hpr : ∀ w, HT.eigProj ρ τ w = tyPart ty τ w) (z : ℂ) {n : ℕ}
    (e : Fin n ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (a : D.La) :
    ∑ k, τ (HT.dualInt E (e k)) • (z • P (RingOfIntegers.basis E (e k) • a)) = z • tyPart ty τ (P a) := by
  have h1 : ∀ s : 𝓞 E, P (s • a) = ρ s (P a) := fun s => by
    rw [hρ]; funext j; exact hP.1 s a j
  rw [← hpr, HT.eigProj, LinearMap.sum_apply, Finset.smul_sum,
    ← Equiv.sum_comp e (fun q => z • (τ (HT.dualInt E q) • ρ (RingOfIntegers.basis E q)) (P a))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h1, smul_comm]
  rfl

theorem isDerivAt0_of_isCMVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (a : PureType.lat hP (sgnRt H b)) (v : epsAt (under X.y) ⟶ Xo.univ.t.G), X.IsCMVec b τ a v → IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • tyPart ty τ (P a)) (spMap (dualMap (algebraMap X.K ℂ)) ≫ v.left) := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X b τ a v hv
  obtain ⟨M, ρ, -, hρ, hder, hpr⟩ := _root_.PositivityTheory.Xgf.lie_model_with_cm_action E H D l Xo c g ty FU i P hP
  obtain ⟨n, e, u, hu, hc⟩ := hv
  have hk : ∀ k, spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap X.K ℂ)) ≫ (u k).left =
      (M.pt ((Z b).z • P (RingOfIntegers.basis E (e k) • (a : (FU.Di i).La)))).left := fun k =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique
      ((_root_.PositivityTheory.Xgf.cm_image_unique_lattice E H D l Xo c g ty FU i Z P hP X b _).2 (u k) (hu k)).2 (hder _)
  have h := comb_eq_pt (algebraMap X.K ℂ) X.pt M _ u v hc _ hk
  rw [h]
  have hs : ∑ k, (algebraMap X.K ℂ) (X.β (tauE c τ (HT.dualInt E (e k)))) •
      ((Z b).z • P (RingOfIntegers.basis E (e k) • (a : (FU.Di i).La))) = (Z b).z • tyPart ty τ (P a) :=
    sum_eq_tyPart hP ρ hρ τ (hpr τ) _ e a
  rw [hs]
  exact hder _

end Main

end GlobalTheory.CompanionTheory.Ar.Fl.CoordPart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackProductFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ggeo.IntBasis

theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  simp [spMap, ← Spec.map_comp]

theorem dualMap_comp_alt {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    (dualMap b).comp (dualMap a) = dualMap (b.comp a) := by
  apply RingHom.ext
  intro x
  apply TrivSqZeroExt.ext <;> simp only [RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, add_zero, zero_add]

end GlobalTheory.CompanionTheory.Ggeo.IntBasis

open GlobalTheory.CompanionTheory.Ggeo.IntBasis in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cm_pack_product_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (N : ℕ) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))) (V : Subring X.K) [IsLocalRing V], 0 < N → (∀ y : (FU.Di i).La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : (FU.Di i).La))) → (∀ s : 𝓞 X.K, (s : X.K) ∈ V) → IsUnit (N : V) → ∃ (T : SAB H (Sp V)) (m'' : SABMap X.t T (spMap (algebraMap V X.K))) (uV : Fin g → (epsAt (𝟙 (Sp V)) ⟶ T.G)), (∀ k, IsTanAt T.G _ (uV k)) ∧ (∀ w, IsTanAt T.G _ w → ∃! cc : Fin g → V, IsComb cc uV w) ∧ ∀ k u, X.IsImage (b k) (a k) u → ∃ s : Sp (DualNumber X.K) ⟶ X.t.G.left, s ≫ X.m.φ = u.left ∧ s ≫ m''.φ = spMap (dualMap (algebraMap V X.K)) ≫ (uV k).left := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X N b a V _ hN hspan hV hNu
  classical
  let f : 𝓞 X.K →+* V := (algebraMap (𝓞 X.K) X.K).codRestrict V hV
  have hf : (algebraMap V X.K).comp f = algebraMap (𝓞 X.K) X.K := by ext; rfl
  obtain ⟨T', m0, hg⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap f) X.B
  have hψ : ∀ k, IsMonHom (X.ψ (b k) (a k)) := fun k => ((X.fam (b k)).1 (a k)).isMonHom
  obtain ⟨hon, hker⟩ := _root_.PositivityTheory.Xgf.cm_pack_torsion_points E H D l Xo c g ty FU i Z P hP X N b a hN hspan
  obtain ⟨χ, hχ, hψχ, hoff⟩ := _root_.GlobalTheory.CompanionTheory.Relay.isogeny_product_decomposition X.K (algebraMap X.K ℂ) g N (fun k => (X.C (b k)).P) X.B.pol
    (fun k => X.ψ (b k) (a k)) hψ hN hon hker
  obtain ⟨uV, huV, htan, hbasis⟩ := GlobalTheory.CompanionTheory.Relay.isogeny_decomposition_product (𝓞 X.K) V f g N (fun k => (X.C (b k)).P) (fun k => (X.C (b k)).v)
    X.B.pol (fun k => X.ψ (b k) (a k)) χ T'.t.G m0.φ X.dim (fun k => (X.C (b k)).basis) hψ hχ hψχ hoff hNu m0.cart
  have hy : spMap (algebraMap V X.K) ≫ spMap f = spMap (algebraMap (𝓞 X.K) X.K) := by rw [spectrumMap_comp, hf]
  obtain ⟨m'', hm''⟩ := (GlobalTheory.CM.Factor.ellMap_cancel_and_sabMap_cancel E H (𝓞 X.K) V X.K f (algebraMap V X.K)).2
    (Sp (𝓞 X.K)) (spMap f) (spMap (algebraMap (𝓞 X.K) X.K)) X.B.t T'.t X.t m0 X.m' hy
  refine ⟨T'.t, m'', uV, htan, hbasis, fun k u hu => ?_⟩
  obtain ⟨r, hr1, hr2⟩ := hu
  refine ⟨r, hr1, ?_⟩
  apply m0.cart.1.hom_ext
  · rw [Category.assoc, hm'', hr2, Category.assoc, huV k]
    simp only [← Category.assoc]
    congr 2
    rw [spectrumMap_comp, dualMap_comp_alt, hf]
  · have w1 := m''.cart.1.w
    have w2 := X.m'.cart.1.w
    have hmono : Mono (spMap (algebraMap (𝓞 X.K) X.K)) := by
      have : Epi (CommRingCat.ofHom (algebraMap (𝓞 X.K) X.K)) := IsLocalization.epi (nonZeroDivisors (𝓞 X.K)) X.K
      exact (inferInstance : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap (𝓞 X.K) X.K)).op))
    have hbase : r ≫ X.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) := by
      apply hmono.right_cancellation
      rw [Category.assoc, ← w2, ← Category.assoc, hr2]
      simp only [Category.assoc]
      rw [Over.w (X.ψ (b k) (a k)), Over.w ((X.C (b k)).v)]
      simp only [Over.mk_hom, spectrumMap_comp]
      congr 1
      ext x <;> simp only [RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, add_zero, zero_add]
    rw [Category.assoc, w1, ← Category.assoc, hbase, Category.assoc, Over.w (uV k)]
    simp only [Over.mk_hom, Category.comp_id]
    show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [spectrumMap_comp, spectrumMap_comp]
    congr 1
    ext x <;> simp only [RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, add_zero, zero_add]
end

