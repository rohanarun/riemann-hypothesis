module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0183
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.VVAlgNonneg

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelAndHeckeOfZeroSignature
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.LevelZero

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.Models GlobalTheory.Models.RankZero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem zeta_mul_pow {a c : ℕ} (ha : 0 < a) (hc : 0 < c) : zeta (a * c) ^ c = zeta a := by
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  rw [zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem KA_le {l l₂ : Level H} (h : l.A ∣ l₂.A) : KA l ≤ KA l₂ := by
  refine IntermediateField.adjoin_le_iff.2 ?_
  rintro x (rfl | rfl)
  · exact IntermediateField.subset_adjoin _ _ (by simp)
  · obtain ⟨c, hc⟩ := h
    have hc0 : 0 < c := Nat.pos_of_ne_zero fun h0 => l₂.A_pos.ne' (by rw [hc, h0, mul_zero])
    rw [← zeta_mul_pow l.A_pos hc0, ← hc]
    exact pow_mem (IntermediateField.subset_adjoin _ _ (by simp)) _

def simOne (hD : D.p + D.q = 0) : Sim D :=
  have := subsingleton_La hD
  { f := fun _ => LinearMap.id
    ν := fun _ => 1
    tower := fun _ _ _ _ _ => ⟨0, Subsingleton.elim _ _⟩
    inv := fun _ _ => ⟨LinearMap.id, fun _ => ⟨⟨0, Subsingleton.elim _ _⟩, ⟨0, Subsingleton.elim _ _⟩⟩⟩
    mult := fun _ _ a b => by
      rw [Subsingleton.elim b 0]
      simp }

theorem simOne_inGam (hD : D.p + D.q = 0) (l l₂ : Level H) : (simOne hD).InGam l l₂ := by
  have := subsingleton_La hD
  refine ⟨by simp [simOne], fun a => ?_, fun a => ⟨0, Subsingleton.elim _ _⟩⟩
  rw [Subsingleton.elim ((simOne hD).f l.M a - a) 0]
  exact zero_mem _

theorem trivAt (hD : D.p + D.q = 0) (g : Sim D) (l₂ : Level H) : g.TrivAt l₂ := by
  have := subsingleton_La hD
  refine ⟨fun a => ?_, fun a => ⟨0, Subsingleton.elim _ _⟩⟩
  rw [Subsingleton.elim (g.f l₂.M a - a) 0]
  exact zero_mem _

theorem isIso_spMap_inclusion {F F' : IntermediateField ℚ ℂ} (h : F = F') :
    IsIso (spMap (IntermediateField.inclusion h.le).toRingHom) := by
  subst h
  have : (IntermediateField.inclusion (le_refl F)).toRingHom = RingHom.id F := RingHom.ext fun _ => rfl
  rw [this]
  have e : spMap (RingHom.id F) = 𝟙 _ := Spec.map_id _
  rw [e]
  infer_instance

def jKA {l l₂ : Level H} (h : l.A ∣ l₂.A) : KA l →+* KA l₂ := (IntermediateField.inclusion (KA_le h)).toRingHom

theorem coe_jKA {l l₂ : Level H} (h : l.A ∣ l₂.A) (x : KA l) : ((jKA h x : KA l₂) : ℂ) = ((x : KA l) : ℂ) :=
  IntermediateField.coe_inclusion (KA_le h) x

theorem spMap_square {l l₂ : Level H} (h : l.A ∣ l₂.A) (c : Coeff l) (c₂ : Coeff l₂) (hc : c.F = c₂.F) :
    spMap (IntermediateField.inclusion c₂.le).toRingHom ≫ spMap (jKA h) =
      spMap (IntermediateField.inclusion hc.le).toRingHom ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
  rw [RankZero.spMap_comp, RankZero.spMap_comp]
  exact congrArg spMap (RingHom.ext fun x => Subtype.ext rfl)

theorem exists_isIso_rF {l l₂ : Level H} (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (hs : IsIso Xo.s) (hs₂ : IsIso Xo₂.s)
    (h : l.A ∣ l₂.A) (r : Xo₂.X ⟶ Xo.X) (hr : r ≫ Xo.s = Xo₂.s ≫ spMap (jKA h)) (c : Coeff l) (c₂ : Coeff l₂)
    (hc : c.F = c₂.F) : ∃ rF : Xo₂.XF c₂ ⟶ Xo.XF c,
      rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r ∧
      rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom ∧ IsIso rF := by
  have hw : (pullback.fst Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫ r) ≫ Xo.s =
      (pullback.snd Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫
        spMap (IntermediateField.inclusion hc.le).toRingHom) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [Category.assoc, hr, ← Category.assoc, pullback.condition, Category.assoc, spMap_square h c c₂ hc, Category.assoc]
  have h₂ := pullback.lift_snd _ _ hw
  have := isIso_spMap_inclusion hc
  exact ⟨pullback.lift _ _ hw, pullback.lift_fst _ _ hw, h₂, IsIso.of_isIso_fac_right h₂⟩

theorem lev_rank_zero (hD : D.p + D.q = 0) : ToroidalLevelCompatibility (H := H) (D := D) := by
  intro l l₂ Xo Xo₂ hd
  obtain ⟨hs, hG⟩ := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo
  obtain ⟨hs₂, hG₂⟩ := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo₂
  obtain ⟨r, hr⟩ : ∃ r : Xo₂.X ⟶ Xo.X, r ≫ Xo.s = Xo₂.s ≫ spMap (jKA hd.2.2) :=
    ⟨Xo₂.s ≫ spMap (jKA hd.2.2) ≫ inv Xo.s, by simp⟩
  obtain ⟨m⟩ := nonempty_sabMap hG₂ hG r
  obtain ⟨ν⟩ := nonempty_sabMap hG₂ hG₂ (Iso.refl Xo₂.X).hom
  have hlev : ∀ g : Sim D, Xo₂.LevAut g (Iso.refl _) := fun g =>
    ⟨Category.id_comp _, ν, fun a => sec_comm hG₂ ν.cart.1.w _ _, fun a => sec_comm hG₂ ν.cart.1.w _ _⟩
  refine ⟨r, jKA hd.2.2, m, coe_jKA _, hr, fun a => sec_comm hG m.cart.1.w _ _, fun a => sec_comm hG m.cart.1.w _ _,
    fun g _ => ⟨Iso.refl _, hlev g, Category.id_comp _⟩, fun c c₂ hc => ?_⟩
  obtain ⟨rF, h₁, h₂, hF⟩ := exists_isIso_rF Xo Xo₂ hs hs₂ hd.2.2 r hr c c₂ hc
  refine ⟨rF, h₁, h₂, inferInstance, inferInstance, inferInstance, fun k _ _ y y' h => ?_⟩
  obtain rfl : y = y' := (cancel_mono rF).1 h
  exact ⟨⟨simOne hD, Iso.refl _, simOne_inGam hD l l₂, hlev _, Category.id_comp _,
    by simp only [Iso.refl_hom, Category.comp_id]⟩, fun g _ _ _ _ => trivAt hD g l₂⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), D.p + D.q = 0 → ToroidalLevelCompatibility (H := H) (D := D) ∧ ToroidalHeckeCompatibility (H := H) (D := D) :=
  fun _ _ _ _ _ _ hD => ⟨lev_rank_zero hD, GoodModel.hecke_rank_zero hD⟩

end GlobalTheory.CompanionTheory.Ar.Top.LevelZero

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompleteDvrBound
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

private theorem exists_isDiffOf_of_isMonHom {S : AlgebraicGeometry.Scheme} {R : Type} [CommRing R] {G : CategoryTheory.Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) (f : G ⟶ G) (hf : IsMonHom f) :
    ∃ A : E →ₗ[R] E, M.IsDiffOf f A := by
  have htan : ∀ e : E, IsTanAt G x (M.pt e ≫ f) := by
    intro e
    have h := M.tan e
    unfold IsTanAt at h ⊢
    rw [CategoryTheory.Over.comp_left, ← Category.assoc, h, ← CategoryTheory.Over.comp_left, MonObj.one_comp]
  choose g hg using fun e => M.onto _ (htan e)
  refine ⟨{ toFun := g, map_add' := ?_, map_smul' := ?_ }, fun e => hg e⟩
  · intro e e'
    apply M.inj
    rw [hg, M.add, M.add, hg, hg, MonObj.mul_comp]
  · intro c e
    simp only [RingHom.id_apply]
    apply M.inj
    apply CategoryTheory.Over.OverMorphism.ext
    rw [hg, CategoryTheory.Over.comp_left, M.smul, M.smul, hg, CategoryTheory.Over.comp_left, Category.assoc]

private theorem isDiffOf_unique {S : AlgebraicGeometry.Scheme} {R : Type} [CommRing R] {G : CategoryTheory.Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) {f : G ⟶ G} {A B : E →ₗ[R] E}
    (hA : M.IsDiffOf f A) (hB : M.IsDiffOf f B) : A = B := by
  ext e
  exact M.inj ((hA e).trans (hB e).symm)

theorem exists_lieModel_act_gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (T : CDVR) (zV : AlgebraicGeometry.Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), ∃ (EC : Type) (_ : AddCommGroup EC) (_ : Module T.Fr EC) (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or T zV
  obtain ⟨EC, i1, i2, ⟨MC⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ Or.𝔐.t.G T.Fr (FinRd.Roots.gen T zV)
  choose D hD using fun o : 𝓞 E => exists_isDiffOf_of_isMonHom MC (Or.𝔐.t.act.act o) (Or.𝔐.t.act.hom o)
  have hD' : ∀ (o : 𝓞 E) (e : EC), MC.pt (D o e) = MC.pt e ≫ Or.𝔐.t.act.act o := fun o e => hD o e
  refine ⟨EC, i1, i2, MC, RingHom.mk' ⟨⟨D, ?_⟩, ?_⟩ ?_, fun o => hD o⟩
  · show D 1 = 1
    apply isDiffOf_unique MC (hD 1)
    intro e
    rw [Or.𝔐.t.act.one, Module.End.one_apply, Category.comp_id]
  · intro o o'
    show D (o * o') = D o * D o'
    apply isDiffOf_unique MC (hD (o * o'))
    intro e
    rw [Module.End.mul_apply, hD', hD', mul_comm, Or.𝔐.t.act.mul, Category.assoc]
  · intro o o'
    show D (o + o') = D o + D o'
    apply isDiffOf_unique MC (hD (o + o'))
    intro e
    rw [LinearMap.add_apply, MC.add, hD', hD', Or.𝔐.t.act.add, MonObj.comp_mul]

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameArchimedean
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem sigma_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ s : CMType H ⊕ CMType H, ∃ σ : 𝓞 E →+* T.V, (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) ∧ ∀ a, algebraMap T.V T.Fr (σ a) = io (labelEmb c s a) := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hev hG la T io e y evT zT t hI zV hR s
  have hgen := Or.𝔐.tie.gen
  have hsp : GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ ⤳ centre zV := Or.𝔐.all _
  obtain ⟨φ, hφ, -⟩ := ValHom.exists_valAt_hom _ _ Or.𝔐.ξ T.V zV hsp hgen
  have hm : ∀ a : 𝓞 E, Or.𝔐.emb s a ∈ regAt Or.𝔐.ξ ⟨centre zV, hsp⟩ := fun a =>
    HodgeBasic.mem_regAt_of_isIntegral hgen Or.𝔐.all Or.𝔐.normal _
      ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (Or.𝔐.emb s).toIntAlgHom)
  let σ : 𝓞 E →+* T.V := φ.comp ((Or.𝔐.emb s).codRestrict _ hm)
  have hv : ∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a) := fun a => (hφ _ _).2 ⟨hm a, rfl⟩
  refine ⟨σ, hv, fun a => ?_⟩
  have hA : Or.𝔐.cst (labelEmb c s a) ∈ A := hG.1 _
  have h1 := LieTangent.valAt_base hgen (algebraMap T.V T.Fr) (hv a)
  have h2 : GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ (gen T zV) (Or.𝔐.emb s a) (evT ⟨_, hA⟩) := hR ⟨_, hA⟩
  have h5 : evT ⟨_, hA⟩ = io (labelEmb c s a) := hI.2.2.2.2.1 _ hA
  exact (LieTangent.valAt_unique hgen h1 h2).trans h5

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameLocalBound
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FrameValue

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory.Limits MonObj

section Grp

variable {S S' T T' : Scheme.{0}}

theorem one_left_pull {G : CategoryTheory.Over S} [GrpObj G] (a : T' ⟶ T) (x : T ⟶ S) (x' : T' ⟶ S) (h : a ≫ x = x') :
    a ≫ (1 : CategoryTheory.Over.mk x ⟶ G).left = (1 : CategoryTheory.Over.mk x' ⟶ G).left := by
  subst h
  exact congrArg (fun q => q.left) (comp_one (M := G) (CategoryTheory.Over.homMk a rfl : CategoryTheory.Over.mk (a ≫ x) ⟶ CategoryTheory.Over.mk x))

theorem one_left_grp {G' : CategoryTheory.Over S'} [GrpObj G'] {G : CategoryTheory.Over S} [GrpObj G] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (x' : T ⟶ S') (x : T ⟶ S) (e : x' ≫ f = x) :
    (1 : CategoryTheory.Over.mk x' ⟶ G').left ≫ φ = (1 : CategoryTheory.Over.mk x ⟶ G).left := by
  subst e
  have hw : ((1 : CategoryTheory.Over.mk x' ⟶ G').left ≫ φ) ≫ G.hom = (CategoryTheory.Over.mk (x' ≫ f)).hom := by
    have h1 := CategoryTheory.Over.w (1 : CategoryTheory.Over.mk x' ⟶ G')
    rw [Category.assoc, h.1.w, ← Category.assoc, h1]
    rfl
  let x₀ : CategoryTheory.Over.mk (x' ≫ f) ⟶ G := CategoryTheory.Over.homMk _ hw
  have h2 := h.2 (CategoryTheory.Over.mk x') 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at h2
  have h3 : x₀ * x₀ = x₀ := CategoryTheory.Over.OverMorphism.ext h2
  have h4 : x₀ = 1 := mul_eq_left.1 h3
  exact congrArg (fun q => q.left) h4

end Grp

section Ring

theorem exists_factor {O' R Ω C : Type} [CommRing O'] [CommRing R] [CommRing Ω] [CommRing C] (g : O' →+* Ω)
    (cl : O' →+* C) (hg : Function.Injective g) (φ : R →+* Ω) (ψ : R →+* C)
    (h : ∀ r, ∃ s, g s = φ r ∧ cl s = ψ r) : ∃ θ : R →+* O', g.comp θ = φ ∧ cl.comp θ = ψ := by
  choose θ h1 h2 using h
  exact ⟨{ toFun := θ
           map_one' := hg (by simp [h1])
           map_mul' := fun a b => hg (by simp [h1])
           map_zero' := hg (by simp [h1])
           map_add' := fun a b => hg (by simp [h1]) }, RingHom.ext h1, RingHom.ext h2⟩

theorem spec_dual_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (a : R →+* R') (b : R' →+* R'') :
    spMap (GlobalTheory.CompanionTheory.Ar.dualMap b) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap a) = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (b.comp a)) := by
  rw [LieTangent.spec_comp]
  congr 2
  refine RingHom.ext fun t => ?_
  ext <;> simp

theorem spec_fst_alg (R : Type) [CommRing R] :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
  rw [LieTangent.spec_comp]
  have e1 : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext a; simp
  rw [e1, CommRingCat.ofHom_id, Spec.map_id]

theorem pts_eq {O' Ω R₀ : Type} [CommRing O'] [Field Ω] [CommRing R₀] (g : O' →+* Ω) (hg : Function.Injective g)
    {B : Scheme.{0}} (s : B ⟶ Sp R₀) [IsSeparated s] {a b : Sp O' ⟶ B} (h : spMap g ≫ a = spMap g ≫ b) : a = b := by
  haveI : IsDomain O' := hg.isDomain g
  haveI : IsDominant (spMap g) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot g).1 hg]
    exact bot_le)⟩
  refine ext_of_isDominant_of_isSeparated s ?_ (spMap g) h
  refine ext_of_isDominant (spMap g) ?_
  rw [← Category.assoc, h, Category.assoc]

end Ring

section Lift

variable {X B : Scheme.{0}} {G : CategoryTheory.Over X} [GrpObj G] {G₀ : CategoryTheory.Over B} [GrpObj G₀] {f : X ⟶ B} {φ : G.left ⟶ G₀.left}

theorem exists_tan_lift (hc : IsGrpPullback G G₀ f φ) {O' R : Type} [CommRing O'] [CommRing R]
    (x : Sp O' ⟶ X) (θ : R →+* O') (P : Sp R ⟶ B) (t : Sp (DualNumber R) ⟶ G₀.left)
    (ht : t ≫ G₀.hom = spMap (algebraMap R (DualNumber R)) ≫ P)
    (h1 : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ t = (1 : CategoryTheory.Over.mk P ⟶ G₀).left)
    (he : x ≫ f = spMap θ ≫ P) :
    ∃ v : epsAt x ⟶ G, GlobalTheory.CompanionTheory.Ar.IsTanAt G x v ∧ v.left ≫ φ = spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ t := by
  have hw : (spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ t) ≫ G₀.hom =
      (spMap (algebraMap O' (DualNumber O')) ≫ x) ≫ f := by
    rw [Category.assoc, ht, ← Category.assoc, LieTangent.spec_dual_alg, Category.assoc, Category.assoc, he]
  have l1 := hc.1.lift_fst _ _ hw
  have l2 := hc.1.lift_snd _ _ hw
  refine ⟨CategoryTheory.Over.homMk (hc.1.lift _ _ hw) l2, ?_, l1⟩
  show spMap (TrivSqZeroExt.fstHom O' O' O').toRingHom ≫ hc.1.lift _ _ hw = (1 : CategoryTheory.Over.mk x ⟶ G).left
  refine hc.1.hom_ext ?_ ?_
  · rw [Category.assoc, l1, ← Category.assoc, LieTangent.spec_fst_dual, Category.assoc, h1,
      one_left_pull _ P _ he.symm, one_left_grp hc x _ rfl]
  · rw [Category.assoc, l2, ← Category.assoc, spec_fst_alg, Category.id_comp]
    exact (CategoryTheory.Over.w (1 : CategoryTheory.Over.mk x ⟶ G)).symm

theorem extends_of (hc : IsGrpPullback G G₀ f φ) {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (M : LieModel G ξ E) (p : Cpt ξ) (e : E)
    (v : epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ⟶ G)
    (hv : GlobalTheory.CompanionTheory.Ar.IsTanAt G _ v)
    (h : (M.pt e).left ≫ φ = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (genMap ξ p))) ≫ v.left ≫ φ) :
    M.Extends p e v := by
  refine ⟨hv, hc.1.hom_ext (h.trans (Category.assoc _ _ _).symm) ?_⟩
  have h2 : (M.pt e).left ≫ G.hom = spMap (algebraMap Ω (DualNumber Ω)) ≫ ξ := CategoryTheory.Over.w (M.pt e)
  have h3 : v.left ≫ G.hom = spMap (algebraMap (X.presheaf.stalk p.1) (DualNumber (X.presheaf.stalk p.1))) ≫
    X.fromSpecStalk p.1 := CategoryTheory.Over.w v
  have h4 : (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (genMap ξ p))) ≫ v.left) ≫ G.hom =
      spMap (algebraMap Ω (DualNumber Ω)) ≫ ξ := by
    rw [Category.assoc, h3, ← Category.assoc, LieTangent.spec_dual_alg, Category.assoc, LieTangent.spec_genMap]
  exact h2.trans h4.symm

end Lift

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
  {S : Type} [CommRing S] [Algebra c.F S]

theorem tanY_one (y : FrPt Xo c S) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ Small.tanY Y y τ i =
      (1 : CategoryTheory.Over.mk (Small.ptY Y y) ⟶ Y.t.G).left := by
  have a : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ Small.tanF Y y τ i =
      (1 : CategoryTheory.Over.mk (Small.ptF y) ⟶ Y.oF.t.G).left := by
    refine Y.m0.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, Small.tanF_φ, (y.tan τ i).2]
      exact (one_left_grp Y.m0.cart (Small.ptF y) y.x (Small.ptF_fst y)).symm
    · rw [Category.assoc, Small.tanF_hom, ← Category.assoc, spec_fst_alg, Category.id_comp]
      exact (CategoryTheory.Over.w (1 : CategoryTheory.Over.mk (Small.ptF y) ⟶ Y.oF.t.G)).symm
  rw [Small.tanY, ← Category.assoc, a]
  exact one_left_grp Y.m.cart (Small.ptF y) (Small.ptY Y y) rfl

end Model

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FrameValue

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots


open FrameValue in
set_option maxHeartbeats 600000 in
theorem frame_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (s : CMType H ⊕ CMType H) (i : Fin (labelRk Dw s)), ∃ w : EC, FinRd.Roots.IsFrameVec Or io zT MC w s i ∧ Or.𝔐.M.ValAt (FinRd.Roots.gen T zV) (Or.Fl.b s i) (MC.pt w) := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hv hG la T io e y evT zT t hI zV hR EC _ _ MC s i
  letI := io.toAlgebra
  letI := Small.cstAlg Or
  obtain ⟨-, -, -, -, -, -, ⟨q, φ, ψ, yq, hφ, hψ, hr⟩, -⟩ := hI
  have hgen : genPt Or.𝔐.ξ ⤳ centre (gen T zV) := Or.𝔐.all _
  let P : Cpt Or.𝔐.ξ := ⟨centre (gen T zV), hgen⟩
  have hinj : Function.Injective (genMap Or.𝔐.ξ P) := Or.𝔐.tie.gen.inj P
  have hreg : ∀ r, ∃ s', genMap Or.𝔐.ξ P s' = φ.toRingHom r ∧
      (Scheme.stalkClosedPointTo (gen T zV)).hom s' = ψ.toRingHom r := fun r => by
    obtain ⟨h, e'⟩ := hr r
    obtain ⟨h', s', hs, hs'⟩ := hR ⟨φ r, h⟩
    exact ⟨s', hs, hs'.trans e'.symm⟩
  obtain ⟨θ, hθ1, hθ2⟩ := exists_factor _ _ hinj φ.toRingHom ψ.toRingHom hreg
  have hsep : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have he : Or.𝔐.X.fromSpecStalk P.1 ≫ Or.𝔐.f = spMap θ ≫ Small.ptY Y yq := by
    refine pts_eq (genMap Or.𝔐.ξ P) hinj Y.s ?_
    rw [← Category.assoc, ← Category.assoc]
    have e1 : spMap (genMap Or.𝔐.ξ P) ≫ Or.𝔐.X.fromSpecStalk P.1 = Or.𝔐.ξ := LieTangent.spec_genMap _ _
    rw [e1, ← Fr.pt_eq, Small.ptY_map Y hφ, ← hθ1, LieTangent.spec_comp]
  obtain ⟨v, hvt, hv'⟩ := exists_tan_lift Or.𝔐.m.cart (Or.𝔐.X.fromSpecStalk P.1) θ (Small.ptY Y yq)
    (Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i)) (Small.tanY_hom Y _ _ _) (tanY_one Y _ _ _) he
  have hext : Or.𝔐.M.Extends P (Or.Fl.b s i) v := by
    refine extends_of Or.𝔐.m.cart _ P _ v hvt ?_
    have e2 := Small.tanY_map Y hφ (Small.labelC s) (Small.labelFin Dw s i)
    have e3 := Fr.tan_eq s i
    have e4 : spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ.toRingHom) ≫ Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) =
        spMap (GlobalTheory.CompanionTheory.Ar.dualMap (genMap Or.𝔐.ξ P)) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫
          Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) := by
      rw [← Category.assoc, spec_dual_comp, hθ1]
    exact e3.symm.trans (e2.trans (e4.trans (congrArg (fun u => _ ≫ u) hv'.symm)))
  have hb := LieTangent.isTanAt_base _ (LieTangent.spec_centre (gen T zV)) hvt
  obtain ⟨w, hw⟩ := MC.onto _ hb
  refine ⟨w, ?_, (Or.𝔐.M.valAt_iff _ _ _).2 ⟨hgen, v, hext, hw⟩⟩
  show (MC.pt w).left ≫ Or.𝔐.m.φ = Small.tanY Y zT (Small.labelC s) (Small.labelFin Dw s i)
  have e5 : (MC.pt w).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (Scheme.stalkClosedPointTo (gen T zV)).hom) ≫ v.left :=
    congrArg (fun u => u.left) hw
  have e6 : spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ.toRingHom) ≫ Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) =
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap (Scheme.stalkClosedPointTo (gen T zV)).hom) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫
        Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) := by
    have e7 : spMap (GlobalTheory.CompanionTheory.Ar.dualMap (Scheme.stalkClosedPointTo (gen T zV)).hom) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) =
        spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ.toRingHom) := (spec_dual_comp θ _).trans (by rw [hθ2])
    exact (congrArg (fun u => u ≫ Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i)) e7.symm).trans
      (Category.assoc _ _ _)
  rw [e5, Small.tanY_map Y hψ, e6]
  exact (Category.assoc _ _ _).trans (congrArg (fun u => _ ≫ u) hv')

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameNonarchimedean
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem inFibre_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → InFibre Or.𝔐.ξ p ⟨centre zV, Or.𝔐.all _⟩ := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev _ _ hGood la T io e y evT zT t hInt zV hR hu
  obtain ⟨-, -, hinv⟩ := hu
  obtain ⟨s, hs⟩ := RingHom.mem_range.1 hinv
  have hgen : IsCptGen Or.𝔐.ξ := Or.𝔐.tie.gen
  have hv : ValAt Or.𝔐.ξ zV ((p : RM.Ω)⁻¹) ((Scheme.stalkClosedPointTo zV).hom s) := ⟨Or.𝔐.all _, s, hs, rfl⟩
  have hv' := LieTangent.valAt_base hgen (algebraMap T.V T.Fr) hv
  have hcst : Or.𝔐.cst ((p : c.F)⁻¹) = (p : RM.Ω)⁻¹ := by simp
  have hmem := hGood.1 ((p : c.F)⁻¹)
  have hla : (p : 𝓞 c.F) ∈ la.asIdeal := hInt.1
  have hOver : OverLa la T.V io e := hInt.2.1
  have hev : evT ⟨_, hmem⟩ = io ((p : c.F)⁻¹) := hInt.2.2.2.2.1 _ hmem
  have hr := hR ⟨_, hmem⟩
  rw [hev] at hr
  change ValAt _ _ (Or.𝔐.cst ((p : c.F)⁻¹)) _ at hr
  rw [hcst] at hr
  have heq := LieTangent.valAt_unique hgen hv' hr
  have hp0 : (p : c.F) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h1 : la.valuation c.F (p : c.F) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 c.F) c.F)]
    exact (la.valuation_lt_one_iff_mem _).2 hla
  have h2 := (WithZero.log_lt_log ((la.valuation c.F).ne_zero_iff.2 hp0) one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  have h3 : 0 < vLa la (p : c.F) := by unfold vLa; omega
  have h4 : 0 < vV T.V (io (p : c.F)) := by
    rw [hOver.2]
    exact mul_pos (by exact_mod_cast hOver.1) h3
  have h5 : vV T.V (io ((p : c.F)⁻¹)) = - vV T.V (io (p : c.F)) := by
    simp [vV, map_inv₀]
  have h6 := ReciprocityTheory.ChartRestriction.G.PullbackSections.vV_alg_nonneg T ((Scheme.stalkClosedPointTo zV).hom s)
  rw [heq, h5] at h6
  omega

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end

