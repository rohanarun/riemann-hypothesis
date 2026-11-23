module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0106
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0219
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisation
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoeffFieldAlgClosedFunctionFieldOfTorsionDefinedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffField_algClosed_functionField_of_torsionDefined : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l), 1 ≤ D.p + D.q → l.A = 1 → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → CurveOver H c.F l.M → FnAlgClosed (Xo := Xo) (c := c) := by
  first | exact @GlobalTheory.CompRat.fnAlgClosed_of_curveOver | exact GlobalTheory.CompRat.fnAlgClosed_of_curveOver | (intros; apply GlobalTheory.CompRat.fnAlgClosed_of_curveOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.LevelCover

theorem exists_lift_of_finite_surjective {F : Type} [Field F] [IsAlgClosed F] {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsFinite f] [Surjective f] (x : Sp F ⟶ Y) : ∃ b : Sp F ⟶ X, b ≫ f = x := by
  have : CompactSpace ↥(pullback f x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f x)
  obtain ⟨p, -⟩ := (pullback.snd f x).surjective (default : PrimeSpectrum F)
  obtain ⟨q, -, hq⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback f x)) ⟨p, trivial⟩
  refine ⟨pointOfClosedPoint (pullback.snd f x) q hq ≫ pullback.fst f x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

theorem one_mem_sec_zero {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) :
    (1 : Rul Xo c) ∈ sec Xo c 0 0 := by
  refine ⟨fun p q φ y z _ => by simp, fun p t y y' _ => ?_⟩
  have : wchar (ex Dw 0 0) t = 1 := by
    unfold wchar
    refine Finset.prod_eq_one fun i _ => ?_
    cases i <;> simp [ex]
  simp [this]

theorem exists_point_over {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l l₂ : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {Xo₂ : Moduli Dw l₂} {c₂ : Coeff l₂} (hc : c.F = c₂.F) (r : Xo₂.X ⟶ Xo.X) (rF : Xo₂.XF c₂ ⟶ Xo.XF c)
    [IsFinite rF] [Surjective rF]
    (h₁ : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r)
    (h₂ : rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom)
    (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra c₂.F k]
    (hk : ∀ a : c.F, algebraMap c₂.F k (IntermediateField.inclusion hc.le a) = algebraMap c.F k a)
    (x : Sp k ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c k) :
    ∃ x₂ : Sp k ⟶ Xo₂.X, x₂ ≫ r = x ∧ x₂ ≫ Xo₂.s = sOf c₂ k := by
  have hw : x ≫ Xo.s = spMap (algebraMap c.F k) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [hx, sOf, ← Spec.map_comp]; rfl
  obtain ⟨b, hb⟩ := exists_lift_of_finite_surjective rF (pullback.lift x (spMap (algebraMap c.F k)) hw)
  refine ⟨b ≫ pullback.fst _ _, ?_, ?_⟩
  · rw [Category.assoc, ← h₁, ← Category.assoc, hb, pullback.lift_fst]
  · have e : b ≫ pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom =
        spMap (algebraMap c.F k) := by
      rw [← h₂, ← Category.assoc, hb, pullback.lift_snd]
    obtain ⟨g, hg⟩ := Spec.map_surjective (b ≫ pullback.snd _ _ : Sp k ⟶ Sp c₂.F)
    rw [← Category.assoc, ← hg, ← Spec.map_comp] at e
    have e' := Spec.map_injective e
    have hgk : g = CommRingCat.ofHom (algebraMap c₂.F k) := by
      ext a
      have ha : IntermediateField.inclusion hc.le ⟨a.1, hc.ge a.2⟩ = a := rfl
      have := congrArg (fun f : CommRingCat.of c.F ⟶ CommRingCat.of k => f.hom ⟨a.1, hc.ge a.2⟩) e'
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
      rw [← hk] at this
      exact this
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← hg, hgk, sOf, ← Spec.map_comp]
    rfl

theorem exists_deltaDat_isLev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ (n pd : ℕ) (I : Ideal (𝓞 E)) (l₂ : Level H) (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂), c₂.F = c.F → l.Dvd l₂ → l₂.M = l.M * pd → pd.Coprime l.M → l₂.Mb = l.Mb * I → I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → ∃ d : DeltaDat Xo c n, d.pd = pd ∧ d.I = I ∧ d.l₂ = l₂ ∧ HEq d.Xo₂ Xo₂ ∧ HEq d.c₂ c₂ ∧ d.cδ = 1 ∧ d.IsLev ∧ ∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂ := by
  intro E _ _ _ H Dw l Xo c hr n pd I l₂ Xo₂ c₂ hF hd hM hcop hMb hI
  have hL := GlobalTheory.firstFiveLaws.1
  obtain ⟨r, jK, m, -, -, he, heA, -, hrF⟩ := (_root_.GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H Dw hr).1 l l₂ Xo Xo₂ hd
  obtain ⟨rF, h₁, h₂, hfin, -, hsur, -⟩ := hrF c c₂ hF.symm
  obtain ⟨st, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab hL E H Dw l₂ Xo₂ c₂
  let d : DeltaDat Xo c n :=
    { pd := pd, I := I, l₂ := l₂, Xo₂ := Xo₂, c₂ := c₂, hF := hF, r := r, m := m, nab₂ := nab, cδ := 1,
      φδ := fun _ => 1 }
  have hdiv : l₂.M / l.M = pd := by
    rw [hM]; exact Nat.mul_div_cancel_left _ (by have := l.three_le; omega)
  refine ⟨d, rfl, rfl, rfl, HEq.rfl, HEq.rfl, rfl, ⟨hd, hM, hcop, hMb, hI, ⟨?_, heA⟩, ?_,
    one_mem_sec_zero Xo₂ c₂, ?_⟩, st, hnab⟩
  · rw [hdiv] at he; exact he
  · intro k _ _ _ i₂ hk y
    obtain ⟨x₂, hx, hs⟩ := @exists_point_over E _ _ _ H Dw l l₂ Xo c Xo₂ c₂ hF.symm r rF hfin hsur h₁ h₂
      k _ _ _ i₂ hk y.x y.x_over
    obtain ⟨y₂, -, hy⟩ := (_root_.GlobalTheory.frames_lift_to_cover hL E H Dw l Xo c n d).1 k hk y x₂ hx hs
    exact ⟨y₂, hy⟩
  · intro k _ _ _ y₂
    have h := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw l₂ Xo₂ c₂ k y₂
    have e : evR d.Xo₂ d.c₂ d.cδ y₂ = 1 := evalAt_one _ _ y₂ h
    rw [e]; exact one_ne_zero

end GlobalTheory.LevelCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FnAlgClosedOfCurveOverLcm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem fnAlgClosed_of_curveOver_lcm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l), 1 ≤ D.p + D.q → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → CurveOver H c.F l.M' → FnAlgClosed (Xo := Xo) (c := c) := by
  intro E _ _ _ H D l Xo c hD hsig hC
  have hex : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty := by
    classical
    let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then D.p else D.q
    let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))).symm
    have h : ∀ τ, Nat.card {i // (e i).1 = τ} = m τ := fun τ => by
      rw [Nat.card_congr ((e.subtypeEquiv (q := fun x => x.1 = τ) fun _ => Iff.rfl).trans
        (Equiv.sigmaSubtype τ))]
      simp
    exact ⟨_, fun i => (e i).1, fun τ => ⟨fun hτ => by rw [h]; simp [m, hτ], fun hτ => by rw [h]; simp [m, hτ]⟩⟩
  obtain ⟨g, ty, hty⟩ := hex
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (algebraMap (KA l) ℂ) g ty hD rfl hty
  refine GlobalTheory.T.coeffField_algClosed_in_functionField_of_aut_fix_periods E H D l Xo _ g ty F hD rfl hty (fun _ => rfl) c fun τ hτ => ?_
  exact _root_.GlobalTheory.CompRat.AnyLevel.permutes_id_of_fixesCurve E H D l Xo _ g ty F hD rfl hty (fun _ => rfl) hsig τ (fun x => hτ _ (c.le x.2)) (hC τ hτ)

end GlobalTheory.CompRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatticePeriodFormIndependentOfModels
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj
open Formalism.MainNotions Formalism.MainNotions.DIV.Cons

namespace GlobalTheory.ModelIndep

theorem norm_unit_eq_one {V C : Type} [CommRing V] [NormedField C] [IsUltrametricDist C] (f : V →+* intO C) (u : Vˣ) :
    ‖((f u : intO C) : C)‖ = 1 := by
  have h1 : ‖((f u : intO C) : C)‖ ≤ 1 := (f u).2
  have h2 : ‖((f (u⁻¹ : Vˣ) : intO C) : C)‖ ≤ 1 := (f (u⁻¹ : Vˣ)).2
  have h3 : ‖((f u : intO C) : C)‖ * ‖((f (u⁻¹ : Vˣ) : intO C) : C)‖ = 1 := by
    rw [← norm_mul, ← Subring.coe_mul, ← map_mul, Units.mul_inv, map_one, Subring.coe_one, norm_one]
  refine le_antisymm h1 ?_
  nlinarith [norm_nonneg ((f u : intO C) : C)]

theorem norm_eq_of_dvr {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] {p : ℕ}
    (hp : p.Prime) (C C' : SCF p) (f : V →+* intO ↥C.S) (f' : V →+* intO ↥C'.S) (r : V) :
    ‖((f r : intO ↥C.S) : ↥C.S)‖ = ‖((f' r : intO ↥C'.S) : ↥C'.S)‖ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have key : ∀ (C : SCF p) (f : V →+* intO ↥C.S) (n : ℕ) (u : Vˣ),
      ‖((f (u * ϖ ^ n) : intO ↥C.S) : ↥C.S)‖ = ‖((f ϖ : intO ↥C.S) : ↥C.S)‖ ^ n := by
    intro C f n u
    rw [map_mul, map_pow, Subring.coe_mul, Subring.coe_pow, norm_mul, norm_pow, norm_unit_eq_one, one_mul]
  have hp0 : (p : V) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have hpe : ∀ (C : SCF p) (f : V →+* intO ↥C.S), ‖((f ϖ : intO ↥C.S) : ↥C.S)‖ ^ e = (p : ℝ)⁻¹ := by
    intro C f
    rw [← key C f e w, ← hw, map_natCast, ← C.norm_p]
    simp
  have he : e ≠ 0 := by
    rintro rfl
    have h := hpe C f
    rw [pow_zero] at h
    have h2 : (p : ℝ) = 1 := inv_eq_one.1 h.symm
    exact hp.ne_one (by exact_mod_cast h2)
  have hϖ' : ‖((f ϖ : intO ↥C.S) : ↥C.S)‖ = ‖((f' ϖ : intO ↥C'.S) : ↥C'.S)‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) he).1 ((hpe C f).trans (hpe C' f').symm)
  by_cases hr : r = 0
  · subst hr; simp
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  rw [key, key, hϖ']

theorem betaAt_eq_of_dvr {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] {p : ℕ}
    (hp : p.Prime) (C C' : SCF p) (f : V →+* intO ↥C.S) (f' : V →+* intO ↥C'.S) (D : DegPre V) (a b : D.X) :
    betaAt D ((intO ↥C.S).subtype.comp f) p a b = betaAt D ((intO ↥C'.S).subtype.comp f') p a b := by
  have h : ∀ χ, vPsiAt D ((intO ↥C.S).subtype.comp f) p χ = vPsiAt D ((intO ↥C'.S).subtype.comp f') p χ := by
    intro χ
    unfold vPsiAt
    split_ifs with h
    · exact congrArg (fun x => -Real.logb p x) (norm_eq_of_dvr hp C C' f f' h.choose)
    · rfl
  simp only [betaAt, h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_extension {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {la : HeightOneSpectrum (𝓞 c.F)} (hB : PointsOfFlagModel.BaseAt la β) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ)
    (ho : OverLa la T.V io e) (x : Sp T.Fr ⟶ Xo.X)
    (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    {p : ℕ} {C : SCF p} (Pc : PointsOfFlagModel.PtC Y C) (eF : T.Fr →+* ↥C.S) (g : T.V →+* intO ↥C.S)
    (h1' : eF.comp io = Pc.fK) (h2' : Pc.y ≫ pullback.fst _ _ = spMap eF ≫ x)
    (h3' : ∀ a, ((g a : intO ↥C.S) : ↥C.S) = eF (algebraMap T.V T.Fr a)) :
    ∃ yt : Sp T.V ⟶ Y.X, spMap g ≫ yt = Pc.yt ∧ Nonempty (SABMap G Y.t yt) := by
  obtain ⟨b, hb⟩ := GlobalTheory.EtaVal.exists_base_map_of_overLa (fun a => (hB.2 (β a)).1 ⟨a, rfl⟩) T io e ho
  have hcond : x ≫ Xo.s = spMap io ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [hxs, GlobalTheory.EtaVal.spMap_comp_spMap]
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift x (spMap io) hcond
  have hzs : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  have hzf : z ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _
  have hx : z ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b := by
    show z ≫ (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]
  obtain ⟨yt, h1, h2⟩ := extPt Y T b z hx
  obtain ⟨PP', cub, sym, adj, prim, mP, -⟩ := sabPull Out.CubePf.cubePull yt Y.t
  obtain ⟨mF, -⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Y.oF.t t' (pullback.fst _ _) z Y.m0.toSABMap
    (PullbackSections.sabMapCast m1 hzf.symm)
  obtain ⟨mJ, -⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t t' (Y.jQ ≫ pullback.fst _ _) z Y.m mF
  have hj : z ≫ Y.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ yt := h1.symm
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t _ t' yt (Out.jK T.V) mP (PullbackSections.sabMapCast mJ hj)
  obtain ⟨-, ψ, -⟩ := GlobalTheory.sab_extensions_iso E H Dw l Xo T.V T.Fr x G _ t' t' m1 m2 m1 mK
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ Y.t _ G yt (𝟙 _) mP ψ
  have hprY : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have hr : (intO ↥C.S).subtype.comp g = eF.comp (algebraMap T.V T.Fr) := RingHom.ext h3'
  have hy : Pc.y = spMap eF ≫ z := by
    apply pullback.hom_ext
    · rw [h2', Category.assoc, hzf]
    · rw [Pc.y_over, Category.assoc, hzs, GlobalTheory.EtaVal.spMap_comp_spMap, h1']
  have halg : g.comp b = Pc.alg := by
    refine RingHom.ext fun a => Subtype.ext ?_
    have q1 := DFunLike.congr_fun Pc.compat a
    have q2 := DFunLike.congr_fun hb a
    have q3 := DFunLike.congr_fun h1' (β a)
    simp only [RingHom.comp_apply] at q1 q2 q3 ⊢
    rw [h3', q2, q3]; exact q1.symm
  refine ⟨yt, ?_, ⟨PullbackSections.sabMapCast n (Category.id_comp yt)⟩⟩
  refine GlobalTheory.EtaVal.point_ext_of_injective (intO ↥C.S).subtype Subtype.val_injective Y.s _ _ ?_ ?_
  · rw [Pc.ext, hy, Category.assoc, ← h1, ← Category.assoc, GlobalTheory.EtaVal.spMap_comp_spMap, hr,
      ← GlobalTheory.EtaVal.spMap_comp_spMap, Category.assoc]
  · rw [Pc.yt_over, Category.assoc, h2, GlobalTheory.EtaVal.spMap_comp_spMap, halg]

theorem exists_equiv_of_uniformisation {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {la : HeightOneSpectrum (𝓞 c.F)} (hB : PointsOfFlagModel.BaseAt la β) (T : CDVR) (hT : T.FinRes) (io : c.F →+* T.Fr) (e : ℕ)
    (ho : OverLa la T.V io e) (x : Sp T.Fr ⟶ Xo.X)
    (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    (T' : CDVR) (φ : T.V →+* T'.V) (hφ : Function.Injective φ) (hφf : φ.Finite) (G' : SAB H (Sp T'.V))
    (mG : SABMap G' G (spMap φ)) (U : PELUnif (maximalIdeal T'.V) G')
    (hU : ∀ χ, PsiUnitOn U.D.toPre χ (abLocus G'.G)) (hTo : U.TorsionIso)
    {p : ℕ} (hp : p.Prime) {C : SCF p} (Pc : PointsOfFlagModel.PtC Y C) (eF : T.Fr →+* ↥C.S)
    (h1' : eF.comp io = Pc.fK) (hle : ∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1)
    (hlt : ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1)
    (h2' : Pc.y ≫ pullback.fst _ _ = spMap eF ≫ x) (A : DatAt Y Pc) :
    ∃ (f : T'.V →+* intO ↥C.S) (q : U.D.toPre.X ≃ₗ[𝓞 E] A.Ylat),
      ∀ a b, A.beta (q a) (q b) = betaAt U.D.toPre ((intO ↥C.S).subtype.comp f) p a b := by
  let g : T.V →+* intO ↥C.S := (eF.comp (algebraMap T.V T.Fr)).codRestrict _ hle
  have hg : Function.Injective g := fun a b h =>
    IsFractionRing.injective T.V T.Fr (eF.injective (congrArg Subtype.val h))
  obtain ⟨yt, hyt, ⟨n⟩⟩ := exists_extension Y hB T io e ho x hxs G t' m1 m2 Pc eF g h1' h2' (fun _ => rfl)
  have hpm : (p : T.V) ∈ maximalIdeal T.V := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h := norm_unit_eq_one g u
    rw [hu, map_natCast] at h
    have h' : ‖(p : ↥C.S)‖ = 1 := by simpa using h
    rw [C.norm_p] at h'
    exact hp.ne_one (by exact_mod_cast inv_eq_one.1 h')
  obtain ⟨f, hf, -, hfl⟩ := (_root_.GlobalTheory.SmallClosedField.exists_embedding_and_extension T p hp hT hpm).2 C g T' φ hg hlt hφ hφf
  obtain ⟨n2, -⟩ := sabComp pullCubComp E H _ _ _ Y.t G G' yt (spMap φ) n mG
  have hab : (spMap φ ≫ yt) ⁻¹' abLocus Y.t.G = abLocus G'.G :=
    Set.ext fun q => abLocus_pullback abLocusOne Y.t.semi n2.cart.1 q
  let A₀ : DatAt Y Pc :=
    { R := T'.V
      noeth := inferInstance
      normal := inferInstance
      complete := inferInstance
      «ι» := spMap φ ≫ yt
      f := f
      f_loc := hfl
      fac := by rw [← Category.assoc, GlobalTheory.EtaVal.spMap_comp_spMap, hf, hyt]
      t := G'
      m := n2
      U := U
      unitOn := fun χ => by rw [hab]; exact hU χ
      tors := hTo }
  obtain ⟨-, q, hq⟩ := _root_.GlobalTheory.DatUniq.coord_ne_zero_and_exists_equiv E H Dw l Xo c O β Y p C Pc hp T g yt hT hg hlt hyt A₀ A
  exact ⟨f, q, hq⟩

theorem exists_equiv_two_models {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
    (Y : Model Xo c β) (Y' : Model Xo c β') {la : HeightOneSpectrum (𝓞 c.F)} (hB : PointsOfFlagModel.BaseAt la β)
    (hB' : PointsOfFlagModel.BaseAt la β') (T : CDVR) (hT : T.FinRes) (io : c.F →+* T.Fr) (e : ℕ)
    (ho : OverLa la T.V io e) (x : Sp T.Fr ⟶ Xo.X)
    (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    {p : ℕ} (hp : p.Prime) {C C' : SCF p} (P : PointsOfFlagModel.PtC Y C) (P' : PointsOfFlagModel.PtC Y' C')
    (eF : T.Fr →+* ↥C.S) (a1 : eF.comp io = P.fK) (a2 : ∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1)
    (a3 : ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1)
    (a4 : P.y ≫ pullback.fst _ _ = spMap eF ≫ x)
    (eF' : T.Fr →+* ↥C'.S) (b1 : eF'.comp io = P'.fK) (b2 : ∀ a : T.V, ‖eF' (algebraMap T.V T.Fr a)‖ ≤ 1)
    (b3 : ∀ a ∈ maximalIdeal T.V, ‖eF' (algebraMap T.V T.Fr a)‖ < 1)
    (b4 : P'.y ≫ pullback.fst _ _ = spMap eF' ≫ x) (A : DatAt Y P) (A' : DatAt Y' P') :
    ∃ f : A.Ylat ≃ₗ[𝓞 E] A'.Ylat, ∀ a b, A'.beta (f a) (f b) = A.beta a b := by
  obtain ⟨T', φ, G', mG, hφ, hφf, -, -, U, hU, hTo⟩ :=
    GlobalTheory.UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T G t' m2 x m1 hT
  obtain ⟨f, q, hq⟩ := exists_equiv_of_uniformisation Y hB T hT io e ho x hxs G t' m1 m2
    T' φ hφ hφf G' mG U hU hTo hp P eF a1 a2 a3 a4 A
  obtain ⟨f', q', hq'⟩ := exists_equiv_of_uniformisation Y' hB' T hT io e ho x hxs G t' m1 m2
    T' φ hφ hφf G' mG U hU hTo hp P' eF' b1 b2 b3 b4 A'
  refine ⟨q.symm.trans q', fun a b => ?_⟩
  have h1 := hq (q.symm a) (q.symm b)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
  exact (hq' (q.symm a) (q.symm b)).trans ((betaAt_eq_of_dvr hp _ _ f' f _ _ _).trans h1.symm)

theorem datIndep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), DatIndep Xo c := by
  intro E _ _ _ H Dw l Xo c la Tw Tw' hTw hTw' T io e y ho hy z z' hz hz' A A'
  letI := io.toAlgebra
  obtain ⟨y, hy1, G, t', m1, m2, hy2⟩ := y
  obtain ⟨v, C, P, Fl⟩ := z
  obtain ⟨v', C', P', Fl'⟩ := z'
  obtain ⟨hv, eF, a1, a2, a3, a4, -⟩ := hz
  obtain ⟨hv', eF', b1, b2, b3, b4, -⟩ := hz'
  obtain rfl : v = lamOf la := hv
  obtain rfl : v' = lamOf la := hv'
  exact exists_equiv_two_models (Tw.Y (lamOf la)) (Tw'.Y (lamOf la)) (hTw.1 (lamOf la)).1 (hTw'.1 (lamOf la)).1 T hy
    io e ho y.x y.x_over G t' m1 m2 (resCh_prime la) P P' eF a1 a2 a3 a4 eF' b1 b2 b3 b4 A A'

end GlobalTheory.ModelIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SameSpaceOfLawsJ
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta

namespace GlobalTheory.ShortLaws

theorem sameSpace_of_lawsJ {D : D7} (J : CoreJ D) (T : Top D) (hJ : LawsJ J) (hT : T.toCore = J.toCore) :
    ∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧
      ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0 := by
  have key : ∀ C : Core D, C = J.toCore → ∀ j, InR D j → ∀ k k', ((C.U j C.σ₀).X k).Gm = ((C.U j C.σ₀).X k').Gm ∧
      ((C.U j C.σ₀).X k).ξ0 = ((C.U j C.σ₀).X k').ξ0 := by
    rintro C rfl j hj k k'
    obtain ⟨hr, hm⟩ := hJ.modelW j hj J.toCore.σ₀ J.toCore.good_σ₀
    exact ⟨(hm k).1.trans (hm k').1.symm, (hm k).2.trans (hm k').2.symm⟩
  exact key _ hT

theorem lawsSh_of_pinned (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {D : D7} (T : Top D) (h : LawsP T) (hb : 0 < badN D)
    (hsp : ∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧
      ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0)
    (p : ℕ) (hp : p = D.host.pde ∨ p = D.host.pde')
    (hd : ∀ j, InR D j → ∀ n, (T.dδ j n).pd = p ∧ (T.dδ j n).IsLev ∧ (T.dδ j n).l₂.A = 1 ∧
      (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.dδ j n).Xo₂ (T.dδ j n).c₂ (T.dδ j n).nab₂) ∧
      (∃ m : ℕ, 0 < m ∧ (T.dδ j n).cδ ^ m = 1) ∧
      (∀ y : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt (T.dδ j n).c₂.F.val.toRingHom), ∃ a : (T.dδ j n).c₂.F,
        evR (T.dδ j n).Xo₂ (T.dδ j n).c₂ (T.dδ j n).cδ y =
          algebraMap (T.dδ j n).c₂.F (CAt (T.dδ j n).c₂.F.val.toRingHom) a) ∧
      ((T.Q.Dw j).p + (T.Q.Dw j).q ≤ n → ∃ ph ψ x₀, ψ ≠ 1 ∧ (T.dδ j n).PhiPin ph ψ x₀ ∧ (T.dδ j n).PsiTie ψ)) :
    LawsSh T := by
  have hM : LawsM T.toCore := h.toLawsCore.toLawsM
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hM.pins
  have hL : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.firstFiveLaws.1
  have hr : ∀ j, InR D j → (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := fun j hj => (hnum j hj).1
  have hr1 : ∀ j, InR D j → 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := fun j hj => (hr j hj).symm ▸ (hnum j hj).2.1
  have hb1 : badN D ≠ 1 := by
    have h2 : 2 ∣ badN D := by
      unfold badN
      exact ((D.host.two_dvd_QS.mul_right _).mul_right _).mul_right _
    omega
  have hroot : ∀ j, InR D j → ∀ n, ∃ (Cls : Type) (_ : CommGroup Cls) (_ : Finite Cls)
      (δ : Cls →* (T.dδ j n).c₂.Fˣ)
      (gdet : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt (T.dδ j n).c₂.F.val.toRingHom) → Cls),
      CMP (T.Q.Xo j) T.Q.c (T.dδ j n) _ Cls δ gdet false := by
    intro j hj n
    obtain ⟨-, hlev, -, -, ⟨m, hm, hm1⟩, hval, -⟩ := hd j hj n
    exact GlobalTheory.RootOfUnityFn.exists_character _ _ _ _ _ _ n (T.dδ j n) m hm hlev.2.2.2.2.2.2.2.1 hm1 hval
  have htot : ∀ j, InR D j → ∀ a n,
      ShortValTot (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV a n (T.dδ j n) := by
    intro j hj a n
    obtain ⟨-, hlev, hA2, hnab, -, -, hphi⟩ := hd j hj n
    refine GlobalTheory.shortValTot_of_pinned hL hC _ _ _ _ _ _ n (T.dδ j n)
      (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 _ _ _ (hr1 j hj)).1 (hM.evalWD j hj) (h.allTest j hj)
      (GlobalTheory.Frames.algebraic_laws hL.secBaseChange _ _ _ _ _ _).2.2.1
      (GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange _ _ _ _ _ _) hlev (hA2.trans hA.symm) hnab ?_ _ _ _ a
    intro hn
    obtain ⟨ph, ψ, x₀, -, h1, h2⟩ := hphi hn
    exact ⟨ph, ψ, x₀, h1, h2⟩
  have hpin : ∀ j, InR D j → ∀ n, (T.Q.Dw j).p + (T.Q.Dw j).q ≤ n → ∃ ph ψ x₀, (T.dδ j n).PhiPin ph ψ x₀ := by
    intro j hj n hn
    obtain ⟨ph, ψ, x₀, -, h1, -⟩ := (hd j hj n).2.2.2.2.2.2 hn
    exact ⟨ph, ψ, x₀, h1⟩
  have hunit : ∀ j, InR D j → ∀ n, GlobalTheory.Dict.UnitC (T.dδ j n) := by
    intro j hj n
    obtain ⟨Cls, _, _, δ, gdet, hc⟩ := hroot j hj n
    exact GlobalTheory.Dict.unitC_of_finite_character _ _ _ _ _ _ _ _ Cls δ gdet (hr1 j hj) hc
  refine
    { beta := fun j _ n => GlobalTheory.betaExists_of_ne_one _ _ _ _ _ n _ hb1
      dLev := fun j hj n => (hd j hj n).2.1
      dNab := fun j hj n => (hd j hj n).2.2.2.1
      dPd := ⟨p, hp, fun j hj n => (hd j hj n).1⟩
      dPhi := fun j hj n hn => (hd j hj n).2.2.2.2.2.2 ((hr j hj).symm ▸ hn)
      dRoot := hroot
      shTot := fun j hj a n _ => htot j hj a n
      shCusp := fun j hj a n _ _ => _root_.GlobalTheory.Dict.shortInCusp_cusp hC D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n (T.dδ j n)
        D.R.r (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (hnum j hj).2.1 (fun σ hσ => hM.unf j hj σ hσ)
        (hd j hj n).2.1 (hd j hj n).2.2.2.1 (hunit j hj n) (hpin j hj n) (T.nab j) (badN D) D.R.nV a
      shNe := ?_ }
  intro j h1 h2
  have hj : InR D j := ⟨h1, h2.le⟩
  refine shortNe0_of_t4Span _ _ _ _ _ _ _ ?_
  refine _root_.GlobalTheory.cusp_le_span_shortGen hC D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) T.σ₀ T.good_σ₀ (hM.unf j hj _ T.good_σ₀) (hnum j hj).2.1 hA
    (hsp j hj) ?_ (fun a n hdom k => hM.chiTriv j hj _ T.good_σ₀ a n hdom k) (T.nab j) (badN D) D.R.nV (T.dδ j) hb ?_
  · intro k ga hga hv
    refine _root_.GlobalTheory.PrincCore.hasPrinc_core D T.toCore h.toLawsCore j hj _ T.good_σ₀ k ga hga fun x hx => ?_
    obtain ⟨u, hu, he⟩ := hv x hx
    refine ⟨u, hu, ?_⟩
    rw [he, Nat.cast_smul_eq_nsmul]
    exact add_sub_cancel_left _ _
  · intro n
    refine ⟨(hd j hj n).2.1, (hd j hj n).2.2.2.1, hunit j hj n, ?_, hpin j hj n, fun a _ => htot j hj a n⟩
    rw [(hd j hj n).1]
    have := D.host.pde_mod
    rcases hp with rfl | rfl <;> omega

end GlobalTheory.ShortLaws
end

