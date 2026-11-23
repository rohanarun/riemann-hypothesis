module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SectionBaseChangeOfBasis
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeadingProductsIndependentModuloDeepProducts
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0073
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
public import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ActLevAndActBC
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldBC

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
  Formalism.BasicNotions

theorem actLev_of_le {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {G : Type} [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La))
    (hL : ActLev (Xo := Xo) c lev) : ActLev (Xo := Xo) c' lev := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g S _ _ y
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    obtain ⟨z, hz⟩ := hL.total g S (y.res hle h)
    exact ⟨z.ext hle h, hz⟩
  · intro g S _ _ y y₁ y₂ h₁ h₂
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.func g S (y.res hle h) (y₁.res hle h) (y₂.res hle h) h₁ h₂
  · intro S _ _ y
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.one S (y.res hle h)
  · intro g g' S _ _ y y₁ y₂ h₁ h₂
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.mul g g' S (y.res hle h) (y₁.res hle h) (y₂.res hle h) h₁ h₂
  · intro g S T _ _ _ _ φ y y' z z' h₀ h₁ h₂
    letI := resAlg hle S
    letI := resAlg hle T
    have hS : AlgOver c c' hle S := fun _ => rfl
    have hT : AlgOver c c' hle T := fun _ => rfl
    let ψ : S →ₐ[c.F] T := { φ.toRingHom with commutes' := fun x => φ.commutes _ }
    exact hL.nat g S T ψ (y.res hle hS) (y'.res hle hS) (z.res hle hT) (z'.res hle hT) h₀ h₁ h₂
  · intro g S _ _ t y y' z z' h₀ h₁ h₂
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.bor g S t (y.res hle h) (y'.res hle h) (z.res hle h) (z'.res hle h) h₀ h₁ h₂

theorem actLev_and_actBC (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (G : Type) [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La))
    (hL : ActLev (Xo := Xo) c lev) :
    ActLev (Xo := Xo) c' lev ∧ ActBC hle (actLev (Xo := Xo) c lev) (actLev (Xo := Xo) c' lev) :=
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hc := fun c => GlobalTheory.Frames.chartCoverF_of_secBaseChange hS D.host.E H Dw l Xo c
  ⟨actLev_of_le hle lev hL, actBC_of hle lev (evalWD_fr (frChartF_of (hc c))) (evalWD_fr (frChartF_of (hc c'))) hL
    (actLev_of_le hle lev hL)⟩

end GlobalTheory.FieldBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFactsOfThetaDataOnModels
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem GlobalTheory.Shares.exists_anFacts_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (N : ℕ) (ka wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (CR c : ℝ), addL wF wL Tn = ka → Nonempty (ArchAt h j w wF Tn (WeightFamilies.c1 D CR Tn c j)) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → MggOnto h j CR Tn c ka → TieMaxCuspSt h j CR Tn c ka → ∃ (R : Rdg (recPlusN h j hj n)) (t : Idx D j N → ℂ) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t ∧ AnFacts R w t ka wF Tn (WeightFamilies.MggK n.base CR Tn c j ka) xs := by
  intro D T h j hj n N ka wL wF w Tn CR c hka hA hOn hM hTie
  subst hka
  obtain ⟨A⟩ := hA
  obtain ⟨R, e, hR⟩ := _root_.GlobalTheory.Shares.exists_isRdgU D T h j hj n
  obtain ⟨t, ht, ⟨Fl⟩⟩ := _root_.GlobalTheory.GenericFlat.exists_generic_flatAt D T h j hj N wL wF w Tn _ A
  classical
  let ι : Type := Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ
  have : Fintype ι := inferInstance
  let en : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let xs : Fin (Fintype.card ι) → R.Y := fun q =>
    e.symm ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩
  have hxs : ∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩ :=
    fun q => e.apply_symm_apply _
  have h1 := _root_.GlobalTheory.Shares.points_and_interp D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs hOn
  refine ⟨R, t, _, xs, ?_, h1.1, h1.2,
    _root_.GlobalTheory.Shares.VanDiv.vanishing_division D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs hOn,
    _root_.GlobalTheory.Shares.LeadDeep.main D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs,
    _root_.GlobalTheory.UpperRecord.upper D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs,
    _root_.GlobalTheory.LowerBound.lower_bound D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs CR c rfl hM,
    _root_.GlobalTheory.Containment.main D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs hOn CR c rfl ?_⟩
  · intro Q hQ
    have hσ : R.σ = T.σ₀ := RingHom.ext hR.1
    rw [hσ]
    exact ht Q hQ
  · exact fun F hF => (hTie F).1 hF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjugateSectionValuesSemilinear
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.GalTw

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CoefChangeCompare (Natural FromT ValueWD map_trans evR_spec evR_not evR_map)

namespace Rule

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {ta : c.F ≃+* c.F}

theorem fixes_symm (h : Fixes c ta) : Fixes c ta.symm :=
  ⟨fun τ a => by rw [RingEquiv.symm_apply_eq, h.emb], fun a => by rw [RingEquiv.symm_apply_eq, h.base]⟩

def twHom (ta : c.F ≃+* c.F) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) : Tw ta S →ₐ[c.F] Tw ta T :=
  { φ.toRingHom with commutes' := fun a => φ.commutes (ta a) }

def untwHom {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] Tw ta T) : Tw ta.symm S →ₐ[c.F] T :=
  { φ.toRingHom with
    commutes' := fun a => (φ.commutes (ta.symm a)).trans
      (congrArg (algebraMap c.F T) (ta.apply_symm_apply a)) }

theorem fromT_tw_test (h : Fixes c ta) (hA : AllTest Xo c) (p : TRing c.F) (y : FrPt Xo c p.R) :
    FromT (twPt h y) := by
  haveI : IsReduced (Tw ta p.R) := ((GlobalTheory.reduced_finiteType_iff_testRing c.F).2 p).2
  exact hA _ _

theorem fromT_of_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (hy : FromT y) (hm : FrMap φ y z) : FromT z := by
  obtain ⟨p, ψ, y₀, h₀⟩ := hy
  exact ⟨p, _, y₀, map_trans ψ φ h₀ hm⟩

theorem frMap_tw (h : Fixes c ta) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (hm : FrMap φ y z) :
    FrMap (twHom ta φ) (twPt h y) (twPt h z) := hm

theorem fromT_of_tw (h : Fixes c ta) (hA : AllTest Xo c) {S : Type} [CommRing S] [Algebra c.F S]
    {y : FrPt Xo c S} (hy : FromT (twPt h y)) : FromT y := by
  obtain ⟨p, φ, y₀, h₀⟩ := hy
  have h₁ : FrMap (untwHom φ) (twPt (fixes_symm h) y₀) y := h₀
  exact fromT_of_map (fromT_tw_test (fixes_symm h) hA p y₀) h₁

theorem evR_galRul (h : Fixes c ta) (hWD : ValueWD Xo c) (hA : AllTest Xo c) {f : Rul Xo c} (hf : Natural c f)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    evR Xo c (galRul h f) y = (evR Xo c f (twPt h y)).val := by
  by_cases hy : FromT y
  · obtain ⟨q, φ, y₀, hm, e⟩ := evR_spec hy
    rw [e, evR_map hWD hf (fromT_tw_test h hA q y₀) (frMap_tw h hm)]
    rfl
  · rw [evR_not hy, evR_not (fun h' => hy (fromT_of_tw h hA h'))]
    rfl

theorem galRul_mem_sec (h : Fixes c ta) (hWD : ValueWD Xo c) (hA : AllTest Xo c) (hB : BorChartF Xo c)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) : galRul h f ∈ sec Xo c a n := by
  refine ⟨fun p q φ y z hm => ?_, fun q t y y' hb => ?_⟩
  · exact evR_map hWD hf.1 (fromT_tw_test h hA p y) (frMap_tw h hm)
  · have hb' : FrBor (S := Tw ta q.R) t (twPt h y) (twPt h y') := hb
    have h3 : evR Xo c f (twPt h y') = _ * evR Xo c f (twPt h y) :=
      wtAll_of_borChart hB (ex Dw a n) hf.1 hf.2 (Tw ta q.R) _ _ _ (fromT_tw_test h hA q y)
        (fromT_tw_test h hA q y') hb'
    exact h3

end Rule

theorem galRul_sec_val_semilinear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, galRul h f ∈ sec Xo c a n ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), evR Xo c (galRul h f) y = (evR Xo c f (twPt h y)).val) ∧ (∀ (t : c.F) (f g : Rul Xo c), galRul h (t • f + g) = ta t • galRul h f + galRul h g) ∧ ∀ (c₀ : Coeff l) (hle : c₀.F ≤ c.F), (∀ x : c₀.F, ta (incF c₀ c hle x) = incF c₀ c hle x) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (as : Fin m → c.F) (fs : Fin m → Rul Xo c₀), ∀ f ∈ sec Xo c a n, IsBC hle f as fs → IsBC hle (galRul h f) (fun i => ta (as i)) fs := by
  intro E _ _ _ H Dw l Xo c ta h
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hc := GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c
  have hWD : ValueWD Xo c := evalWD_fr (frChartF_of hc)
  have hA : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  have hB : BorChartF Xo c := borChartF_of_cover hc
  refine ⟨fun a n f hf => ⟨Rule.galRul_mem_sec h hWD hA hB hf, fun S _ _ y => Rule.evR_galRul h hWD hA hf.1 y⟩,
    fun t f g => ?_, ?_⟩
  · funext p y
    have h1 : evR Xo c (t • f + g) (twPt h y) =
        algebraMap c.F (Tw ta p.R) t * evR Xo c f (twPt h y) + evR Xo c g (twPt h y) := by
      unfold evR
      rw [evalAt_add, evalAt_smul]
    refine h1.trans ?_
    show _ = ta t • galRul h f p y + galRul h g p y
    rw [Algebra.smul_def]
    rfl
  · intro c₀ hle hfix a n m as fs f hf hbc S _ A _ ho y
    letI : Algebra c₀.F (Tw ta S) := A
    have ho' : AlgOver c₀ c hle (Tw ta S) := fun x =>
      (congrArg (algebraMap c.F S) (hfix x)).trans (ho x)
    rw [Rule.evR_galRul h hWD hA hf.1 y]
    exact hbc (Tw ta S) ho' (twPt h y)

end GlobalTheory.GalTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqOfForallAlgClosed
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory.ClassSumUnique

theorem eq_of_forall_algClosed {K R : Type} [Field K] [CommRing R] [Algebra K R] [IsReduced R] (u v : R)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : R →ₐ[K] k), φ u = φ v) : u = v := by
  rw [← sub_eq_zero]
  refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun J hJ => ?_)
  let ψ : R →+* AlgebraicClosure J.ResidueField :=
    (algebraMap J.ResidueField (AlgebraicClosure J.ResidueField)).comp (algebraMap R J.ResidueField)
  letI : Algebra K (AlgebraicClosure J.ResidueField) := (ψ.comp (algebraMap K R)).toAlgebra
  have e : ψ u = ψ v := h (AlgebraicClosure J.ResidueField) { ψ with commutes' := fun _ => rfl }
  have e' : algebraMap R J.ResidueField u = algebraMap R J.ResidueField v :=
    (algebraMap J.ResidueField (AlgebraicClosure J.ResidueField)).injective e
  rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, e', sub_self]

theorem sec_eq_of_geometric {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {a : (E →+* ℂ) × ℕ → ℕ} {m : ℕ} {f f' : Rul Xo c} (hf : f ∈ sec Xo c a m)
    (hf' : f' ∈ sec Xo c a m)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k), evR Xo c f y = evR Xo c f' y) :
    f = f' := by
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hWD : GlobalTheory.CoefChangeCompare.ValueWD Xo c :=
    evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
  have hBC : GlobalTheory.CoefChangeCompare.HasBC Xo c := GlobalTheory.CoefChangeCompare.hasBC_of hS
  funext p y
  haveI := ((GlobalTheory.reduced_finiteType_iff_testRing c.F).2 p).2
  refine eq_of_forall_algClosed (K := c.F) _ _ fun k _ _ _ φ => ?_
  obtain ⟨z, hz⟩ := hBC p.R k φ y
  rw [← GlobalTheory.CoefChangeCompare.evR_of_map hWD hf.1 hz, ← GlobalTheory.CoefChangeCompare.evR_of_map hWD hf'.1 hz]
  exact h k z

theorem isThClsD_unique : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F), d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → (∀ k, (La k).Unimod ∧ (La k).TrivAt d.l₂.M ∧ (La k).LevOK (Nc k) d.l₂.M) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), (∀ v, io v ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ (x : Cl → Vs) (a' : (E →+* ℂ) × ℕ → ℕ) (m : ℕ), ∀ f ∈ sec Xo c a' m, ∀ f' ∈ sec Xo c a' m, IsThClsD Xo c d w La Nc gam vol ep io x f → IsThClsD Xo c d w La Nc gam vol ep io x f' → f = f' := by
  intro hC E _ _ _ H Dw l Xo c n d Cl _ w La Nc gam vol ep Vs _ _ io hd hnab hLa a hio x a' m f hf f' hf' h h'
  obtain ⟨_, hnab⟩ := hnab
  refine sec_eq_of_geometric hf hf' fun k _ _ _ y => ?_
  letI : Algebra d.c₂.F k := ((algebraMap c.F k).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  have hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a => by
    show algebraMap c.F k (d.eF.symm (d.eF a)) = _
    rw [AlgEquiv.symm_apply_apply]
  obtain ⟨y₂, hy⟩ := hd.2.2.2.2.2.2.1 k hk y
  obtain ⟨v, hv, e⟩ := h k hk y y₂ hy
  obtain ⟨v', hv', e'⟩ := h' k hk y y₂ hy
  have hvv : v = v' := funext fun cl =>
    ((GlobalTheory.shortThetaValue_existsUnique_natural GlobalTheory.abelianSchemeLaws_all.1 hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n
      (La cl) (Nc cl) (hLa cl).1 (hLa cl).2.1 (hLa cl).2.2 a _
      ((GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hio (x cl))) (fun q => d.eF (w cl q)) 1).1 k y₂).unique
      (hv cl) (hv' cl)
  rw [e, e', hvv]

end GlobalTheory.ClassSumUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsHomogeneousAevalEqZero
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.SecRelation

theorem coeff_aeval_C_mul_X {K Ω σ : Type} [Field K] [Field Ω] [Algebra K Ω] [Fintype σ] (v : σ → Ω)
    (P : MvPolynomial σ K) (d : ℕ) :
    (MvPolynomial.aeval (fun i => Polynomial.C (v i) * Polynomial.X) P).coeff d =
      MvPolynomial.aeval v (MvPolynomial.homogeneousComponent d P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    have h : MvPolynomial.aeval (fun i => Polynomial.C (v i) * Polynomial.X) (MvPolynomial.monomial s a) =
        Polynomial.C (MvPolynomial.aeval v (MvPolynomial.monomial s a)) * Polynomial.X ^ s.degree := by
      rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, Finsupp.prod, Finsupp.prod]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow,
        Polynomial.algebraMap_apply, Finsupp.degree_apply, mul_assoc]
    rw [h, Polynomial.coeff_C_mul_X_pow,
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial a rfl)]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add (f := _), Polynomial.coeff_add, hp, hq]

theorem exists_isHomogeneous_aeval_eq_zero {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
    (hD : Algebra.trdeg K Ω = D) (hm : D + 2 ≤ m) (v : Fin m → Ω) :
    ∃ (Q : MvPolynomial (Fin m) K) (d : ℕ), Q ≠ 0 ∧ Q.IsHomogeneous d ∧ MvPolynomial.aeval v Q = 0 := by
  have htr : Algebra.trdeg K (Polynomial Ω) = ((D + 1 : ℕ) : Cardinal) := by
    rw [← trdeg_add_eq K Ω (A := Polynomial Ω), Polynomial.trdeg_of_isDomain, hD]
    push_cast
    rfl
  have hdep : ¬ AlgebraicIndependent K (fun i => Polynomial.C (v i) * Polynomial.X) := by
    intro h
    have h1 := h.cardinalMk_le_trdeg
    rw [htr, Cardinal.mk_fin, Nat.cast_le] at h1
    omega
  rw [algebraicIndependent_iff] at hdep
  push_neg at hdep
  obtain ⟨P, hP, hP0⟩ := hdep
  have hex : ∃ d, MvPolynomial.homogeneousComponent d P ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hP0
    rw [← MvPolynomial.sum_homogeneousComponent P]
    exact Finset.sum_eq_zero fun d _ => hall d
  obtain ⟨d, hd⟩ := hex
  refine ⟨_, d, hd, MvPolynomial.homogeneousComponent_isHomogeneous d P, ?_⟩
  rw [← coeff_aeval_C_mul_X, hP, Polynomial.coeff_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem one_mem_sec : (1 : Rul Xo c) ∈ sec Xo c 0 0 := by
  refine ⟨fun p q φ y z _ => ?_, fun p t y y' _ => ?_⟩
  · show (1 : q.R) = φ 1
    rw [map_one]
  · show (1 : p.R) = wchar (ex Dw 0 0) t * 1
    have : ex Dw (0 : (E →+* ℂ) × ℕ → ℕ) 0 = fun _ => 0 := by funext i; cases i <;> rfl
    simp [wchar, this]

theorem multiset_prod_mem_sec {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {σ : Type} (u : σ → Rul Xo c)
    (hu : ∀ i, u i ∈ sec Xo c a n) (s : Multiset σ) :
    (s.map u).prod ∈ sec Xo c (s.card • a) (s.card • n) := by
  induction s using Multiset.induction_on with
  | empty => simpa using one_mem_sec
  | cons i s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, succ_nsmul', succ_nsmul']
    exact sec_mul Xo c _ _ _ _ (hu i) ih

theorem aeval_mem_sec {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {σ : Type} (u : σ → Rul Xo c)
    (hu : ∀ i, u i ∈ sec Xo c a n) {Q : MvPolynomial σ c.F} {d : ℕ} (hQ : Q.IsHomogeneous d) :
    MvPolynomial.aeval u Q ∈ sec Xo c (d • a) (d • n) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Q.as_sum, map_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  have hc : s.toMultiset.card = d := by
    rw [Finsupp.card_toMultiset]
    have := hQ (MvPolynomial.mem_support_iff.1 hs)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have h1 := multiset_prod_mem_sec u hu s.toMultiset
  rw [hc, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (by simp) (by intros; rw [pow_add])] at h1
  rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ h1

theorem exists_algHom_evR {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) :
    ∃ ψ : Rul Xo c →ₐ[c.F] S, ∀ f, evR Xo c f y = ψ f :=
  ⟨AlgHom.ofLinearMap (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y)
    (evalAt_one _ _ y h) (fun f g => evalAt_mul _ _ f g y), fun _ => rfl⟩

theorem exists_homogeneous_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ), Module.finrank ℚ E / 2 * (Dw.p * Dw.q + Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2) + 2 ≤ m → ∀ u : Fin m → Rul Xo c, (∀ i, u i ∈ sec Xo c a n) → ∃ (Q : MvPolynomial (Fin m) c.F) (d : ℕ), Q ≠ 0 ∧ Q.IsHomogeneous d ∧ MvPolynomial.aeval u Q = 0 := by
  intro E _ _ _ H Dw l Xo c a n m hm u hu
  classical
  obtain ⟨hL, -, h, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have htr := (GlobalTheory.FlagDim.fnFG_fnTrdeg E H Dw l Xo c).2
  haveI := CompFin.finite_comp Xo c
  haveI : Fintype (Comp Xo c) := Fintype.ofFinite _
  choose Q d hQ0 hQd hQv using fun Z : Comp Xo c =>
    exists_isHomogeneous_aeval_eq_zero (htr Z) hm (fun i => evC h Z (u i))
  have hhom : (∏ Z, Q Z).IsHomogeneous (∑ Z, d Z) := MvPolynomial.IsHomogeneous.prod _ _ _ fun Z _ => hQd Z
  refine ⟨∏ Z, Q Z, ∑ Z, d Z, Finset.prod_ne_zero_iff.2 fun Z _ => hQ0 Z, hhom, ?_⟩
  refine GlobalTheory.Reg.sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) _ _ _ (aeval_mem_sec u hu hhom) fun Z => ?_
  obtain ⟨ψ, hψ⟩ := exists_algHom_evR (genFr h Z) (hL.test _ _)
  have h1 : ψ (MvPolynomial.aeval u (Q Z)) = 0 := by
    rw [← hQv Z, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    exact congrArg (fun v => MvPolynomial.aeval v (Q Z)) (funext fun i => (hψ (u i)).symm)
  show evR Xo c _ (genFr h Z) = 0
  rw [hψ, map_prod, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ Z) h1

end GlobalTheory.SecRelation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogCardComponentsLeAtGoodEmbedding
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem log_card_comp_le : ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → 16 ≤ D.R.f → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → Real.log (Fintype.card (T.U j σ).Comp) ≤ 41 * Zb D large₂ ^ 2 := by
  intro D T h large₂ j hj w hP h2 hrn h16 σ hσ
  obtain ⟨hg, hlrd, hd, hcc, hf, -, -, -, hn⟩ := hP
  obtain ⟨-, -, -, -, -, hfd, hdE, -, -, -, hsk, hne, -⟩ := _root_.GlobalTheory.HostClear.host_clear D large₂.sc.L h2 hlrd hd hcc
  obtain ⟨AA, hFG, hA, hdual⟩ := _root_.GlobalTheory.principalDatum_trace_perfect D
  obtain ⟨-, -, hM, -, -, -, hJ⟩ := _root_.GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨-, hr, -⟩ := hJ j hj
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hrL : Real.log D.R.r ≤ large₂.sc.L :=
    le_trans (Real.log_le_log (by exact_mod_cast hr) (by exact_mod_cast hrn)) hn
  have hML : Real.log T.Q.l.M' ≤ 30 * large₂.sc.L := by
    rw [hM, hMg]
    have h0 := hg 0
    have h1 := hg 1
    rcases Nat.eq_zero_or_pos (D.host.g 0) with a | a
    · rw [a]; simp; linarith
    rcases Nat.eq_zero_or_pos (D.host.g 1) with b | b
    · rw [b]; simp; linarith
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast a.ne') (by exact_mod_cast b.ne')]
    linarith
  have key := GlobalTheory.log_card_comp_unf_le _root_.GlobalTheory.QNorm.hasseNormSt _root_.GlobalTheory.thetaUnifAV_all _root_.GlobalTheory.abelianSchemeLaws_all.1 D.host.E _ _ _ (T.Q.Xo j) T.Q.c σ D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hr hσ ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ hσ))
    D.host.xi0 AA hsk hne hFG hA hdual large₂.sc.L (by rw [hfd]; exact_mod_cast h16) h2 hdE hrL
    (by rw [hfd]; exact_mod_cast hf) hML
  rw [hfd] at key
  exact key

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SecBCAndCuspBC
section
set_option autoImplicit false

namespace GlobalTheory.FieldBC

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem secBC_and_cuspBC (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) :
    SecBC Xo hle ∧ ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), CuspBC hle U :=
  ⟨GlobalTheory.SecFieldChange.secBC_holds hle, fun _ U => GlobalTheory.SecFieldChange.cuspBC_holds hle U⟩

end GlobalTheory.FieldBC
end

