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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import Development.WeilBound.CoreStatements.AmpleLineBundles.IsPrincipalIffOfBaseChange
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartFactorsThrough
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.AbPartPull

theorem exists_sabMap_tK : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (m : SABMap t' t f) (K : Type) [Field K] (z : Sp K ⟶ S') (P : AbPart t (z ≫ f)), ∃ m' : SABMap P.tK t' z, m'.φ ≫ m.φ = P.m.φ := by
  intro E _ _ _ H S S' t' t f m K _ z P
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ t t' P.tK f z m P.m
  exact ⟨n, hn.symm⟩

end GlobalTheory.CompanionTheory.Ar.AbPartPull
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeTangentCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_tangent_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (X : Scheme.{0}) (t : SAB H X) (h : Sp C.R ⟶ X) (m : SABMap C.t t h) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (N : ℕ) (b : Fin N → Li) (x : Fin N → Fin C.g → C.R) (z : Fin n → ℂ) (Hm : Matrix (Fin C.g) (Fin C.g) ℂ) (w : Fin N → (epsAt (spMap (C.ψ z) ≫ h) ⟶ t.G)), C.IsRiem z Hm → (∀ k, M.ValAt _ (b k) (w k)) → (∀ k, (w k).left = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (x k)).left ≫ m.φ) → M.GramAt t.PP.L (spMap (C.ψ z) ≫ h) b (Matrix.of fun i j => (Real.pi : ℂ) * ((fun e => C.ψ z (x j e)) ⬝ᵥ Hm *ᵥ star (fun e => C.ψ z (x i e)))) := by
  intro E _ _ _ H D l Xo σ n a C X t h m Ω _ ξ Li _ _ M N b x z Hm w hR hval hw
  exact GlobalTheory.CompanionTheory.Ar.RiemGram.gramAt_of_isRiem E H D l Xo σ n a C X t h m Ω ξ Li M N b x z Hm w hR hval hw
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDvrThroughDiscPoint
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi _root_.GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.Flat

section Curve

variable {R : Type} [CommRing R] {n : ℕ} {ψ : (Fin n → ℂ) → (R →+* ℂ)} {z : Fin n → ℂ}

def diagLine (z : Fin n → ℂ) (T : ℂ) : Fin n → ℂ := fun i => z i + T

theorem diagLine_zero (z : Fin n → ℂ) : diagLine z 0 = z := by
  funext i; simp [diagLine]

theorem diagLine_mem_ball (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) {T : ℂ}
    (hT : T ∈ Metric.ball (0 : ℂ) (1 - ‖z‖)) : diagLine z T ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff] at hT ⊢
  rw [pi_norm_lt_iff one_pos]
  intro i
  have h₁ := norm_le_pi_norm z i
  calc ‖z i + T‖ ≤ ‖z i‖ + ‖T‖ := norm_add_le _ _
    _ < 1 := by linarith

theorem analyticOnNhd_diagLine (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) (x : R) :
    AnalyticOnNhd ℂ (fun T => ψ (diagLine z T) x) (Metric.ball (0 : ℂ) (1 - ‖z‖)) := by
  have hl : DifferentiableOn ℂ (diagLine z) (Metric.ball (0 : ℂ) (1 - ‖z‖)) :=
    (differentiable_pi.2 fun i => (differentiable_const (z i)).add differentiable_id).differentiableOn
  exact ((h.2 x).comp hl fun T hT => diagLine_mem_ball hz hT).analyticOnNhd Metric.isOpen_ball

theorem zero_mem_ball_norm (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (1 - ‖z‖) := by
  have := mem_ball_zero_iff.1 hz
  simpa using this

theorem analyticAt_diagLine (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) (x : R) :
    AnalyticAt ℂ (fun T => ψ (diagLine z T) x) 0 :=
  analyticOnNhd_diagLine h hz x 0 (zero_mem_ball_norm hz)

def taylorHom (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) : R →+* PowerSeries ℂ where
  toFun x := Formalism.L2.Th1.F.taylor0 (fun T => ψ (diagLine z T) x)
  map_one' := by
    simp only [map_one]
    rw [Formalism.L2.Th1.F.Taylor.taylor0_const, map_one]
  map_zero' := by
    simp only [map_zero]
    rw [Formalism.L2.Th1.F.Taylor.taylor0_const, map_zero]
  map_mul' x y := by
    simp only [map_mul]
    exact Formalism.L2.Th1.F.Taylor.taylor0_mul (analyticAt_diagLine h hz x) (analyticAt_diagLine h hz y)
  map_add' x y := by
    simp only [map_add (f := _)]
    exact Formalism.L2.Th1.F.Taylor.taylor0_add (analyticAt_diagLine h hz x) (analyticAt_diagLine h hz y)

theorem constantCoeff_comp_taylorHom (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    (PowerSeries.constantCoeff (R := ℂ)).comp (taylorHom h hz) = ψ z := by
  ext x
  have e := Formalism.L2.Th1.F.Taylor.coeff_taylor0 (fun T => ψ (diagLine z T) x) 0
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, diagLine_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] at e
  exact e

theorem eq_zero_of_taylorHom (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) {x : R}
    (hx : taylorHom h hz x = 0) {T : ℂ} (hT : T ∈ Metric.ball (0 : ℂ) (1 - ‖z‖)) : ψ (diagLine z T) x = 0 := by
  have h₀ : Formalism.L2.Th1.F.taylor0 (fun T => ψ (diagLine z T) x) = Formalism.L2.Th1.F.taylor0 (fun _ => (0 : ℂ)) := by
    rw [Formalism.L2.Th1.F.Taylor.taylor0_const, map_zero]
    exact hx
  have he := Formalism.L2.Th1.F.Taylor.taylor0_inj (analyticAt_diagLine h hz x) analyticAt_const h₀
  exact (analyticOnNhd_diagLine h hz x).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected (zero_mem_ball_norm hz) he hT

theorem exists_diagLine_mem_punct (a : ℕ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    ∃ T ∈ Metric.ball (0 : ℂ) (1 - ‖z‖), diagLine z T ∈ punct n a 1 := by
  have hinf : (Metric.ball (0 : ℂ) (1 - ‖z‖)).Infinite :=
    infinite_of_mem_nhds 0 (Metric.isOpen_ball.mem_nhds (zero_mem_ball_norm hz))
  obtain ⟨T, hT, hn⟩ := hinf.exists_notMem_finset (Finset.univ.image fun i : Fin n => -z i)
  refine ⟨T, hT, diagLine_mem_ball hz hT, fun i _ he => hn ?_⟩
  refine Finset.mem_image.2 ⟨i, Finset.mem_univ _, ?_⟩
  have : z i + T = 0 := he
  linear_combination -this

end Curve

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem range_jK_taylorHom_subset {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : Flat.BdryChart Xo σ n a)
    {z : Fin n → ℂ} (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    Set.range (Out.jK (PowerSeries ℂ) ≫ spMap (taylorHom C.hol hz)) ⊆ Set.range C.j := by
  have := C.j_open
  rintro _ ⟨q, rfl⟩
  obtain ⟨T, hT, hp⟩ := exists_diagLine_mem_punct a hz
  obtain ⟨s⟩ : Nonempty (Sp ℂ) := inferInstance
  have hw : spMap (C.ψ (diagLine z T)) s ∈ Set.range C.j :=
    ⟨C.pt (diagLine z T) s, by rw [← (C.pt_eq _ hp).1, Scheme.Hom.comp_apply]⟩
  refine Specializes.mem_open ?_ C.j.isOpenEmbedding.isOpen_range hw
  refine (PrimeSpectrum.le_iff_specializes _ _).1 fun x hx => ?_
  have hq : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top
  rw [Scheme.Hom.comp_apply] at hx
  have h₁ : algebraMap (PowerSeries ℂ) (FractionRing (PowerSeries ℂ)) (taylorHom C.hol hz x) ∈ q.asIdeal := hx
  rw [hq, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h₁
  have h₂ : C.ψ (diagLine z T) x = 0 := eq_zero_of_taylorHom C.hol hz h₁ hT
  show C.ψ (diagLine z T) x ∈ s.asIdeal
  rw [h₂]
  exact Ideal.zero_mem _

section Pulled

open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem polAt_of_pulled {S S' X : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {K : Type} [Field K] {tK : SAB H (Sp K)} {j : Sp K ⟶ S} (mK : SABMap tK t j)
    {u : SAB H X} {x : Sp K ⟶ X} (mx : SABMap tK u x) (hp : IsProper u.G.hom) (ha : Out.RelAmple u.G u.PP.L)
    (hk : Out.KTriv u.G u.PP.L) (j' : Sp K ⟶ S') (h : j' ≫ f = j) : GlobalTheory.LN.PolAt t' j' := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull j' t'
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₂
  have cancel : ∀ (t₂ : SAB H (Sp K)) (p : Sp K ⟶ S) (_ : p = 𝟙 _ ≫ j) (_ : SABMap t₂ t p),
      Nonempty (SABMap t₂ u (𝟙 _ ≫ x)) := by
    intro t₂ p hp n
    subst hp
    exact ⟨(sabComp pullCubComp E H _ _ _ _ _ _ _ _ mx
      (sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mK n).choose).choose⟩
  obtain ⟨m₃⟩ := cancel _ _ (h.trans (Category.id_comp _).symm) n
  have h₂ : LBIso PP'.L (t'.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (u.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull t'.PP.isLB (pullback.fst t'.G.hom j')
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 hp,
    amplePt _ _ (𝟙 _ ≫ x) _ _ m₃.φ m₃.cart _ _ u.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull u.PP.isLB _) h₂.symm h₃) ha hk⟩

end Pulled

theorem exists_curve_through_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (z : Fin n → ℂ), z ∈ Metric.ball (0 : Fin n → ℂ) 1 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : C.R →+* V) (r : V →+* ℂ) (tV : SAB H (Sp V)) (_ : SABMap tV C.t (spMap f)), GlobalTheory.LN.CDvr V ∧ Function.Surjective r ∧ RingHom.ker r = IsLocalRing.maximalIdeal V ∧ r.comp f = C.ψ z ∧ GlobalTheory.LN.PolAt tV (Out.jK V) := by
  intro E _ _ _ H D l Xo σ n a C z hz
  have := C.j_open
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (taylorHom C.hol hz)) C.t
  have hc : GlobalTheory.LN.CDvr (PowerSeries ℂ) :=
    ⟨inferInstance, by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance, algebraRat.charZero _⟩
  have hsurj : Function.Surjective (PowerSeries.constantCoeff (R := ℂ)) := fun c =>
    ⟨PowerSeries.C c, by simp⟩
  refine ⟨PowerSeries ℂ, inferInstance, inferInstance, inferInstance, taylorHom C.hol hz,
    PowerSeries.constantCoeff (R := ℂ), _, m, hc, hsurj, ?_, constantCoeff_comp_taylorHom C.hol hz, ?_⟩
  · have := RingHom.ker_isMaximal_of_surjective _ hsurj
    exact IsLocalRing.eq_maximalIdeal this
  · have hr := range_jK_taylorHom_subset C hz
    let y := IsOpenImmersion.lift C.j _ hr
    have hy : y ≫ C.j = Out.jK (PowerSeries ℂ) ≫ spMap (taylorHom C.hol hz) := IsOpenImmersion.lift_fac _ _ _
    obtain ⟨_, _, _, _, _, m₀, -⟩ := sabPull Out.CubePf.cubePull y C.tV
    obtain ⟨mK, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m₁ m₀
    obtain ⟨mx, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m₂ m₀
    exact polAt_of_pulled m mK mx Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (Out.jK (PowerSeries ℂ)) hy.symm

end GlobalTheory.CompanionTheory.Ar.QuotLoc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermJetLiftStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_germ_jet_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (xk : ∀ m, Sp (Jet k (Fin 1 × Fin d) m) ⟶ pullback t.G.hom x), (∀ m, xk m ≫ pullback.fst _ _ = (g.x m).left) → (∀ m, xk m ≫ pullback.snd _ _ = spMap (algebraMap k _)) → ∃ _ : IsIntegral (pullback t.G.hom x), IsNormalScheme (pullback t.G.hom x) ∧ CharP (pullback t.G.hom x).functionField p ∧ ∀ (U : (pullback t.G.hom x).Opens) (hU : ∀ m, ⊤ ≤ xk m ⁻¹ᵁ U) [Nonempty U] (f : Γ(pullback t.G.hom x, U)), ∃ F : MvPowerSeries (Fin 1 × Fin d) k, (∀ m, ((xk m).appLE U ⊤ (hU m)).hom f = toΓ _ (psJet m F)) ∧ (F = 0 → f = 0) ∧ ((∀ q, MvPowerSeries.pderiv (R := k) q F = 0) → ∃ r : (pullback t.G.hom x).functionField, r ^ p = ((pullback t.G.hom x).germToFunctionField U).hom f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FibreTaylor.fibre_taylor_expansion | exact GlobalTheory.CompanionTheory.Ar.FibreTaylor.fibre_taylor_expansion | (intros; apply GlobalTheory.CompanionTheory.Ar.FibreTaylor.fibre_taylor_expansion <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrincipalBaseChangeIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem isPrincipal_iff_of_sabMap_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L L' : Type) [Field L] [Field L'] (e : L →+* L') (t : SAB H (Sp L)) (t' : SAB H (Sp L')) (_ : SABMap t' t (spMap e)), IsPrincipal t' ↔ IsPrincipal t := by
  exact @CoverDenseAlt.isPrincipal_iff_of_base_change

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeIsoCompat
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GMove

section Ring

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

theorem dualMap_algebraMap (f : R →+* S) :
    (dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap S (DualNumber S)).comp f := by
  ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fstHom_dualMap (f : R →+* S) :
    (TrivSqZeroExt.fstHom S S S).toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom :=
  RingHom.ext fun x => by simp [dualMap]

theorem dualMap_comp (f : R →+* S) (g : S →+* T) : dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  ext x <;> simp [dualMap]

theorem specMap_comp (f : R →+* S) (g : S →+* T) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← Spec.map_comp]; rfl

end Ring

section Scheme

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω]

theorem specializes_of_iso (e : X' ≅ X) {a b : X'} (h : e.hom a ⤳ e.hom b) : a ⤳ b := by
  have := h.map e.inv.continuous
  simpa using this

theorem genMap_stalkMap_eq (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (q : Cpt ξ')
    (h : genPt (ξ' ≫ g) ⤳ g q.1) (s : X.presheaf.stalk (g q.1)) :
    genMap ξ' q ((g.stalkMap q.1).hom s) = genMap (ξ' ≫ g) ⟨g q.1, h⟩ s := by
  have e := Scheme.Hom.stalkSpecializes_stalkMap g _ _ q.2
  have e2 := congrArg (fun t => (t ≫ Scheme.stalkClosedPointTo ξ').hom s) e
  have e3 := Scheme.stalkClosedPointTo_comp ξ' g
  have e4 := congrArg (fun t => (X.presheaf.stalkSpecializes h ≫ t).hom s) e3
  exact e2.symm.trans e4.symm

theorem eta_comp {G : Over X} [GrpObj G] {G' : Over X'} [GrpObj G'] (f : X' ⟶ X) (φ : G'.left ⟶ G.left)
    (h : IsGrpPullback G' G f φ) : η[G'].left ≫ φ = f ≫ η[G].left := by
  have hw := h.1.w
  let x₀ : Over.mk ((Over.mk (𝟙 X')).hom ≫ f) ⟶ G :=
    Over.homMk ((1 : Over.mk (𝟙 X') ⟶ G').left ≫ φ) (by
      rw [Category.assoc, hw, ← Category.assoc, Over.w]; simp)
  have hm := h.2 (Over.mk (𝟙 X')) 1 1 x₀ x₀ rfl rfl
  have hx : x₀ * x₀ = x₀ := by
    ext1
    rw [hm, _root_.mul_one]
    rfl
  have h1 : x₀ = 1 := by simpa using hx
  have h2 := congrArg (fun u => u.left) h1
  simpa [x₀, Hom.one_def] using h2

end Scheme

section Move

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]

theorem valAt_up (e : X' ≅ X) {G : Over X} [GrpObj G] {G' : Over X'} [GrpObj G'] (φ : G'.left ≅ G.left)
    (hw : φ.hom ≫ G.hom = G'.hom ≫ e.hom) (hη : η[G'].left ≫ φ.hom = e.hom ≫ η[G].left)
    {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω ⟶ X'} (M : LieModel G ξ V) (M' : LieModel G' ξ' V) (hξ : ξ' ≫ e.hom = ξ)
    (hpt : ∀ v, (M'.pt v).left ≫ φ.hom = (M.pt v).left)
    {z : Sp ℂ ⟶ X'} {z₀ : Sp ℂ ⟶ X} (hz : z ≫ e.hom = z₀) {b : V} {w : epsAt z₀ ⟶ G} {w' : epsAt z ⟶ G'}
    (hww : w'.left ≫ φ.hom = w.left) : M.ValAt z₀ b w → M'.ValAt z b w' := by
  subst hξ hz
  rintro ⟨h, v, ⟨hvt, hve⟩, hvw⟩
  have h' : genPt ξ' ⤳ centre z := specializes_of_iso e h
  change e.hom (genPt ξ') ⤳ e.hom (centre z) at h
  change epsAt (R := X.presheaf.stalk (e.hom (centre z))) (X.fromSpecStalk (e.hom (centre z))) ⟶ G at v
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk (e.hom (centre z)))
      (X.presheaf.stalk (e.hom (centre z))) (X.presheaf.stalk (e.hom (centre z)))).toRingHom) ≫ v.left =
      (1 : Over.mk (X.fromSpecStalk (e.hom (centre z))) ⟶ G).left at hvt
  change (M.pt b).left = Spec.map (CommRingCat.ofHom (dualMap (genMap (ξ' ≫ e.hom) ⟨e.hom (centre z), h⟩))) ≫
      v.left at hve
  change w.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo (z ≫ e.hom)).hom)) ≫ v.left at hvw
  have hφ : φ.inv ≫ G'.hom = G.hom ≫ e.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hw, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hη' : e.hom ≫ η[G].left ≫ φ.inv = η[G'].left := by
    rw [← Category.assoc, ← hη, Category.assoc, φ.hom_inv_id, Category.comp_id]
  have hv : v.left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (e.hom (centre z)))
      (DualNumber (X.presheaf.stalk (e.hom (centre z)))))) ≫ X.fromSpecStalk (e.hom (centre z)) := Over.w v
  have hσ : Spec.map (e.hom.stalkMap (centre z)) ≫ X.fromSpecStalk (e.hom (centre z)) =
      X'.fromSpecStalk (centre z) ≫ e.hom := Scheme.SpecMap_stalkMap_fromSpecStalk e.hom
  have k1 : Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (e.hom (centre z)))
        (DualNumber (X.presheaf.stalk (e.hom (centre z)))))) =
      Spec.map (CommRingCat.ofHom (algebraMap (X'.presheaf.stalk (centre z))
        (DualNumber (X'.presheaf.stalk (centre z))))) ≫ Spec.map (e.hom.stalkMap (centre z)) := by
    rw [specMap_comp, dualMap_algebraMap, ← specMap_comp]
    rfl
  let v' : epsAt (R := X'.presheaf.stalk (centre z)) (X'.fromSpecStalk (centre z)) ⟶ G' :=
    Over.homMk (Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) ≫ v.left ≫ φ.inv) (by
      show _ ≫ (v.left ≫ φ.inv) ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap (X'.presheaf.stalk (centre z))
        (DualNumber (X'.presheaf.stalk (centre z))))) ≫ X'.fromSpecStalk (centre z)
      rw [Category.assoc, hφ, reassoc_of% hv]
      show Spec.map _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (e.hom (centre z)))
        (DualNumber (X.presheaf.stalk (e.hom (centre z)))))) ≫ X.fromSpecStalk (e.hom (centre z))) ≫ e.inv = _
      rw [← Category.assoc, ← Category.assoc]
      erw [k1]
      erw [Category.assoc, Category.assoc, reassoc_of% hσ, e.hom_inv_id, Category.comp_id]
      rfl)
  have hv' : v'.left = Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) ≫ v.left ≫ φ.inv := rfl
  refine ⟨h', v', ⟨?_, ?_⟩, ?_⟩
  · have e1 : (1 : Over.mk (X'.fromSpecStalk (centre z)) ⟶ G').left = X'.fromSpecStalk (centre z) ≫ η[G'].left := by
      simp [Hom.one_def]
    have e2 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk (e.hom (centre z)))
        (X.presheaf.stalk (e.hom (centre z))) (X.presheaf.stalk (e.hom (centre z)))).toRingHom) ≫ v.left =
        X.fromSpecStalk (e.hom (centre z)) ≫ η[G].left := by
      rw [hvt]
      simp [Hom.one_def]
    have k2 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X'.presheaf.stalk (centre z))
        (X'.presheaf.stalk (centre z)) (X'.presheaf.stalk (centre z))).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (e.hom.stalkMap (centre z)).hom)) =
        Spec.map (e.hom.stalkMap (centre z)) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom
        (X.presheaf.stalk (e.hom (centre z))) (X.presheaf.stalk (e.hom (centre z)))
        (X.presheaf.stalk (e.hom (centre z)))).toRingHom) := by
      rw [specMap_comp, fstHom_dualMap, ← specMap_comp]
      rfl
    show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X'.presheaf.stalk (centre z))
        (X'.presheaf.stalk (centre z)) (X'.presheaf.stalk (centre z))).toRingHom) ≫ v'.left =
        (1 : Over.mk (X'.fromSpecStalk (centre z)) ⟶ G').left
    rw [hv', e1, ← hη', ← reassoc_of% hσ, ← reassoc_of% e2, reassoc_of% k2]
    rfl
  · have k3 : Spec.map (CommRingCat.ofHom (dualMap (genMap ξ' ⟨centre z, h'⟩))) ≫
        Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) =
        Spec.map (CommRingCat.ofHom (dualMap (genMap (ξ' ≫ e.hom) ⟨e.hom (centre z), h⟩))) := by
      have hg : (genMap ξ' ⟨centre z, h'⟩).comp (e.hom.stalkMap (centre z)).hom =
          genMap (ξ' ≫ e.hom) ⟨e.hom (centre z), h⟩ :=
        RingHom.ext (genMap_stalkMap_eq ξ' e.hom ⟨centre z, h'⟩ h)
      rw [specMap_comp, ← dualMap_comp, hg]
    show (M'.pt b).left = Spec.map (CommRingCat.ofHom (dualMap (genMap ξ' ⟨centre z, h'⟩))) ≫ v'.left
    rw [(Iso.eq_comp_inv φ).2 (hpt b), hve, hv', reassoc_of% k3]
    exact Category.assoc _ _ _
  · have k4 : Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫
        Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) =
        Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo (z ≫ e.hom)).hom)) := by
      refine (specMap_comp (dualMap (e.hom.stalkMap (centre z)).hom) (dualMap (Scheme.stalkClosedPointTo z).hom)).trans ?_
      rw [Scheme.stalkClosedPointTo_comp]
      exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (dualMap_comp _ _).symm
    rw [(Iso.eq_comp_inv φ).2 hww, hvw, hv', ← k4]
    erw [Category.assoc, Category.assoc]

end Move


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem gramAt_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (e : X' ≅ X)
    (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (k : SABMap t' t e.hom)
    (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V),
    ξ' ≫ e.hom = ξ → (∀ v, (M'.pt v).left ≫ k.φ = (M.pt v).left) →
    ∀ (z : Sp ℂ ⟶ X') (r : ℕ) (b : Fin r → V) (Γ : Matrix (Fin r) (Fin r) ℂ),
      M'.GramAt t'.PP.L z b Γ ↔ M.GramAt t.PP.L (z ≫ e.hom) b Γ := by
  intro E _ _ _ H X X' e Ω _ ξ ξ' t t' k V _ _ M M' hξ hpt z r b Γ
  haveI : IsIso k.φ := k.cart.1.isIso_fst_of_isIso
  let φ : t'.G.left ≅ t.G.left := asIso k.φ
  have hw : φ.hom ≫ t.G.hom = t'.G.hom ≫ e.hom := k.cart.1.w
  have hη : η[t'.G].left ≫ φ.hom = e.hom ≫ η[t.G].left := eta_comp e.hom k.φ k.cart
  have hw' : φ.symm.hom ≫ t'.G.hom = t.G.hom ≫ e.symm.hom := by
    show φ.inv ≫ _ = _ ≫ e.inv
    rw [Iso.inv_comp_eq, ← Category.assoc, hw, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hη' : η[t.G].left ≫ φ.symm.hom = e.symm.hom ≫ η[t'.G].left := by
    show _ ≫ φ.inv = e.inv ≫ _
    rw [Iso.eq_inv_comp, ← reassoc_of% hη, φ.hom_inv_id, Category.comp_id]
  have hpt' : ∀ v, (M.pt v).left ≫ φ.symm.hom = (M'.pt v).left := fun v => by
    show _ ≫ φ.inv = _
    rw [← hpt v, Category.assoc]
    erw [φ.hom_inv_id]
    exact Category.comp_id _
  have hξ' : ξ ≫ e.symm.hom = ξ' := by rw [← hξ]; simp
  constructor
  · rintro ⟨v', hval, hip⟩
    let v : Fin r → (epsAt (z ≫ e.hom) ⟶ t.G) := fun i => Over.homMk ((v' i).left ≫ k.φ) (by
      have h1 := Over.w (v' i)
      rw [Category.assoc, k.cart.1.w, ← Category.assoc, h1]
      simp [epsAt])
    refine ⟨v, fun i => ?_, fun p q => ?_⟩
    · refine valAt_up e.symm φ.symm hw' hη' M' M hξ' hpt' (z := z ≫ e.hom) (z₀ := z) (by simp) ?_ (hval i)
      show ((v' i).left ≫ k.φ) ≫ φ.inv = _
      simp [φ]
    · exact (_root_.GlobalTheory.CompanionTheory.Ar.HodgePullBack.hodgeInnerProduct_iff_of_abelianSchemeMap E H X X' t t' e.hom k z (v' p) (v' q) (v p) (v q) (Γ p q) rfl rfl).1 (hip p q)
  · rintro ⟨v, hval, hip⟩
    let v' : Fin r → (epsAt z ⟶ t'.G) := fun i => Over.homMk ((v i).left ≫ φ.inv) (by
      have h1 := Over.w (v i)
      rw [Category.assoc, ← Iso.symm_hom, hw', ← Category.assoc, h1]
      simp [epsAt])
    have hv' : ∀ i, (v' i).left ≫ k.φ = (v i).left := fun i => by
      show ((v i).left ≫ φ.inv) ≫ φ.hom = _
      simp
    refine ⟨v', fun i => ?_, fun p q => ?_⟩
    · exact valAt_up e φ hw hη M M' hξ hpt (z := z) (z₀ := z ≫ e.hom) rfl (hv' i) (hval i)
    · exact (_root_.GlobalTheory.CompanionTheory.Ar.HodgePullBack.hodgeInnerProduct_iff_of_abelianSchemeMap E H X X' t t' e.hom k z (v' p) (v' q) (v p) (v q) (Γ p q) (hv' p) (hv' q)).2 (hip p q)

end GlobalTheory.CompanionTheory.Ar.GMove
end
end

