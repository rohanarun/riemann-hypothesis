module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffInvariantOperatorAlongMatrix
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantDvdTraceOfJacobianFiniteColength
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DetJacobianFormalModuleMatrixEqConstMulUnit
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRamifiedEigenLiftsOfChartDirections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupPointsOfIntegralChartSpec
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0039
public import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RegularSectionIntegralGermUniqueScale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsOfCubeBundleGenerator
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankSectionsLineBundlePowEqPow
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecMInvariantEqBotOrUnivAtGeometricPoint
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffInvariantOperatorAlongMatrixStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_invariant_operator_along_matrix : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] (n : ℕ) (mu : Matrix (Fin n) (Fin n) O) (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (σ : Ty → O →+* K) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → K), (∀ ℓ a, (dAct K B a).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → ∀ (P : MvPolynomial (Letter Ty r n) K) (g : PS K n d), MvPowerSeries.constantCoeff (DpolyN (B.FK K) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) P (ev (n := n) (fun b i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)) g)) = MvPowerSeries.constantCoeff (DpolyN (B.FK K) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.aeval (fun ℓ : Letter Ty r n => ∑ b, MvPolynomial.C (σ ℓ.1 (mu b ℓ.2.2)) * MvPolynomial.X (⟨ℓ.1, ℓ.2.1, b⟩ : Letter Ty r n)) P) g) := by
  first | exact @GlobalTheory.MatChain.constantCoeff_dpolyN_matV | exact GlobalTheory.MatChain.constantCoeff_dpolyN_matV | (intros; apply GlobalTheory.MatChain.constantCoeff_dpolyN_matV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantDvdTraceOfJacobianFiniteColengthStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_dvd_trace_of_jacobian_finite_colength : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (σ : Type) [Fintype σ] [DecidableEq σ] (φ : σ → MvPowerSeries σ V), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField V))) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue V) (φ j))) → ∀ (δ : V) (U : (MvPowerSeries σ V)ˣ), δ ≠ 0 → Matrix.det (Matrix.of fun i j : σ => MvPowerSeries.pderiv (R := V) j (φ i)) = MvPowerSeries.C δ * (U : MvPowerSeries σ V) → ∀ (r : ℕ) (b : Fin r → MvPowerSeries σ V), (∀ f, ∃! cf : Fin r → MvPowerSeries σ V, f = ∑ i, MvPowerSeries.subst φ (cf i) * b i) → ∀ (f : MvPowerSeries σ V) (M : Matrix (Fin r) (Fin r) (MvPowerSeries σ V)), (∀ j, f * b j = ∑ i, MvPowerSeries.subst φ (M i j) * b i) → MvPowerSeries.C δ ∣ M.trace := by
  first | exact @GlobalTheory.C_dvd_trace_of_jacobian | exact GlobalTheory.C_dvd_trace_of_jacobian | (intros; apply GlobalTheory.C_dvd_trace_of_jacobian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DetJacobianFormalModuleMatrixEqConstMulUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_jacobian_formal_module_matrix_eq_const_mul_unit : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (n : ℕ) (p : Matrix (Fin n) (Fin n) O), ∃ U : (PS V n d)ˣ, Matrix.det (Matrix.of fun i j : Fin n × Fin d => MvPowerSeries.pderiv (R := V) j (matV B p (fun j => pt V (n := n) d j) i.1 i.2)) = MvPowerSeries.C (jacM B p) * (U : PS V n d) := by
  first | exact @GlobalTheory.PlaceInt.MatJac.det_jacobian_matV | exact GlobalTheory.PlaceInt.MatJac.det_jacobian_matV | (intros; apply GlobalTheory.PlaceInt.MatJac.det_jacobian_matV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRamifiedEigenLiftsOfChartDirectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ramified_eigen_lifts_of_chart_directions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), IsGalois ℚ E → ∀ (p a m : ℕ), p.Prime → ¬ IsUnit (p : T.V) → ¬ p ∣ m → (NumberField.discr E).natAbs = p ^ a * m → (∀ 𝔭 : Ideal (𝓞 E), 𝔭.IsPrime → (p : 𝓞 E) ∈ 𝔭 → ∃ x ∈ 𝔭, H.bar x ∉ 𝔭) → ∀ e : ℕ, 0 < e → letI := io.toAlgebra; ∃ (π : Type) (_ : Fintype π) (_ : DecidableEq π) (cc : (E →+* ℂ) → π) (s : (E →+* ℂ) → Bool), (∀ τ, cc (ComplexEmbedding.conjugate τ) = cc τ ∧ s (ComplexEmbedding.conjugate τ) ≠ s τ) ∧ ∃ (φ : Lt1 Dw → Fin (chD C.ch) → T.V) (ψ : Lt1 Dw → Fin (chD C.ch) → T.Fr), (∀ ℓ i, (((-((vV T.V (p : T.Fr) : ℝ) / e * ((a : ℝ) / Module.finrank ℚ E))) : ℝ) : EReal) ≤ nval T.V e (ψ ℓ i)) ∧ (∀ ℓ ℓ' : Lt1 Dw, ℓ'.1 ≠ ComplexEmbedding.conjugate ℓ.1 → ∑ i, (algebraMap T.V T.Fr (φ ℓ' i) + ψ ℓ' i - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ') i) * C.ch.uvec ℓ i = 0) ∧ TB.OppositePairVanishing T.Fr (fun ℓ : Lt1 Dw => cc ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap T.V T.Fr (φ ℓ i) - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap T.V T.Fr (φ ℓ i) - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) ∧ TB.OppositePairVanishing T.Fr (fun ℓ : Lt1 Dw => cc ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (0, ψ ℓ)) (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap T.V T.Fr (φ ℓ i) - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) ∧ TB.OppositePairVanishing T.Fr (fun ℓ : Lt1 Dw => cc ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap T.V T.Fr (φ ℓ i) - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) (fun ℓ => (0, ψ ℓ)) := by
  first | exact @GlobalTheory.PlaceInt.exists_ramified_eigenLifts | exact GlobalTheory.PlaceInt.exists_ramified_eigenLifts | (intros; apply GlobalTheory.PlaceInt.exists_ramified_eigenLifts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueIntegralPointEqValueOnBiextensionCoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicValue_integralPoint_eq_value_on_biextensionCopies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → ∀ (k n : ℕ) (F : Fin n → SecN Xo (xOf y) k) (f : Fin n → PS T.V 1 (chD C.ch)), (∀ b, GermIs C k (F b) (f b)) → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → letI := io.toAlgebra; hv Xo c nab y.1 k F P = nabValN B T.Fr (gaugeOf C) H.w0 k (FB.toK T.Fr (∏ b, evV (n := n) ![pt T.V (chD C.ch) b] (f b))) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) := by
  first | exact @GlobalTheory.PlaceInt.hv_eq_nabValN | exact GlobalTheory.PlaceInt.hv_eq_nabValN | (intros; apply GlobalTheory.PlaceInt.hv_eq_nabValN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.KillsFormalPointsIffMemCoordinateKernel
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.FormKer

lemma cpt_const {V : Type} [CommRing V] {d : ℕ} (x : Pt V 0 d) :
    (cpt (fun i => MvPowerSeries.constantCoeff (x i)) : Pt V 0 d) = x := by
  funext i
  ext m

  obtain rfl : m = 0 := Subsingleton.elim _ _
  simp [cpt]

lemma rel_prod {M P : Type*} [Monoid M] (R : M → P → Prop) (z : P) (s : P → P → P) (h1 : R 1 z)
    (hm : ∀ a a' x x', R a x → R a' x' → R (a * a') (s x x')) :
    ∀ (n : ℕ) (f : Fin n → M) (g : Fin n → P), (∀ j, R (f j) (g j)) →
      R (List.ofFn f).prod ((List.ofFn g).foldr s z) := by
  intro n
  induction n with
  | zero => intro f g _; simpa using h1
  | succ n ih =>
    intro f g hfg
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.foldr_cons]
    exact hm _ _ _ _ (hfg 0) (ih _ _ fun j => hfg j.succ)

theorem kills_iff_mem_kerM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → ∀ (n : ℕ) (mu : Matrix (Fin n) (Fin n) (𝓞 E)) (a : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (α : Fin n → Fin (chD C.ch) → T.V), (∀ b, FormPt C (a b) (α b)) → (Kills Xo mu a ↔ α ∈ kerM B mu) := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C B hB n mu a α hα
  obtain ⟨h1, hinj, hmul, hact, -⟩ := _root_.GlobalTheory.PlaceFormPt.formPt_spec E H Dw l Xo c hstar T io y C B hB

  have h0 : (0 : Pt T.V 0 (chD C.ch)) = cpt 0 := by
    funext k
    simp [cpt]
  have hstep : ∀ (g g' : ptO Xo (xOf y) ⟶ Xo.univ.t.G) (x x' : Pt T.V 0 (chD C.ch)),
      (∃ δ, x = cpt δ ∧ FormPt C g δ) → (∃ δ, x' = cpt δ ∧ FormPt C g' δ) →
        ∃ δ, addV B.G.F x x' = cpt δ ∧ FormPt C (g * g') δ := by
    rintro g g' x x' ⟨al, rfl, hg⟩ ⟨al', rfl, hg'⟩
    exact ⟨_, (cpt_const _).symm, hmul g g' al al' _ hg hg' (cpt_const _)⟩
  have key : ∀ i, ∃ δ : Fin (chD C.ch) → T.V,
      matV B (m := 0) mu (fun j => cpt (α j)) i = cpt δ ∧
        FormPt C (List.ofFn fun j => a j ≫ Xo.univ.t.act.act (mu i j)).prod δ := by
    intro i
    have hrow : ∀ j, ∃ δ, compV (B.A.act (mu i j)) (cpt (α j)) = cpt δ ∧
        FormPt C (a j ≫ Xo.univ.t.act.act (mu i j)) δ := fun j =>
      ⟨_, (cpt_const _).symm, hact (a j) (α j) _ (mu i j) (hα j) (cpt_const _)⟩
    exact rel_prod (fun g x => ∃ δ, x = cpt δ ∧ FormPt C g δ) 0 (addV B.G.F) ⟨0, h0, h1⟩
      hstep n (fun j => a j ≫ Xo.univ.t.act.act (mu i j))
      (fun j => compV (B.A.act (mu i j)) (cpt (α j))) hrow
  have hcpt : ∀ δ : Fin (chD C.ch) → T.V, cpt (n := 0) δ = 0 → δ = 0 := by
    intro δ h
    funext k
    have := congrArg MvPowerSeries.constantCoeff (congrFun h k)
    simpa [cpt] using this
  simp only [Kills, kerM, Set.mem_ofPred_eq]
  constructor
  · intro hk
    refine ⟨fun b => (hα b).1, funext fun i => ?_⟩
    obtain ⟨δ, hm, hF⟩ := key i
    obtain rfl : δ = 0 := (hinj _ 1 δ 0 hF h1).mp (hk i)
    rw [hm, ← h0]
    rfl
  · rintro ⟨-, hz⟩ i
    obtain ⟨δ, hm, hF⟩ := key i
    have hδ : δ = 0 := hcpt δ (by rw [← hm]; exact congrFun hz i)
    subst hδ
    exact (hinj _ 1 0 0 hF h1).mpr rfl

end GlobalTheory.PlaceInt.FormKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LatticeTrivialAtPrimeIndicesAndUnitsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_trivial_at_prime_indices_and_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.Unimod → Λ.LevOK N M → ℓ.Prime → Λ.TrivAt ℓ → (Λ.zCard N (Dw.p + Dw.q)).factorization ℓ = (Λ.mIdx N (Dw.p + Dw.q)).factorization ℓ ∧ Λ.mIdx N (Dw.p + Dw.q) ≠ 0 ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr), ¬ IsUnit (ℓ : T.V) → (∀ β : c.F, β ≠ 0 → BetaIs (Dw := Dw) c Λ β → vV T.V (io β) = 0) ∧ ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → MvPolynomial.map io P ∈ FFV (Dw := Dw) T w n := by
  first | exact @GlobalTheory.TrivLattice.trivAt_units | exact GlobalTheory.TrivLattice.trivAt_units | (intros; apply GlobalTheory.TrivLattice.trivAt_units <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RamifiedPrimeLossLeValuationPrimePowerStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramified_prime_loss_le_valuation_prime_power : ∀ (D : D7) (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (j : ℕ) (w : WeightFamilies.Wt D j) (a b : ℕ), c2 D w ≤ a → Formalism.MainNotions.DIV.Cons.cHalf w ≤ b → ramLoss D la w ≤ ((vLa la ((pPow D a b b : ℕ) : K) : ℤ) : ℝ) := by
  first | exact @GlobalTheory.PlaceTop.ramLoss_le_vLa_pPow | exact GlobalTheory.PlaceTop.ramLoss_le_vLa_pPow | (intros; apply GlobalTheory.PlaceTop.ramLoss_le_vLa_pPow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RegularSectionIntegralGermUniqueScaleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_section_integral_germ_unique_scale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (k : ℕ) (F : SecN Xo (xOf y) k), (Regular C k F → ∃ f, GermIs C k F f) ∧ (∀ f f', GermIs C k F f → GermIs C k F f' → f = f') ∧ ∀ (F' : SecN Xo (xOf y) k) (r : T.V) (f : PS T.V 1 (chD C.ch)), (∀ j, F'.f j = liftFun Xo.univ.t.G _ (T := ptO Xo (xOf y)) (toΓ T.Fr (algebraMap T.V T.Fr r)) * F.f j) → GermIs C k F f → GermIs C k F' (r • f) := by
  first | exact @GlobalTheory.RegularGerm.regular_germ | exact GlobalTheory.RegularGerm.regular_germ | (intros; apply GlobalTheory.RegularGerm.regular_germ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TwistBaseChangeOfFinrankSectionsOne
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem twistBaseChange_of_finrank_sections_one :
    (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))),
      Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
        (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) = 1) → DVR.TwistBaseChangeStatement := by
  intro h1
  obtain ⟨hGF, -, hBC, -, -⟩ := _root_.GlobalTheory.laws_without_cohomology
  obtain ⟨hcube, -, hgrow⟩ := _root_.GlobalTheory.AbLaw.CubeAssembly.cube_and_sections
  obtain ⟨-, -, -, -, -, -, -, -, hmulq, hrel⟩ := _root_.GlobalTheory.AbLaw.FromCube.all_of_cubeGen hcube
  have hproj := GlobalTheory.AbLaw.polAV_veryAmpleBy hBC
  have hmul := (GlobalTheory.MulPull.mulPull_of_cube_of_symm hcube (GlobalTheory.exists_gen_negLB hGF)).1
  have hvan := GlobalTheory.AbLaw.PowVanish.first_cohomology_vanishes_powers hproj _root_.GlobalTheory.AbLaw.serre_h1Zero_and_sections_polynomial.1 GlobalTheory.AbLaw.h1Zero_of_isIso hmul hmulq
    (GlobalTheory.torsion_invariant_descends hmulq)
  have h0 := GlobalTheory.FinrankGrowthBounds.finrank_sections_lineBundlePow_eq_pow
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected h1 hrel hgrow hmulq
  exact GlobalTheory.T.sections_powerTwist_basis_stable_baseChange _root_.GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy hproj hvan GlobalTheory.AbLaw.h1Zero_of_isIso
    GlobalTheory.exists_matrix_basis_ker_of_exact_at_point hBC ((GlobalTheory.secM_invariant_eq_bot_or_univ_at_geometric_point hBC).1 h0)
    (GlobalTheory.twisted_pow_translate (GlobalTheory.AbSquare.square_of_cube hcube).1 hmulq)

end GlobalTheory
end

