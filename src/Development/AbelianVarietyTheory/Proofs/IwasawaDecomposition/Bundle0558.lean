module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0511
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0510
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlowOrbitFirstMinimumOfIsotropicFlowMajorant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumEqZeroOfRankZero
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0546
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRealCombinationsOfIndependent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem linearIndependent_real_combination (g r d : ℕ) (x : Fin r → Fin g → ℂ)
    (e : Fin d → Fin r → ℝ) (hx : LinearIndependent ℝ x) (he : LinearIndependent ℝ e) :
    LinearIndependent ℝ (fun i => ∑ m, (e i m : ℂ) • x m) := by
  rw [Fintype.linearIndependent_iff] at hx he ⊢
  intro c hc
  have hreal : ∀ i, (∑ m, (e i m : ℂ) • x m) = ∑ m, e i m • x m := by
    intro i
    refine Finset.sum_congr rfl fun m _ => ?_
    funext k
    simp [Pi.smul_apply, Complex.real_smul]
  have h1 : ∑ m, (∑ i, c i * e i m) • x m = 0 := by
    have h0 : ∑ i, c i • ∑ m, e i m • x m = 0 := by
      simpa only [hreal] using hc
    rw [← h0]
    simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have h2 := hx _ h1
  refine he c ?_
  funext m
  simpa [Finset.sum_apply, Pi.smul_apply] using h2 m

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralFlagDensityFibreBoundedDomain
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibreInt

theorem dens_neg {m : ℕ} (B : Matrix (Fin m) (Fin m) ℂ) (y : Low m → ℂ) : dens (-B) y = dens B y := by
  unfold dens
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.mul_neg, Matrix.neg_mul, lminor, lminor, submatrix_neg, Pi.neg_apply, Pi.neg_apply, det_neg]
  simp

theorem shear_neg_J {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) :
    shear (-Jpq p q) Z = fromBlocks (-1) (-Z) (-Zᴴ) (hQ Z) := by
  simp [shear, Jpq, hQ, fromBlocks_neg, fromBlocks_conjTranspose, fromBlocks_multiply, sub_eq_neg_add]

theorem flagConst_pos (m : ℕ) : 0 < flagConst m :=
  Finset.prod_pos fun i _ => by have := Real.pi_pos; positivity

theorem lintegral_dens_glue : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ), reindex e e A = -Jpq p q → ∀ v : Fin p × Fin q → ℂ, toMat v ∈ hcDom p q → ∫⁻ b : (Low q → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, b))) = ENNReal.ofReal ((hQ (toMat v)).det.re ^ (-((p + q : ℕ) : ℤ)) / (flagConst p * flagConst q)) := by
  intro r p q e he A hA v hv
  set Z := toMat v with hZ
  have hH : (hQ Z).PosDef := hv
  have hd := hH.det_pos
  have hu : IsUnit (hQ Z).det := hd.ne'.isUnit
  set B : Matrix (Fin p) (Fin p) ℂ := 1 + Z * (hQ Z)⁻¹ * Zᴴ with hB
  have hBp : B.PosDef := PosDef.one.add_posSemidef (hH.inv.posSemidef.mul_mul_conjTranspose_same Z)
  have hs : schur (shear (-Jpq p q) Z) = -B := by
    rw [shear_neg_J, schur, hB]
    simp
    abel
  have h22 : (shear (-Jpq p q) Z).toBlocks₂₂ = hQ Z := by rw [shear_neg_J, toBlocks_fromBlocks₂₂]
  have hdet : B.det = ((hQ Z).det)⁻¹ := by
    have e1 : (1 : Matrix (Fin q) (Fin q) ℂ) + (hQ Z)⁻¹ * Zᴴ * Z = (hQ Z)⁻¹ := by
      rw [Matrix.mul_assoc, ← nonsing_inv_mul _ hu, ← Matrix.mul_add, hQ, sub_add_cancel, Matrix.mul_one]
    rw [hB, Matrix.mul_assoc, det_one_add_mul_comm, e1, det_nonsing_inv, Ring.inverse_eq_inv']
  obtain ⟨d, hd0, hdd⟩ : ∃ d : ℝ, 0 < d ∧ (hQ Z).det = d := by
    obtain ⟨h1, h2⟩ := Complex.pos_iff.1 hd
    exact ⟨_, h1, Complex.ext (by simp) (by simp [← h2])⟩
  have hpt : ∀ b : (Low q → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, b))) =
      (ENNReal.ofReal (d ^ (-(2 * p : ℤ))) * ENNReal.ofReal (dens (hQ Z) b.1)) * ENNReal.ofReal (dens B b.2) := by
    intro b
    rw [_root_.GlobalTheory.FlagFibre.dens_glue r p q e he A (v, b) (by rw [hA]; exact h22 ▸ hu), hA]
    simp only [← hZ]
    rw [h22, hs, dens_neg, hdd, Complex.norm_real, Real.norm_of_nonneg hd0.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (mul_nonneg (by positivity) (dens_nonneg _ _)),
      mul_comm (dens (hQ Z) b.1)]
  simp only [hpt]
  rw [Measure.volume_eq_prod, lintegral_prod_mul
    (f := fun y => ENNReal.ofReal (d ^ (-(2 * p : ℤ))) * ENNReal.ofReal (dens (hQ Z) y))
    (g := fun y => ENNReal.ofReal (dens B y))
    ((measurable_dens _).ennreal_ofReal.const_mul _).aemeasurable (measurable_dens _).ennreal_ofReal.aemeasurable,
    lintegral_const_mul _ (measurable_dens _).ennreal_ofReal, _root_.GlobalTheory.FlagFibre.FlagInt.lintegral_dens _ _ hH, _root_.GlobalTheory.FlagFibre.FlagInt.lintegral_dens _ _ hBp, hdet, hdd,
    ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_re]
  have hp := flagConst_pos p
  have hq := flagConst_pos q
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [_root_.inv_zpow', ← mul_div_assoc _ _ (flagConst q), div_mul_div_comm, ← zpow_add₀ hd0.ne', ← zpow_add₀ hd0.ne', mul_comm (flagConst q)]
  congr 2
  push_cast
  ring

end GlobalTheory.FlagFibreInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCuspOfVanishOn
section
noncomputable section

namespace GlobalTheory.CuspFrom

section Analytic

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {la : Wt X.Ψ r}
  {P : Frame X.Ψ r → ℂ}

theorem thickBdd (hP : X.IsSec la P) : ThickBdd X (X.pnorm la P) := by
  intro ε hε
  obtain ⟨K, hK, hKd, hcov⟩ := GlobalTheory.FlagMahler.mahler_compactness (E := E) r X ε hε
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn ((AR.Up.BigB.pnorm_contOn X la hP).mono hKd)).bddAbove
  refine ⟨C, fun x hx hl => ?_⟩
  obtain ⟨γ, hγ, b, hb, h⟩ := hcov x hx hl
  have := hC ⟨_, h, rfl⟩
  rwa [AR.Up.OW.pnorm_lact la hP hγ (AR.Up.OntoS.dom_rmul X hx hb), FrameDegreeData.pnorm_rmul X la P hP.2.1 x hx b hb] at this

theorem freqNonneg (hf : 1 < Module.finrank ℚ E / 2) (hP : X.IsSec la P) : FreqNonneg X la P :=
  _root_.GlobalTheory.freqNonneg_of_thickBdd (_root_.GlobalTheory.CuspFrom.OrbitThick.orbitThick_of_flowMaj _root_.GlobalTheory.CuspFrom.flowMajSt_holds) E r X la P hf hP (thickBdd X hP)

theorem growth (hf : 1 < Module.finrank ℚ E / 2) (hP : X.IsSec la P) {w : ℝ} (hw : 0 ≤ w)
    (h : ∀ τ, X.spread la τ / 2 ≤ w) : ∃ C A : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C * X.la1 x ^ (-(A * w)) :=
  GlobalTheory.T.moderate_growth_of_firstMinimum_and_flow_bounds _root_.GlobalTheory.CuspFrom.flowMajSt_holds E r X w _ hw (fun x _ => mul_nonneg (norm_nonneg _) (Formalism.L2.Pj.pnorm_fac_nonneg X la x))
    (thickBdd X hP) (GlobalTheory.T.maximum_principle_isotropicFlow_rescaledBound E r X la P w hP (freqNonneg X hf hP) h)

theorem isModerate (hf : 1 < Module.finrank ℚ E / 2) (hP : X.IsSec la P) : X.IsModerate la P := by
  obtain ⟨C, A, h⟩ := growth X hf hP (w := ∑ τ, |X.spread la τ / 2|) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    fun τ => (le_abs_self _).trans (Finset.single_le_sum (f := fun τ => |X.spread la τ / 2|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  exact ⟨C, _, h⟩

end Analytic

section Geometric

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam
open scoped LaurentSeries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}

theorem exists_input [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (Uw : UnfWit U)
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) {k : U.Comp} {ξ' : Fin r → E}
    (hξ : (U.X k).IsIso ξ') {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom) :
    ∃ a : ArcIn Dw l (RingHom.id c.F) ℂ σ, ∀ (O : Type) [CommRing O] (β : O →+* c.F),
      FlowTie Uw (a.restrict β) k ξ' x := by
  letI := H.starRing
  obtain ⟨hp, hq⟩ := GlobalTheory.ArcCM.Exist.one_le_of_isIso hU hξ
  obtain ⟨A, gam, ξ, jj, DB, tyB, eB, hO, hξ0, hrk, hdvd, -, hprim, -, hab, hDp, hDq⟩ :=
    GlobalTheory.T.exists_analytic_model_on_frame_orbit_isolating E H Dw l Xo c σ r U Uw k ξ' x 0 0 hσ hU hξ hx
      (fun m _ => ⟨0, by simp, by funext τ i; simp [Data.embV, Data.emb]⟩) (by simp [cc]) (by simp)
      (fun s _ _ => ⟨0, by simp⟩)
  obtain ⟨B, ex, hex⟩ := _root_.GlobalTheory.CuspFrom.exists_pat_isExp_of_isPeriod E H l DB _ tyB _ hab.2.1 hab.2.2.2.2
  obtain ⟨aC, Λ, hA, h1, h2⟩ := GlobalTheory.T.exists_complex_arc_of_analytic_model_on_flow_orbit E H Dw l Xo c σ r U Uw k ξ' x B hσ hU A gam ξ DB tyB eB ex hO hrk hdvd
    hprim hab hDp hDq hp hq hex
  subst hA
  exact ⟨aC, GlobalTheory.T.arcs_on_flow_lines_of_analytic_model_on_orbit E H Dw l Xo c σ r U Uw k ξ' x aC Λ hσ hU hξ hx gam ξ hO hξ0 hrk h1 h2⟩

theorem exists_model (Xo : Moduli Dw l) (c : Coeff l) (hr : 1 ≤ Dw.p + Dw.q) :
    ∃ (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype), Y.N4 ∧ PushInvertible Y.t.G Y.t.PP.L := by
  classical
  have hK := GlobalTheory.ArcCM.known_holds
  obtain ⟨W, hW⟩ := GlobalTheory.GlobalModelGuards.exists_place 2 Nat.prime_two
  have hg : l.GoodAt 2 := by
    have := l.three_le
    rwa [Level.GoodAt, Nat.factorization_eq_zero_of_not_dvd l.odd.not_two_dvd_nat, pow_zero, Nat.div_one]
  have key : ∀ Xs : ∀ l' : Level H, Moduli Dw l',
      ∃ Y : Model (Xs l) c (c.V W).subtype, Y.N4 ∧ PushInvertible Y.t.G Y.t.PP.L := by
    intro Xs
    obtain ⟨Y, hY, -⟩ := hK.models.2 E H Dw hr Xs
    obtain ⟨h2, h4⟩ := hY 2 W Nat.prime_two hW
    exact ⟨Y 2 W Nat.prime_two hW ⟨l, c, hg⟩, (h4 _).2.2, (h2.1 ⟨l, c, hg⟩).2.2.1⟩
  have h := key (Function.update (fun l' => Classical.choice (hK.n1ab E H Dw l' hr)) l Xo)
  rw [Function.update_self] at h
  exact ⟨W, h⟩

theorem coeff_eq_zero {v : PowerSeries ℂ} (hv : v ∈ IsLocalRing.maximalIdeal (PowerSeries ℂ)) {j : ℤ} (hj : j ≤ 0) :
    (algebraMap (PowerSeries ℂ) ℂ⸨X⸩ v).coeff j = 0 := by
  rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] at hv
  rw [LaurentSeries.coe_algebraMap, PowerSeries.coeff_coe]
  split_ifs with h0
  · rfl
  · obtain rfl : j = 0 := by omega
    simpa using hv

end Geometric

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped LaurentSeries

end GlobalTheory.CuspFrom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemOfCoeffNeZero
section
noncomputable section

open GlobalTheory.Toroidal GlobalTheory.LocM

namespace GlobalTheory.PolFan

namespace ConeMeet

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m m' : ℕ}

theorem inCone {n : ℕ} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hγ' : IsCone bar φ γ')
    {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X) (hβp : ∀ i y, 0 ≤ β i y y)
    {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (γ' j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • γ' j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ'.strict
  have hsum : ∑ i, a i * (ℓ (β i) : ℝ) = ∑ j, b j * (ℓ (γ' j) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim β γ') (c := Sum.elim a (-b)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrel,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hφ : ∑ i, a i * φ.evalZ (β i) = ∑ j, b j * φ.evalZ (γ' j) := by
    rw [← hlin, hrel]; exact (linearOn_iff φ γ').1 hγ'.linear b hb
  have hterm : ∑ i, a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum, show ∑ i, a i * (N * φ.evalZ (β i)) = N * ∑ i, a i * φ.evalZ (β i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hφ, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) := fun i _ =>
    mul_nonneg (ha i) (sub_nonneg.2 (h2 _ (hβ i) (hβp i)))
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm i (Finset.mem_univ _)
  have he : (N : ℝ) * φ.evalZ (β i) = ℓ (β i) := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hi
    · linarith
  exact h3 _ (hβ i) (hβp i) he

theorem apply_sum_nsmul {L : Type} [AddCommGroup L] (F : L →ₗ[ℤ] ℤ) {p : ℕ} (n : Fin p → ℕ) (v : Fin p → L) :
    F (∑ j, n j • v j) = ∑ j, (n j : ℤ) * F (v j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_nsmul]

theorem ray {γ : Fin m → LinearMap.BilinForm ℤ X} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hγ : IsCone bar φ γ)
    (hγ' : IsCone bar φ γ') {i : Fin m} {k : ℕ} {d : Fin m' → ℕ} (hk : 0 < k) (hkd : k • γ i = ∑ j, d j • γ' j)
    (hback : ∀ j, d j ≠ 0 → ∃ (kj : ℕ) (e : Fin m → ℕ), 0 < kj ∧ kj • γ' j = ∑ l, e l • γ l) :
    ∃ j, γ i = γ' j := by
  classical
  let g : Fin m → balForms bar X := fun l => ⟨γ l, hγ.mem l⟩
  let g' : Fin m' → balForms bar X := fun l => ⟨γ' l, hγ'.mem l⟩
  obtain ⟨f, hf⟩ := hγ.basis.exists_dual
  obtain ⟨f', hf'⟩ := hγ'.basis.exists_dual
  have hf : ∀ a b, f a (g b) = if a = b then 1 else 0 := hf
  have hf' : ∀ a b, f' a (g' b) = if a = b then 1 else 0 := hf'
  have H1 : k • g i = ∑ j, d j • g' j := Subtype.ext (by simpa [g, g', Submodule.coe_sum] using hkd)
  have H2 : ∀ j, d j ≠ 0 → ∃ (kj : ℕ) (e : Fin m → ℕ), 0 < kj ∧ kj • g' j = ∑ l, e l • g l := fun j hj => by
    obtain ⟨kj, e, hkj, he⟩ := hback j hj
    exact ⟨kj, e, hkj, Subtype.ext (by simpa [g, g', Submodule.coe_sum] using he)⟩

  have coord : ∀ j, d j ≠ 0 → ∃ (kj : ℕ) (e : Fin m → ℕ), 0 < kj ∧ kj • g' j = ∑ l, e l • g l ∧
      ∀ l, (kj : ℤ) * f l (g' j) = e l := fun j hj => by
    obtain ⟨kj, e, hkj, he⟩ := H2 j hj
    refine ⟨kj, e, hkj, he, fun l => ?_⟩
    have t := congrArg (f l) he
    rw [map_nsmul, apply_sum_nsmul] at t
    simpa [hf] using t
  have Z : ∀ l, l ≠ i → ∀ j, d j ≠ 0 → f l (g' j) = 0 := by
    intro l hl
    have s := congrArg (f l) H1
    rw [map_nsmul, apply_sum_nsmul, hf, if_neg hl, smul_zero] at s
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ (d j : ℤ) * f l (g' j) := fun j _ => by
      by_cases hd : d j = 0
      · simp [hd]
      · obtain ⟨kj, e, hkj, -, he⟩ := coord j hd
        have : 0 ≤ (kj : ℤ) * f l (g' j) := (he l).symm ▸ Int.natCast_nonneg _
        exact mul_nonneg (Int.natCast_nonneg _) ((mul_nonneg_iff_of_pos_left (by exact_mod_cast hkj)).1 this)
    intro j hd
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 s.symm j (Finset.mem_univ _)
    exact (mul_eq_zero.1 this).resolve_left (by exact_mod_cast hd)
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    by_contra hc
    push_neg at hc
    have : k • g i = 0 := by rw [H1]; simp [hc]
    have s := congrArg (f i) this
    rw [map_nsmul, hf, if_pos rfl, map_zero] at s
    simp at s
    omega
  obtain ⟨kj, e, hkj, he, hc⟩ := coord j hj
  have hel : ∀ l, l ≠ i → e l = 0 := fun l hl => by
    have := hc l
    rw [Z l hl j hj, mul_zero] at this
    exact_mod_cast this.symm
  have he' : kj • g' j = e i • g i := by
    rw [he, Finset.sum_eq_single i (fun l _ hl => by rw [hel l hl, zero_smul]) (by simp)]
  have t := congrArg (f' j) he'
  rw [map_nsmul, map_nsmul, hf', if_pos rfl] at t
  simp only [nsmul_eq_mul, mul_one] at t
  have hx := hc i
  have hx0 : 0 ≤ f i (g' j) := (mul_nonneg_iff_of_pos_left (by exact_mod_cast hkj)).1 (hx ▸ Int.natCast_nonneg _)
  have hxy : f i (g' j) * f' j (g i) = 1 := by
    have : (kj : ℤ) * (f i (g' j) * f' j (g i)) = kj * 1 := by
      rw [← mul_assoc, hx, mul_one]; exact_mod_cast t.symm
    exact mul_left_cancel₀ (by exact_mod_cast hkj.ne') this
  have hx1 : f i (g' j) = 1 := Int.eq_one_of_mul_eq_one_right hx0 hxy
  have hei : e i = kj := by rw [hx1, mul_one] at hx; exact_mod_cast hx.symm
  rw [hei] at he'
  refine ⟨j, LinearMap.ext₂ fun a b => ?_⟩
  have := LinearMap.congr_fun₂ (congrArg Subtype.val he') a b
  simp [g, g'] at this
  rcases this with h | h
  · exact h.symm
  · omega

theorem mem_of_coeff_ne_zero {γ : Fin m → LinearMap.BilinForm ℤ X} {γ' : Fin m' → LinearMap.BilinForm ℤ X}
    (hγ : IsCone bar φ γ) (hγ' : IsCone bar φ γ') {c : Fin m → ℝ} {c' : Fin m' → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hc' : ∀ j, 0 ≤ c' j) (hrel : ∑ i, c i • toReal (γ i) = ∑ j, c' j • toReal (γ' j)) (i : Fin m) (hi : c i ≠ 0) :
    ∃ j, γ i = γ' j := by
  classical
  obtain ⟨k, d, hk, hkd⟩ := inCone hγ' hγ.mem hγ.nonneg hc hc' ((linearOn_iff φ γ).1 hγ.linear c hc) hrel i hi
  refine ray hγ hγ' hk hkd fun j hj => ?_
  refine inCone (a := fun j => (d j : ℝ)) (b := Pi.single i (k : ℝ)) hγ hγ'.mem hγ'.nonneg
    (fun j => Nat.cast_nonneg _) (fun l => by by_cases h : l = i <;> simp [h])
    ((linearOn_iff φ γ').1 hγ'.linear _ fun j => Nat.cast_nonneg _) ?_ j (by exact_mod_cast hj)
  refine LinearMap.ext₂ fun a b => ?_
  have := LinearMap.congr_fun₂ hkd a b
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, nsmul_eq_mul] at this ⊢
  simp only [Pi.single_apply, ite_smul, zero_smul, LinearMap.smul_apply, toReal_apply, smul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
  exact_mod_cast this.symm

end ConeMeet


open ConeMeet in
theorem cone_meet : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin m' → LinearMap.BilinForm ℤ X)
    (c : Fin m → ℝ) (c' : Fin m' → ℝ), IsCone bar φ γ → IsCone bar φ γ' → (∀ i, 0 ≤ c i) → (∀ j, 0 ≤ c' j) →
    ∑ i, c i • toReal (γ i) = ∑ j, c' j • toReal (γ' j) → ∀ i, c i ≠ 0 → ∃ j, γ i = γ' j ∧ c i = c' j := by
  intro O _ bar φ X _ _ _ m m' γ γ' c c' hγ hγ' hc hc' hrel i hi
  classical
  obtain ⟨j, hj⟩ := mem_of_coeff_ne_zero hγ hγ' hc hc' hrel i hi
  refine ⟨j, hj, ?_⟩
  let g : Fin m → balForms bar X := fun l => ⟨γ l, hγ.mem l⟩
  let g' : Fin m' → balForms bar X := fun l => ⟨γ' l, hγ'.mem l⟩
  obtain ⟨f', hf'⟩ := hγ'.basis.exists_dual
  have hf' : ∀ a b, f' a (g' b) = if a = b then 1 else 0 := hf'
  have s := sum_mul_eq_zero_of_sum_toReal (X := X) (j := (balForms bar X).subtype) Subtype.val_injective (f' j)
    (β := Sum.elim g g') (c := Sum.elim c (-c')) (by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Submodule.subtype_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib,
        g, g', hrel, add_neg_cancel])
  rw [Fintype.sum_sum_type] at s
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, hf', Int.cast_ite,
    Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at s
  have h1 : ∑ l, c l * (f' j (g l) : ℝ) = c i := by
    rw [Finset.sum_eq_single i]
    · have : g i = g' j := Subtype.ext hj
      rw [this, hf', if_pos rfl, Int.cast_one, mul_one]
    · intro l _ hl
      by_cases hcl : c l = 0
      · rw [hcl, zero_mul]
      · obtain ⟨p, hp⟩ := mem_of_coeff_ne_zero hγ hγ' hc hc' hrel l hcl
        have : g l = g' p := Subtype.ext hp
        rw [this, hf', if_neg, Int.cast_zero, mul_zero]
        rintro rfl
        exact hl (hγ.injective (hp.trans hj.symm))
    · simp
  linarith

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NumbersEqConcreteNumbersAtBaseLevelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numbers_eq_concreteNumbers_at_baseLevel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D) (JM : MjHIds D A3.A Xd (A3.indefDown (s0Of R F))), Pins R F cG → Holds R F → MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW JM → IdxDefs D Xd → NumTie D A3.A (A3.indefDown (s0Of R F)) Y.tup := by
  first | exact @GlobalTheory.Mem.ReadIndexNumerics.numTie_of_read | exact GlobalTheory.Mem.ReadIndexNumerics.numTie_of_read | (intros; apply GlobalTheory.Mem.ReadIndexNumerics.numTie_of_read <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthMatrixMulBoundedVectors
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem matrix_mul_bounded_poly_growth : ∀ (n g d : ℕ) (R : Set (Fin n → ℂ)) (τ : (Fin n → ℂ) → Fin d → Fin d → ℂ) (E : (Fin n → ℂ) → Fin d → Fin g → ℂ), (∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖τ s‖ ≤ C * (1 + ‖s‖) ^ k) → (∀ i, ∃ C : ℝ, ∀ s ∈ R, ‖E s i‖ ≤ C) → ∀ j, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ i, τ s i j • E s i‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n g d R τ E ⟨C, k, hC⟩ hE j
  choose C' hC' using hE
  refine ⟨max C 0 * ∑ i, max (C' i) 0, k, fun s hs => ?_⟩
  have hp : (0:ℝ) ≤ (1 + ‖s‖) ^ k := pow_nonneg (by positivity) _
  have h1 : ∀ i, ‖τ s i j‖ ≤ max C 0 * (1 + ‖s‖) ^ k := fun i =>
    (norm_le_pi_norm (τ s i) j).trans ((norm_le_pi_norm (τ s) i).trans
      ((hC s hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)))
  calc ‖∑ i, τ s i j • E s i‖ ≤ ∑ i, ‖τ s i j • E s i‖ := norm_sum_le _ _
    _ = ∑ i, ‖τ s i j‖ * ‖E s i‖ := by simp only [norm_smul]
    _ ≤ ∑ i, (max C 0 * (1 + ‖s‖) ^ k) * max (C' i) 0 :=
        Finset.sum_le_sum fun i _ => mul_le_mul (h1 i) (le_max_of_le_left (hC' i s hs))
          (norm_nonneg _) (mul_nonneg (le_max_right _ _) hp)
    _ = max C 0 * (∑ i, max (C' i) 0) * (1 + ‖s‖) ^ k := by rw [← Finset.mul_sum]; ring

end GlobalTheory
end

