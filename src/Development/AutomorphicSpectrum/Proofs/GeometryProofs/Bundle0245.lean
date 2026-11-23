module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0241
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0237
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0147
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0062
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0136
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0240
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramBoundNearBoundary
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem one_le_logSize_lb {n : ℕ} (a : ℕ) (z : Fin n → ℂ) : 1 ≤ logSize a z :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem logSize_smul_le_lb {n : ℕ} (a : ℕ) (c : ℂ) (hc : c ≠ 0) (z : Fin n → ℂ)
    (hz : ∀ i : Fin n, i.val < a → z i ≠ 0) :
    logSize a (c • z) ≤ (1 + n * |Real.log ‖c‖|) * logSize a z := by
  have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖(c • z) i‖| ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), (|Real.log ‖c‖| + |Real.log ‖z i‖|) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : z i ≠ 0 := hz i (Finset.mem_filter.mp hi).2
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hi')]
    exact abs_add_le _ _
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : ((Finset.univ.filter (fun i : Fin n => i.val < a)).card : ℝ) ≤ n := by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i : Fin n => i.val < a)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have h3 : 0 ≤ |Real.log ‖c‖| := abs_nonneg _
  have h4 : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h5 := mul_le_mul_of_nonneg_right h2 h3
  have h6 : 0 ≤ (n : ℝ) * |Real.log ‖c‖| * ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| :=
    by positivity
  unfold logSize
  nlinarith

theorem hermForm_rows_lb {m g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (F : Matrix (Fin m) (Fin g) ℂ) (i j : Fin m) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (F i) (F j) = (F * Hm * F.conjTranspose) i j := by
  rw [Matrix.mul_assoc]
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, Matrix.mul_apply, dotProduct, Matrix.mulVec,
    Matrix.conjTranspose_apply, Pi.star_apply]

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter _root_.Topology Metric

theorem hodgeGram_det_log_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : BdryChart Xo σ n a), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → ∀ (m : ℕ) (u : Fin m → Fin C.g → C.R), LinearIndependent ℂ (fun i b => C.ψ 0 (u i b)) → ∃ (ρ K : ℝ) (N : ℕ), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ punct n a ρ, ∀ v, C.IsVal z u v → (∃ Γ, IsHodgeGram C.t.G C.t.PP.L (spMap (C.ψ z)) v Γ) ∧ ∀ Γ, IsHodgeGram C.t.G C.t.PP.L (spMap (C.ψ z)) v Γ → ‖Γ.det‖ ≤ K ∧ 1 ≤ K * logSize a z ^ N * ‖Γ.det‖ := by
  intro E _ _ _ H D l Xo σ n a C h1 h2 m u hu
  obtain ⟨ρ, Λ, _, L, hρ, hρ1, hR⟩ := GlobalTheory.CompanionTheory.Ar.Flat.exists_logPeriods_isRiem E H D l Xo σ n a C h1 h2
  let F : (Fin n → ℂ) → Matrix (Fin m) (Fin C.g) ℂ := fun z => Matrix.of fun i b => C.ψ ((ρ : ℂ) • z) (u i b)
  have hFc : ContinuousAt F 0 := by
    refine continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun b => ?_
    have hd : DifferentiableOn ℂ (fun z => C.ψ z (u i b)) (Metric.ball 0 1) := C.hol.2 (u i b)
    have hc : ContinuousAt (fun z => C.ψ z (u i b)) ((ρ : ℂ) • (0 : Fin n → ℂ)) := by
      rw [smul_zero]
      exact hd.continuousOn.continuousAt (Metric.ball_mem_nhds _ one_pos)
    exact ContinuousAt.comp (f := fun z : Fin n → ℂ => (ρ : ℂ) • z) hc (continuous_const_smul _).continuousAt
  have hFr : (F 0).rank = m := by
    have : LinearIndependent ℂ (F 0).row := by
      have e : (F 0).row = fun i b => C.ψ 0 (u i b) := by
        funext i b
        simp [F, Matrix.row]
      rw [e]; exact hu
    simpa using this.rank_matrix
  obtain ⟨ρ', K, N, hρ', hρ'1, hB⟩ := GlobalTheory.CompanionTheory.Ar.Flat.logPeriods_subframe_det_bounds n a C.g Λ L m F hFc hFr
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  set c : ℝ := 1 + n * |Real.log ‖(ρ : ℂ)⁻¹‖| with hcdef
  have hc1 : 1 ≤ c := le_add_of_nonneg_right (by positivity)
  refine ⟨ρ * ρ', K * Real.pi ^ m * c ^ N, N, mul_pos hρ hρ', mul_le_one₀ hρ1 hρ'.le hρ'1, ?_⟩
  intro z hz v hv
  obtain ⟨hz1, hz2⟩ := hz
  have hw1 : (ρ : ℂ)⁻¹ • z ∈ Metric.ball (0 : Fin n → ℂ) ρ' := by
    rw [mem_ball_zero_iff] at hz1 ⊢
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ.le, inv_mul_lt_iff₀ hρ]
    exact hz1
  have hw2 : ∀ i : Fin n, i.val < a → ((ρ : ℂ)⁻¹ • z) i ≠ 0 := fun i hi =>
    mul_ne_zero (inv_ne_zero hρc) (hz2 i hi)
  have hwz : (ρ : ℂ) • (ρ : ℂ)⁻¹ • z = z := smul_inv_smul₀ hρc z
  have hRz := hR ((ρ : ℂ)⁻¹ • z) ⟨Metric.ball_subset_ball hρ'1 hw1, hw2⟩
  rw [hwz] at hRz
  obtain ⟨hB1, hB2⟩ := hB _ hw1 hw2
  have hG : ∀ Γ, IsHodgeGram C.t.G C.t.PP.L (spMap (C.ψ z)) v Γ ↔
      Γ = (Real.pi : ℂ) • (F ((ρ : ℂ)⁻¹ • z) * L.H ((ρ : ℂ)⁻¹ • z) * (F ((ρ : ℂ)⁻¹ • z)).conjTranspose) := by
    intro Γ
    rw [hRz m u v Γ hv, ← Matrix.ext_iff]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [Matrix.smul_apply, smul_eq_mul, ← hermForm_rows_lb]
    simp only [F, hwz]
    rfl
  refine ⟨⟨_, (hG _).mpr rfl⟩, fun Γ hΓ => ?_⟩
  rw [(hG Γ).mp hΓ, Matrix.det_smul, Fintype.card_fin, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  have hS := logSize_smul_le_lb a _ (inv_ne_zero hρc) z hz2
  rw [← hcdef] at hS
  change 1 ≤ K * logSize a ((ρ : ℂ)⁻¹ • z) ^ N * _ at hB2
  have hd0 := norm_nonneg (F ((ρ : ℂ)⁻¹ • z) * L.H ((ρ : ℂ)⁻¹ • z) * (F ((ρ : ℂ)⁻¹ • z)).conjTranspose).det
  generalize ‖(F ((ρ : ℂ)⁻¹ • z) * L.H ((ρ : ℂ)⁻¹ • z) * (F ((ρ : ℂ)⁻¹ • z)).conjTranspose).det‖ = d at hB1 hB2 hd0 ⊢
  have hs0 := one_le_logSize_lb a ((ρ : ℂ)⁻¹ • z)
  have hs1 := one_le_logSize_lb a z
  have hp : 1 ≤ Real.pi ^ m := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hcN : 1 ≤ c ^ N := one_le_pow₀ hc1
  have hpow : logSize a ((ρ : ℂ)⁻¹ • z) ^ N ≤ c ^ N * logSize a z ^ N := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) hS N
  have hK : 0 ≤ K := hd0.trans hB1
  have hp0 : 0 ≤ Real.pi ^ m := by positivity
  constructor
  · calc Real.pi ^ m * d ≤ K * Real.pi ^ m * 1 := by nlinarith
      _ ≤ _ := by gcongr
  · calc 1 ≤ K * logSize a ((ρ : ℂ)⁻¹ • z) ^ N * d := hB2
      _ ≤ K * (c ^ N * logSize a z ^ N) * d := by gcongr
      _ = K * 1 * c ^ N * logSize a z ^ N * (1 * d) := by ring
      _ ≤ _ := by gcongr

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowValIntCast
section
noncomputable section

namespace GlobalTheory.CompanionTheory.HtLink

open PositivityTheory.HtPt.Htat

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT
open GlobalTheory.CompanionTheory.Ar.HTTie

theorem pow_val_intCast {G : Type} [Group G] (g : G) (N : ℕ) [NeZero N] (hg : g ^ N = 1) (j : ℤ) :
    g ^ (j : ZMod N).val = g ^ j := by
  have h : (((j : ZMod N).val : ℕ) : ℤ) = j % N := ZMod.val_intCast j
  rw [← zpow_natCast, h, ← zpow_eq_zpow_emod' j hg]

theorem cp_descend {A Ω : Type} [CommRing A] [Field Ω] [Algebra A Ω] (hinj : Function.Injective (algebraMap A Ω))
    (p : ℕ) (κ : A) (h : IsCp p (algebraMap A Ω κ)) :
    if p = 2 then κ = 4 else ∃ ζ : A, IsPrimitiveRoot ζ p ∧ κ = ζ - 1 := by
  unfold IsCp at h
  split_ifs at h ⊢
  · exact hinj (by rw [h, map_ofNat])
  · obtain ⟨ζ, h1, h2⟩ := h
    refine ⟨κ + 1, IsPrimitiveRoot.of_map_of_injective (f := algebraMap A Ω) ?_ hinj, by ring⟩
    rwa [map_add, map_one, h2, sub_add_cancel]

theorem exists_chart (h876 : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.BT.section_eq_zero_of_val_generic) (h450 : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_torsion)
    (h758 : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.BT.ChartEx.htChartExists) (h576 : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.HT.hasTestPoints_of_tate)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Scheme.{0}}
    [IsLocallyNoetherian X] (t : SAB H X) {Ω : Type} [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (hξ : IsCptGen ξ)
    (hall : ∀ q : X, genPt ξ ⤳ q)
    {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li)
    (hρ : M.IsActOf t.act.act ρ) (p m : ℕ) [Fact p.Prime] {ev : D.La → (Over.mk ξ ⟶ t.G)} {ζ₀ : Ωˣ}
    (hev : IsParam D t ξ (p ^ m) ev ζ₀) (hprop : IsProper (pullback.snd t.G.hom ξ))
    (hfull : FullTorsion t.G ξ (p ^ m)) (hrk : 2 * Module.finrank Ω Li = Module.finrank ℤ D.La)
    (u : Fin (D.p + D.q) → D.La) (hu : IsPolLattice (cmConj E) p D.EF u)
    (π : Multiplicative (Fin (D.p + D.q) → 𝓞 E) →* LevGrp D.La p m)
    (e : (Fin (D.p + D.q) → 𝓞 E) →+ (Fin (D.p + D.q) → 𝓞 E) →+ ZMod (p ^ m))
    (hπ : ∀ z, π (Multiplicative.ofAdd z) = lev p m (∑ k, z k • u k))
    (he : ∀ z z', e z z' = ((D.EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ m)))
    (hsurj : Function.Surjective π)
    (hker : ∀ y, π (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = (p ^ m) • y')
    (halt : ∀ y, e y y = 0)
    (hadj : ∀ (a : 𝓞 E) (y z : Fin (D.p + D.q) → 𝓞 E),
      e (a • y) z = e y (RingOfIntegers.mapRingEquiv (cmConj E) a • z))
    (hes : ∀ φ : (Fin (D.p + D.q) → 𝓞 E) →+ ZMod (p ^ m), ∃ y, e y = φ)
    (hei : ∀ y, e y = 0 → ∃ y', y = (p ^ m) • y')
    (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra A Ω]
    [IsFractionRing A Ω] (x : Sp A ⟶ X) (hx : spMap (algebraMap A Ω) ≫ x = ξ)
    (hsub : ∀ q : Cpt ξ, q.1 ∈ Set.range x → ∀ a, algebraMap A Ω a ∈ regAt ξ q) :
    ∃ Dc : HTChart A Ω (cmConj E) p m (D.p + D.q) (Module.Dual Ω Li), Dc.e = e ∧
      (∀ a w, Dc.ρΩ a w = w ∘ₗ ρ (H.bar a)) ∧
      (∀ w, w ∈ Dc.om ↔ ∀ q : Cpt ξ, q.1 ∈ Set.range x → w ∈ M.omLat q) ∧
      (∀ q : Cpt ξ, q.1 ∈ Set.range x →
        M.omLat q = Submodule.span (regAt ξ q) (Dc.om : Set (Module.Dual Ω Li))) ∧
      (∀ q : Cpt ξ, q.1 ∈ Set.range x → ∀ z w', M.IsHTAt t.PP.L (p ^ m) (ev (∑ k, z k • u k)) q w' ↔
        ∃ v ∈ M.omLat q, w' = Dc.h z + (p ^ m) • v) ∧
      ∀ κ : A, PointHT → IsCp p (algebraMap A Ω κ) → Dc.HasTestPoints κ := by
  have hinj := IsFractionRing.injective A Ω
  have : CharZero A := (algebraMap A Ω).charZero
  have hp := (Fact.out : p.Prime)
  have hn : p ^ m ≠ 0 := pow_ne_zero _ hp.ne_zero
  have : NeZero (p ^ m) := ⟨hn⟩
  have := t.semi.smooth
  have := t.semi.separated
  let κ : FractionRing A ≃+* Ω := (FractionRing.algEquiv A Ω).toRingEquiv
  have hκ : ∀ a, κ (algebraMap A _ a) = algebraMap A Ω a := (FractionRing.algEquiv A Ω).commutes
  have hκ' : κ.toRingHom.comp (algebraMap A (FractionRing A)) = algebraMap A Ω := RingHom.ext hκ
  have hx' : spMap (κ.toRingHom.comp (algebraMap A (FractionRing A))) ≫ x = ξ := by rw [hκ', hx]
  obtain ⟨Γ, i, htor, hpt, hact, hprop', htate⟩ := exists_chartGroup D t ξ h450 p m hev hprop hfull A x κ hx'
  have : Finite (LevGrp D.La p m) := by
    have := hu.finite
    have : Finite (D.La ⧸ LinearMap.range ((p ^ m) • (LinearMap.id : D.La →ₗ[ℤ] D.La))) := by
      refine Module.finite_of_fg_torsion _ fun a => ?_
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      refine ⟨⟨((p ^ m : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (Int.natCast_ne_zero.2 hn)⟩, ?_⟩
      rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨a, (natCast_zsmul a (p ^ m)).symm⟩
    infer_instance
  obtain ⟨L₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X t.G A x
  obtain ⟨ρ₀, hρ₀, -⟩ := lieModel_exists_unique_act X t.G A x L₀ M₀ (𝓞 E) t.act.act t.act.hom t.act.one t.act.mul
    t.act.add
  have hfin : Module.Finite A L₀ := (lie_proj X t.G A x L₀ M₀).1
  obtain ⟨j₀, j, hj, hjj, hj₀, hspan, hrk₀⟩ : ∃ (j₀ : L₀ →+ Li) (j : Module.Dual A L₀ →ₗ[A] Module.Dual Ω Li),
      IsBaseChange Ω j ∧ (∀ w b, j w (j₀ b) = algebraMap A Ω (w b)) ∧
      (∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left) ∧
      ((∀ w w' : Module.Dual Ω Li, (∀ b, w (j₀ b) = w' (j₀ b)) → w = w') ∧
        ∀ w : Module.Dual Ω Li, ∃ w' : L₀ →ₗ[A] Ω, ∀ b, w' b = w (j₀ b)) ∧
      Module.finrank Ω Li = Module.finrank A L₀ := by
    letI : Module A Li := Module.compHom Li (algebraMap A Ω)
    haveI : IsScalarTower A Ω Li := ⟨fun r a l => by rw [Algebra.smul_def, mul_smul]; rfl⟩
    obtain ⟨j₀, h1, h2⟩ := exists_lieBC M M₀ hx
    obtain ⟨j, h3, h4⟩ := exists_dualBC j₀ h1
    exact ⟨j₀.toAddMonoidHom, j, h3, h4, h2,
      ⟨fun w w' h => h1.algHom_ext _ _ h, fun w => ⟨w.restrictScalars A ∘ₗ j₀, fun _ => rfl⟩⟩, h1.finrank_eq⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Aˣ, algebraMap A Ω ζ = ζ₀ := by
    have h0 : (ζ₀ : Ω) ^ (p ^ m) = 1 := by rw [← Units.val_pow_eq_pow_val, hev.prim.pow_eq_one, Units.val_one]
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := A) (K := Ω)
      (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (by rw [h0]; exact isIntegral_one))
    exact ⟨Units.ofPowEqOne a (p ^ m) (hinj (by rw [map_pow, ha, h0, map_one])) hn, ha⟩
  have hζ1 : ζ ^ (p ^ m) = 1 := Units.ext (hinj (by
    rw [Units.val_pow_eq_pow_val, map_pow, hζ, ← Units.val_pow_eq_pow_val, hev.prim.pow_eq_one]; simp))
  obtain ⟨Dc, hDe, hDc⟩ := h758 A Ω E (cmConj E) p m (D.p + D.q) _ Γ X t.G x i htor inferInstance t.act.act
    t.act.hom L₀ M₀ ρ₀ hρ₀ _ j hj π hsurj hker (fun a y => by
      rw [hπ, hπ, ← hact, Finset.smul_sum]
      simp only [Pi.smul_apply, smul_eq_mul, mul_smul]) ζ hζ1 e halt hadj hes hei
  have hom := fun q hq w => mem_omLat_iff M M₀ hξ hinj hx j₀ hj₀ q hq (hsub q hq) w
  have hsm : ∀ (a : A) (w : Module.Dual Ω Li), a • w = algebraMap A Ω a • w := fun a w =>
    (algebraMap_smul Ω a w).symm
  refine ⟨Dc, hDe, fun a w => ?_, fun w => ⟨?_, fun h => ?_⟩, fun q hq => le_antisymm (fun w hw => ?_) ?_,
    fun q hq z w' => ?_, fun c hPt hc => ?_⟩
  · induction w using hj.inductionOn with
    | tmul w =>
      rw [hDc.2.1, ModelTest.bar_eq H]
      refine hspan.1 _ _ fun b => ?_
      have : ρ (H.bar a) (j₀ b) = j₀ (ρ₀ (H.bar a) b) := M.inj (Over.OverMorphism.ext (by
        rw [hρ, hj₀, hρ₀, Over.comp_left, Over.comp_left, hj₀, Category.assoc]))
      rw [LinearMap.comp_apply, this, hjj, hjj]; rfl
    | smul s w ih => rw [map_smul, ih, LinearMap.smul_comp]
    | add w w' ih ih' => rw [map_add (f := _), ih, ih', LinearMap.add_comp]
  · rw [hDc.1]
    rintro ⟨w₀, rfl⟩ q hq
    exact (hom q hq _).2 fun b => by rw [hjj]; exact hsub q hq _
  · obtain ⟨w₁, hw₁⟩ := hspan.2 w
    obtain ⟨v, w₀, h1, h2, h3⟩ := clear_denom hinj (algebraMap A Ω).range
      (by rintro _ ⟨a, rfl⟩; exact ⟨1, a, by simp, by simp, by simp⟩) w₁ (fun b => by
        let I : Ideal A := (Submodule.span A {(1 : Ω)}).comap (LinearMap.toSpanSingleton A Ω (w₁ b))
        by_cases hI : I = ⊤
        · have h1 : (1 : A) ∈ I := hI ▸ Submodule.mem_top
          obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
          exact ⟨a, by simpa [Algebra.smul_def] using ha⟩
        · obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal I hI
          let P' : PrimeSpectrum A := ⟨P, hP.isPrime⟩
          obtain ⟨s, a, hs, hsa⟩ := (regAt_frac hξ hinj hx P' ⟨x P', hall _⟩ rfl (hsub _ ⟨P', rfl⟩)).2 (w₁ b)
            (by rw [hw₁]; exact (hom _ ⟨P', rfl⟩ w).1 (h _ ⟨P', rfl⟩) b)
          exact absurd (hle (Submodule.mem_span_singleton.2 ⟨a, by simp [Algebra.smul_def, hsa]⟩)) hs)
    obtain ⟨v', hv'⟩ := h2
    rw [hDc.1]
    refine ⟨v' • w₀, hspan.1 _ _ fun b => ?_⟩
    rw [hjj, LinearMap.smul_apply, smul_eq_mul, map_mul, h3, hv', ← _root_.mul_assoc, inv_mul_cancel₀ h1,
      _root_.one_mul, hw₁]
  · obtain ⟨w₁, hw₁⟩ := hspan.2 w
    obtain ⟨P, hP⟩ : ∃ P : PrimeSpectrum A, x P = q.1 := hq
    have hf := regAt_frac hξ hinj hx P q hP (hsub q ⟨P, hP⟩)
    obtain ⟨v, w₀, h1, h2, h3⟩ := clear_denom hinj (regAt ξ q) (fun b hb => by
      obtain ⟨s, a, hs, hsa⟩ := hf.2 b hb
      exact ⟨s, a, (hf.1 s hs).1, (hf.1 s hs).2, hsa⟩) w₁ (fun b => by rw [hw₁]; exact (hom q ⟨P, hP⟩ w).1 hw b)
    have : w = (⟨_, h2⟩ : regAt ξ q) • j w₀ := hspan.1 _ _ fun b => by
      show _ = (algebraMap A Ω v)⁻¹ * j w₀ (j₀ b)
      rw [hjj, h3, ← _root_.mul_assoc, inv_mul_cancel₀ h1, _root_.one_mul, hw₁]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by rw [hDc.1]; exact ⟨w₀, rfl⟩))
  · rw [Submodule.span_le, hDc.1]
    rintro _ ⟨w₀, rfl⟩
    exact (hom q hq _).2 fun b => by rw [hjj]; exact hsub q hq _
  · obtain ⟨χ, w₀, hχ, hh, hHT⟩ := hDc.2.2 z
    refine isHTAt_iff lie_proj h876 hξ t.PP.L hn hfull M x κ hx' Γ i htor M₀ j₀ (by rw [hκ']; exact hj₀) _ χ w₀ _
      (fun s k _ _ a xk gk c h1 h2 => by
        obtain ⟨z', rfl⟩ := hsurj s
        have hz' : z' = Multiplicative.ofAdd (Multiplicative.toAdd z') := rfl
        rw [hz'] at h2 ⊢
        rw [hπ] at h2
        rw [hev.weil _ _ k a xk gk c h1 (h2.trans (congrArg (spMap a ≫ ·) (hpt _))), hχ, hDe, he, hκ,
          ← pow_val_intCast ζ₀ (p ^ m) hev.prim.pow_eq_one, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow,
          map_pow, map_pow, hζ]) hHT (fun b => by rw [hh, hjj, hκ]) q hq
      (fun a => by rw [hκ]; exact hsub q hq a) w'
  · refine h576 hPt E H D p A Ω m _ Dc u hu X t x Γ i htor L₀ M₀ ρ₀ hρ₀ j hj π ζ c hDc hπ (by rw [hDe]; exact he)
      (by rw [← hrk₀, hrk]) hprop' (fun k _ _ f => ?_) (cp_descend hinj p c hc)
    obtain ⟨I, h1, h2⟩ := htate k f
    exact ⟨I, by rw [h1, ← hζ, ← hκ, RingEquiv.symm_apply_apply], h2⟩

end GlobalTheory.CompanionTheory.HtLink
end
end

