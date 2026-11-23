module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ContinuousCompTorusMap
section
noncomputable section

namespace UpperTheory.Esk.OrbitalSingularIntegrals

open Complex Metric MeasureTheory Set Filter Topology
open ReciprocityTheory.AnForm.Osgood hiding SepHol

open scoped Real

def SepHol {n : ℕ} (f : (Fin n → ℂ) → ℂ) (S : Set (Fin n → ℂ)) : Prop :=
  ContinuousOn f S ∧ ∀ ζ ∈ S, ∀ i, DifferentiableAt ℂ (fun t => f (Function.update ζ i t)) (ζ i)

theorem continuous_comp_torusMap' {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ContinuousOn f (closedBall c r)) :
    Continuous fun θ => f (torusMap c (fun _ => r) θ) :=
  hf.comp_continuous (continuous_torusMap c r) (torusMap_mem_closedBall c hr)

theorem torusIntegrable_kernel' {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (closedBall c r)) (hz : z ∈ ball c r) :
    TorusIntegrable (fun ζ => (∏ i, (ζ i - z i)⁻¹) * f ζ) c (fun _ => r) := by
  refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
  refine Continuous.mul ?_ (continuous_comp_torusMap' hr.le hf)
  refine continuous_finsetProd _ fun i _ => Continuous.inv₀ ?_ fun θ => torusMap_sub_ne hr hz θ i
  exact ((continuous_apply i).comp (continuous_torusMap c r)).sub continuous_const

theorem cauchy' : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (r : ℝ), 0 < r →
    _root_.UpperTheory.Esk.OrbitalSingularIntegrals.SepHol f (closedBall c r) → ∀ z ∈ ball c r,
    (∯ ζ in T(c, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * f ζ) = (2 * π * I) ^ n * f z := by
  intro n
  induction n with
  | zero =>
    intro f c r _ _ z _
    rw [torusIntegral_dim0]
    simp [Subsingleton.elim z c]
  | succ n ih =>
    intro f c r hr hf z hz
    rw [torusIntegral_succ (torusIntegrable_kernel' hr hf.1 hz)]
    have hz0 : z 0 ∈ ball (c 0) r := (mem_ball_pi_iff hr).mp hz 0
    have hz' : Fin.tail z ∈ ball (fun i => c (Fin.succ i)) r :=
      (mem_ball_pi_iff hr).mpr fun i => (mem_ball_pi_iff hr).mp hz i.succ
    have hcons : ∀ x ∈ closedBall (c 0) r, ∀ y ∈ closedBall (fun i => c (Fin.succ i)) r,
        (Fin.cons x y : Fin (n + 1) → ℂ) ∈ closedBall c r := by
      intro x hx y hy
      refine (mem_closedBall_pi_iff hr.le).mpr fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using (mem_closedBall_pi_iff hr.le).mp hy j
    have key : EqOn (fun x => ∯ y in T(c ∘ Fin.succ, (fun _ => r) ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) * f (Fin.cons x y))
        (fun x => (2 * π * I) ^ n * ((x - z 0)⁻¹ * f (Fin.cons x (Fin.tail z)))) (sphere (c 0) r) := by
      intro x hx
      have hxc : x ∈ closedBall (c 0) r := sphere_subset_closedBall hx
      have hS : _root_.UpperTheory.Esk.OrbitalSingularIntegrals.SepHol (fun y => f (Fin.cons x y)) (closedBall (fun i => c (Fin.succ i)) r) := by
        refine ⟨?_, fun ζ hζ j => ?_⟩
        · exact hf.1.comp (differentiable_cons_right x).continuous.continuousOn
            (fun y hy => hcons x hxc y hy)
        · have h1 := hf.2 (Fin.cons x ζ) (hcons x hxc ζ hζ) j.succ
          have e : (fun t => f (Fin.cons x (Function.update ζ j t) : Fin (n + 1) → ℂ)) =
              fun t => f (Function.update (Fin.cons x ζ : Fin (n + 1) → ℂ) j.succ t) := by
            funext t
            rw [Fin.cons_update]
          show DifferentiableAt ℂ (fun t => f (Fin.cons x (Function.update ζ j t) : Fin (n + 1) → ℂ)) (ζ j)
          rw [e]
          simpa only [Fin.cons_succ] using h1
      have htail := ih (fun y => f (Fin.cons x y)) (fun i => c (Fin.succ i)) r hr hS (Fin.tail z) hz'
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Function.comp_def, mul_assoc]
      rw [torusIntegral_const_mul]
      simp only [Fin.tail] at htail
      rw [htail]
      ring
    rw [circleIntegral.integral_congr hr.le key, circleIntegral.integral_const_mul]
    have hd : DifferentiableOn ℂ (fun x => f (Fin.cons x (Fin.tail z))) (closedBall (c 0) r) := by
      intro x hx
      have h1 := hf.2 (Fin.cons x (Fin.tail z)) (hcons x hx _ (ball_subset_closedBall hz')) 0
      simp only [Fin.update_cons_zero, Fin.cons_zero] at h1
      exact h1.differentiableWithinAt
    have h1 := hd.circleIntegral_sub_inv_smul hz0
    simp only [smul_eq_mul] at h1
    rw [h1, Fin.cons_self_tail, pow_succ]
    ring

variable {n : ℕ}

theorem integrableOn_fctl' {c : Fin n → ℂ} {r : ℝ} {f : (Fin n → ℂ) → ℂ}
    (hc : Continuous fun θ => f (torusMap c (fun _ => r) θ)) (g : C(Cube n, ℂ)) :
    IntegrableOn (fun θ => jac r θ * g (cubeProj θ) * f (torusMap c (fun _ => r) θ))
      (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)) := by
  refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
  exact ((continuous_jac r).mul (g.continuous.comp continuous_cubeProj)).mul hc

def fctlCLM' (c : Fin n → ℂ) (r : ℝ) (f : (Fin n → ℂ) → ℂ)
    (hc : Continuous fun θ => f (torusMap c (fun _ => r) θ)) : C(Cube n, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fctl c r f
      map_add' := fun g g' => by
        simp only [fctl, ContinuousMap.add_apply, mul_add, add_mul]
        exact integral_add (integrableOn_fctl' hc g) (integrableOn_fctl' hc g')
      map_smul' := fun a g => by
        simp only [fctl, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext θ
        ring }
    (by
      obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => 2 * π)).exists_bound_of_continuousOn
        (((continuous_jac r).mul hc).continuousOn)
      refine ⟨M * volume.real (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)), fun g => ?_⟩
      refine (norm_setIntegral_le_of_norm_le_const (C := M * ‖g‖) measure_Icc_lt_top
        fun θ hθ => ?_).trans (le_of_eq (by ring))
      have h1 : ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ ≤ M := hM θ hθ
      rw [mul_comm (jac r θ), mul_assoc, norm_mul, mul_comm M]
      calc ‖g (cubeProj θ)‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖
          ≤ ‖g‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ :=
            mul_le_mul_of_nonneg_right (g.norm_coe_le_norm _) (norm_nonneg _)
        _ ≤ ‖g‖ * M := mul_le_mul_of_nonneg_left h1 (norm_nonneg _))

theorem fctlCLM'_kern {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) {f : (Fin n → ℂ) → ℂ}
    (hf : _root_.UpperTheory.Esk.OrbitalSingularIntegrals.SepHol f (closedBall c r)) (hz : z ∈ ball c r) :
    fctlCLM' c r f (continuous_comp_torusMap' hr.le hf.1) (kern c r z) = (2 * π * I) ^ n * f z := by
  rw [← cauchy' n f c r hr hf z hz]
  show fctl c r f (kern c r z) = _
  unfold fctl torusIntegral
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  simp only [jac, kern_apply hr hz, cubeProj_of_mem hθ, smul_eq_mul]
  ring

theorem osgFin (U : Set (Fin n → ℂ)) (hU : IsOpen U) (f : (Fin n → ℂ) → ℂ) (hf : _root_.UpperTheory.Esk.OrbitalSingularIntegrals.SepHol f U) :
    AnalyticOnNhd ℂ f U := by
  intro z0 hz0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z0 hz0
  have hr : 0 < ε / 2 := half_pos hε
  have hsub : closedBall z0 (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hball
  have hS : _root_.UpperTheory.Esk.OrbitalSingularIntegrals.SepHol f (closedBall z0 (ε / 2)) :=
    ⟨hf.1.mono hsub, fun ζ hζ i => hf.2 ζ (hsub hζ) i⟩
  have hne : (2 * π * I : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero])
  have han : AnalyticAt ℂ (fun z => ((2 * π * I : ℂ) ^ n)⁻¹ *
      fctlCLM' z0 (ε / 2) f (continuous_comp_torusMap' hr.le hS.1) (kern z0 (ε / 2) z)) z0 :=
    analyticAt_const.mul (((fctlCLM' z0 (ε / 2) f _).analyticAt _).comp (kern_analyticAt z0 hr))
  refine han.congr ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
  rw [fctlCLM'_kern hr hS hz, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end UpperTheory.Esk.OrbitalSingularIntegrals

open UpperTheory.Esk.OrbitalSingularIntegrals in
theorem UpperTheory.Esk.pf_Osg : UpperTheory.Esk.Osg := by
  intro I _ _ U hU f hf hsep
  set n := Fintype.card I
  let e : I ≃ Fin n := Fintype.equivFin I
  let Φ : (Fin n → ℂ) → (I → ℂ) := fun w i => w (e i)
  have hΦ : Continuous Φ := continuous_pi fun i => continuous_apply (e i)
  let g : (Fin n → ℂ) → ℂ := fun w => f (Φ w)
  let V : Set (Fin n → ℂ) := Φ ⁻¹' U
  have hV : IsOpen V := hU.preimage hΦ
  have hupd : ∀ (w : Fin n → ℂ) (j : Fin n) (t : ℂ), Φ (Function.update w j t) = Function.update (Φ w) (e.symm j) t := by
    intro w j t
    funext i
    by_cases h : i = e.symm j
    · subst h
      simp [Φ]
    · have h' : e i ≠ j := fun h' => h (by rw [← h']; simp)
      simp [Φ, h, h']
  have hg : UpperTheory.Esk.OrbitalSingularIntegrals.SepHol g V := by
    refine ⟨hf.comp hΦ.continuousOn (fun w hw => hw), fun w hw j => ?_⟩
    have h1 := hsep (Φ w) hw (e.symm j)
    have e1 : (fun t => g (Function.update w j t)) = fun t => f (Function.update (Φ w) (e.symm j) t) := by
      funext t
      simp only [g, hupd]
    rw [e1]
    simpa [Φ] using h1
  have hA := osgFin V hV g hg
  let Ψ : (I → ℂ) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (e.symm j)
  have hΨ : ∀ z, Φ (Ψ z) = z := by
    intro z
    funext i
    simp [Φ, Ψ]
  intro z hz
  have hmem : Ψ z ∈ V := by
    show Φ (Ψ z) ∈ U
    rw [hΨ]
    exact hz
  have h2 := (hA (Ψ z) hmem).comp (Ψ.analyticAt z)
  have hfe : g ∘ Ψ = f := by
    funext w
    simp only [Function.comp, g, hΨ]
  rwa [hfe] at h2
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.E5OfReproducingFormula
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.ReproducingKernelExpansion

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf)

theorem rep_eq (ω : D.Om) (u : Gf) (hu : (u : Gf ⧸ D.H) = ω) : ∃ h : D.H, D.rep ω = u * h := by
  have h1 : ((D.rep ω : Gf) : Gf ⧸ D.H) = ω := QuotientGroup.out_eq' _
  refine ⟨⟨u⁻¹ * D.rep ω, QuotientGroup.eq.1 (hu.trans h1.symm)⟩, ?_⟩
  simp

theorem ee_mul (h : D.H) (u : Gf) : D.ee ((h : Gf)⁻¹ * u) * (D.χ h : ℂ) = D.ee u := by
  unfold Dat.ee
  by_cases hu : u ∈ D.H
  · have hu' : (h : Gf)⁻¹ * u ∈ D.H := D.H.mul_mem (D.H.inv_mem h.2) hu
    rw [dite_eq_left hu', dite_eq_left hu, mul_comm, ← Units.val_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    simp
  · have hu' : (h : Gf)⁻¹ * u ∉ D.H := fun hh => hu (by simpa using D.H.mul_mem h.2 hh)
    rw [dite_eq_right hu', dite_eq_right hu, zero_mul]

theorem ee_one : D.ee 1 = 1 := by
  unfold Dat.ee
  rw [dite_eq_left D.H.one_mem]
  exact congrArg Units.val (map_one D.χ)

theorem smul_fst (γ : PG F) (ω : D.Om) : γ • ω = (((D.j γ.out * D.rep ω : Gf)) : Gf ⧸ D.H) := by
  have h2 : ((D.rep ω : Gf) : Gf ⧸ D.H) = ω := QuotientGroup.out_eq' _
  conv_lhs => rw [← QuotientGroup.out_eq' γ, ← h2]
  exact D.mk_smulO γ.out (D.rep ω)

theorem smul_snd (γ : PG F) (w : D.Xs) : γ • w = D.act γ.out w := by
  conv_lhs => rw [← QuotientGroup.out_eq' γ]
  exact D.mk_smulX γ.out w

variable [Fintype I]

theorem term (k : I → ℕ) (f : X I × Gf → ℂ) (hf : D.IsForm k f) (z : X I) (x : Gf) (γ : PG F) (y : D.Y) :
    D.ee ((D.rep (γ • y).1)⁻¹ * x) * (qq k z (γ • y).2 * f ((γ • y).2, D.rep (γ • y).1)) =
      D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x) * (qq k z (D.act γ.out y.2) * D.J k γ.out y.2) * f (y.2, D.rep y.1) := by
  obtain ⟨h, hh⟩ := rep_eq D (γ • y).1 (D.j γ.out * D.rep y.1) (by rw [Prod.smul_fst, smul_fst])
  have hs2 : (γ • y).2 = D.act γ.out y.2 := by rw [Prod.smul_snd, smul_snd]
  have key : (D.j γ.out * D.rep y.1 * (h : Gf))⁻¹ * x = (h : Gf)⁻¹ * ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x) := by
    group
  rw [hh, hs2, hf.lev, show f (D.act γ.out y.2, D.j γ.out * D.rep y.1) = D.J k γ.out y.2 * f (y.2, D.rep y.1) from hf.aut _ _ _, key, ← ee_mul D h ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x)]
  ring

open Classical in
theorem supp (k : I → ℕ) (f : X I × Gf → ℂ) (hf : D.IsForm k f) (z : X I) (x : Gf) (y : D.Y) :
    D.ee ((D.rep y.1)⁻¹ * x) * (qq k z y.2 * f (y.2, D.rep y.1)) =
      if y.1 = ((x : Gf) : Gf ⧸ D.H) then qq k z y.2 * f (y.2, x) else 0 := by
  split_ifs with hy
  · obtain ⟨h, hh⟩ := rep_eq D y.1 x hy.symm
    have he := ee_mul D h 1
    rw [ee_one, mul_one] at he
    have key : (x * (h : Gf))⁻¹ * x = (h : Gf)⁻¹ := by group
    rw [hh, show f (y.2, x * (h : Gf)) = (D.χ h : ℂ) * f (y.2, x) from hf.lev _ _ _, key]
    calc _ = (D.ee ((h : Gf)⁻¹) * (D.χ h : ℂ)) * (qq k z y.2 * f (y.2, x)) := by ring
      _ = _ := by rw [he, one_mul]
  · have hn : (D.rep y.1)⁻¹ * x ∉ D.H := by
      intro hm
      apply hy
      have h1 : ((D.rep y.1 : Gf) : Gf ⧸ D.H) = y.1 := QuotientGroup.out_eq' _
      exact h1.symm.trans (QuotientGroup.eq.2 hm)
    have h0 : D.ee ((D.rep y.1)⁻¹ * x) = 0 := by
      unfold Dat.ee
      rw [dite_eq_right hn]
    rw [h0, zero_mul]

end UpperTheory.Esk.ReproducingKernelExpansion

open UpperTheory.Esk UpperTheory.Esk.ReproducingKernelExpansion in
theorem UpperTheory.Esk.e5_of_reproducing_formula : UpperTheory.Esk.B1b → UpperTheory.Esk.C3 → UpperTheory.Esk.E0a → UpperTheory.Esk.faceMap_zero_comp_eq_one → UpperTheory.Esk.MultivariableReproducingFormula → UpperTheory.Esk.E5 := by
  intro hB1 hC3 hE0 _hE4 hB3 F I Gf _ _ _ D hAx k hk _hcomp b hb f hf p
  obtain ⟨z, x⟩ := p
  obtain ⟨hcount, hsf, -, hpres, -, -, hborel, -⟩ := hE0 F I Gf D hAx
  have := hcount
  have := hsf
  have := hborel
  have := hAx.cO
  let ω₀ : D.Om := ((x : Gf) : Gf ⧸ D.H)
  let a : D.Om → ℂ := ({ω₀} : Set D.Om).indicator fun _ => (1 : ℂ)
  let h0 : D.Xs → ℂ := fun w => qq k z w * f (w, x)
  let G : D.Y → ℂ := fun y => D.ee ((D.rep y.1)⁻¹ * x) * (qq k z y.2 * f (y.2, D.rep y.1))
  have hG : G = fun y => a y.1 * h0 y.2 := by
    funext y
    change D.ee ((D.rep y.1)⁻¹ * x) * (qq k z y.2 * f (y.2, D.rep y.1)) = a y.1 * h0 y.2
    rw [supp D k f hf z x y]
    by_cases hy : y.1 = ((x : Gf) : Gf ⧸ D.H)
    · rw [if_pos hy]
      have ha : a y.1 = 1 := by
        classical
        simp only [a]
        rw [Set.indicator_apply, if_pos (show y.1 ∈ ({ω₀} : Set D.Om) from hy)]
      rw [ha, one_mul]
    · rw [if_neg hy]
      have ha : a y.1 = 0 := by
        classical
        simp only [a]
        rw [Set.indicator_apply, if_neg (show y.1 ∉ ({ω₀} : Set D.Om) from hy)]
      rw [ha, zero_mul]
  have hqc : Continuous fun w : X I => qq k z w := by
    unfold qq
    exact continuous_finsetProd _ fun v _ =>
      (hB1.2.2.2.2.2.2.2.1 (k v)).comp (continuous_const.prodMk (continuous_apply v))
  have hh0c : Continuous fun w : X I => qq k z w * f (w, x) := hqc.mul (hf.hol x).1
  have hh0m : Measurable h0 := hh0c.measurable
  obtain ⟨C, hC⟩ := hf.bdd
  have hB := hB3 I k hk (fun w => f (w, x)) (hf.hol x) ⟨C, fun w => hC w x⟩ z
  have hh0i : Integrable h0 := hB.1
  have ham : Measurable a := measurable_const.indicator (MeasurableSet.of_discrete)
  have hai : Integrable a Measure.count :=
    (integrable_indicator_iff (MeasurableSet.of_discrete)).2
      ((integrableOn_singleton_iff (by simp)).2 (Or.inr (by simp)))
  have ha1 : ∫ ω, a ω ∂Measure.count = 1 := by
    simp only [a]
    rw [integral_indicator (MeasurableSet.of_discrete)]
    simp
  have hGm : Measurable G := by
    rw [hG]
    exact (ham.comp measurable_fst).mul (hh0m.comp measurable_snd)
  have hGi : Integrable G D.μY := by
    rw [hG]
    unfold Dat.μY
    exact MeasureTheory.Integrable.mul_prod hai hh0i
  have hKf : ∀ y : D.Y, D.Kern k y (z, x) * f (y.2, D.rep y.1) = ∑' γ : PG F, G (γ • y) := by
    intro y
    unfold Dat.Kern
    rw [← tsum_mul_right]
    refine tsum_congr fun γ => ?_
    exact (term D k f hf z x γ y).symm
  have hCC := hC3 (PG F) D.Y D.μY hpres b hb G hGm hGi
  calc ∫ y, b y • (D.Kern k y (z, x) * f (y.2, D.rep y.1)) ∂D.μY
      = ∫ y, b y • ∑' γ : PG F, G (γ • y) ∂D.μY := by simp_rw [hKf]
    _ = ∫ y, G y ∂D.μY := hCC.2
    _ = ∫ y, a y.1 * h0 y.2 ∂(Measure.count.prod volume) := by rw [hG]; rfl
    _ = (∫ ω, a ω ∂Measure.count) * ∫ w, h0 w := integral_prod_mul _ _
    _ = f (z, x) := by rw [ha1, one_mul]; exact hB.2
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.E6OfLinearTraceIdentity
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.LinearTraceIdentity

open UpperTheory.Esk

theorem op_kern {F I Gf ι : Type} [Field F] [Group Gf] [Fintype I] [Fintype ι] (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf)
    (y : D.Y) (hs : ∀ i, Summable fun γ : PG F =>
      D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * (D.rep y.1 * a i)) * (qq k y.2 (D.act γ.out y.2) * D.J k γ.out y.2)) :
    Dat.Op a (D.Kern k y) (y.2, D.rep y.1) = ∑' γ : PG F, D.kk k a γ y := by
  show ∑ i, D.Kern k y (y.2, D.rep y.1 * a i) = ∑' γ : PG F, D.kk k a γ y
  simp only [Dat.Kern, Dat.kk, Dat.kt, Dat.Te]
  rw [← Summable.tsum_finsetSum (fun i _ => hs i)]
  refine tsum_congr fun γ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_assoc]

end UpperTheory.Esk.LinearTraceIdentity

theorem UpperTheory.Esk.e6_of_linear_trace_identity : UpperTheory.Esk.E0a → UpperTheory.Esk.FormsStableUnderOperators → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E3 → UpperTheory.Esk.E4 → UpperTheory.Esk.faceMap_zero_comp_eq_one → UpperTheory.Esk.E5 → UpperTheory.Esk.LinTr → UpperTheory.Esk.E6 := by
  intro hE0a hE0b _ hE3 hE4 hE4b hE5 hLin
  intro F I Gf ι _ _ _ _ D k a hH hfd h b hb
  have hM : ∀ f, f ∈ D.M k ↔ D.IsForm k f := (hE0b F I Gf D hH.ax k).1
  have hE4' := hE4 F I Gf D hH.ax k hH.four hH.compat
  have hE4b' := hE4b F I Gf D hH.ax k hH.four hH.compat
  have hE5' := hE5 F I Gf D hH.ax k hH.four hH.compat b hb
  have hbm : Measurable fun y => (b y).toNNReal := hb.meas.real_toNNReal
  obtain ⟨ν, hν⟩ : ∃ ν : Measure D.Y, ν = D.μY.withDensity fun y => ((b y).toNNReal : ℝ≥0∞) := ⟨_, rfl⟩
  haveI : IsFiniteMeasure ν := by
    rw [hν]
    exact MeasureTheory.isFiniteMeasure_withDensity (hE3 F I Gf D hH.ax b hb).ne
  have hint : ∀ g : D.Y → ℂ, ∫ y, g y ∂ν = ∫ y, b y • g y ∂D.μY := by
    intro g
    rw [hν, integral_withDensity_eq_integral_smul hbm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (hb.nonneg y)]
  obtain ⟨K, hK⟩ : ∃ K : D.Y → D.M k, ∀ y, (K y).1 = D.Kern k y :=
    ⟨fun y => ⟨D.Kern k y, (hM _).2 (hE4' y)⟩, fun _ => rfl⟩
  have hn0 : Measurable fun z : X I => nrm k z := by
    unfold nrm
    refine Finset.measurable_prod _ fun v _ => ?_
    exact (continuous_abs.measurable.comp
      (Complex.measurable_im.comp (measurable_subtype_coe.comp (measurable_pi_apply v)))).pow_const _
  have hn_meas : Measurable fun y : D.Y => nrm k y.2 := hn0.comp measurable_snd
  have hn_pos : ∀ y : D.Y, 0 < nrm k y.2 := fun y =>
    Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (abs_pos.mpr (y.2 v).2) _
  have hK_meas : ∀ p, Measurable fun y => (K y).1 p := by
    intro p
    simp only [hK]
    exact (hE4b' p).2.1
  have hf_meas : ∀ f : D.M k, Measurable fun y : D.Y => f.1 (y.2, D.rep y.1) := by
    intro f
    have hF := (hM f.1).1 f.2
    haveI : Countable D.Om := hH.ax.cO
    refine measurable_from_prod_countable_right fun ω => ?_
    have hc : Measurable fun z : X I => f.1 (z, D.rep ω) := ((hF.hol (D.rep ω)).1).measurable
    exact hc
  have hK_bdd : ∀ p, ∃ C, ∀ y, ‖(K y).1 p‖ ≤ C * nrm k y.2 := by
    intro p
    simp only [hK]
    exact (hE4b' p).2.2
  have hf_bdd : ∀ f : D.M k, ∃ C, ∀ y : D.Y, ‖f.1 (y.2, D.rep y.1)‖ * nrm k y.2 ≤ C := by
    intro f
    obtain ⟨C, hC⟩ := ((hM f.1).1 f.2).bdd
    exact ⟨C, fun y => hC _ _⟩
  have hrep : ∀ (f : D.M k) p, ∫ y, (K y).1 p * f.1 (y.2, D.rep y.1) ∂ν = f.1 p := by
    intro f p
    rw [hint]
    simp only [hK]
    exact hE5' f.1 ((hM f.1).1 f.2) p
  obtain ⟨hmeas, ⟨C, hC⟩, htr⟩ := hLin (X I × Gf) D.Y ν (D.M k) ((Dat.Op a).restrict h) K
    (fun y => (y.2, D.rep y.1)) (fun y => nrm k y.2) hn_meas hn_pos hK_meas hf_meas hK_bdd hf_bdd hrep
  have hval : ∀ y : D.Y, ((Dat.Op a).restrict h (K y)).1 (y.2, D.rep y.1) = ∑' γ : PG F, D.kk k a γ y := by
    intro y
    rw [LinearMap.restrict_coe_apply, hK]
    exact LinearTraceIdentity.op_kern D k a y (fun i => ((hE4b' (y.2, D.rep y.1 * a i)).1 y).of_norm)
  have hm2 : Measurable fun y => ∑' γ : PG F, D.kk k a γ y := by
    simpa only [hval] using hmeas
  refine ⟨?_, ?_⟩
  · have hgi : Integrable (fun y => ∑' γ : PG F, D.kk k a γ y) ν := by
      refine (integrable_const C).mono' hm2.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
      have := hC y
      simp only [hval] at this
      exact this
    rw [hν, MeasureTheory.integrable_withDensity_iff_integrable_smul hbm] at hgi
    refine hgi.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (hb.nonneg y)]
  · rw [htr, hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hval]
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfFcen
section
open Matrix

namespace UpperTheory.Esk.CentralTermsContribution

theorem trace_conj {F : Type} [Field F] (γ δ : GL (Fin 2) F) :
    ((δ * γ * δ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = (γ : Matrix (Fin 2) (Fin 2) F).trace := by
  simp only [Units.val_mul]
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

end UpperTheory.Esk.CentralTermsContribution

theorem UpperTheory.Esk.pf_Fcen : UpperTheory.Esk.Fcen := by
  intro F _ γ δ htr h
  have h' : ((δ * γ * δ⁻¹ : GL (Fin 2) F) : UpperTheory.Esk.PG F) = (γ : UpperTheory.Esk.PG F) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]; exact h
  rw [QuotientGroup.eq] at h'
  set c := (δ * γ * δ⁻¹)⁻¹ * γ with hc
  obtain ⟨h1, h2, h3⟩ := UpperTheory.Esk.center_entries h'
  have hcv : (c : Matrix (Fin 2) (Fin 2) F) = c 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]
  have hγ : γ = (δ * γ * δ⁻¹) * c := by rw [hc]; group
  have hv : (γ : Matrix (Fin 2) (Fin 2) F) = ((δ * γ * δ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F) := by
    conv_lhs => rw [hγ]
    rw [Units.val_mul]
  have htr2 : c 0 0 * (γ : Matrix (Fin 2) (Fin 2) F).trace = 1 * (γ : Matrix (Fin 2) (Fin 2) F).trace := by
    conv_rhs => rw [hv, hcv, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, UpperTheory.Esk.CentralTermsContribution.trace_conj]
    ring
  have ht : c 0 0 = 1 := mul_right_cancel₀ htr htr2
  have hc1 : c = 1 := by
    ext : 1
    rw [hcv, ht, one_smul, Units.val_one]
  rw [hc1, mul_one] at hγ
  calc δ * γ = δ * γ * δ⁻¹ * δ := by group
    _ = γ * δ := by rw [← hγ]
end

