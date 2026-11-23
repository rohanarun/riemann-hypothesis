module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0569
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0051
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0580
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0581

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointStalkFrameVectorsEq
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase


attribute [local instance] Over.cartesianMonoidalCategory in
theorem isCombAtG_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}
    {t : SAB H X0} {R : Type} [CommRing R] {x0 : Sp R ⟶ X0} {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)}
    {cf : Fin m → R} {w w' : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t x0 v cf w)
    (h' : IsCombAtG t x0 v cf w') : w = w' := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨u', hu', rfl⟩ := h'
  have : u = u' := funext fun k => Over.OverMorphism.ext ((hu k).trans (hu' k).symm)
  rw [this]

theorem frameAt_v_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (A₀ A : Mat Dw.mult X.Fn) (y : CxPts X.str (σ.comp e.toRingHom)) (x x' : Sp ℂ ⟶ Z.X) (g : EigFrame Z σ x) (g' : EigFrame Z σ x'), FrameAt e f₀ A₀ A y g → FrameAt e f₀ A₀ A y g' → ∀ τ i, g.v τ i = g'.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ X j f₀ A₀ A y x x' g g' h h' τ i
  obtain ⟨φ, fz, ψ, hy, hc, hg⟩ := h
  obtain ⟨φ', fz', ψ', hy', hc', hg'⟩ := h'
  have hψ : ψ = ψ' := EigLoc.spMap_inj ((cancel_mono (X.X.fromSpecStalk (under y))).1 (hy.symm.trans hy'))
  subst hψ
  have hι := IsFractionRing.injective (X.X.presheaf.stalk (under y)) X.X.functionField
  obtain rfl : φ = φ' := RingHom.ext fun a => hι ((RingHom.congr_fun hc.2.1 a).symm.trans (RingHom.congr_fun hc'.2.1 a))
  obtain ⟨fK, hK⟩ := fz.exists_isMap _ hc.2.1 hc.1
  obtain ⟨fK', hK'⟩ := fz'.exists_isMap _ hc.2.1 hc.1
  have e1 : fK.co f₀ τ = fK'.co f₀ τ := by
    rw [EigFrame.co_eq (T := Matrix.of fun a k => (A₀ * A⁻¹) τ k a) fun k => by
        rw [funext (hK τ)]; exact hc.2.2 τ k,
      EigFrame.co_eq (T := Matrix.of fun a k => (A₀ * A⁻¹) τ k a) fun k => by
        rw [funext (hK' τ)]; exact hc'.2.2 τ k]
  have e2 : fK.co fK' τ = 1 := by
    rw [← fK.co_mul f₀ fK' τ, e1, fK'.co_mul, fK'.co_self]
  have e3 : fz.co fz' τ = 1 := by
    have e := (hK.co τ hK' hc.1).symm.trans e2
    ext a b
    have e' := congrFun (congrFun e a) b
    rw [Matrix.map_apply] at e'
    apply hι
    rw [e', Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e4 := fz.co_spec fz' τ i
  rw [e3] at e4
  have e5 : fz'.v τ i = fz.v τ i := isCombAtG_eq e4 (by
    convert isCombAtG_single Z.t _ (fz.tan τ) i using 2
    simp only [Matrix.one_apply, Pi.single_apply])
  rw [hg τ i, hg' τ i, e5]

end GlobalTheory.LieBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

section ConeFacts

variable {X : Type} [AddCommGroup X]

theorem apply_eq_of_toReal_eq {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {c : Fin m → ℝ}
    {β : LinearMap.BilinForm ℤ X} (h : toReal β = ∑ i, c i • toReal (γ i)) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    (ℓ β : ℝ) = ∑ i, c i * ℓ (γ i) := by
  have h0 : ∑ i : Fin (m + 1), (Fin.cons (-1) c : Fin (m + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β γ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, LinearMap.id_apply, neg_one_smul, ← h, neg_add_cancel]
  have key := sum_mul_eq_zero_of_sum_toReal (fun _ _ hab => hab) ℓ h0
  rw [Fin.sum_univ_succ] at key
  simp only [Fin.cons_zero, Fin.cons_succ] at key
  linarith

theorem InRCone.apply_nonneg {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X}
    (h : InRCone γ β) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (hℓ : ∀ i, 0 ≤ ℓ (γ i)) : 0 ≤ ℓ β := by
  obtain ⟨c, hc, hβ⟩ := h
  have e := apply_eq_of_toReal_eq hβ ℓ
  have hr : (0 : ℝ) ≤ ℓ β := by
    rw [e]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (by exact_mod_cast hℓ i)
  exact_mod_cast hr

theorem inRCone_trans {m n : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {δ : Fin n → LinearMap.BilinForm ℤ X}
    (hδ : ∀ j, InRCone γ (δ j)) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone δ β) : InRCone γ β := by
  choose a ha hδe using hδ
  obtain ⟨b, hb, hβe⟩ := hβ
  refine ⟨fun i => ∑ j, b j * a j i, fun i => Finset.sum_nonneg fun j _ => mul_nonneg (hb j) (ha j i), ?_⟩
  rw [hβe]
  simp only [hδe, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

theorem eq_zero_of_toReal_rel {a b : ℕ} {u : Fin a → LinearMap.BilinForm ℤ X} {v : Fin b → LinearMap.BilinForm ℤ X}
    (hind : ∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0)
    {r : Fin a → ℝ} {s : Fin b → ℝ} (h : ∑ j, r j • toReal (u j) = ∑ k, s k • toReal (v k)) : r = 0 := by

  have hpt : ∀ x y : X, ∑ j, r j * (u j x y : ℝ) = ∑ k, s k * (v k x y : ℝ) := by
    intro x y
    have hxy := congrArg (fun B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ => B x y) h
    simpa [LinearMap.sum_apply, toReal_apply] using hxy

  suffices hf : ∀ (f : Module.Dual ℚ ℝ) (j : Fin a), f (r j) = 0 by
    funext j
    exact (Module.forall_dual_apply_eq_zero_iff ℚ (r j)).mp fun f => hf f j
  intro f
  have e : ∀ (t : ℝ) (n : ℤ), f (t * n) = n * f t := by
    intro t n
    rw [mul_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
  have hq : ∀ x y : X, ∑ j, ((u j x y : ℤ) : ℚ) * f (r j) = ∑ k, ((v k x y : ℤ) : ℚ) * f (s k) := by
    intro x y
    have hxy := congrArg f (hpt x y)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum] at hxy
    simpa only [e] using hxy

  let N : ℕ := (∏ j, (f (r j)).den) * ∏ k, (f (s k)).den
  have hN : (N : ℚ) ≠ 0 := by
    have : N ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => (f (r j)).den_nz)
      (Finset.prod_ne_zero_iff.mpr fun k _ => (f (s k)).den_nz)
    exact_mod_cast this
  have key : ∀ q : ℚ, q.den ∣ N → ((((N / q.den : ℕ) : ℤ) * q.num : ℤ) : ℚ) = N * q := by
    intro q hq'
    have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div hq' hd]
    rw [div_mul_eq_mul_div, mul_div_assoc, Rat.num_div_den]
  have hdr : ∀ j, (f (r j)).den ∣ N := fun j =>
    dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) _
  have hds : ∀ k, (f (s k)).den ∣ N := fun k =>
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) _
  let c : Fin a → ℤ := fun j => ((N / (f (r j)).den : ℕ) : ℤ) * (f (r j)).num
  let d : Fin b → ℤ := fun k => ((N / (f (s k)).den : ℕ) : ℤ) * (f (s k)).num
  have hc : ∀ j, (c j : ℚ) = N * f (r j) := fun j => key _ (hdr j)
  have hd : ∀ k, (d k : ℚ) = N * f (s k) := fun k => key _ (hds k)
  have hrel : ∑ j, c j • u j = ∑ k, d k • v k := by
    ext x y
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Int.cast_injective (α := ℚ)
    push_cast
    simp only [hc, hd]
    have := hq x y
    calc ∑ j, (N : ℚ) * f (r j) * (u j x y : ℚ) = N * ∑ j, ((u j x y : ℤ) : ℚ) * f (r j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = N * ∑ k, ((v k x y : ℤ) : ℚ) * f (s k) := by rw [this]
      _ = ∑ k, (N : ℚ) * f (s k) * (v k x y : ℚ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have h0 := hind d c hrel
  intro j
  have hcj : (c j : ℚ) = 0 := by rw [h0]; simp
  rw [hc j] at hcj
  have : (f (r j) : ℚ) = 0 := (mul_eq_zero.mp hcj).resolve_left hN
  exact_mod_cast this

end ConeFacts

section CellFacts

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem IsCell.reindex {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (h : IsCell bar φ γ) (e : Fin m' ≃ Fin m) :
    IsCell bar φ fun i => γ (e i) := by
  obtain ⟨hmem, hnn, hlin, hstr⟩ := h
  refine ⟨fun i => hmem (e i), fun i y => hnn (e i) y, ?_, ?_⟩
  · intro c hc
    convert hlin (fun i => c (e.symm i)) (fun i => hc _) using 1
    · congr 1
      funext x y
      exact Fintype.sum_equiv e _ _ (fun i => by simp)
    · exact Fintype.sum_equiv e _ _ (fun i => by simp)
  · obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hstr
    refine ⟨N, ℓ, hN, fun i => h1 (e i), h2, ?_⟩
    intro β hβ hβn heq
    obtain ⟨k, c, hk, hkc⟩ := h3 β hβ hβn heq
    refine ⟨k, fun i => c (e i), hk, ?_⟩
    rw [hkc]
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm

end CellFacts

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDifferentiableAtOfForms
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Filter Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolCoordEv

theorem eventually_differentiableAt_of_forms {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {g : ℕ}
    (W : V → Fin g → ℂ) (b₀ : V) (H : ∀ w : Fin g → ℂ, (∀ L : V → ((Fin g → ℂ) →L[ℂ] ℂ),
      (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ L b) → (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ (fun b => L b (W b)) b) →
        L b₀ w = 0) → w = 0) : ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ W b := by
  let M : Submodule ℂ (Module.Dual ℂ (Fin g → ℂ)) :=
    { carrier := {l | ∃ L : V → ((Fin g → ℂ) →L[ℂ] ℂ), (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ L b) ∧
        (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ (fun b => L b (W b)) b) ∧ ∀ w, L b₀ w = l w}
      add_mem' := by
        rintro l l' ⟨L, h1, h2, h3⟩ ⟨L', h1', h2', h3'⟩
        refine ⟨fun b => L b + L' b, ?_, ?_, fun w => by simp [h3, h3']⟩
        · filter_upwards [h1, h1'] with b hb hb' using hb.add hb'
        · filter_upwards [h2, h2'] with b hb hb' using hb.add hb'
      zero_mem' := ⟨fun _ => 0, Eventually.of_forall fun _ => differentiableAt_const _,
        Eventually.of_forall fun _ => by simp, by simp⟩
      smul_mem' := by
        rintro c l ⟨L, h1, h2, h3⟩
        refine ⟨fun b => c • L b, ?_, ?_, fun w => by simp [h3]⟩
        · filter_upwards [h1] with b hb using hb.const_smul c
        · filter_upwards [h2] with b hb using hb.const_smul c }
  have hM : M = ⊤ := by
    have h0 : M.dualCoannihilator = ⊥ := by
      refine eq_bot_iff.2 fun w hw => H w fun L h1 h2 => ?_
      exact (Submodule.mem_dualCoannihilator w).1 hw (L b₀).toLinearMap ⟨L, h1, h2, fun _ => rfl⟩
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := M), h0, Submodule.dualAnnihilator_bot]
  have hj : ∀ j : Fin g, LinearMap.proj j ∈ M := fun j => hM ▸ Submodule.mem_top
  choose L h1 h2 h3 using hj
  let J : V → ((Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) := fun b => ContinuousLinearMap.pi fun j => L j b
  have hJ : ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ J b := by
    filter_upwards [eventually_all.2 h1] with b hb
    exact (ContinuousLinearMap.piEquivL ℂ (Fin g → ℂ) (fun _ : Fin g => ℂ)).differentiableAt.comp b
      (differentiableAt_pi.2 hb)
  have hJ0 : IsUnit (J b₀) := by
    have : J b₀ = 1 := by
      ext1 w
      funext j
      exact h3 j w
    rw [this]; exact isUnit_one
  have hU : ∀ᶠ b in 𝓝 b₀, IsUnit (J b) :=
    hJ.self_of_nhds.continuousAt.eventually (Units.isOpen.mem_nhds hJ0)
  filter_upwards [hJ, hU, eventually_all.2 h2] with b hJb hUb hWb
  have hW : DifferentiableAt ℂ (fun b => J b (W b)) b := differentiableAt_pi.2 hWb
  refine ((hJb.inverse hUb).clm_apply hW).congr_of_eventuallyEq ?_
  filter_upwards [hJb.continuousAt.eventually (Units.isOpen.mem_nhds hUb)] with b' hb'
  have := congrArg (fun T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) => T (W b')) (Ring.inverse_mul_cancel _ hb')
  exact this.symm


open GlobalTheory.TangentOrigin GlobalTheory.HolLieFrame in
theorem exists_hol_snd_ev {V R : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CommRing R] {X : Scheme.{0}}
    (ψ : Sp (DualNumber R) ⟶ X) (ev : V → (R →+* ℂ)) (b₀ : V)
    (hev : ∀ c, ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ (fun b => ev b c) b)
    (U : X.Opens) (f : Γ(X, U)) (h₀ : ⊤ ≤ (spMap (Chart.dualMapR (ev b₀)) ≫ ψ) ⁻¹ᵁ U) :
    ∃ F : V → ℂ, (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ F b) ∧ ∀ᶠ b in 𝓝 b₀,
      ∃ h : ⊤ ≤ (spMap (Chart.dualMapR (ev b)) ≫ ψ) ⁻¹ᵁ U, (evalPt _ U h f).snd = F b := by
  have h₁ : ⊤ ≤ (spMap (fstC.comp (Chart.dualMapR (ev b₀))) ≫ ψ) ⁻¹ᵁ U := by
    have := (top_le_preimage_iff _ U).1 h₀
    rwa [← Category.assoc, ← Spec.map_comp] at this
  obtain ⟨r, a, hr, H⟩ := exists_fraction ψ U f _ h₁
  have hf : ∀ b (x : DualNumber R), (Chart.dualMapR (ev b) x).fst = ev b x.fst := fun b x => by simp [Chart.dualMapR]
  have hs : ∀ b (x : DualNumber R), (Chart.dualMapR (ev b) x).snd = ev b x.snd := fun b x => by simp [Chart.dualMapR]
  have hr' : ev b₀ r.fst ≠ 0 := (hf b₀ r) ▸ hr
  have hne : ∀ᶠ b in 𝓝 b₀, ev b r.fst ≠ 0 := (hev r.fst).self_of_nhds.continuousAt.eventually_ne hr'
  refine ⟨fun b => (ev b a.snd - ev b a.fst * (ev b r.fst)⁻¹ * ev b r.snd) * (ev b r.fst)⁻¹, ?_, ?_⟩
  · filter_upwards [hev a.snd, hev a.fst, hev r.fst, hev r.snd, hne] with b h1 h2 h3 h4 h5
    exact (h1.sub ((h2.mul (h3.inv h5)).mul h4)).mul (h3.inv h5)
  filter_upwards [hne] with b hb
  obtain ⟨h, e⟩ := H _ (Chart.dualMapR (ev b)) (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by rw [hf]; exact hb.isUnit))
  refine ⟨h, ?_⟩
  have e1 := congrArg TrivSqZeroExt.fst e
  have e2 := congrArg TrivSqZeroExt.snd e
  rw [TrivSqZeroExt.fst_mul, hf, hf] at e1
  rw [DualNumber.snd_mul, hf, hs, hs] at e2
  rw [← e1, ← e2]
  field_simp
  ring

end GlobalTheory.HolCoordEv

namespace GlobalTheory.HolCoordEv

open GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_unique)

theorem eventually_differentiableAt_dir {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
    (σ : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) {n : ℕ}
    {B : Set (Fin n → ℂ)} (hB : IsOpen B) {P : (Fin n → ℂ) → ((Fu.Di i).La →+ (Fin g → ℂ))}
    {p : (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c)}
    (hu : ∀ b, Fu.u i (P b) = p b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (hP : ∀ b, IsPeriod (Fu.Di i) ty (P b)) (hPd : ∀ a, DifferentiableOn ℂ (fun b => P b a) B)
    (hs : ∀ b, p b ≫ pullback.snd _ _ = spMap σ) {R : Type} [CommRing R] (v : Sp (DualNumber R) ⟶ Z.t.G.left)
    (ev : (Fin n → ℂ) → (R →+* ℂ)) {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ B)
    (hev : ∀ t, ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ (fun b => ev b t) b) (W : (Fin n → ℂ) → Fin g → ℂ)
    (hW : ∀ᶠ b in 𝓝 b₀, IsDerivAt0 (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b)
      (spMap (Formalism.L2.Pj.dualMap (ev b)) ≫ v)) :
    ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ W b := by
  classical
  have h1 := Fu.hol i n B P hB ⟨fun b _ => hP b, hPd⟩
  have hp : IsHolTo B p := TrueCx.TorHolo.isHolTo_of_fst _ _ hB (spMap σ) hs
    (LocLift.isHolTo_congr h1.1 fun b _ => (hu b).symm)
  have h2 := TrueCx.TorFrHolo.isHolTo_lift Z.m0.toSABMap.cart.1 hB (fun b z => (Fu.ex i (P b) z).left) p h1.2 hp
    (fun b z => by rw [Over.w (Fu.ex i (P b) z), ← hu b]; rfl)
  have hFt : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) =>
      liftEx Z Fu (p bz.1) i (P bz.1) (hu bz.1) bz.2 ≫ Z.m.φ) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 Z.m.φ
  have hExp : IsExpAt Z.t (p b₀ ≫ Z.jQ ≫ genι Z)
      (pushEx Z Fu (p b₀) i (P b₀) (p b₀ ≫ Z.jQ ≫ genι Z) (hu b₀) rfl) :=
    isExpAt_pushEx E H Dw l Xo c O β Z g ty _ Fu (p b₀) i (P b₀) (p b₀ ≫ Z.jQ ≫ genι Z) (hu b₀) rfl (hP b₀)
  have hW' : ∀ᶠ b in 𝓝 b₀, IsDerivAt0 (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b)
      (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (ev b)) ≫ v) := by
    filter_upwards [hW] with b hb
    rwa [← HolFrameMatrix.dualMap_eq]
  refine eventually_differentiableAt_of_forms W b₀ fun w hw => ?_
  have hw' : ∀ (O : Z.t.G.left.Opens) (f : Γ(Z.t.G.left, O)),
      ⊤ ≤ (liftEx Z Fu (p b₀) i (P b₀) (hu b₀) 0 ≫ Z.m.φ) ⁻¹ᵁ O →
      fderiv ℂ (fun z => valAt' (liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) O f) 0 w = 0 := by
    intro O f hO
    refine hw (fun b => fderiv ℂ (fun z => valAt' (liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) O f) 0) ?_ ?_
    · have hc : ContinuousAt (fun b : Fin n → ℂ => (b, (0 : Fin g → ℂ))) b₀ :=
        continuousAt_id.prodMk continuousAt_const
      filter_upwards [hc.preimage_mem_nhds ((hFt O f).1.mem_nhds ⟨⟨hb₀, trivial⟩, hO⟩)] with b hb
      exact HolLieFrame.differentiableAt_fderiv
        (e := fun b z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) hFt hb.1.1 O f hb.2
    · obtain ⟨Fn, hF, hF'⟩ := exists_hol_snd_ev v ev b₀ hev O f
        ((TangentOrigin.top_le_preimage_iff _ O).2 (by rw [hW'.self_of_nhds.1]; exact hO))
      filter_upwards [hF, (hF'.and hW').eventually_nhds] with b hFb hnear
      refine hFb.congr_of_eventuallyEq ?_
      filter_upwards [hnear] with b' ⟨⟨h, e'⟩, hd⟩
      exact (hd.2 O h f).symm.trans e'
  have d₁ := LocalLift.isDerivAt0_const (fun z => liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) w hw'
  have d₀ := LocalLift.isDerivAt0_const (fun z => liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) 0
    fun _ _ _ => map_zero _
  obtain ⟨u, ⟨hut, hud⟩, -⟩ := hExp.2.1 0
  have hu0 := isDerivAt0_unique hud d₀
  obtain ⟨w', -, hw''⟩ := hExp.2.2 u hut
  have a1 : w = w' := hw'' w (by rw [hu0]; exact d₁)
  have a0 : (0 : Fin g → ℂ) = w' := hw'' 0 hud
  exact a1.trans a0.symm

end GlobalTheory.HolCoordEv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedSiegelBasisBalancedForms
section
noncomputable section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

theorem exists_siegel_split {X X₁ : Type} [AddCommGroup X] [AddCommGroup X₁] [Module.Finite ℤ X] [Module.Free ℤ X]
    [Module.Finite ℤ X₁] [Module.Free ℤ X₁] (r : X →ₗ[ℤ] X₁) (σ : X₁ →ₗ[ℤ] X) (hrσ : ∀ y, r (σ y) = y)
    (B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (hs₀ : ∀ y z, B₀ y z = B₀ z y) (hp₀ : IsPosDef B₀)
    (B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) (hs₁ : ∀ y z, B₁ y z = B₁ z y) (hp₁ : IsPosDef B₁)
    (n : ℕ) (hn : Module.finrank ℤ X = n) :
    ∃ (b : Module.Basis (Fin n) ℤ X) (d d' : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) (t : ℝ),
      IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ (∀ i j, B₁ (r (b i)) (r (b j)) = gram d u i j) ∧
      ∀ i j, t * B₀ (b i - σ (r (b i))) (b j - σ (r (b j))) + B₁ (r (b i)) (r (b j)) = gram d' u i j := by
  classical
  have hfree : Module.Free ℤ (LinearMap.ker r) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, ⟨bK⟩⟩ : ∃ s, Nonempty (Module.Basis (Fin s) ℤ (LinearMap.ker r)) := ⟨_, ⟨Module.finBasis ℤ _⟩⟩
  obtain ⟨m, ⟨bQ⟩⟩ : ∃ m, Nonempty (Module.Basis (Fin m) ℤ X₁) := ⟨_, ⟨Module.finBasis ℤ _⟩⟩
  let BK : LinearMap.ker r →ₗ[ℤ] LinearMap.ker r →ₗ[ℤ] ℝ := B₀.compl₁₂ (LinearMap.ker r).subtype (LinearMap.ker r).subtype
  have hpK : IsPosDef BK := fun k x hx c hc =>
    hp₀ k (fun i => (x i : X)) (hx.map' (LinearMap.ker r).subtype (Submodule.ker_subtype _)) c hc
  obtain ⟨b₁, d₁, u₁, hS₁, hd₁, hg₁⟩ := _root_.GlobalTheory.RedTh.RedBasis.exists_siegel_basis s _ bK BK (fun y z => hs₀ _ _) hpK
  obtain ⟨b₂, d₂, u₂, hS₂, hd₂, hg₂⟩ := _root_.GlobalTheory.RedTh.RedBasis.exists_siegel_basis m _ bQ B₁ hs₁ hp₁
  obtain ⟨t, d, d', u, -, hS, hS', hd', g11, g12, g22⟩ := _root_.GlobalTheory.RedTh.siegelData_glue_scaled s m d₁ u₁ d₂ u₂ hS₁ hS₂ hd₁ hd₂
  let p : X →ₗ[ℤ] LinearMap.ker r := LinearMap.codRestrict _ (LinearMap.id - σ ∘ₗ r) fun x => by
    simp [hrσ]
  let e : X ≃ₗ[ℤ] LinearMap.ker r × X₁ := LinearEquiv.ofLinear (p.prod r) ((LinearMap.ker r).subtype.coprod σ)
    (by
      ext x
      · simp [p, LinearMap.mem_ker.1 x.2]
      · simp [LinearMap.mem_ker.1 x.2]
      · simp [p, hrσ]
      · simp [hrσ])
    (by ext x; simp [p])
  let c : Module.Basis (Fin (s + m)) ℤ X := ((b₁.prod b₂).map e.symm).reindex finSumFinEquiv
  have hc₁ : ∀ i, c (Fin.castAdd m i) = (b₁ i : X) := fun i => by
    have : finSumFinEquiv.symm (Fin.castAdd m i) = Sum.inl i := finSumFinEquiv_symm_apply_castAdd i
    simp [c, this, e]
  have hc₂ : ∀ j, c (Fin.natAdd s j) = σ (b₂ j) := fun j => by
    have : finSumFinEquiv.symm (Fin.natAdd s j) = Sum.inr j := finSumFinEquiv_symm_apply_natAdd j
    simp [c, this, e]
  have hnm : n = s + m := by
    rw [← hn, Module.finrank_eq_card_basis c, Fintype.card_fin]
  subst hnm
  have hr₁ : ∀ i, r (c (Fin.castAdd m i)) = 0 := fun i => by rw [hc₁]; exact (b₁ i).2
  have hr₂ : ∀ j, r (c (Fin.natAdd s j)) = b₂ j := fun j => by rw [hc₂, hrσ]
  have hq₁ : ∀ i, c (Fin.castAdd m i) - σ (r (c (Fin.castAdd m i))) = (b₁ i : X) := fun i => by
    rw [hr₁, map_zero, sub_zero, hc₁]
  have hq₂ : ∀ j, c (Fin.natAdd s j) - σ (r (c (Fin.natAdd s j))) = 0 := fun j => by rw [hr₂, hc₂, sub_self]
  refine ⟨c, d, d', u, t, hS, hS', hd', fun i j => ?_, fun i j => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [hr₁, (g11 _ _).1]
    · simp [hr₁, (g12 _ _).1]
    · simp [hr₁, (g12 _ _).2.1]
    · rw [hr₂, hr₂, hg₂, (g22 _ _).1]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [hq₁, hq₁, hr₁, hr₁, map_zero, add_zero, (g11 _ _).2, ← hg₁]
      rfl
    · rw [hq₁, hq₂, hr₁]
      simp only [map_zero, LinearMap.zero_apply, mul_zero, add_zero]
      exact (g12 _ _).2.2.1.symm
    · rw [hq₂, hq₁, hr₁]
      simp only [map_zero, LinearMap.zero_apply, mul_zero, add_zero]
      exact (g12 _ _).2.2.2.symm
    · rw [hq₂, hq₂, hr₂, hr₂]
      simp only [map_zero, LinearMap.zero_apply, mul_zero, zero_add]
      rw [hg₂, (g22 _ _).2]

theorem projective_int_of_projective {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] [Module.Free ℤ O]
    [Module.Projective O M] : Module.Projective ℤ M := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective O M›
  let i : M →ₗ[ℤ] (M →₀ O) := s.toAddMonoidHom.toIntLinearMap
  let p : (M →₀ O) →ₗ[ℤ] M := (Finsupp.linearCombination O id).toAddMonoidHom.toIntLinearMap
  exact Module.Projective.of_split i p (LinearMap.ext fun x => LinearMap.congr_fun hs x)

theorem exists_adapted_siegel_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), B₀ ∈ realForms H.bar X → IsPosDef B₀ → ∀ n : ℕ, Module.finrank ℤ X = n → ∀ B ∈ psdCone (bar := H.bar) (X := X), ∃ (b : Module.Basis (Fin n) ℤ X) (d d' : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) (B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ B' ∈ realForms H.bar X ∧ (∀ i j, B (b i) (b j) = gram d u i j) ∧ ∀ i j, B' (b i) (b j) = gram d' u i j := by
  intro E _ _ _ H X _ _ _ _ B₀ hB₀ hp₀ n hn B hB
  obtain ⟨X₁, _, _, _, r, B₁, hr, hB₁, hp₁, hBr⟩ := hB
  have : Module.Finite (𝓞 E) X₁ := Module.Finite.of_surjective r hr
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property r LinearMap.id hr
  have hrσ : ∀ y, r (σ y) = y := fun y => LinearMap.congr_fun hσ y
  have : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have : Module.Finite ℤ X₁ := Module.Finite.trans (𝓞 E) X₁
  have : Module.Projective ℤ X := projective_int_of_projective (O := 𝓞 E)
  have : Module.Projective ℤ X₁ := projective_int_of_projective (O := 𝓞 E)
  have : Module.Free ℤ X := Module.free_of_finite_type_torsion_free'
  have : Module.Free ℤ X₁ := Module.free_of_finite_type_torsion_free'
  let rZ : X →ₗ[ℤ] X₁ := r.toAddMonoidHom.toIntLinearMap
  let σZ : X₁ →ₗ[ℤ] X := σ.toAddMonoidHom.toIntLinearMap
  obtain ⟨b, d, d', u, t, hS, hS', hd', hg, hg'⟩ := exists_siegel_split rZ σZ hrσ B₀ hB₀.1 hp₀ B₁ hB₁.1 hp₁ n hn
  let π : X →ₗ[𝓞 E] X := LinearMap.id - σ ∘ₗ r
  let πZ : X →ₗ[ℤ] X := π.toAddMonoidHom.toIntLinearMap
  refine ⟨b, d, d', u, t • B₀.compl₁₂ πZ πZ + B₁.compl₁₂ rZ rZ, hS, hS', hd', ⟨fun y z => ?_, fun a y z => ?_⟩,
    fun i j => (hBr _ _).trans (hg i j), fun i j => (hg' i j).symm ▸ ?_⟩
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply]
    rw [hB₀.1, hB₁.1]
  · have e₁ : ∀ y, πZ (a • y) = a • πZ y := fun y => π.map_smul a y
    have e₂ : ∀ y, rZ (a • y) = a • rZ y := fun y => r.map_smul a y
    have e₃ : ∀ y, πZ (H.bar a • y) = H.bar a • πZ y := fun y => π.map_smul _ y
    have e₄ : ∀ y, rZ (H.bar a • y) = H.bar a • rZ y := fun y => r.map_smul _ y
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply, e₁, e₂, e₃, e₄]
    rw [hB₀.2, hB₁.2]
  · rfl

end GlobalTheory.RedTh
end
end

