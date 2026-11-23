module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnReadingsNormalisedThetaPoints
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.FrameUnif.NormUnHol

theorem differentiableOn_det {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {g : ℕ} {s : Set V}
    {h : V → Matrix (Fin g) (Fin g) ℂ} (hh : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) s) :
    DifferentiableOn ℂ (fun b => (h b).det) s := by
  simp_rw [Matrix.det_apply']
  refine DifferentiableOn.fun_sum fun π _ => ?_
  have key : DifferentiableOn ℂ (∏ i, fun b => h b (π i) i) s :=
    Finset.prod_induction _ (fun f => DifferentiableOn ℂ f s) (fun _ _ ha hb => ha.mul hb)
      (differentiableOn_const (1 : ℂ)) (fun i _ => hh _ _)
  have e : (∏ i, fun b => h b (π i) i) = fun b => ∏ i, h b (π i) i := by
    funext b; simp [Finset.prod_apply]
  exact (differentiableOn_const _).mul (e ▸ key)

theorem normConst_ne_zero {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) {ξ : E} (hξ : ξ ≠ 0) :
    Real.sqrt (2 ^ g / ∏ j, (2 * ‖ty j ξ‖)) ≠ 0 := by
  have hpos : ∀ j, 0 < 2 * ‖ty j ξ‖ := fun j => by
    have : ty j ξ ≠ 0 := (map_ne_zero (ty j)).mpr hξ
    positivity
  exact (Real.sqrt_pos.mpr (div_pos (by positivity) (Finset.prod_pos fun j _ => hpos j))).ne'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

theorem wchar_gen {S : Type} [CommRing S] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t₀ : Sˣ) :
    wchar (ex Dw a n) (fun i => Option.elim i t₀ (fun _ => 1)) = (t₀ : S) ^ n := by
  unfold wchar ex
  simp [Fintype.prod_option]

theorem differentiableOn_thetaPt (hbc : Out.SecBaseChangeSt) (htw : Out.SecTwistSt) {g : ℕ}
    {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)}
    {r : ℕ} {M : ModelsOf F r} {k : Fin F.n} (T : ThetaData e F M k)
    (y : (Fin T.m → ℂ) → FrPt Xo c (CAt σ)) (hy : ∀ b ∈ T.co ⁻¹' (M.X k).dom, IsThetaPt T b 1 (y b))
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) (hf : f ∈ sec Xo c a n) :
    DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (evR Xo c f (y b))) (T.co ⁻¹' (M.X k).dom) := by
  intro b₀ hb₀
  obtain ⟨p, y₀, B, ψ, hBo, hb₀B, hBd, hψu, hψd⟩ :=
    _root_.GlobalTheory.HolChart.exists_chart_holomorphic hbc E H Dw l Xo c σ g e F r M k T b₀ hb₀
  choose z hz using fun b =>
    GlobalTheory.Frames.FramedBaseChange.exists_frMap hbc E H Dw l Xo c p.R (CAt σ) (ψ b) y₀
  have hx : ∀ b ∈ B, (y b).x = (z b).x := by
    intro b hb
    rw [(hy b (hBd hb)).1, hψu b hb]
    exact ((hz b).1).symm
  have hch : ∀ b, ∃ (gch : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))
      (sch : CAt σ), b ∈ B → FrChg gch sch (z b) (y b) := by
    intro b
    by_cases hb : b ∈ B
    · obtain ⟨gch, u, -, hc⟩ :=
        (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) (z b) (y b)).1 (hx b hb)
      exact ⟨gch, u, fun _ => hc⟩
    · exact ⟨fun _ => 0, 0, fun h => absurd h hb⟩
  choose gch sch hgs using hch
  have hall : ∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (gch b) (sch b) (z b) (y b) ∧
      IsThetaPt T b 1 (y b) := fun b hb => ⟨hz b, hgs b hb, hy b (hBd hb)⟩
  have hG := _root_.GlobalTheory.HolFrameMatrix.differentiableOn_frameMatrix E H Dw l Xo c σ g e F r M k T p.R y₀ B ψ (fun _ => 1) z y gch sch
    hBo hBd hψd hall
  have hS := _root_.GlobalTheory.HolGen.differentiableOn_generator_factor htw E H Dw l Xo c σ g e F r M k T p.R y₀ B ψ (fun _ => 1) z y gch sch
    hBo hBd hψd hall (differentiableOn_const 1)
  have hB := _root_.GlobalTheory.HolEval.differentiableOn_evR hbc E H Dw l Xo c σ (Fin T.m → ℂ) B p y₀ ψ z y gch sch
    (fun b hb => ⟨hz b, hgs b hb⟩) hψd hG hS a n f hf
  exact (hB.differentiableAt (hBo.mem_nhds hb₀B)).differentiableWithinAt

theorem differentiableOn_rdU : Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (k : Fin F.n) (T : ThetaData e F M k), IsNormUn T (un k) → ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, DifferentiableOn ℂ (rdU (unfOf e F M un) f k) (M.X k).dom := by
  intro hbc htw E _ _ _ H Dw l Xo c σ g e F r M un k T hT a n hD f hf
  obtain ⟨m, hm⟩ := hD.2
  rcases Set.eq_empty_or_nonempty (M.X k).dom with h0 | ⟨x₀, hx₀⟩
  · rw [h0]
    exact differentiableOn_empty
  have hx₀' : T.co.symm x₀ ∈ T.co ⁻¹' (M.X k).dom := by simpa using hx₀
  obtain ⟨y₀, -⟩ := _root_.GlobalTheory.FrameUnif.ThetaPtEx.exists_thetaPt htw E H Dw l Xo c σ g e F r M k T _ hx₀' 1 one_ne_zero
  have hy1 : ∀ b, ∃ y : FrPt Xo c (CAt σ), b ∈ T.co ⁻¹' (M.X k).dom → IsThetaPt T b 1 y := by
    intro b
    by_cases hb : b ∈ T.co ⁻¹' (M.X k).dom
    · obtain ⟨y, hy⟩ := _root_.GlobalTheory.FrameUnif.ThetaPtEx.exists_thetaPt htw E H Dw l Xo c σ g e F r M k T b hb 1 one_ne_zero
      exact ⟨y, fun _ => hy⟩
    · exact ⟨y₀, fun h => absurd h hb⟩
  choose y hy using hy1
  have hth := differentiableOn_thetaPt hbc htw T y hy a n f hf
  have key : ∀ x (hx : x ∈ (M.X k).dom),
      Formalism.L2.PjFree.toC (evR Xo c f (un k ⟨x, hx⟩)) =
        ((normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) * (T.h (T.co.symm x)).det) ^ m *
          Formalism.L2.PjFree.toC (evR Xo c f (y (T.co.symm x))) := by
    intro x hx
    have hb : T.co.symm x ∈ T.co ⁻¹' (M.X k).dom := by simpa using hx
    obtain ⟨κ, hκ2, hθ⟩ := hT ⟨x, hx⟩
    have hN : (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (normConst_ne_zero _ (M.X k).ξ0_ne)
    have hdet : (T.h (T.co.symm x)).det ≠ 0 := (T.norm _ hb).1.ne_zero
    have hκ : κ ≠ 0 := by
      intro h0
      apply mul_ne_zero hN hdet
      rw [← hκ2, h0]
      ring
    let t₀ : (CAt σ)ˣ := ⟨(κ : ℂ), (κ⁻¹ : ℂ), mul_inv_cancel₀ hκ, inv_mul_cancel₀ hκ⟩
    have hθ' : IsThetaPt T (T.co.symm x) (Formalism.L2.PjFree.toC (t₀ : CAt σ) * 1) (un k ⟨x, hx⟩) := by
      have h1 : Formalism.L2.PjFree.toC (t₀ : CAt σ) * 1 = κ := by
        show κ * 1 = κ
        ring
      rw [h1]
      exact hθ
    have hbor := _root_.GlobalTheory.frBor_of_isThetaPt htw E H Dw l Xo c σ g e F r M k T (T.co.symm x) hb 1 t₀ _ _
      (hy _ hb) hθ'
    have hred : IsReduced (CAt σ) := by
      show IsReduced ℂ
      infer_instance
    have hev := (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hbc E H Dw l Xo c).2.2.2.2.2.2 (CAt σ) hred a n f hf _ _ _ hbor
    rw [hev, wchar_gen]
    have e1 : Formalism.L2.PjFree.toC ((t₀ : CAt σ) ^ n * evR Xo c f (y (T.co.symm x))) =
        κ ^ n * Formalism.L2.PjFree.toC (evR Xo c f (y (T.co.symm x))) := rfl
    rw [e1, hm, ← two_mul, pow_mul, hκ2]
  have hΦ : DifferentiableOn ℂ (fun b => ((normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) *
      (T.h b).det) ^ m * Formalism.L2.PjFree.toC (evR Xo c f (y b))) (T.co ⁻¹' (M.X k).dom) :=
    (((differentiableOn_const _).mul (differentiableOn_det fun i j => (T.hol i j).1)).pow m).mul hth
  have hcomp := hΦ.comp T.co.symm.differentiableOn (fun x hx => by simpa using hx)
  refine hcomp.congr fun x hx => ?_
  unfold Formalism.L2.PjFree.rdU unfOf
  simp only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos hx]
  exact key x hx

end GlobalTheory.FrameUnif.NormUnHol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory


set_option synthInstance.maxHeartbeats 200000 in
theorem reading_linearIndependent_and_injective : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), IsUnf U → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ (m : ℕ) (b : Fin m → Rul Xo c), (∀ i, b i ∈ sec Xo c a n) → LinearIndependent c.F b → LinearIndependent ℂ (fun i => rdU U (b i))) ∧ ∀ f ∈ sec Xo c a n, (∀ k, ∀ x ∈ (U.X k).dom, rdU U f k x = 0) → f = 0 := by
  intro hS E _ _ _ H Dw l Xo c σ r U hU a n
  have h : ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ),
      ∃ (k : U.Comp) (x : (U.X k).dom) (u : ℂ), ∀ f ∈ sec Xo c a n,
        cvalR σ (ψ (f p y)) = u * rdU U f k x.1 :=
    fun p y ψ => _root_.GlobalTheory.FrameUnif.test_value_eq_const_mul_reading hS E H Dw l Xo c σ r U hU a n p y ψ
  have : CharZero c.F := RingHom.charZero σ
  refine ⟨fun m b hb hli => ?_, fun f hf h0 => ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro w hw
    have hθ : ∀ θ : Module.Dual c.F (CAt σ), ∀ i, θ (toCAt σ (w i)) = 0 := by
      intro θ
      have hz : ∑ i, θ (toCAt σ (w i)) • b i = 0 := by
        funext p y
        have hpt := descend_cpts σ p (fun i => b i p y) w (fun ψ => by
          obtain ⟨k', x, u, hk⟩ := h p y ψ
          have e1 : ∀ i, w i * cvalR σ (ψ (b i p y)) = u * (w i * rdU U (b i) k' x.1) := by
            intro i; rw [hk (b i) (hb i)]; ring
          have e2 := congrFun (congrFun hw k') x.1
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e2
          simp_rw [e1]
          rw [← Finset.mul_sum, e2, mul_zero]) θ
        simpa [Finset.sum_apply] using hpt
      exact fun i => Fintype.linearIndependent_iff.1 hli _ hz i
    intro i
    exact (Module.forall_dual_apply_eq_zero_iff c.F (toCAt σ (w i))).1 fun θ => hθ θ i
  · funext p y
    show f p y = 0
    refine eq_zero_of_cpts σ p _ fun ψ => ?_
    obtain ⟨k, x, u, hk⟩ := h p y ψ
    have e := hk f hf
    rw [h0 k x.1 x.2, mul_zero] at e
    exact e

end GlobalTheory
end

