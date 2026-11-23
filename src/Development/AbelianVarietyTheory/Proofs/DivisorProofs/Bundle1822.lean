module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverReadingEqPowMulMovedFrameReading
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGenEqOneOfFrOver
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0607
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1717
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1810
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelComponentTransportReadsCuspFormsConstMul
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

theorem exists_const_of_forall_unit_mul {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {O : Set V} (hO : IsOpen O) (hc : IsPreconnected O) (hne : O.Nonempty) {ι : Type} (P Q : ι → V → ℂ)
    (hP : ∀ j, DifferentiableOn ℂ (P j) O) (hQ : ∀ j, DifferentiableOn ℂ (Q j) O)
    (h : ∀ x ∈ O, ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ j, P j x = u * Q j x) :
    ∃ c : ℂˣ, ∀ j, ∀ x ∈ O, P j x = c * Q j x := by
  by_cases h0 : ∃ j, ∃ x₁ ∈ O, Q j x₁ ≠ 0
  · obtain ⟨j₀, x₁, hx₁, hq⟩ := h0
    obtain ⟨u₁, hu₁, hPu⟩ := h x₁ hx₁
    have hu0 : u₁ ≠ 0 := by
      intro e
      rw [e, norm_zero] at hu₁
      exact zero_ne_one hu₁

    have step : ∀ j, ∀ x ∈ O, P j x + (1 - Q j x₁) / Q j₀ x₁ * P j₀ x =
        u₁ * (Q j x + (1 - Q j x₁) / Q j₀ x₁ * Q j₀ x) := by
      intro j
      set μ : ℂ := (1 - Q j x₁) / Q j₀ x₁ with hμ
      obtain ⟨-, c', hc'⟩ := GlobalTheory.exists_eq_const_mul_of_forall_exists_norm_eq V Unit O hO hc hne
        (fun x => P j x + μ * P j₀ x) (fun _ x => Q j x + μ * Q j₀ x)
        ((hP j).add ((hP j₀).const_smul μ))
        (fun _ => (hQ j).add ((hQ j₀).const_smul μ))
        (fun x hx => by
          obtain ⟨u, hu, hPx⟩ := h x hx
          refine ⟨(), ?_⟩
          simp only [hPx, ← mul_add, mul_left_comm μ u, norm_mul, hu, one_mul])
      have hQ1 : Q j x₁ + μ * Q j₀ x₁ = 1 := by
        rw [hμ, div_mul_cancel₀ _ hq]
        ring
      have hc1 : c' = u₁ := by
        have e := hc' x₁ hx₁
        rw [hQ1, mul_one, hPu j, hPu j₀, mul_left_comm μ u₁, ← mul_add, hQ1, mul_one] at e
        exact e.symm
      intro x hx
      rw [hc' x hx, hc1]
    have h₀ : ∀ x ∈ O, P j₀ x = u₁ * Q j₀ x := by
      intro x hx
      have e := step j₀ x hx
      have hne' : 1 + (1 - Q j₀ x₁) / Q j₀ x₁ ≠ 0 := by
        rw [add_div' _ _ _ hq]
        simp [hq]
      have : (1 + (1 - Q j₀ x₁) / Q j₀ x₁) * (P j₀ x - u₁ * Q j₀ x) = 0 := by
        linear_combination e
      rcases mul_eq_zero.1 this with h1 | h1
      · exact (hne' h1).elim
      · exact sub_eq_zero.1 h1
    refine ⟨Units.mk0 u₁ hu0, fun j x hx => ?_⟩
    have e := step j x hx
    rw [Units.val_mk0]
    linear_combination e - (1 - Q j x₁) / Q j₀ x₁ * h₀ x hx
  · push_neg at h0
    refine ⟨1, fun j x hx => ?_⟩
    obtain ⟨u, -, hPx⟩ := h x hx
    rw [hPx j, h0 j x hx, mul_zero, mul_zero]

end GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem transp_reads_const_mul : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ k k' a → ∃ c : ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (x : Frame ((uAt r v i).X k).Ψ D.R.r), x ∈ ((uAt r v i).X k).dom → ∀ (h2 : ((uAt r v i).X k).Ψ = ((uAt r v i).X k').Ψ), rdU (uAt r v i) (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) γ F.1) k x = (c : ℂ) * rdU (uAt r v i) F.1 k' (castFrame h2 (lact a x)) := by
  intro D L hT Gi Gl Kc Y cX eX Csz p hp r h hr i v ψ γ k k' a ht
  obtain ⟨hm, hb, -⟩ := ht
  have hl := h.laws v
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hσ := (r.used v).full.toCore.good_σ₀
  have hU : IsUnf (uAt r v i) := hl.p.unf _ hj _ hσ
  have hpins := hl.p.pins
  have hpq : 1 ≤ ((r.used v).full.Q.Dw ((i : ℕ) + 1)).p + ((r.used v).full.Q.Dw ((i : ℕ) + 1)).q := by
    rw [(hpins.2.2.2 _ hj).1, (hpins.2.2.2 _ hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  have hL := GlobalTheory.T.actLev_full_level_group_framedPoints D (r.used v).full.Q ((i : ℕ) + 1) hpq hpins.2.1.2
  have hsecF : ∀ F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i),
      F.1 ∈ sec ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (wtA (p.κ i)) (p.κ i).n := fun F =>
    ((mem_cusp _ _ _ _ _ _).1 (Submodule.mem_inf.1 F.2).1).1
  have hsecG : ∀ F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i),
      actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1 ∈
        sec ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (wtA (p.κ i)) (p.κ i).n := fun F =>
    actL_mem _ _ _ _ hL.total hL.nat hL.bor _ γ (hsecF F)
  have P1 : ∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom)
      (hy : castFrame hm.psi (lact a x) ∈ ((uAt r v i).X k').dom) (t : _)
      (hbt : FrBor t ((uAt r v i).un k' ⟨castFrame hm.psi (lact a x), hy⟩)
        (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c γ ((uAt r v i).un k ⟨x, hx⟩)))
      (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)),
      rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x =
        toC (wchar (ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n) t : CAt (r.used v).full.σ₀) *
          rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)) := by
    intro x hx hy t hbt F
    have e1 : rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x =
        toC (evR _ _ (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1)
          ((uAt r v i).un k ⟨x, hx⟩)) := dif_pos hx
    have e2 : rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)) =
        toC (evR _ _ F.1 ((uAt r v i).un k' ⟨_, hy⟩)) := dif_pos hy
    have e3 := evalAt_actL hL (hl.p.evalWD _ hj) frMap_trans_id γ (hsecF F).1 ((uAt r v i).un k ⟨x, hx⟩)
    have e4 := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ _ _).2.2.2.2.2.2 (CAt _)
      (inferInstanceAs (IsReduced ℂ)) _ _ F.1 (hsecF F) t _ _ hbt
    rw [e1, e2]
    exact congrArg toC (e3.trans e4)
  have hUf : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) := hU
  have hσf : Formalism.L2.PjFree.GoodEmb (r.used v).full.Q.c (r.used v).full.σ₀ := hσ
  have hr1 : 1 ≤ D.R.r := hU.1 ▸ hpq
  have hxi : ∀ k k' (τ : D.host.E →+* ℂ), ‖τ ((uAt r v i).X k).ξ0‖ = ‖τ ((uAt r v i).X k').ξ0‖ :=
    fun k k' τ => (hl.p.xiAbs _ hj _ hσ k τ).trans (hl.p.xiAbs _ hj _ hσ k' τ).symm
  obtain ⟨hun1, -⟩ := GlobalTheory.FrameNorm.exists_unitFr_frBor _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hσf hUf
  have hsk : ∀ (f : Rul ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c),
      f ∈ sec ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (wtA (p.κ i)) (p.κ i).n → ∀ k,
      ((uAt r v i).X k).IsSec (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k) (rdU (uAt r v i) f k) :=
    fun f hf k => hU.2.2.2.2.1 _ _ (dom_wtA _) f hf k
  have key : ∀ x ∈ ((uAt r v i).X k).dom, ∃ u : ℂ, ‖u‖ = 1 ∧
      ∀ F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i),
        rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x =
          u * rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)) := by
    intro x hx
    obtain ⟨x₀, hx₀, ⟨b₀, hb₀, e₀'⟩, -⟩ := hun1 k ⟨x, hx⟩
    have e₀ : x₀.1 = rmul x b₀ := e₀'
    obtain ⟨hy₀, t₀, hbt₀⟩ := hb x₀.1 x₀.2
    obtain ⟨ρ, ν, -, -, hmv⟩ := mvPt_spec hL.total γ ((uAt r v i).un k x₀)
    have hx₀' : GlobalTheory.FrameNorm.IsUnitFr ((uAt r v i).X k') (castFrame hm.psi (lact a x₀.1)) := fun τ j => by
      exact (congrArg norm (hm.dmin_eq x₀.1 τ j)).trans (hx₀ _ _)
    obtain ⟨-, -, -, -, -, -, ht1⟩ := GlobalTheory.LevelCusp.exists_match (U := Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hσf hUf hr1
      hxi (x := x₀) (x' := ⟨castFrame hm.psi (lact a x₀.1), hy₀⟩) hmv hbt₀ hx₀ hx₀'
    refine ⟨toC (wchar (ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n) t₀ : CAt (r.used v).full.σ₀), ?_, fun F => ?_⟩
    · have : toC (wchar (ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n) t₀ : CAt (r.used v).full.σ₀) =
          ∏ j, toC (t₀ j : CAt (r.used v).full.σ₀) ^ ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n j := rfl
      rw [this, norm_prod]
      exact Finset.prod_eq_one fun j _ => by
        rw [norm_pow, show ‖toC (t₀ j : CAt (r.used v).full.σ₀)‖ = 1 from ht1 j, one_pow]
    · have A := P1 x₀.1 x₀.2 hy₀ t₀ hbt₀ F
      have B := (hsk _ (hsecG F) k).2.1 x hx b₀ hb₀
      have C := (hsk _ (hsecF F) k').2.1 _ (hb x hx).1 _ (GlobalTheory.Dict.Pull.cast_bor hm.psi hb₀)
      have e5 : castFrame hm.psi (lact a x₀.1) = rmul (castFrame hm.psi (lact a x)) (GlobalTheory.Dict.castFr hm.psi b₀) := by
        rw [e₀]
        exact (congrArg (castFrame hm.psi) (GlobalTheory.Dict.Extend.lact_rmul a x b₀)).trans (GlobalTheory.Dict.Pull.cast_rmul hm.psi _ _)
      have e6 : bchar (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k') (GlobalTheory.Dict.castFr hm.psi b₀) =
          bchar (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k) b₀ :=
        GlobalTheory.Dict.Pull.cast_bchar hm.psi (GlobalTheory.LevelCusp.laU_match (U := Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hm _ _) b₀
      rw [e5, C, e6, e₀, B] at A
      have hβ := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.bchar_ne ((uAt r v i).X k) (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k) hb₀
      apply mul_left_cancel₀ hβ
      rw [A]
      ring
  obtain ⟨c, hc⟩ := exists_const_of_forall_unit_mul (FourierCoefficientDomain.isOpen_dom _)
    (GlobalTheory.frames_isConnected D.host.E D.R.r ((uAt r v i).X k)).isPreconnected
    (GlobalTheory.frames_isConnected D.host.E D.R.r ((uAt r v i).X k)).nonempty
    (fun (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) x =>
      rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x)
    (fun (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) x =>
      rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)))
    (fun F => (hsk _ (hsecG F) k).1)
    (fun F => (hsk _ (hsecF F) k').1.comp
      ((GlobalTheory.Dict.Pull.cast_diff hm.psi).comp (GlobalTheory.Dict.Extend.differentiable_lact a)).differentiableOn
      (fun x hx => (hb x hx).1))
    key
  refine ⟨c, fun F x hx h2 => ?_⟩
  exact hc F x hx

end GlobalTheory.ShareOn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComponentOverBaseRationalIsometry
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevModel

section Mark

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {g : ℕ}

theorem mark_of_exp {D : Datum H} {l l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂}
    {r : Xo₂.X ⟶ Xo.X} (m : SABMap Xo₂.univ.t Xo.univ.t r) (pd : ℕ) (hM : l₂.M = l.M * pd) (hle : l₂.Mb ≤ l.Mb)
    (heta : ∀ a, (Xo₂.univ.eta a ^ pd).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    {σ : KA l →+* ℂ} {σ₂ : KA l₂ →+* ℂ} {ty ty₂ : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (F₂ : FamilyUnif Xo₂ σ₂ ty₂) (k : Fin F.n) (k₂ : Fin F₂.n) {P : (F.Di k).La →+ (Fin g → ℂ)}
    {P₂ : (F₂.Di k₂).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di k) ty P) (hP₂ : IsPeriod (F₂.Di k₂) ty₂ P₂)
    (hu : F₂.u k₂ P₂ ≫ r = F.u k P)
    (gam : (F₂.Di k₂).La ≃ₗ[𝓞 E] (F.Di k).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hh : ∀ a, P (gam a) = h (P₂ a))
    (hx : ∀ z, (F.ex k P (h z)).left = (F₂.ex k₂ P₂ z).left ≫ m.φ) :
    ∀ a ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      ∃ x, gam (F₂.t k₂ a) = F.t k a + l.M • x := by
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hp0 : pd ≠ 0 := fun h0 => by
    have := l₂.three_le
    rw [hM, h0] at this
    omega
  have hmap : l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.map_mono hle
  intro a ha
  have j₂ := F.ex_eta k P hP a (Submodule.smul_mono_left hmap ha)
  have j₁ : toUnit _ ≫ Xo₂.univ.eta a ^ pd = F₂.ex k₂ P₂ ((l.M : ℂ)⁻¹ • P₂ (F₂.t k₂ a)) := by
    rw [MonObj.comp_pow, F₂.ex_eta k₂ P₂ hP₂ a ha, ← GlobalTheory.CoverExp.pow_of_add (F₂.ex_add k₂ P₂ hP₂), hM,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_mul, mul_inv, mul_left_comm,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hp0), _root_.mul_one]
  have e : F.ex k P ((l.M : ℂ)⁻¹ • P (gam (F₂.t k₂ a))) = F.ex k P ((l.M : ℂ)⁻¹ • P (F.t k a)) := by
    apply Over.OverMorphism.ext
    rw [hh, ← map_smul h, hx, ← j₁, ← j₂, Over.comp_left, Over.comp_left, Category.assoc, heta]
    have w₂ : (toUnit (Over.mk (F₂.u k₂ P₂))).left = F₂.u k₂ P₂ := by
      simpa using Over.w (toUnit (Over.mk (F₂.u k₂ P₂)))
    have w₁ : (toUnit (Over.mk (F.u k P))).left = F.u k P := by
      simpa using Over.w (toUnit (Over.mk (F.u k P)))
    rw [w₂, w₁, ← Category.assoc, hu]
  exact (GlobalTheory.UnifPoint.div_eq_iff hP.2.1 (F.ex_add k P hP) (F.ex_ker k P hP) hM0 _ _).1 e

end Mark

section Down

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.FrameLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem exists_frOver_down (d : DeltaDat Xo c n) {S : Type} [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S]
    (y₂ : FrPt d.Xo₂ d.c₂ S) (y₀ : FrPt Xo c S) (e : y₂.x ≫ d.r = y₀.x) (hu : ∀ τ i, y₂.u τ i ≫ d.m.φ = y₀.u τ i) :
    ∃ y : FrPt Xo c S, y.x = y₀.x ∧ y.u = y₀.u ∧ FrOver d y₂ y := by
  obtain ⟨w, hw, hw', -⟩ := d.m.lin
  obtain ⟨p, k, p₁, p₂, hk, hk'⟩ := exists_pm_iso d.m e
  have hL := Xo.univ.t.PP.isLB
  have hL₂ := d.Xo₂.univ.t.PP.isLB
  obtain ⟨s, hs⟩ := exists_up hL hL₂ hw p₁ hk hk' y₂.s
  refine ⟨⟨y₀.x, y₀.x_over, y₀.u, y₀.tan, y₀.eig, y₀.basis, s, fun s' => ?_⟩, rfl, rfl,
    (frOver_iff d _ _).2 ⟨e, hu, w, p, ⟨hw, hw'⟩, p₁, p₂, hs⟩⟩
  obtain ⟨s₂', hs'⟩ := exists_down hL hL₂ hw p₁ s'
  refine (existsUnique_congr fun a => ?_).1 (y₂.gen s₂')
  exact (scal_iff (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left (toΓ S a) y₂.s s₂').trans
    ((rel_scal_iff hL hL₂ p₁ hk p₂ (toΓ S a) hs hs').trans
      (scal_iff (fst (Over.mk y₀.x) Xo.univ.t.G).left (toΓ S a) s s').symm)

end Down

section Emb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem good_comp (d : DeltaDat Xo c n) (σ₂ : d.c₂.F →+* ℂ) (h : GoodEmb d.c₂ σ₂) :
    GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) :=
  (congrArg σ₂ (Subtype.ext rfl)).trans h

theorem genScal_eq {S : Type} [CommRing S] (t : Sˣ) :
    genScal (Dw := Dw) t = fun i => Option.elim i t (fun _ => 1) := by
  funext i
  cases i <;> simp [genScal]

end Emb


open AlgebraicGeometry CategoryTheory in
set_option maxHeartbeats 1600000 in
theorem over_comp : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ k₂ : (U₂ σ₂).Comp, ∃ (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂ k₂
  have hσ : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) := good_comp d σ₂ hσ₂
  set σ := σ₂.comp (d.eF : c.F →+* d.c₂.F) with hσe
  have hA : l.A = 1 := hL.levA
  have hA₂ : d.l₂.A = 1 := hL₂.levA
  have hU := hL.unf σ hσ
  have hU₂ := hL₂.unf σ₂ hσ₂
  obtain ⟨hr₀, hW⟩ := hL.modelW σ hσ
  obtain ⟨hr₂, hW₂⟩ := hL₂.modelW σ₂ hσ₂
  have hpq : Dw.p ≠ Dw.q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hL.inR
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hle : KA l ≤ KA d.l₂ := by rw [KA, KA, hA, hA₂]
  have hinc : (σ₂.comp (IntermediateField.inclusion d.c₂.le).toRingHom).comp
      (IntermediateField.inclusion hle).toRingHom = σ.comp (IntermediateField.inclusion c.le).toRingHom :=
    RingHom.ext fun a => congrArg σ₂ (Subtype.ext rfl)
  have hrel : ∀ τ : D.host.E →+* ℂ, relab c σ τ = relab d.c₂ σ₂ τ := fun τ => by
    ext a
    exact congrArg σ₂ (Subtype.ext rfl)
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hEF, hper⟩ := id hU
  obtain ⟨-, -, -, -, -, g₂, e₂, F₂, ik₂, φ₂, hEF₂, hper₂⟩ := id hU₂
  obtain rfl : g₂ = g := by simpa using Fintype.card_congr (e₂.trans e.symm)
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.UnifFamily.dom_nonempty ((U₂ σ₂).X k₂)
  obtain ⟨P₀, hP₀, hp₀, hu₀, -⟩ := hper₂ k₂ ⟨x₀, hx₀⟩
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  have hy : (F₂.u (ik₂ k₂) P₀ ≫ d.r) ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := by
    rw [CategoryTheory.Category.assoc, GlobalTheory.ClsVal.Cmp.point_over_of_ne hpq hA d hle,
      ← CategoryTheory.Category.assoc, F₂.over_σ _ P₀ hp₀, GlobalTheory.ClsVal.Cmp.spMap_comp', hinc]
  have hframe {S : Type} [Field S] [Algebra c.F S] (x : Sp S ⟶ Xo.X)
      (hx : x ≫ Xo.s = sOf c S) : ∃ y : FrPt Xo c S, y.x = x := by
    choose u hu using fun τ => GlobalTheory.IntFramesCompare.exists_eigenBasisAt (c := c) hx τ
    obtain ⟨s, hs⟩ := gfp_gen GlobalTheory.abelianSchemeLaws_all.2.secTwist x
    exact ⟨⟨x, hx, u, fun τ => (hu τ).1, fun τ => (hu τ).2.1, fun τ => (hu τ).2.2, s, hs⟩, rfl⟩
  obtain ⟨y, hyx⟩ := @hframe (CAt σ) (inferInstanceAs (Field ℂ)) (instAlgebraCAt σ) (F₂.u (ik₂ k₂) P₀ ≫ d.r) (by
    exact hy)
  obtain ⟨k, x₁, t₁, hb⟩ := hU.2.2.1 y
  obtain ⟨P₁, hP₁, hp₁, hu₁, -⟩ := hper k x₁
  have hu : F₂.u (ik₂ k₂) P₀ ≫ d.r = F.u (ik k) P₁ := by
    rw [← hu₁, ← hb.1]
    exact hyx.symm
  obtain ⟨gam, hl, hg, hh, hx⟩ := GlobalTheory.CoverFrameMod.exists_isometry_of_cover F₂ F d.m hp₀ hp₁ hu
  have gM := mark_of_exp d.m d.pd hd.2.1 hd.1.2.1 hd.2.2.2.2.2.1.1 F F₂ (ik k) (ik₂ k₂) hp₁ hp₀ hu gam hl hh hx
  obtain ⟨a, ε, hε, hξ, hmul, -, hiso⟩ := GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry D.host.E D.R.r
    ((U₂ σ₂).X k₂) ((U σ).X k) (fun τ => (hL₂.xiAbs σ₂ hσ₂ k₂ τ).trans (hL.xiAbs σ hσ k τ).symm)
    ((φ₂ k₂).symm.trans (gam.trans (φ k))) (fun u v => by
      have e₁ := hEF k (gam ((φ₂ k₂).symm u)) (gam ((φ₂ k₂).symm v))
      have e₂ := hEF₂ k₂ ((φ₂ k₂).symm u) ((φ₂ k₂).symm v)
      rw [hg] at e₁
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e₂
      exact e₁.symm.trans e₂)
  have hξ₀ : ((U σ).X k).ξ0 = ((U₂ σ₂).X k₂).ξ0 := (hW k).2.trans (hW₂ k₂).2.symm
  obtain rfl : ε = 1 := mul_right_cancel₀ ((U₂ σ₂).X k₂).ξ0_ne (by rw [← hξ, one_mul, hξ₀])
  have hG : ((U σ).X k).Gm = ((U₂ σ₂).X k₂).Gm := (hW k).1.trans (hW₂ k₂).1.symm
  have hΨ : ∀ τ, τ ∈ ((U σ).X k).Ψ ↔ τ ∈ ((U₂ σ₂).X k₂).Ψ := fun τ =>
    ((hU.2.1 k).2 τ).trans ((hU₂.2.1 k₂).2 τ).symm
  have hp0 : ((U σ).X k).p0 = ((U₂ σ₂).X k₂).p0 := (hU.2.1 k).1.trans (hU₂.2.1 k₂).1.symm
  have hiso' : ∀ v w, herm ((U σ).X k).Gm ((a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v)
      ((a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w := fun v w => by
    rw [hiso, one_mul]
  have hgam : ∀ b, (φ k (gam b) : Fin D.R.r → D.host.E) =
      (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec (φ₂ k₂ b : Fin D.R.r → D.host.E) := fun b => by
    rw [hmul (φ₂ k₂ b)]
    simp
  refine ⟨k, a, hG.symm, fun v w => ?_, ?_⟩
  · have h' := hiso' v w
    rwa [hG] at h'
  intro x hx x' hmv
  have hx' : x' ∈ ((U σ).X k).dom :=
    GlobalTheory.FrameDom.mem_dom_of_isometry _ _ _ _ a hp0 hΨ hiso' x x' hx hmv
  refine ⟨hx', ?_⟩
  obtain ⟨Q₁, hQ₁, hq₁, hqu₁, hqv₁, hqn₁⟩ := hper k ⟨x', hx'⟩
  obtain ⟨Q₂, hQ₂, hq₂, hqu₂, hqv₂, hqn₂⟩ := hper₂ k₂ ⟨x, hx⟩
  obtain ⟨c₁, c₂⟩ := GlobalTheory.CoverFrameRead.point_over d hd hpq hA hle hinc e e₂ F F₂ (ik k) (ik₂ k₂) hq₁ hq₂ gam hg gM
    (fun b i => by
      rw [hQ₁, hQ₂, hgam, Equiv.apply_symm_apply, hrel]
      exact GlobalTheory.CoverFrameRead.perFr_move _ _ hΨ hp0 hG a hiso' x x' hmv _ _ _)
  have hx₂ : ((U₂ σ₂).un k₂ ⟨x, hx⟩).x ≫ d.r = ((U σ).un k ⟨x', hx'⟩).x := by
    rw [hqu₁, hqu₂]
    exact c₁
  have hu₂ : ∀ τ i, ((U₂ σ₂).un k₂ ⟨x, hx⟩).u τ i ≫ d.m.φ = ((U σ).un k ⟨x', hx'⟩).u τ i :=
    fun τ i => c₂ ⟨τ, i⟩ _ _ (hqv₁ τ i) (hqv₂ τ i)
  letI : Algebra c.F (CAt σ₂) := σ.toAlgebra
  obtain ⟨z, hzx, hzu, ho⟩ := exists_frOver_down (S := CAt σ₂) d ((U₂ σ₂).un k₂ ⟨x, hx⟩) ((U σ).un k ⟨x', hx'⟩) hx₂ hu₂
  obtain ⟨t, ht⟩ := GlobalTheory.GeoLevel.exists_frBor_gen (σ := σ) ((U σ).un k ⟨x', hx'⟩) z hzx hzu
  have hn' : (∀ τ i, ‖dmin ((U₂ σ₂).X k₂).Gm x τ i‖ = 1) → ∀ τ i, ‖dmin ((U σ).X k).Gm x' τ i‖ = 1 := by
    intro hn τ i
    obtain ⟨τ, h₁⟩ := τ
    have h₂ := (hΨ τ).1 h₁
    have e' : dmin ((U σ).X k).Gm x' ⟨τ, h₁⟩ i = dmin ((U₂ σ₂).X k₂).Gm x ⟨τ, h₂⟩ i := by
      unfold dmin
      rw [hmv τ h₂ h₁, GlobalTheory.FrameDom.gram_mul _ _ _ hiso' τ]
    rw [e']
    exact hn _ _
  refine ⟨t, fun hn => ?_, z, ?_, ho⟩
  · exact GlobalTheory.CoverFrameMod.norm_gen_eq_one_of_frOver d F₂ F (ik₂ k₂) (ik k) Q₂ Q₁ ((U₂ σ₂).un k₂ ⟨x, hx⟩)
      ((U σ).un k ⟨x', hx'⟩) z (fun i => Option.elim i t (fun _ => 1)) hq₂ hq₁ hqu₂ hqu₁ (hqn₂ hn) (hqn₁ (hn' hn)) ho ht
  · have e' : genScal (Dw := Dw) (S := CAt σ₂) t = fun i => Option.elim i t (fun _ => 1) := genScal_eq _
    exact e'.symm ▸ ht

end GlobalTheory.LevModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelLocalGoodPlace
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SwapActs

theorem swap_acts_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
    ∀ (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl (incM F G.V'.J)),
      ((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    ∃ c : ℂ, ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      ∀ ψ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ ψ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      ι ψ₁ = (fun Y => starRingEnd ℂ (ι (fun y => starRingEnd ℂ (φ₂ y)) (-Y))) →
      ι (fun y => starRingEnd ℂ (ψ₂ y)) = (fun Y => starRingEnd ℂ (ι φ₁ (-Y))) →
      Acts (evFin F v) (omd w) (boxFun φ₁ φ₂) (c • boxFun ψ₁ ψ₂) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv t ι hι d' hd' dd hdd omd hspl f hf1 hf2 hf3 hf4 hf5 w hw
  have hcm : IsCMExt F E σ := hT.base.cm
  obtain ⟨hAt, -⟩ := GlobalTheory.T.local_idempotent_character_value σ hcm (incM F G.V'.J) (d := a + a') v t f hf1 hf2 hf3 hf4 hf5 w hw
  have atAct : ∀ u : Matrix (Fin (a + a')) (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u →
      At (evFin F v) (actB (cA σ) w u) := by
    intro u hu r hr
    simp only [actB]
    rw [← Matrix.smul_mul, hu r hr, Matrix.zero_mul]
  have hex := GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v w hAt
  obtain ⟨S, hS, hSh⟩ := GlobalTheory.T.splitting_preserves_local_schwartz dd B.ψ hT.base.std (actB (cA σ)) omd hspl.toIsSplitting v w atAct hex
  have hSlin := GlobalTheory.LocWeilAct.linear_of_acts v (omd w) S hS
  obtain ⟨c, hc⟩ := GlobalTheory.T.linear_bar_model_local_triple F E σ B a a' G X om om' hT v t ι hι d' hd' dd hdd f hf1 hf2 hf3 hf4 hf5 w hw S
    (fun Φ hΦ => (hS Φ hΦ).1) hSlin hSh
  refine ⟨c, fun φ₁ h₁ φ₂ h₂ ψ₁ k₁ ψ₂ k₂ e₁ e₂ => ?_⟩
  have hbij := _root_.GlobalTheory.SwapSliceBij.sliceT_bijOn ι hι.bij
  have hΦ := GlobalTheory.BoxSpan.boxFun_mem_SB' h₁ h₂
  have hΨ : c • boxFun ψ₁ ψ₂ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) :=
    (SB _).smul_mem c (GlobalTheory.BoxSpan.boxFun_mem_SB' k₁ k₂)
  have key : S (boxFun φ₁ φ₂) = c • boxFun ψ₁ ψ₂ := by
    refine hbij.injOn (hS _ hΦ).1 hΨ ?_
    rw [hc _ hΦ, map_smul]
    congr 1
    funext Z
    rw [Function.comp_apply, GlobalTheory.SwapSlice.sliceT_boxFun, GlobalTheory.SwapSlice.sliceT_boxFun, GlobalTheory.SwapSlice.swapNeg_apply,
      GlobalTheory.SwapSlice.barL_apply, GlobalTheory.SwapSlice.barL_apply, e₁, e₂]
    simp only [Complex.conj_conj]
    ring
  have h := (hS _ hΦ).2
  rwa [key] at h

end GlobalTheory.SwapActs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDepthSumRoundingOscillationStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productDepth_sum_rounding_oscillation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ∀ (cx : Lt1 Dw → ℕ), (∀ A B : Lt1 Dw → ℝ, (∀ f, FacBetween Xo la f (cx f) (A f) (B f)) → NuBetween Xo la cx (∑ f, A f) (∑ f, B f) ∧ ∃ n : ℕ, NuBetween Xo la cx n (n + (∑ f, (B f - A f) + 1))) ∧ ∀ b : ℝ, OscLe Xo c p cx b → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Comp Xo c), (letI := H.starRing; eLoc Y Z la cx ≤ (b : EReal)) := by
  first | exact @GlobalTheory.RefSum.nuBetween_sum_and_eLoc_le | exact GlobalTheory.RefSum.nuBetween_sum_and_eLoc_le | (intros; apply GlobalTheory.RefSum.nuBetween_sum_and_eLoc_le <;> assumption)
end

