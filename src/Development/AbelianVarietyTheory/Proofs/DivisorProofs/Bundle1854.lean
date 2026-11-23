module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransporterMovesFrameReadsInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniqueUpToTargetGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesaw
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportIdentityOfMemComponentGroup
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShareOn.OneFrame

section Geo

open NumberField AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open scoped Matrix CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l}
variable {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}

theorem exists_marking_match_at (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hr : 1 ≤ r)
    (hxi : ∀ k k' (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ‖τ (U.X k').ξ0‖) :
    ∃ T : ∀ k, Dw.La →ₗ[𝓞 E] (U.X k).Λ, (∀ k, BijMod l.Mb (T k)) ∧
      ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La), IsLevMove ρ ν gM gA →
      ∀ (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
      FrMove ρ ν (U.un k x) y' → FrBor t (U.un k' x') y' →
      ∃ (a : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k') a) (gam : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k').Λ),
        (∀ v : (U.X k).Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) = (gam v : Fin r → E)) ∧
        (∀ u, gam (T k (gM u)) - T k' u ∈ l.Mb • (⊤ : Submodule (𝓞 E) (U.X k').Λ)) ∧
        ∃ b ∈ Bor (U.X k').Ψ r, x'.1 = rmul (lact a (castFr h.psi x.1)) b := by
  obtain ⟨T, hT, hmv⟩ := exists_marking_tri hU
  refine ⟨T, hT, fun ρ ν gM gA hν k k' x x' y' t hm hb => ?_⟩
  obtain ⟨gam, A, htr, hA0, hA, hmk⟩ := hmv ρ ν gM gA hν k k' x x' y' t hm hb
  obtain ⟨a, ε, hε, hξ, hav, hlat, hiso⟩ :=
    GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry E r (U.X k) (U.X k') (hxi k k') gam htr
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hrr, hty, -, -, -⟩ := hU
  have hΨ : (U.X k).Ψ = (U.X k').Ψ := Finset.ext fun τ => ((hty k).2 τ).trans ((hty k').2 τ).symm
  have hp : (U.X k).p0 = (U.X k').p0 := (hty k).1.trans (hty k').1.symm
  let e := Equiv.ofBijective _ hbij
  have he : ∀ τ, Formalism.L2.PjFree.relab c σ (e.symm τ) = τ := e.apply_symm_apply
  have m1 : ∀ τ ∈ (U.X k).Ψ, Dw.mult (e.symm τ) = r - (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_pos ((hrt _).1 (by rw [he]; exact ((hty k).2 τ).1 hτ)), (hty k).1]
    omega
  have m2 : ∀ τ ∉ (U.X k).Ψ, Dw.mult (e.symm τ) = (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_neg (fun h => hτ (((hty k).2 τ).2 (by rw [← he τ]; exact (hrt _).2 h))), (hty k).1]
  have hrel : ∀ τ, ∀ i < Dw.mult (e.symm τ), ∀ v ∈ (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k') x'.1 ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i =
        ∑ j ∈ Finset.range (Dw.mult (e.symm τ)), A (e.symm τ) i j * Formalism.L2.PjFree.perFr (U.X k) x.1 v τ j :=
    fun τ i hi v hv => by
      have := hA (e.symm τ) i hi ⟨v, hv⟩
      rwa [he, ← hav] at this
  rcases hε with rfl | rfl
  · have h : IsMatch (U.X k) (U.X k') a :=
      ⟨hΨ, hp, by rw [hξ, _root_.one_mul], fun u v => by rw [hiso, _root_.one_mul], hlat⟩
    obtain ⟨b, hbB, hxb, -⟩ := GlobalTheory.PeriodBorel.borel_of_periods E r _ _ a h (fun τ => Dw.mult (e.symm τ)) m1 m2
      x.1 x.2 x'.1 x'.2 (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel
    exact ⟨a, h, gam, hav, hmk, b, hbB, hxb⟩
  · exact (GlobalTheory.AntiIsom.not_antiIsometry E r _ _ hΨ hp hr a hiso (fun τ => Dw.mult (e.symm τ)) m1 m2 x.1 x.2
      x'.1 x'.2 (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel).elim

end Geo

section Frames

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem unit_mem_Bor (Ψ : Finset (E →+* ℂ)) :
    ((fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) : Frame Ψ r) ∈ Bor Ψ r := fun τ =>
  ⟨by
    show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp, fun a c hac => by
    show (1 : Matrix (Fin r) (Fin r) ℂ) a c = 0
    exact Matrix.one_apply_ne hac.ne'⟩

theorem rmul_unit {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) :
    rmul x ((fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) : Frame Ψ r) = x := by
  funext τ
  exact Matrix.mul_one (mat x τ)

theorem eq_of_lact_eq_rmul (X : Data E r) {g a : GL (Fin r) E} (hg : g ∈ X.Γ) (ha : a ∈ X.Γ) {x b : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) (e : lact g x = rmul (lact a x) b) : g = a := by
  have h1 := X.Γ_free (a⁻¹ * g) (X.Γ.mul_mem (X.Γ.inv_mem ha) hg) x hx b hb (by
    funext τ
    have e1 : (g : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
        (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat b τ := congrFun e τ
    show ((a⁻¹ * g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ * mat b τ
    rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul])
  exact (inv_mul_eq_one.1 h1).symm

end Frames

end GlobalTheory.ShareOn.OneFrame

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_Γ_of_cong_half {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
    {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
    {Csz : ℝ} (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (k : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E)
    (ha : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k) a)
    (hcong : ∀ w ∈ lattice₂ D ((uAt r v i).X k).Λ,
      (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ w - w ∈ p.T.Q.l.Mb • lattice₂ D ((uAt r v i).X k).Λ) :
    a ∈ ((uAt r v i).X k).Γ := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨Xx, ⟨e1, e2, e3⟩, -⟩ := GlobalTheory.ModelLatticeCheck.holds_by_value D (r.used v).full.toCore
    (h.laws v).p.toLawsCore ((i : ℕ) + 1) hj (r.used v).full.σ₀ (r.used v).full.toCore.good_σ₀ k
  have eL : Xx.L' = lattice₂ D ((uAt r v i).X k).Λ := by
    rw [GlobalTheory.ModelLatExamples.eq_latP D Xx.Λ Xx.L' e3]
    show lattice₂ D Xx.toData.Λ = _
    rw [e1]
  have hGm : Xx.Gm = ((uAt r v i).X k).Gm := congrArg Data.Gm e1
  have hΛ : Xx.Λ = ((uAt r v i).X k).Λ := congrArg Data.Λ e1
  have hΓ : Xx.Γ = ((uAt r v i).X k).Γ := congrArg Data.Γ e1
  have hlatL := mem_localLattice_iff_mulVec D _ ha.lat
  have hM := sub_mem_natSMul_of_unitary Xx.Gm Xx.L' Xx.L'_int Xx.L'_dual p.T.Q.H.bar (fun a => p.T.Q.H.bar_eq a)
    p.T.Q.l.Mb p.T.Q.l.M (by have := p.T.Q.l.three_le; omega) p.T.Q.l.prod p.T.Q.l.coprime a
    (by rw [hGm]; exact ha.iso) (by rw [eL]; exact hlatL) (by rw [eL]; exact hcong)
  have hMΛ := sub_mem_natSMul_span D.host.AA Xx.L' Xx.Λ e3 _ p.T.Q.l.M hM
  have hin := Xx.cong a ⟨by rw [hGm]; exact ha.iso, by rw [hΛ]; exact ha.lat⟩ (by rw [e2]; exact hMΛ)
  rw [← hΓ]
  exact hin


open GlobalTheory.ShareOn.OneFrame in
set_option maxHeartbeats 1000000 in
theorem isTransp_one_of_mem_Γ : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (k : (uAt r v i).Comp) (γ₀ : GL (Fin D.R.r) D.host.E), γ₀ ∈ ((uAt r v i).X k).Γ → IsTransp p r i v ψ 1 k k γ₀ := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v ψ k γ₀ hγ₀
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hp := (h.laws v).p
  have hpin := hp.pins
  have hσ := (r.used v).full.toCore.good_σ₀
  have hpq : 1 ≤ ((r.used v).full.Q.Dw ((i : ℕ) + 1)).p + ((r.used v).full.Q.Dw ((i : ℕ) + 1)).q := by
    rw [(hpin.2.2.2 _ hj).1, (hpin.2.2.2 _ hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  have hL := GlobalTheory.FullLevelAction.actLev_levFull D (r.used v).full.Q _ hpq hpin.2.1.2
  have hU : IsUnf (uAt r v i) := hp.unf _ hj _ hσ
  have hm₀ := GlobalTheory.LevelCusp.isMatch_of_isUStab _ (((uAt r v i).X k).Γ_stab γ₀ hγ₀)
  obtain ⟨-, -, hsy, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid D.host.E _ _ _
    ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (CAt (r.used v).full.σ₀)

  have hfr : ∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom),
      ∃ (hy : lact γ₀ x ∈ ((uAt r v i).X k).dom) (t : _),
        FrBor t ((uAt r v i).un k ⟨lact γ₀ x, hy⟩)
          (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩)) := by
    intro x hx
    have hy : lact γ₀ x ∈ ((uAt r v i).X k).dom := hm₀.mem_dom hx
    obtain ⟨t, ht⟩ := (hU.2.2.2.1 k k ⟨x, hx⟩ ⟨lact γ₀ x, hy⟩).2
      ⟨γ₀, hγ₀, _, unit_mem_Bor _, by rw [rmul_unit]⟩
    have hf := hL.func 1 _ ((uAt r v i).un k ⟨x, hx⟩) ((uAt r v i).un k ⟨x, hx⟩)
      (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩))
      (hL.one _ _) (Formalism.L2.Pj.mvPt_spec hL.total 1 _)
    have he : (uAt r v i).un k ⟨x, hx⟩ =
        mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩) :=
      (GlobalTheory.LevelLawsCompare.frMap_id_iff _ _).1 hf
    exact ⟨hy, _, (congrArg (FrBor _ ((uAt r v i).un k ⟨lact γ₀ x, hy⟩)) he).mp (hsy _ _ _ ht)⟩
  refine ⟨hm₀, hfr, ?_⟩

  obtain ⟨T, hTb, hmv⟩ := exists_marking_match_at (U := Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hσ hU (hU.1 ▸ hpq)
    (fun k k' τ => (hp.xiAbs _ hj _ hσ k τ).trans (hp.xiAbs _ hj _ hσ k' τ).symm)
  have hI : p.T.Q.l.Mb ≠ ⊥ := fun e => by
    have h1 := natCast_M_mem p.T.Q.l
    rw [e, Ideal.mem_bot, Nat.cast_eq_zero] at h1
    have := p.T.Q.l.three_le
    omega
  obtain ⟨s, f, hf, hfs⟩ := exists_scale D hI D.R.r
  have hb : BijMod p.T.Q.l.Mb (f ((uAt r v i).X k).Λ ∘ₗ T k) := (hTb k).comp (hf _)
  obtain ⟨x, hx⟩ := (GlobalTheory.frames_isConnected _ _ ((uAt r v i).X k)).nonempty
  obtain ⟨hy, t, ht⟩ := hfr x hx
  obtain ⟨ρ, ν, -, hν, hm⟩ := mvPt_spec hL.total 1 ((uAt r v i).un k ⟨x, hx⟩)
  obtain ⟨a, ha, gam, hav, hmk, b, hbB, hxb⟩ := hmv ρ ν _ _ hν k k ⟨x, hx⟩ ⟨lact γ₀ x, hy⟩ _ t hm ht
  have hrd : ∀ w : lattice₂ D ((uAt r v i).X k).Λ,
      Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (lattice₂ D ((uAt r v i).X k).Λ)))
        (latPMap D _ ha.lat w) = Submodule.Quotient.mk w := fun w => by
    refine (hb.reads hb 1 (liftLa 1) (liftLa_spec 1) (latPMap D _ ha.lat) (fun u => ?_) w).trans
      (hb.equiv.apply_symm_apply _)
    have h1 := map_mem_smul_top _ (f ((uAt r v i).X k).Λ) (hmk u)
    have h2 : latPMap D _ ha.lat (f ((uAt r v i).X k).Λ (T k (liftLa (l := p.T.Q.l) 1 u))) =
        f ((uAt r v i).X k).Λ (gam (T k (liftLa (l := p.T.Q.l) 1 u))) := by
      refine Subtype.ext ?_
      refine (congrArg (Matrix.mulVec _) (hfs _ _)).trans (Eq.trans ?_ (hfs _ _).symm)
      rw [Matrix.mulVec_smul]
      exact congrArg _ (hav _)
    have h3 := (f ((uAt r v i).X k).Λ).map_sub (gam (T k (liftLa (l := p.T.Q.l) 1 u))) (T k u)
    rw [← h2] at h3
    exact h3 ▸ h1
  have haΓ : a ∈ ((uAt r v i).X k).Γ := mem_Γ_of_cong_half p r h i v k a ha fun w hw => by
    have hq := (Submodule.Quotient.eq _).1 (hrd ⟨w, hw⟩)
    have hmem := Submodule.mem_map_of_mem (f := (lattice₂ D ((uAt r v i).X k).Λ).subtype) hq
    rw [Submodule.map_smul'', Submodule.map_subtype_top] at hmem
    exact hmem
  have hga : γ₀ = a := eq_of_lact_eq_rmul _ hγ₀ haΓ hx hbB hxb
  subst hga
  intro w
  exact ⟨(mem_localLattice_iff_mulVec D _ ha.lat _).1 w.2, (hrd w).trans ((ψ k).apply_symm_apply _).symm⟩

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicIntegralInvariantHeisenbergFirstVars
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LagIntTransl

def liftFst {R : Type} [CommRing R] {κ : Type} (a : (κ → R) × (κ → R)) : (κ ⊕ κ → R) × (κ ⊕ κ → R) :=
  (Sum.elim a.1 0, Sum.elim a.2 0)

theorem liftFst_add {R : Type} [CommRing R] {κ : Type} (a b : (κ → R) × (κ → R)) :
    liftFst (a + b) = liftFst a + liftFst b := by
  simp only [liftFst, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  refine Prod.ext ?_ ?_ <;> funext i <;> cases i <;> simp

theorem liftFst_dot {R : Type} [CommRing R] {κ : Type} [Fintype κ] (a b : (κ → R) × (κ → R)) :
    (liftFst a).1 ⬝ᵥ (liftFst b).2 = a.1 ⬝ᵥ b.2 := by
  simp [liftFst, dotProduct, Fintype.sum_sum_type]

theorem boxFun_schr {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a : (κ → R) × (κ → R)) (φ₁ φ₂ : (κ → R) → ℂ) :
    boxFun (schr ψ a φ₁) φ₂ = schr ψ (liftFst a) (boxFun φ₁ φ₂) := by
  funext z
  simp only [boxFun, schr, liftFst, dotProduct, Fintype.sum_sum_type, Function.comp_apply, Sum.elim_inl, Sum.elim_inr,
    Pi.add_apply, Pi.zero_apply, mul_zero, add_zero, mul_assoc]
  have e1 : (z + Sum.elim a.1 0) ∘ Sum.inl = z ∘ Sum.inl + a.1 := by funext i; simp
  have e2 : (z + Sum.elim a.1 0) ∘ Sum.inr = z ∘ Sum.inr := by funext i; simp
  rw [e1, e2]
  simp

theorem diagW_schr (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ)
    (μ : @Measure (κ → Fv F v) (borel _)) (a w : (κ → Fv F v) × (κ → Fv F v)) (h : w.1 ⬝ᵥ a.2 = a.1 ⬝ᵥ w.2)
    (φ₁ φ₂ : (κ → Fv F v) → ℂ) :
    diagW ψ μ (boxFun (schr ψ a φ₁) φ₂) w = diagW ψ μ (boxFun φ₁ φ₂) (w + a) := by
  unfold diagW
  rw [boxFun_schr]
  congr 1
  funext x
  have h' : (liftFst w).1 ⬝ᵥ (liftFst a).2 = (liftFst a).1 ⬝ᵥ (liftFst w).2 := by
    rw [liftFst_dot, liftFst_dot, h]
  have := GlobalTheory.MixXEvUniq.schr_add ψ (liftFst w) (liftFst a) h' (boxFun φ₁ φ₂)
  rw [← liftFst_add] at this
  rw [show ((Sum.elim (w + a).1 0, Sum.elim (w + a).2 0) : (κ ⊕ κ → Fv F v) × (κ ⊕ κ → Fv F v)) = liftFst (w + a) from rfl,
    this]
  rfl

theorem main : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), (∀ y y', (j y).1 ⬝ᵥ (j y').2 = (j y').1 ⬝ᵥ (j y).2) →
    ∀ (y₀ : Fin N → Fv F v) (φ₁ φ₂ : (κ → Fv F v) → ℂ),
      lagInt ψ μ ν j (boxFun (schr ψ (j y₀) φ₁) φ₂) = lagInt ψ μ ν j (boxFun φ₁ φ₂) := by
  intro F _ _ v κ _ ψ μ _ N ν hν j hj y₀ φ₁ φ₂
  unfold lagInt
  have h1 : ∀ y, diagW ψ μ (boxFun (schr ψ (j y₀) φ₁) φ₂) (j y) = diagW ψ μ (boxFun φ₁ φ₂) (j (y + y₀)) := fun y => by
    rw [diagW_schr F v κ ψ μ _ _ (hj y y₀), map_add (f := _)]
  simp only [h1]
  letI : MeasurableSpace (Fin N → Fv F v) := borel _
  haveI : BorelSpace (Fin N → Fv F v) := ⟨rfl⟩
  exact integral_add_right_eq_self (μ := ν) (fun y => diagW ψ μ (boxFun φ₁ φ₂) (j y)) y₀

end GlobalTheory.LagIntTransl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowDualEigenvectorMemSpanField
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist

theorem ksRow_exists_lieComb : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {O : Type} [CommRing O] (a : OAct O A) (cO : O → O) (ψ : LinearMap.BilinForm K (HdR A)), (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) → (∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A) → LinearMap.IsPerfPair ψ → IsAdjointFor a cO ψ → KSRegular h → (∀ (z : O) (f : HdR A) (w : epsR K ⟶ A), IsKSValue h f w → IsKSValue h (act (dp0 K) (𝟙 _) a z f) (w ≫ a.act z)) → ∀ {ι : Type} {m : ι → ℕ} (χ : ι → O →+* K) (ub : ∀ σ, Fin (m σ) → (epsR K ⟶ A)) (hb : (Σ σ, Fin (m σ)) → HdR A), Submodule.span K (Set.range hb) ⊔ Fil A = ⊤ → LinearIndependent K (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) → (∀ k (z : O), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A) → (∀ σ (w : epsR K ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w) → ∀ (τ τb : ι), (∀ z, χ τb (cO z) = χ τ z) → ∀ (j : Fin (m τb)), ∃ cf : Fin (m τ) → K, ∃ w, IsLieComb cf (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨τb, j⟩ w := by
  intro K _ A _ _ A' _ i h O _ a cO ψ hiso hlag hperf hadj hK hEq ι m χ ub hb hspan hind heig hbasis τ τb hconj j
  classical

  have hsp : ⊤ ≤ Submodule.span K (Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
    have e : (Fil A).mkQ '' Set.range hb =
        Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A) := by
      rw [← Set.range_comp]; rfl
    rw [← e, ← Submodule.map_span]
    intro q _
    obtain ⟨x, rfl⟩ := (Fil A).mkQ_surjective q
    have hx : x ∈ Submodule.span K (Set.range hb) ⊔ Fil A := hspan ▸ Submodule.mem_top
    obtain ⟨y, hy, g, hg, rfl⟩ := Submodule.mem_sup.1 hx
    refine ⟨y, hy, ?_⟩
    have hg0 : (Fil A).mkQ g = 0 := (Submodule.Quotient.mk_eq_zero _).2 hg
    rw [map_add (f := _), hg0, add_zero]
  let B := Module.Basis.mk hind hsp
  let k₀ : (Σ σ, Fin (m σ)) := ⟨τb, j⟩
  obtain ⟨f, hl⟩ := hperf.bijective_left.2 (B.coord k₀ ∘ₗ (Fil A).mkQ)
  have hval : ∀ x, ψ f x = B.coord k₀ ((Fil A).mkQ x) := fun x => by rw [hl]; rfl
  have hf : f ∈ Fil A := hlag f fun g hg => by
    have hg0 : (Fil A).mkQ g = 0 := (Submodule.Quotient.mk_eq_zero _).2 hg
    rw [hval, hg0, map_zero]
  have hδ : ∀ k, ψ f (hb k) = if k = k₀ then 1 else 0 := fun k => by
    have e : (Fil A).mkQ (hb k) = B k := by simp [B]
    rw [hval, e, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

  have hact : ∀ z, act (dp0 K) (𝟙 _) a z f = χ τ z • f := fun z => by
    haveI := a.hom z
    have hz : act (dp0 K) (𝟙 _) a z f ∈ Fil A := by
      rw [act_apply]; exact push_mem_Fil _ hf
    have hf' : act (dp0 K) (𝟙 _) a z f - χ τ z • f ∈ Fil A :=
      sub_mem hz (Submodule.smul_mem _ _ hf)
    have hker : (Submodule.span K (Set.range hb) ⊔ Fil A) ≤
        LinearMap.ker (ψ (act (dp0 K) (𝟙 _) a z f - χ τ z • f)) := by
      refine sup_le ((Submodule.span_le).2 ?_) fun g hg => hiso _ hf' g hg
      rintro _ ⟨k, rfl⟩
      have e := hiso f hf _ (heig k (cO z))
      rw [map_sub, map_smul, sub_eq_zero] at e
      have e2 := hadj z f (hb k)
      change ψ (act (dp0 K) (𝟙 _) a z f - χ τ z • f) (hb k) = 0
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, e2, e, hδ]
      by_cases hk : k = k₀
      · subst hk
        simp [k₀, hconj z]
      · simp [hk]
    have h0 : ψ (act (dp0 K) (𝟙 _) a z f - χ τ z • f) = 0 := by
      refine LinearMap.ext fun x => ?_
      have : x ∈ Submodule.span K (Set.range hb) ⊔ Fil A := hspan ▸ Submodule.mem_top
      exact hker this
    exact sub_eq_zero.1 (hperf.bijective_left.1 (h0.trans (map_zero ψ).symm))

  obtain ⟨w, hw, hu⟩ := hK f hf
  have htan : IsTangent w := by
    obtain ⟨k, -, l⟩ := hw
    exact l.1
  have heq : ∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ τ z) ≫ w := fun z => by
    have e1 := hEq z f w hw
    rw [hact z] at e1
    exact (hK _ (Submodule.smul_mem _ _ hf)).unique e1 (hw.smul _)
  obtain ⟨cf, hcf⟩ := hbasis τ w htan heq
  exact ⟨cf, w, hcf, f, hf, fun k => by convert hδ k, hw⟩

end GlobalTheory.KSExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowDualEigenvectorMemSpanRing
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSRing

theorem ksRow_exists_lieComb_ring : ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {O : Type} [CommRing O] (a : OAct O A) (cO : O → O) (ψ : LinearMap.BilinForm R (HdR A)), (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) → (∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A) → LinearMap.IsPerfPair ψ → IsAdjointFor a cO ψ → KSRegular h → (∀ (z : O) (f : HdR A) (w : epsR R ⟶ A), IsKSValue h f w → IsKSValue h (act (dp0 R) (𝟙 _) a z f) (w ≫ a.act z)) → ∀ {ι : Type} {m : ι → ℕ} (χ : ι → O →+* R) (ub : ∀ σ, Fin (m σ) → (epsR R ⟶ A)) (hb : (Σ σ, Fin (m σ)) → HdR A), Submodule.span R (Set.range hb) ⊔ Fil A = ⊤ → LinearIndependent R (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) → (∀ k (z : O), act (dp0 R) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A) → (∀ σ (w : epsR R ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w) → ∀ (τ τb : ι), (∀ z, χ τb (cO z) = χ τ z) → ∀ (j : Fin (m τb)), ∃ cf : Fin (m τ) → R, ∃ w, IsLieComb cf (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨τb, j⟩ w := by
  intro R _ A _ _ A' _ i h O _ a cO ψ hiso hlag hperf hadj hK hEq ι m χ ub hb hspan hind heig hbasis τ τb hconj j
  classical

  have hsp : ⊤ ≤ Submodule.span R (Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
    have e : (Fil A).mkQ '' Set.range hb =
        Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A) := by
      rw [← Set.range_comp]; rfl
    rw [← e, ← Submodule.map_span]
    intro q _
    obtain ⟨x, rfl⟩ := (Fil A).mkQ_surjective q
    have hx : x ∈ Submodule.span R (Set.range hb) ⊔ Fil A := hspan ▸ Submodule.mem_top
    obtain ⟨y, hy, g, hg, rfl⟩ := Submodule.mem_sup.1 hx
    refine ⟨y, hy, ?_⟩
    have hg0 : (Fil A).mkQ g = 0 := (Submodule.Quotient.mk_eq_zero _).2 hg
    rw [map_add (f := _), hg0, add_zero]
  let B := Module.Basis.mk hind hsp
  let k₀ : (Σ σ, Fin (m σ)) := ⟨τb, j⟩
  obtain ⟨f, hl⟩ := hperf.bijective_left.2 (B.coord k₀ ∘ₗ (Fil A).mkQ)
  have hval : ∀ x, ψ f x = B.coord k₀ ((Fil A).mkQ x) := fun x => by rw [hl]; rfl
  have hf : f ∈ Fil A := hlag f fun g hg => by
    have hg0 : (Fil A).mkQ g = 0 := (Submodule.Quotient.mk_eq_zero _).2 hg
    rw [hval, hg0, map_zero]
  have hδ : ∀ k, ψ f (hb k) = if k = k₀ then 1 else 0 := fun k => by
    have e : (Fil A).mkQ (hb k) = B k := by simp [B]
    rw [hval, e, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

  have hact : ∀ z, act (dp0 R) (𝟙 _) a z f = χ τ z • f := fun z => by
    haveI := a.hom z
    have hz : act (dp0 R) (𝟙 _) a z f ∈ Fil A := by
      rw [act_apply]; exact push_mem_Fil _ hf
    have hf' : act (dp0 R) (𝟙 _) a z f - χ τ z • f ∈ Fil A :=
      sub_mem hz (Submodule.smul_mem _ _ hf)
    have hker : (Submodule.span R (Set.range hb) ⊔ Fil A) ≤
        LinearMap.ker (ψ (act (dp0 R) (𝟙 _) a z f - χ τ z • f)) := by
      refine sup_le ((Submodule.span_le).2 ?_) fun g hg => hiso _ hf' g hg
      rintro _ ⟨k, rfl⟩
      have e := hiso f hf _ (heig k (cO z))
      rw [map_sub, map_smul, sub_eq_zero] at e
      have e2 := hadj z f (hb k)
      change ψ (act (dp0 R) (𝟙 _) a z f - χ τ z • f) (hb k) = 0
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, e2, e, hδ]
      by_cases hk : k = k₀
      · subst hk
        simp [k₀, hconj z]
      · simp [hk]
    have h0 : ψ (act (dp0 R) (𝟙 _) a z f - χ τ z • f) = 0 := by
      refine LinearMap.ext fun x => ?_
      have : x ∈ Submodule.span R (Set.range hb) ⊔ Fil A := hspan ▸ Submodule.mem_top
      exact hker this
    exact sub_eq_zero.1 (hperf.bijective_left.1 (h0.trans (map_zero ψ).symm))

  obtain ⟨w, hw, hu⟩ := hK f hf
  have htan : IsTangent w := by
    obtain ⟨k, -, l⟩ := hw
    exact l.1
  have heq : ∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ τ z) ≫ w := fun z => by
    have e1 := hEq z f w hw
    rw [hact z] at e1
    exact (hK _ (Submodule.smul_mem _ _ hf)).unique e1 (hw.smul _)
  obtain ⟨cf, hcf⟩ := hbasis τ w htan heq
  exact ⟨cf, w, hcf, f, hf, fun k => by convert hδ k, hw⟩

end GlobalTheory.KSRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormMulTwistingSectionEqConstMul
section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatTw.PetTw

theorem homN_mul_sig_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
    {Z : Comp Xo c} {G₀ : WTZ E} (s : TwSec U x Z G₀) {G : WTZ E} (hG : Even G.2) {f : Rul Xo c} (hf : f ∈ suppOn Z)
    (σ : c.F →+* ℂ) (z : Σ k, Frame ((U (goodOf c σ)).X k).Ψ r) :
    homN (U (goodOf c σ)) x (G + G₀) (f * s.sig) z = s.cInf σ * homN (U (goodOf c σ)) x G f z := by
  by_cases hz : z ∈ framesOn (U (goodOf c σ)) Z
  · rw [s.homN_mul_sig hG f hz, mul_comm]
  · have h1 : rdU (U (goodOf c σ)) (f * s.sig) z.1 z.2 = 0 :=
      rdU_eq_zero _ (mul_mem_suppOn f s.sig_mem_suppOn) hz
    have h2 : rdU (U (goodOf c σ)) f z.1 z.2 = 0 := rdU_eq_zero _ hf hz
    show _ * (‖rdU (U (goodOf c σ)) (f * s.sig) z.1 z.2‖ * _) = s.cInf σ * (_ * (‖rdU (U (goodOf c σ)) f z.1 z.2‖ * _))
    rw [h1, h2, norm_zero, zero_mul, zero_mul, mul_zero, mul_zero, mul_zero]

theorem petAt_mul_sig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E), Even G.2 → ∀ f ∈ suppOn Z, ∀ (σ : c.F →+* ℂ) (D : D7) (V : HSp D) (dict : GA D V → Σ k, Frame ((U (goodOf c σ)).X k).Ψ r) (μ : Measure (AutQ V)), petAt (U (goodOf c σ)) x V dict μ (G + G₀) (f * s.sig) = s.cInf σ * petAt (U (goodOf c σ)) x V dict μ G f := by
  intro E _ _ _ H Dw l Xo c r U x Z G₀ s G hG f hf σ D V dict μ
  rw [petAt_eq, petAt_eq]
  have e : (fun q : AutQ V => homN (U (goodOf c σ)) x (G + G₀) (f * s.sig) (dict q.out)) =
      s.cInf σ • fun q : AutQ V => homN (U (goodOf c σ)) x G f (dict q.out) :=
    funext fun q => homN_mul_sig_eq s hG hf σ (dict q.out)
  rw [e, eLpNorm'_const_smul _ (by norm_num), ENNReal.toReal_mul, Real.eNorm_eq_ofReal (s.cInf_pos σ).le,
    ENNReal.toReal_ofReal (s.cInf_pos σ).le]

end GlobalTheory.FlatTw.PetTw
end
end

