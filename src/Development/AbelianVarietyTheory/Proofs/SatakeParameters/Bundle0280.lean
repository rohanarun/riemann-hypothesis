module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
public import Formalism.LocalToGlobal.Columns.Bundle0035
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0259
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MqRowSGUnif
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0265

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormMemOfUnderEq
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace GlobalTheory.DenseUsable

theorem isSquare_neg_padic (q : ℕ) [hq : Fact q.Prime] (d : ℕ) (a : ℤ)
    (h1 : (q : ℤ) ∣ a ^ 2 + d) (h2 : ¬ (q : ℤ) ∣ 2 * a) : IsSquare (-(d : ℚ_[q])) := by
  let F : Polynomial ℤ := Polynomial.X ^ 2 + Polynomial.C (d : ℤ)
  have hF : ∀ z : ℤ_[q], Polynomial.aeval z F = z ^ 2 + d := by intro z; simp [F]
  have hF' : ∀ z : ℤ_[q], Polynomial.aeval z (Polynomial.derivative F) = 2 * z := by
    intro z; simp [F]; left; exact map_ofNat _ 2
  have hlt : ‖((a ^ 2 + d : ℤ) : ℤ_[q])‖ < 1 := (PadicInt.norm_int_lt_one_iff_dvd _).2 h1
  have hn : ‖((2 * a : ℤ) : ℤ_[q])‖ = 1 :=
    le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => h2 ((PadicInt.norm_int_lt_one_iff_dvd _).1 h))
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := (a : ℤ_[q])) (by
    rw [hF, hF']; push_cast at hn hlt; rw [hn]; simpa using hlt)
  rw [hF] at hz
  refine ⟨(z : ℚ_[q]), ?_⟩
  have : ((z ^ 2 + d : ℤ_[q]) : ℚ_[q]) = 0 := by rw [hz]; simp
  push_cast at this
  linear_combination -this

theorem intCast_mem_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (hp : (Ideal.absNorm w.asIdeal).Prime) (n : ℤ) :
    ((n : 𝓞 E) ∈ w.asIdeal ↔ ((Ideal.absNorm w.asIdeal : ℕ) : ℤ) ∣ n) := by
  set p := Ideal.absNorm w.asIdeal
  letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card (𝓞 E ⧸ w.asIdeal) = p := by
    rw [← Nat.card_eq_fintype_card]
    show _ = Ideal.absNorm w.asIdeal
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  let e : ZMod p ≃+* (𝓞 E ⧸ w.asIdeal) := ZMod.ringEquivOfPrime _ hp hc
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← ZMod.intCast_zmod_eq_zero_iff_dvd, map_intCast, ← map_intCast e,
    map_eq_zero_iff _ e.injective]

end GlobalTheory.DenseUsable

namespace GlobalTheory.DenseUsable

theorem exists_int_sub_mem {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (hp : (Ideal.absNorm w.asIdeal).Prime) (y : 𝓞 E) : ∃ a : ℤ, y - (a : 𝓞 E) ∈ w.asIdeal := by
  set p := Ideal.absNorm w.asIdeal
  letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card (𝓞 E ⧸ w.asIdeal) = p := by
    rw [← Nat.card_eq_fintype_card]
    show _ = Ideal.absNorm w.asIdeal
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  let e : ZMod p ≃+* (𝓞 E ⧸ w.asIdeal) := ZMod.ringEquivOfPrime _ hp hc
  obtain ⟨c, hc'⟩ := e.surjective (Ideal.Quotient.mk w.asIdeal y)
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective c
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hc', map_intCast, map_intCast, sub_self]

theorem usPl_of_absNorm_prime {E : Type} [Field E] [NumberField E] [IsCMField E] {d : ℕ} (hd : ImQ E d)
    (w : HeightOneSpectrum (𝓞 E)) (hp : (Ideal.absNorm w.asIdeal).Prime)
    (he : w.asIdeal.ramificationIdx ℤ = 1) (h2d : ((2 * d : ℕ) : 𝓞 E) ∉ w.asIdeal) : UsPl d w := by
  have hf := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 w).1 hp
  refine ⟨GlobalTheory.DenseInvFrob.isSplitAt_of_inertiaDeg_eq_one w hf he, fun q hq hqw => ?_⟩
  have hqw' : ((q : ℤ) : 𝓞 E) ∈ w.asIdeal := by rwa [Int.cast_natCast]
  have hpq : Ideal.absNorm w.asIdeal = q := by
    have := (intCast_mem_iff w hp q).1 hqw'
    exact (Nat.prime_dvd_prime_iff_eq hp hq).1 (Int.natCast_dvd_natCast.1 this)
  obtain ⟨-, x, hx⟩ := hd
  have hi : IsIntegral ℤ x := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hx]
    have : -(d : E) = algebraMap ℤ E (-(d : ℤ)) := by simp
    rw [this]; exact isIntegral_algebraMap
  let y : 𝓞 E := ⟨x, hi⟩
  have hy : y ^ 2 = -(d : 𝓞 E) := by
    apply RingOfIntegers.ext
    push_cast
    exact hx
  obtain ⟨a, ha⟩ := exists_int_sub_mem w hp y
  have h1 : ((q : ℤ) : ℤ) ∣ a ^ 2 + d := by
    rw [← hpq]
    refine (intCast_mem_iff w hp _).1 ?_
    have : (((a ^ 2 + d : ℤ)) : 𝓞 E) = (y - a) * (-(y + a)) + (y ^ 2 + d) := by push_cast; ring
    rw [this, hy, neg_add_cancel, add_zero]
    exact w.asIdeal.mul_mem_right _ ha
  have hnd : ¬ (q : ℤ) ∣ 2 * d := by
    intro h
    apply h2d
    have := (intCast_mem_iff w hp (2 * d)).2 (by rw [hpq]; exact h)
    simpa using this
  have hqz : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  haveI : Fact q.Prime := ⟨hq⟩
  refine isSquare_neg_padic q d a h1 fun h => ?_
  rcases hqz.dvd_or_dvd h with h' | h'
  · exact hnd (dvd_mul_of_dvd_left h' _)
  · apply hnd
    refine dvd_mul_of_dvd_right ?_ _
    have h3 : (q : ℤ) ∣ a ^ 2 := dvd_pow h' two_ne_zero
    have := (Int.dvd_add_right h3).1 h1
    exact this

end GlobalTheory.DenseUsable

namespace GlobalTheory.DenseUsable

theorem natCast_mem_of_dvd {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {n M : ℕ}
    (h : n ∣ M) (hn : (n : 𝓞 E) ∈ w.asIdeal) : (M : 𝓞 E) ∈ w.asIdeal := by
  obtain ⟨k, rfl⟩ := h
  push_cast
  exact w.asIdeal.mul_mem_right _ hn

theorem absNorm_mem_of_under_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w u : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E))) :
    ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ∈ w.asIdeal := by
  have hu : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ∈ u.asIdeal := Ideal.absNorm_mem u.asIdeal
  have h' := congrArg HeightOneSpectrum.asIdeal h
  simp only [HeightOneSpectrum.under_asIdeal] at h'
  have hm : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal.under (𝓞 (maximalRealSubfield E)) := by
    rw [Ideal.under, Ideal.mem_comap, map_natCast]; exact hu
  rw [← h', Ideal.under, Ideal.mem_comap, map_natCast] at hm
  exact hm

end GlobalTheory.DenseUsable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesMulAdeleAtBadPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFrames_mul_adele_at_badPrime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
    (κ : GL (Fin (D.R.N j)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), x₁.1 = x.1 * κ →
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    ∀ (P : SB t μ) (dep : SB t μ → ℕ) (g : Sp t.X.E (D.R.N j) ≃ₗ[t.X.E] Sp t.X.E (D.R.N j)),
      1 ≤ dep P → dep P ≤ (t.cst μ).D P → g ∈ GLint t.X.E (D.R.N j) P.1 →
      InFrame t.seam (A.fb j hj β) dep P κ g →
      (frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) ∈ GLint t.X.E (D.R.N j) P.1 ∧
      ∀ w ∈ stdAt t.X.E (D.R.N j) P.1, ((qOf P.1 : t.X.E) ^ dep P)⁻¹ •
        ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) w - w) ∈ stdAt t.X.E (D.R.N j) P.1) := by
  first | exact @GlobalTheory.FrameMove.frames_mul | exact GlobalTheory.FrameMove.frames_mul | (intros; apply GlobalTheory.FrameMove.frames_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointFramesMoveIntegralRightTranslate
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open GlobalTheory.TopStep
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FrameShift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_glint_nearAt {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (d : ℕ)
    (k : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hk : CongAt (seamP s P) 0 k) (hk' : CongAt (seamP s P) 0 k⁻¹) :
    ∃ g : GLint X.E n P, NearAt (seamP s P) d k (seamGL s g.1) := by
  obtain ⟨g0, hg0⟩ := GlobalTheory.TwU.Approx.exists_nearAt D.host.F D.host.E n (d + 1) (seamP s P) k
  set h := seamLE s g0 with hhdef
  have hh : seamGL s h = g0 := seamGL_seamLE s g0
  have hC : CongAt (F := D.host.F) (seamP s P) (d + 1) (k⁻¹ * ratA D.host.F (seamGL s h)) := by
    rw [hh]; exact hg0
  have h0 : CongAt (F := D.host.F) (seamP s P) 0 (ratA D.host.F (seamGL s h)) := by
    have e : ratA D.host.F (seamGL s h) = k * (k⁻¹ * ratA D.host.F (seamGL s h)) := by group
    rw [e]
    exact GlobalTheory.CplPt.congAt_mul 0 hk (GlobalTheory.FrameMove.congAt_mono (Nat.zero_le _) hC)
  have h0' : CongAt (F := D.host.F) (seamP s P) 0 (ratA D.host.F (seamGL s h⁻¹)) := by
    rw [map_inv, map_inv]
    have e : (ratA D.host.F (seamGL s h))⁻¹ = (k⁻¹ * ratA D.host.F (seamGL s h))⁻¹ * k⁻¹ := by group
    rw [e]
    exact GlobalTheory.CplPt.congAt_mul 0 (GlobalTheory.FrameMove.congAt_mono (Nat.zero_le _)
      (GlobalTheory.LevFrame.congAt_inv _ _ _ _ _ _ (Nat.succ_pos d) hC)) hk'
  have l1 := GlobalTheory.TwU.MidIndep.congAt_local s P 0 n h h0
  have l2 := GlobalTheory.TwU.MidIndep.congAt_local s P 0 n h⁻¹ h0'
  have hmem : h ∈ GLint X.E n P := by
    refine fun w => ⟨fun hw => ?_, fun hw => GlobalTheory.FrameMove.mem_of_local P 0 h l1 w hw⟩
    have := GlobalTheory.FrameMove.mem_of_local P 0 h⁻¹ l2 _ hw
    rwa [show (h⁻¹ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (h w) = w from h.symm_apply_apply w] at this
  refine ⟨⟨h, hmem⟩, ?_⟩
  show CongAt _ d (k⁻¹ * ratA D.host.F (seamGL s h))
  exact GlobalTheory.FrameMove.congAt_mono (Nat.le_succ d) hC

end GlobalTheory.FrameShift

namespace GlobalTheory.FrameShift

theorem exists_pt_mul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (y k : SB t μ → GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), (∀ P : SB t μ, CongAt (seamP t.seam P.1) 0 (k P) ∧ CongAt (seamP t.seam P.1) 0 (k P)⁻¹) → (∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P) (y P) (seamGL t.seam (frsF t.sel (t.tup μ) p P))) → ∃ p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i, p'.deco.1.N = p.deco.1.N ∧ p'.deco.1.f = p.deco.1.f ∧ ∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P) (y P * k P) (seamGL t.seam (frsF t.sel (t.tup μ) p' P))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie i p y k hk hy
  choose g hg using fun P : SB t μ => exists_glint_nearAt t.seam P.1 ((t.cst μ).D P) (k P) (hk P).1 (hk P).2
  obtain ⟨q, κ, hN, hf, hfr, hκ⟩ := GlobalTheory.CplPt.exists_pt_frames p g
  refine ⟨q, hN, hf, fun P => ?_⟩
  have base := GlobalTheory.CplPt.nearAt_mul_int _ (hy P) (hg P) (GlobalTheory.CplPt.seamGL_int t.seam (g P))
  rw [hfr P, map_mul]
  by_cases hP : P.1 ∈ t.Pr.vGs
  · have hD : (t.cst μ).D P = 1 := (t.idx_ok μ).depthG P hP
    have hq := (GlobalTheory.ColPeriod.levelPrimes t.X t.Pr t.sel t.S (t.tup μ) hPin.fields.ok t.pr_ok hPin.sel P).1.2
    have e : ((κ P)⁻¹).1 = (g P).1 * ((g P)⁻¹ * (κ P)⁻¹).1 := by
      rw [← Subgroup.coe_mul, mul_inv_cancel_left]
    rw [e, map_mul, ← mul_assoc]
    refine GlobalTheory.CplPt.nearAt_mul _ base ?_
    rw [hD]
    exact GlobalTheory.CplPt.congAt_one_of_redGL t.seam hq ((g P)⁻¹ * (κ P)⁻¹) (hκ P).1
  · rw [(hκ P).2 hP]
    exact base

end GlobalTheory.FrameShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointFramesMoveRationalIsometryStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartPointFrames_move_rationalIsometry : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → ∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P)
        (ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P)) (seamGL t.seam (frsF t.sel (t.tup μ) (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p) P))) := by
  first | exact @GlobalTheory.RatFrame.frame_rat | exact GlobalTheory.RatFrame.frame_rat | (intros; apply GlobalTheory.RatFrame.frame_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointLeftTranslateRationalUnitary
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory.TwRat

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem ratPt : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p, ∀ γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D i hi), x'.1 = ratA D.host.F γ * x.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p') := by
  intro D _ _ _ _ _ _ _ _ t u μ St A dtU a hP _ i hi β x x' p γ hγ hx hp
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.TwU.UnitaryFrom.exists_uf_seamGL_eq t.seam t.seam_ok (A.crd i hi * γ * (A.crd i hi)⁻¹) (_root_.GlobalTheory.unitary_conj_orthonormal D _ _ _ (hP.crd_orth i hi) hγ)
  have hmv : ∀ y : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      ratA D.host.F (A.crd i hi) * (ratA D.host.F γ * y) = ratA D.host.F (seamGL t.seam g.1) * (ratA D.host.F (A.crd i hi) * y) := by
    intro y
    rw [hg, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel_right]
  let a' : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K)) := (g, 1, 1)
  refine ⟨a' • p, ?_, ?_, ?_⟩
  · have e1 : (a' • p).deco.1.N = Formalism.HermitianLatticesTheory.gmap g.1 p.deco.1.N := rfl
    rw [e1, _root_.GlobalTheory.RatLat.lat_gmap, hg, hp.lat, hx, latCo_rat _ _ _ hγ]
  · intro P
    have hb := hp.frame P
    rw [hx, hmv, mul_assoc (ratA D.host.F (seamGL t.seam g.1))]
    by_cases hPg : P.1 ∈ t.Pr.vGs
    · have hD : (t.cst μ).D P = 1 := (t.idx_ok μ).depthG P hPg
      have e0 : frsF t.sel (t.tup μ) p P = p.deco.1.liftFr ⟨P.1, hPg⟩ := dif_pos hPg
      have e1 : frsF (R := D.R) t.sel (t.tup μ) (a' • p) P = ((g, (1 : GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs))) • p.deco).1.liftFr ⟨P.1, hPg⟩ := dif_pos hPg
      rw [hD, e0] at hb
      rw [hD, e1]
      exact GlobalTheory.T.levelFrameLift_unitaryAut_near_adelicMatrix_depth_one t.seam p.deco ⟨P.1, hPg⟩ g (mq_rowSG_unif (t.tup μ) hP.fields.ok t.pr_ok hP.sel P) _ hb
    · have e1 : frsF (R := D.R) t.sel (t.tup μ) (a' • p) P = g.1 * frsF t.sel (t.tup μ) p P := by
        unfold frsF
        rw [dite_eq_right hPg, dite_eq_right hPg]
        show g.1 * p.fr _ * (((1 : GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) _)⁻¹).1 = _
        simp
      rw [e1, map_mul, nearAt_rat_mul]
      exact hb
  · intro P v h hv
    rw [hx, hmv]
    exact GlobalTheory.T.levelPrimeFunctionals_move_rational_lattice_aut t.seam _ P v h _ _ _ g.1 1 (hp.fnl P v h hv)

end GlobalTheory.TwRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointsFramesCongrAwayFromBadPrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

noncomputable section

namespace GlobalTheory.AwayFr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem congAt_of_prV_eq (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 E)) (hv : Formalism.L2.Col.IsOver v Q) (n : ℕ)
    (y y₁ : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F)))
    (h : Formalism.UG.bc (Formalism.UG.prV (E := E) v) y₁ = Formalism.UG.bc (Formalism.UG.prV (E := E) v) y) :
    GlobalTheory.TwU.CongAt Q n (y⁻¹ * y₁) := by
  intro a b
  apply GlobalTheory.T.intAtAdele_mul_of_placeComponent_eq_zero F E v Q hv
  have h1 : Formalism.UG.bc (Formalism.UG.prV (E := E) v) (y⁻¹ * y₁) = 1 := by
    rw [map_mul, h, map_inv, inv_mul_cancel]
  have h2 := congrArg (fun g : GL (Fin N) (TensorProduct F E (v.adicCompletion F)) => (g : Matrix (Fin N) (Fin N) (TensorProduct F E (v.adicCompletion F))) a b) h1
  have h3 : Formalism.UG.prV (E := E) v (((y⁻¹ * y₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) a b) =
      (1 : Matrix (Fin N) (Fin N) (TensorProduct F E (v.adicCompletion F))) a b := h2
  rw [Matrix.sub_apply, map_sub, h3, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem congAt_ratA_of_near (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 E)) (hv : Formalism.L2.Col.IsOver v Q) (n : ℕ)
    (hn : 1 ≤ n) (y y₁ : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) (g g₁ : GL (Fin N) E)
    (h : Formalism.UG.bc (Formalism.UG.prV (E := E) v) y₁ = Formalism.UG.bc (Formalism.UG.prV (E := E) v) y)
    (hg : GlobalTheory.TwU.NearAt Q n y g) (hg₁ : GlobalTheory.TwU.NearAt Q n y₁ g₁) :
    GlobalTheory.TwU.CongAt Q n (GlobalTheory.TwU.ratA F (g⁻¹ * g₁)) := by
  have e : GlobalTheory.TwU.ratA F (g⁻¹ * g₁) = (y⁻¹ * GlobalTheory.TwU.ratA F g)⁻¹ * ((y⁻¹ * y₁) * (y₁⁻¹ * GlobalTheory.TwU.ratA F g₁)) := by
    rw [map_mul, map_inv]; group
  rw [e]
  exact _root_.GlobalTheory.CongProd.congAt_mul_prod F E Q n N _ _ (_root_.GlobalTheory.TwU.congAt_inv_pos_depth F E Q n N _ hn hg) (_root_.GlobalTheory.CongProd.congAt_mul_prod F E Q n N _ _ (congAt_of_prV_eq v Q hv n y y₁ h) hg₁)

end GlobalTheory.AwayFr

namespace GlobalTheory.AwayFr

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

theorem monoidHom_mul_mul_congr_middle {M M' : Type} [Monoid M] [Monoid M'] (φ : M →* M') (a b b₁ c : M) (h : φ b₁ = φ b) :
    φ (a * b₁ * c) = φ (a * b * c) := by
  rw [map_mul, map_mul, h, ← map_mul, ← map_mul]

theorem intAt_of_cong {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (z δ : E) (hδ : IntAt P δ)
    (h : IntAt P ((((qOf P : ℕ) : E) ^ n)⁻¹ * (z - δ))) : IntAt P z := by
  have e : z = δ + (((qOf P ^ n : ℕ) : ℕ) : E) * ((((qOf P : ℕ) : E) ^ n)⁻¹ * (z - δ)) := by
    rw [← mul_assoc, Nat.cast_pow, mul_inv_cancel₀ (pow_ne_zero _ (GlobalTheory.TopInv.qOf_ne P)), one_mul]; ring
  rw [e]
  exact hδ.add ((GlobalTheory.TopInv.intAt_nat (P := P) (qOf P ^ n)).mul h)

theorem intAt_single {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (s l : Fin n) :
    IntAt P ((Pi.single s 1 : Fin n → E) l) := by
  rw [Pi.single_apply]
  split_ifs
  · simpa using GlobalTheory.TopInv.intAt_nat (P := P) 1
  · simpa using GlobalTheory.TopInv.intAt_nat (P := P) 0

theorem intAt_of_seam {D : D7} {X : Fields} (s : Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) (z : X.E)
    (h : IntAt (seamP s P) (s.iE z)) : IntAt P z := by
  obtain ⟨r, c, hc, e⟩ := h
  refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r, (RingOfIntegers.mapRingEquiv s.iE).symm c, ?_, ?_⟩
  · rwa [← mem_seamP s P, RingEquiv.apply_symm_apply]
  · apply s.iE.injective
    have k : ∀ w : 𝓞 D.host.E, s.iE (algebraMap (𝓞 X.E) X.E ((RingOfIntegers.mapRingEquiv s.iE).symm w)) = algebraMap _ _ w := by
      intro w
      conv_rhs => rw [← RingEquiv.apply_symm_apply (RingOfIntegers.mapRingEquiv s.iE) w]
      rfl
    rw [map_mul, k, k, e]

theorem mem_stdAt_of_int {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (g : Sp E n ≃ₗ[E] Sp E n) (hg : ∀ s l, IntAt P (g (Pi.single s 1) l)) (w : Sp E n) (hw : w ∈ stdAt E n P) :
    g w ∈ stdAt E n P := by
  rw [stdAt, mem_localization_standardLattice] at hw ⊢
  intro l
  have e : g w l = ∑ s, g (Pi.single s 1) l * w s := by
    have := congrFun (LinearMap.toMatrix'_mulVec g.toLinearMap w) l
    rw [← LinearEquiv.coe_toLinearMap, ← this]
    simp only [Matrix.mulVec, dotProduct, LinearMap.toMatrix'_apply, LinearEquiv.coe_toLinearMap]
  rw [e]
  refine Finset.sum_induction _ (IntAt P) (fun a b ha hb => ha.add hb) (by simpa using GlobalTheory.TopInv.intAt_nat (P := P) 0)
    fun s _ => (hg s l).mul (hw s)

end GlobalTheory.AwayFr

namespace GlobalTheory.AwayFr

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

theorem frames_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : SB t μ, ∃ k : GLint t.X.E (D.R.N j) P.1, frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k.1 ∧
      ∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ ((t.cst μ).D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp t.X.E (D.R.N j)) l))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hPins hTie j hj β x x₁ p p₁ hp hp₁ hx P
  classical
  have hSS := ((isChainTop_iff _ _ _ _ _ _ _ _ _).1 hTie.isChainTop).1
  have hQ : seamP t.seam P.1 ∈ ssRec t u μ :=
    (mem_ssRec t u μ P.1).2 (by rw [hSS]; exact Finset.mem_union_right _ P.2)
  have hv : IsOver (underPl D.host.F (seamP t.seam P.1)) (seamP t.seam P.1) := rfl
  have hxv := hx _ ⟨_, hQ, hv⟩
  have hD : 1 ≤ (t.cst μ).D P := ((t.idx_ok μ).cst_ok).D_pos P
  have c1 := congAt_ratA_of_near _ _ hv _ hD _ _ _ _ (monoidHom_mul_mul_congr_middle _ _ _ _ _ hxv) (hp.frame P) (hp₁.frame P)
  have c2 := congAt_ratA_of_near _ _ hv _ hD _ _ _ _ (monoidHom_mul_mul_congr_middle _ _ _ _ _ hxv.symm) (hp₁.frame P) (hp.frame P)
  rw [← map_inv, ← map_mul] at c1 c2
  have i1 := GlobalTheory.T.rationalMatrix_entries_congruent_one_of_adelic_congruent _ _ _ _ _ _ c1
  have i2 := GlobalTheory.T.rationalMatrix_entries_congruent_one_of_adelic_congruent _ _ _ _ _ _ c2
  rw [_root_.GlobalTheory.qOf_seamP] at i1 i2
  have entry : ∀ (g : Sp t.X.E (D.R.N j) ≃ₗ[t.X.E] Sp t.X.E (D.R.N j)) (l s : Fin (D.R.N j)),
      ((seamGL t.seam g : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) l s =
        t.seam.iE (g (Pi.single s 1) l) := by
    intro g l s
    show ((LinearMap.toMatrix' g.toLinearMap).map (t.seam.iE : t.X.E →+* D.host.E)) l s = _
    rw [Matrix.map_apply, LinearMap.toMatrix'_apply]
    rfl
  have cong : ∀ g : Sp t.X.E (D.R.N j) ≃ₗ[t.X.E] Sp t.X.E (D.R.N j),
      (∀ l s : Fin (D.R.N j), IntAt (seamP t.seam P.1) ((((qOf P.1 : ℕ) : D.host.E) ^ (t.cst μ).D P)⁻¹ *
        (((seamGL t.seam g : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) l s -
          (1 : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) l s))) →
      ∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ ((t.cst μ).D P))⁻¹ * (g (Pi.single s 1) l - (Pi.single s 1 : Sp t.X.E (D.R.N j)) l)) := by
    intro g h s l
    apply intAt_of_seam t.seam P.1
    have := h l s
    rw [entry, Matrix.one_apply] at this
    convert this using 1
    rw [map_mul, map_inv₀, map_pow, map_natCast, map_sub, Pi.single_apply]
    split_ifs <;> simp
  have h1 := cong ((frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P) (by simpa only [map_mul, map_inv] using i1)
  have h2 := cong ((frsF t.sel (t.tup μ) p₁ P)⁻¹ * frsF t.sel (t.tup μ) p P) (by simpa only [map_mul, map_inv] using i2)
  have int1 : ∀ s l, IntAt P.1 (((frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P) (Pi.single s 1) l) := fun s l =>
    intAt_of_cong P.1 _ _ _ (intAt_single P.1 s l) (h1 s l)
  have int2 : ∀ s l, IntAt P.1 (((frsF t.sel (t.tup μ) p₁ P)⁻¹ * frsF t.sel (t.tup μ) p P) (Pi.single s 1) l) := fun s l =>
    intAt_of_cong P.1 _ _ _ (intAt_single P.1 s l) (h2 s l)
  have hk : (frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P ∈ GLint t.X.E (D.R.N j) P.1 := by
    intro w
    constructor
    · intro hw
      have e : w = ((frsF t.sel (t.tup μ) p₁ P)⁻¹ * frsF t.sel (t.tup μ) p P) (((frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P) w) := by
        rw [← LinearEquiv.mul_apply, mul_assoc, mul_inv_cancel_left, inv_mul_cancel]
        rfl
      rw [e]
      exact mem_stdAt_of_int P.1 _ int2 _ hw
    · exact mem_stdAt_of_int P.1 _ int1 w
  exact ⟨⟨(frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P, hk⟩, by simp, h1⟩

end GlobalTheory.AwayFr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmIdeleConjMemCongruenceUnitIdelesConjPlacesStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmIdeleConj_mem_congruenceUnitIdeles_conj_places : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (T : Set (HeightOneSpectrum (𝓞 E))) (N : ℕ) (u : Ideles E), u ∈ levT E T N → ideleConj (maximalRealSubfield E) E u ∈ levT E {w | ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → w' ∈ T} N := by
  first | exact @GlobalTheory.HeckeConjLev.ideleConj_mem_levT | exact GlobalTheory.HeckeConjLev.ideleConj_mem_levT | (intros; apply GlobalTheory.HeckeConjLev.ideleConj_mem_levT <;> assumption)
end

