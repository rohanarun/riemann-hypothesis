module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0266
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Formalism.LocalToGlobal.Columns.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0271
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0159
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0267

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicMatrixCongruentOneAtPrimeInvOfPosDepth
section
open NumberField IsDedekindDomain

theorem GlobalTheory.TwU.congAt_inv_pos_depth : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (Q : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (k : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))),
    1 ≤ n → GlobalTheory.TwU.CongAt Q n k → GlobalTheory.TwU.CongAt Q n k⁻¹ :=
  fun F E _ _ _ _ _ Q n N k hn hk => GlobalTheory.LevFrame.congAt_inv F E N n Q k hn hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainChartFramesBadPrimeCongruentOneOfAdelicAgreStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainChart_frames_badPrime_congruent_one_of_adelic_agree : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : SB t μ,
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∃ k : Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i), frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k ∧
      ∀ s l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (k (Pi.single s (1 : t.X.E)) l - (Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N i)) l)) := by
  first | exact @GlobalTheory.FrameAway.frame_away | exact GlobalTheory.FrameAway.frame_away | (intros; apply GlobalTheory.FrameAway.frame_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBasePointAdelicRightMulLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_base_point_adelic_right_mul_level : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (κ : ((St i hi).K β).lev.U) (x x₁ : UA D i hi)
    (p q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (k : SB t μ → (Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i))),
    x₁.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → q.deco.1.N = p.deco.1.N → q.deco.1.f = p.deco.1.f →
    (∀ P, frsF t.sel (t.tup μ) q P = frsF t.sel (t.tup μ) p P * k P) → (∀ P, k P ∈ GLint t.X.E (D.R.N i) P.1) →
    (∀ P, InFrame t.seam (A.fb i hi β) (t.cst μ).D P κ.1 (k P)) → IsPtAd A a i hi β x₁ q) := by
  first | exact @GlobalTheory.PtMove.isPtAd_mul_lev | exact GlobalTheory.PtMove.isPtAd_mul_lev | (intros; apply GlobalTheory.PtMove.isPtAd_mul_lev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesCongruentOneOfSameBadPlaceComponentsStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFrames_congruent_one_of_same_badPlace_components : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ P : SB t μ, (frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm ∈ GLint t.X.E (D.R.N j) P.1 ∧
    ∀ w ∈ stdAt t.X.E (D.R.N j) P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ •
      ((frsF t.sel (t.tup μ) p P).symm (frsF t.sel (t.tup μ) p₁ P w) - w) ∈ stdAt t.X.E (D.R.N j) P.1) := by
  first | exact @GlobalTheory.FrameAgree.frame_away | exact GlobalTheory.FrameAgree.frame_away | (intros; apply GlobalTheory.FrameAgree.frame_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesMulAdeleAtBadPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameMove

section Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem congAt_mono {P : HeightOneSpectrum (𝓞 E)} {m n : ℕ} (hmn : m ≤ n) {k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (h : CongAt (F := F) P n k) : CongAt (F := F) P m k := by
  intro a b
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  have e0 : (((qOf P : ℕ) : E) ^ m)⁻¹ = algebraMap (𝓞 E) E (((qOf P : ℕ) : 𝓞 E) ^ (n - m)) * (((qOf P : ℕ) : E) ^ n)⁻¹ := by
    rw [map_pow, map_natCast]
    have hn : ((qOf P : ℕ) : E) ^ n = ((qOf P : ℕ) : E) ^ m * ((qOf P : ℕ) : E) ^ (n - m) := by
      rw [← pow_add, Nat.add_sub_cancel' hmn]
    rw [hn]
    field_simp
  have e : iA F E (((qOf P : ℕ) : E) ^ m)⁻¹ * ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b =
      iA F E (algebraMap (𝓞 E) E (((qOf P : ℕ) : 𝓞 E) ^ (n - m))) *
        (iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ * ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b) := by
    rw [← mul_assoc, ← map_mul, e0]
  rw [e]
  exact GlobalTheory.CplPt.intAtA_mul (GlobalTheory.CplPt.intAtA_int _) (h a b)

end Cong

theorem mem_of_local {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ)
    (k : Sp E n ≃ₗ[E] Sp E n) (hk : ∀ x ∈ stdAt E n P, ((qOf P ^ d : ℕ) : E)⁻¹ • (k x - x) ∈ stdAt E n P)
    (x : Sp E n) (hx : x ∈ stdAt E n P) : k x ∈ stdAt E n P := by
  have hq : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hc : ((qOf P ^ d : ℕ) : E) ≠ 0 := by exact_mod_cast pow_ne_zero d hq
  have e : k x = x + (qOf P ^ d) • (((qOf P ^ d : ℕ) : E)⁻¹ • (k x - x)) := by
    rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hc, one_smul, add_sub_cancel]
  rw [e]
  exact add_mem hx (nsmul_mem (hk x hx) _)

end GlobalTheory.FrameMove

namespace GlobalTheory.FrameMove

theorem frames_mul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
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
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ j hj β x x₁ κ p p₁ hxκ hp hp₁ P dep g hd1 hdD hg hIn
  have hD1 : 1 ≤ (t.cst μ).D P := hd1.trans hdD
  have hu := hp.frame P
  have hu₁ := hp₁.frame P
  unfold NearAt at hu hu₁
  unfold InFrame NearAt at hIn
  rw [hxκ] at hu₁
  set h := (frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) with hh
  have hs : h = g⁻¹ * ((frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P) := by
    ext w; rfl
  have key : ratA D.host.F (seamGL t.seam h) =
      ((ratA D.host.F (seamGL t.seam g))⁻¹ *
        ((ratA D.host.F (A.crd j hj) * x.1 * ratA D.host.F (A.fb j hj β P))⁻¹ * ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p P)))⁻¹ *
        ratA D.host.F (seamGL t.seam g)) *
      (((ratA D.host.F (A.fb j hj β P))⁻¹ * κ * ratA D.host.F (A.fb j hj β P))⁻¹ * ratA D.host.F (seamGL t.seam g))⁻¹ *
      ((ratA D.host.F (A.crd j hj) * (x.1 * κ) * ratA D.host.F (A.fb j hj β P))⁻¹ *
        ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p₁ P))) := by
    rw [hs]
    simp only [map_mul, map_inv]
    group
  have c1 := GlobalTheory.CplPt.congAt_conj (dep P)
    (congAt_mono hdD (GlobalTheory.LevFrame.congAt_inv _ _ _ _ _ _ hD1 hu))
    (fun a b => GlobalTheory.CplPt.seamGL_int t.seam ⟨g, hg⟩ a b)
  have c2 := GlobalTheory.LevFrame.congAt_inv _ _ _ _ _ _ hd1 hIn
  have c3 := congAt_mono hdD hu₁
  have hC : CongAt (F := D.host.F) (seamP t.seam P.1) (dep P) (ratA D.host.F (seamGL t.seam h)) := by
    rw [key]
    exact GlobalTheory.CplPt.congAt_mul _ (GlobalTheory.CplPt.congAt_mul _ c1 c2) c3
  have hCi : CongAt (F := D.host.F) (seamP t.seam P.1) (dep P) (ratA D.host.F (seamGL t.seam h⁻¹)) := by
    rw [map_inv, map_inv]
    exact GlobalTheory.LevFrame.congAt_inv _ _ _ _ _ _ hd1 hC
  have l1 := GlobalTheory.TwU.MidIndep.congAt_local t.seam P.1 (dep P) (D.R.N j) h hC
  have l2 := GlobalTheory.TwU.MidIndep.congAt_local t.seam P.1 (dep P) (D.R.N j) h⁻¹ hCi
  refine ⟨fun w => ⟨fun hw => ?_, fun hw => mem_of_local P.1 (dep P) h l1 w hw⟩, fun w hw => ?_⟩
  · have := mem_of_local P.1 (dep P) h⁻¹ l2 _ hw
    rwa [show (h⁻¹ : Sp t.X.E (D.R.N j) ≃ₗ[t.X.E] Sp t.X.E (D.R.N j)) (h w) = w from h.symm_apply_apply w] at this
  · have := l1 w hw
    rwa [Nat.cast_pow] at this

end GlobalTheory.FrameMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointFramesMoveRationalIsometry
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.RatFrame


set_option maxHeartbeats 400000 in
theorem frame_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → ∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P)
        (ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P)) (seamGL t.seam (frsF t.sel (t.tup μ) (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p) P))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie i hi β x x₁ γ hγ h₁ g hg p hp P
  have hx : ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P) =
      ratA D.host.F (seamGL t.seam g.1) * (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) := by
    rw [h₁, hg, map_mul, map_mul, map_inv]
    group
  rw [hx]
  have h0 := hp.frame P
  by_cases hP : P.1 ∈ t.Pr.vGs
  · have hD : (t.cst μ).D P = 1 := (t.idx_ok μ).depthG P hP
    have hq := GlobalTheory.TopStep.qOf_notMem_sq hPin.fields.ok t.pr_ok hP
    have e1 : frsF t.sel (t.tup μ) p P = p.deco.1.liftFr ⟨P.1, hP⟩ := by
      unfold frsF
      rw [dite_eq_left hP]
    have h1 : NearAt (seamP t.seam P.1) 1 (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) (seamGL t.seam (p.deco.1.liftFr ⟨P.1, hP⟩)) := by
      rw [← e1, ← hD]; exact h0
    have e2 : frsF t.sel (t.tup μ) (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) ×
        GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p) P =
        (((g, (1 : GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs))) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs)) • p.deco).1.liftFr ⟨P.1, hP⟩ := by
      unfold frsF
      rw [dite_eq_left hP]
      rfl
    have key := GlobalTheory.FrameRat.nearAt_liftFr_smul t.seam p.deco ⟨P.1, hP⟩ g hq _ h1
    rw [e2, hD]
    exact key
  · have e : frsF t.sel (t.tup μ) (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) ×
        GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p) P = g.1 * frsF t.sel (t.tup μ) p P := by
      unfold frsF
      rw [dite_eq_right hP, dite_eq_right hP]
      show g.1 * _ * _ = _
      simp
      rfl
    rw [e, map_mul, nearAt_rat_mul]
    exact h0

end GlobalTheory.RatFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmIdeleConjMemCongruenceUnitIdelesConjPlaces
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj finiteCompletionMap)

namespace GlobalTheory.HeckeConjLev

theorem ideleMap_mem_levT (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (T : Set (HeightOneSpectrum (𝓞 K))) (T' : Set (HeightOneSpectrum (𝓞 L)))
    (hT : ∀ w ∈ T', w.under (𝓞 K) ∈ T) (N : ℕ) (y : Ideles K) (hy : y ∈ levT K T N) :
    ideleMap K L y ∈ levT L T' N := by
  have hc : ∀ w : HeightOneSpectrum (𝓞 L), (ideleMap K L y).val.2 w =
      finiteCompletionMap K L w (y.val.2 (w.under (𝓞 K))) := fun w => rfl
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · show Valued.v ((ideleMap K L y).val.2 w) = 1
    have h : Valued.v (y.val.2 (w.under (𝓞 K))) = 1 := hy.1 _
    rw [hc, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, h, one_pow]
  · show Valued.v ((ideleMap K L y).val.2 w - 1) ≤ Valued.v (N : w.adicCompletion L)
    rw [hc, ← map_one (finiteCompletionMap K L w), ← map_sub, ← map_natCast (finiteCompletionMap K L w),
      GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap]
    exact pow_le_pow_left₀ zero_le (hy.2 _ (hT w hw)) _

theorem under_under (F K L : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra F K] [Algebra K L] [Algebra F L]
    (h : ∀ x : F, algebraMap K L (algebraMap F K x) = algebraMap F L x) (w : HeightOneSpectrum (𝓞 L)) :
    (w.under (𝓞 K)).under (𝓞 F) = w.under (𝓞 F) := by
  haveI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun x => (h x).symm
  exact HeightOneSpectrum.ext (Ideal.under_under w.asIdeal)

theorem ideleConj_mem_levT (E : Type) [Field E] [NumberField E] [IsCMField E]
    (T : Set (HeightOneSpectrum (𝓞 E))) (N : ℕ) (u : Ideles E) (hu : u ∈ levT E T N) :
    ideleConj (maximalRealSubfield E) E u ∈ levT E {w | ∀ w' : HeightOneSpectrum (𝓞 E),
      w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → w' ∈ T} N :=
  @ideleMap_mem_levT E E _ _ _ _
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra T
    {w | ∀ w' : HeightOneSpectrum (𝓞 E),
      w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → w' ∈ T}
    (fun w hw => hw _ (@under_under (maximalRealSubfield E) E E _ _ _ _ _ _ _
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra _
      (fun x => (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).commutes x) w)) N u hu

end GlobalTheory.HeckeConjLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeVectorLocalMemDualBaseCompletion
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

open Formalism.MainNotions.G.KAat Matrix

namespace GlobalTheory.CompanLocal

theorem mem_latS_dual_of_mem_latCo : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (sp : Spaces R F E) (J : Matrix (Fin N) (Fin N) E) (crd : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F) → IsUnit J.det →
    ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    (∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (u : Fin N → E), u ∈ latCo sp J crd a x Lb →
    ∃ z : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)),
      z.1 = fun l => prV (E := E) v (pullV (F := F) (ratA F crd * x) u l) := by
  intro R F E _ _ _ _ _ _ N sp J crd a x hx hJ Lb hfin hspan hint v u hu
  set y := bc (prV (E := E) v) x with hy_def
  simp only [latCo, mvL, Submodule.mem_map] at hu
  obtain ⟨w, hw, rfl⟩ := hu
  let locV : (Fin N → E) → (Fin N → E ⊗[F] v.adicCompletion F) := fun z i => inclE (F := F) (v.adicCompletion F) (z i)
  have hcomp : (fun l => prV (E := E) v (pullV (F := F) (ratA F crd * x)
      (((toLE crd : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E) w) l)) =
      ((y⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) *ᵥ locV w := by
    have h1 : pullV (F := F) (ratA F crd * x)
        (((toLE crd : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E) w) =
        ((x⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _) *ᵥ
          (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (w i)) := by
      unfold pullV
      rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← map_inv]
      congr 1
      have := bc_mulVec (F := F) crd⁻¹ (toLE crd w)
      refine this.trans ?_
      funext i
      show inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (toLE crd⁻¹ (toLE crd w) i) = _
      rw [toLE_inv_apply']
    rw [h1, GlobalTheory.LocCarry.prV_mulVec, ← GlobalTheory.LocCarry.coe_bc_inv]
    congr 1
  have hlat : latAd x Lb = Formalism.UG.CS.globLat x Lb := Submodule.span_eq (Formalism.UG.CS.globLat x Lb)
  have hL : Submodule.IsFullLattice E (latAd x Lb) := by
    rw [hlat]; exact Formalism.UG.P.csGlob_lattice Lb hfin hspan x
  have hLb : Submodule.IsFullLattice E Lb := {
    toIsLattice := Submodule.IsLattice.of_fg E (Module.Finite.iff_fg.mp hfin)
    span_eq_top := hspan }
  have hyU : y ∈ UPts sp.cm.sig J (v.adicCompletion F) := Formalism.UG.P.afsplit_bc_mem _ J v x hx
  have hyl := fun z => GlobalTheory.LocCarry.mem_latS_latAd_iff x Lb hfin hspan v z
  have hdm := GlobalTheory.DualCompletion.dual_move F E sp.cm.sig N J v (latAd x Lb) Lb y hJ hL hLb hyU hyl
  have hsub : latS (F := F) (v.adicCompletion F) (intV E v) Lb ≤
      latS (F := F) (v.adicCompletion F) (intV E v) (Formalism.L2.Forms.dualL (sp.cm.sig : E →+* E) J Lb) :=
    Submodule.span_mono (Set.image_mono (fun z hz => Submodule.subset_span (hint z hz)))
  have hmem : ∀ (Λ : Submodule (𝓞 E) (Fin N → E)) z, z ∈ Λ → locV z ∈ latS (F := F) (v.adicCompletion F) (intV E v) Λ :=
    fun Λ z hz => Submodule.subset_span ⟨z, hz, rfl⟩
  simp only [compan] at hw
  obtain ⟨w1, hw1, w2, hw2, rfl⟩ := Submodule.mem_sup.1 hw
  have hw2' : w2 ∈ Formalism.L2.Forms.dualL (sp.cm.sig : E →+* E) J (latAd x Lb) := Submodule.smul_le_right hw2
  have hadd : locV (w1 + w2) = locV w1 + locV w2 := by funext i; simp [locV, map_add (f := _)]
  have key : ((y⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) *ᵥ
      locV (w1 + w2) ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Formalism.L2.Forms.dualL (sp.cm.sig : E →+* E) J Lb) := by
    rw [hadd, Matrix.mulVec_add]
    exact add_mem (hsub ((hyl _).1 (hmem _ _ hw1))) ((hdm _).1 (hmem _ _ hw2'))
  exact ⟨⟨_, key⟩, hcomp.symm⟩

end GlobalTheory.CompanLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruentOneMemStepLevelsCharacterOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

noncomputable section

namespace GlobalTheory.LevOneAt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV _root_.Formalism.L2.Col

theorem cong_mem_level_chr_one' : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.Ok → Pr.Ok → L.Ok Ch sel mu cst G m2 → ∀ (j : ℕ), j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu)
    (k : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N j)) l))) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (k x)) ∧ chiInv Ch sel mu cst j P (L.h j b P) r = 1 := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hL j hj b P k hk
  classical
  obtain ⟨hkG, hkC⟩ := GlobalTheory.T.mem_integralGL_principalCongruence_of_cols_cong P.1 (cst.D P) k (hL.cst_ok.D_pos P) hk
  set κ : GLint X.E (R.N j) P.1 := ⟨k, hkG⟩ with hκdef
  have hψ : cst.psi P (Loc.n1Arg (GlobalTheory.CongLevel.extE (cOf R j) k)) = 1 := by
    rw [GlobalTheory.Mem.Col2.LevMod.unipotentArg_extendByIdOnLastCoords]
    exact hL.cst_ok.psi_int P 0 (by simpa using GlobalTheory.CongLevel.intAt_nat P.1 0)
  have hq : ((qOf P.1 : ℕ) : X.E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  by_cases hP : P.1 ∈ Pr.vGs
  · have hD1 : cst.D P = 1 := hL.depthG P hP
    have hdu := GlobalTheory.Mem.Col2.degOneUnram_of_mem_vGs hX hPr hP
    have hd : ∀ a : X.E, IntAt P.1 a → redP P.1 a = 0 → IntAt P.1 (a / (qOf P.1 : X.E)) :=
      fun a ha h0 => GlobalTheory.TopStep.intAt_div_of_redP hdu.2 ha h0
    have hred : ∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (k x) = redV P.1 x := by
      have h1 := GlobalTheory.TopStep.redGL_of_prinCong (by omega : 0 < cst.D P) hkC
      intro x hx
      have h2 := GlobalTheory.TopStep.redV_redGL κ hx
      rw [h1, Units.val_one, Matrix.one_mulVec] at h2
      exact h2
    have hh := hL.stabG j b P hP
    refine ⟨GlobalTheory.CongLevel.extE (cOf R j) k, GlobalTheory.Mem.Col2.LevMod.extE_mem_Cbe cst.sharp j P.1 hP hd (L.h j b P) hh k hkG hred, GlobalTheory.CongLevel.extE_inX _ k, ?_⟩
    have hh' := hh
    unfold lamYat at hh'
    rw [if_pos hP] at hh'
    have hcong := GlobalTheory.CongLevel.conj_cong (qOf P.1) _ _ (L.h j b P) hh'
      (GlobalTheory.CongLevel.extE_cong P.1 (qOf P.1) (cOf R j) (fun i => i + 1) hd k hkG hred)
    have h1 := GlobalTheory.T.rowCharacter_id_add_q_smul_latticePreserving_eq_one Ch mu cst.sharp j P.1 hP ((qOf P.1 : X.E)⁻¹ •
      (((L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) k * L.h j b P : AutY X R j).toLinearMap - LinearMap.id))
      fun x hx => by
        have hx' := hx
        unfold lamYat at hx' ⊢
        rw [if_pos hP] at hx' ⊢
        have h2 := hcong x hx'
        rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
        exact h2
    rw [smul_inv_smul₀ hq, add_sub_cancel] at h1
    unfold chiInv
    rw [h1, hψ, inv_one, one_mul]
  · have hstd : ∀ x, x ∈ lamYat (Pr := Pr) (R := R) j P.1 ↔ x ∈ stdAt X.E (R.N j + cOf R j) P.1 := by
      intro x
      unfold lamYat
      rw [if_neg hP]
      unfold LocE.lamY
      rw [GlobalTheory.CongLevel.mem_sclLat, GlobalTheory.TopStep.mem_stdAt]
      simp only [LocE.scE, Pi.zero_apply, Nat.cast_zero, ite_self, zpow_zero, inv_one, one_mul]
    have hbd := hL.boundQ j b P hP
    have hbd' : ∀ x ∈ stdAt X.E (R.N j + cOf R j) P.1, (L.h j b P)⁻¹ x ∈ stdAt X.E (R.N j + cOf R j) P.1 ∧
        ((qOf P.1 : X.E) ^ j) • (L.h j b P) x ∈ stdAt X.E (R.N j + cOf R j) P.1 := fun x hx => by
      have h1 := hbd x ((hstd x).2 hx)
      exact ⟨(hstd _).1 h1.1, (hstd _).1 h1.2⟩
    have hjD : j + 1 ≤ cst.D P := by
      have h1 := hL.depthQ' P hP
      have h2 := hL.hm
      omega
    have hg := _root_.GlobalTheory.QCong.conj_extE_cong P.1 (cOf R j) j (cst.D P) (L.h j b P) κ hkC hjD hbd'
    have hginv := _root_.GlobalTheory.QCong.conj_extE_cong P.1 (cOf R j) j (cst.D P) (L.h j b P) κ⁻¹ (inv_mem hkC) hjD hbd'
    have einv : ((L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) κ.1 * L.h j b P)⁻¹ =
        (L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) (κ⁻¹).1 * L.h j b P := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, GlobalTheory.CongLevel.extE_inv, mul_assoc]
      rfl
    refine ⟨GlobalTheory.CongLevel.extE (cOf R j) k, ⟨GlobalTheory.CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ k, ?_⟩, GlobalTheory.CongLevel.extE_inX _ k, ?_⟩
    · have e : (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R j) k) =
          (L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) k * L.h j b P := by simp
      show (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R j) k) ∈ Jat (Pr := Pr) cst.sharp j P.1
      rw [e]
      unfold Jat
      rw [if_neg hP]
      refine _root_.GlobalTheory.ParahoricOfCong.mem_JQ_of_cong P.1 (R.k + j) (R.N j) (cOf R j) _ hg ?_
      rw [einv]
      exact hginv
    · unfold chiInv
      rw [hψ, inv_one, one_mul]
      unfold lamRow
      rw [if_neg hP]
      exact _root_.GlobalTheory.LamQBCong.lamQB_eq_one_of_cong P.1 _ (R.k + j) (R.N j) (R.N j + cOf R j) _ (by omega) hg

theorem levAt_one : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.Ok → Pr.Ok → ChIdx.Ok Ch sel mu cst L G m2 → ∀ j (b : L.β j) (P : rowSG Pr sel mu) (k : GLint X.E (R.N j) P.1), j ≤ m2 + 1 →
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E (R.N j)) l))) →
    GlobalTheory.TopLaw.LevAt (L.levG j b) (L.levQ j b) P k 1 := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hL j b P k hj hk
  obtain ⟨r, hr, hrx, hchi⟩ := cong_mem_level_chr_one' Ch sel mu cst L G m2 hX hPr hL j hj b P k.1 hk
  obtain ⟨c, hc, ec⟩ := GlobalTheory.CplLev.levAt_of_lift hL b P k r hr hrx
  have : c = 1 := Units.ext (by rw [ec, hchi, Units.val_one])
  rwa [this] at hc

end GlobalTheory.LevOneAt
end
end

