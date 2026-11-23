module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHormanderPeakOrthonormalFrameL2Bound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormQuotientClassEqOfRelDifferences
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormPeakAtInjectiveChartFrame
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

theorem GlobalTheory.PeakThick.peak : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ b : ℝ) - la τ a) → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ∀ (x0 : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X))), ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet X x0 FF → ∃ P ∈ X.SS la, P x ≠ 0 ∧ ENNReal.ofReal (Real.exp (-(C * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8)))) * ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la P (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) ≤ ENNReal.ofReal (X.pnorm la P x ^ 2) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0 FF := by
  obtain ⟨CH, hCH, hH⟩ := _root_.GlobalTheory.HormanderPeak.hormander_peak
  obtain ⟨CS, hCS, hS⟩ := _root_.GlobalTheory.PoincareL2.poincare_l2_inequality
  refine ⟨CH + CS + 1, by linarith, ?_⟩
  intro E _ _ _ r X la x hp0 hp0r hx hgap hpair hinj x0 FF hx0 hFF
  classical
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hΨ : ∃ τ0 : X.Ψ, True := by
    by_cases hσ : σ ∈ X.Ψ
    · exact ⟨⟨σ, hσ⟩, trivial⟩
    · exact ⟨⟨ComplexEmbedding.conjugate σ, by
        by_contra h
        exact hσ ((X.cmType σ).2 h)⟩, trivial⟩
  obtain ⟨τ0, -⟩ := hΨ
  have hcard : (1 : ℝ) ≤ X.Ψ.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨τ0.1, τ0.2⟩
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hN : (1 : ℝ) ≤ (X.Ψ.card : ℝ) * r := by nlinarith
  have hN8 : (1 : ℝ) ≤ ((X.Ψ.card : ℝ) * r) ^ 8 := one_le_pow₀ hN
  have hS0 : 0 ≤ ∑ τ, ∑ a, |(la τ a : ℝ)| := by positivity
  have hgapH : ∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 →
      CH * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ a : ℝ) - la τ b := fun τ a b h1 h2 =>
    le_trans (by nlinarith) (hgap τ a b h1 h2)
  have hpairH : ∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 →
      CH * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ b : ℝ) - la τ a := fun τ a b h1 h2 =>
    le_trans (by nlinarith) (hpair τ a b h1 h2)
  obtain ⟨F, P0, hFd, hP0, hagree, hP0x, hvan, hInAt, hbound⟩ :=
    hH E r X la x hp0 hp0r hx hgapH hpairH hinj
  have hInv : IsInvFn X (fun _ : Frame X.Ψ r => (0 : ℝ)) := fun _ _ _ _ _ _ => rfl
  have hW := IW.metricW_of GlobalTheory.NormFactor.nfacRmul_holds GlobalTheory.NormFactor.nfacLact_holds ortho_holds
    lu_holds X la (fun _ => 0) hInv (fun _ _ => contDiffOn_const) ⟨0, fun _ _ => le_rfl⟩
  have hbb : 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1 := by linarith
  have hpoin := poin_holds r X x hx (GlobalTheory.ClosedDiscontinuity.propDisc_closed r X) la _ _ hW.1 hW.2
    hbb F P0 hFd hInAt hP0 hagree
  have hbdd : X.IsBddSec la (poin X la P0) := hpoin.2.1
  have hSS : poin X la P0 ∈ X.SS la := by
    refine cuspStatement_holds r X la τ0 hp0 hp0r (fun i j h1 h2 => ?_) (fun i0 i1 h1 h2 => ?_) _ hbdd
    · have := hgap τ0 i j h1 h2
      have h3 : ((la τ0 j : ℤ) : ℝ) ≤ la τ0 i := by nlinarith
      exact_mod_cast h3
    · have := hpair τ0 i0 i1 h1 h2
      have h3 : ((la τ0 i0 : ℤ) : ℝ) < la τ0 i1 := by nlinarith
      exact_mod_cast h3
  have hchi1 : X.χ la 1 = 1 := by
    have h1 := X.χ_mul la 1 X.Γ.one_mem 1 X.Γ.one_mem
    rw [one_mul] at h1
    have h2 := IC.chi_ne_zero X la X.Γ.one_mem
    have h3 : X.χ la 1 * (X.χ la 1 - 1) = 0 := by linear_combination -h1
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h h2
    · linear_combination h
  have hPx : poin X la P0 x = 1 := by
    rw [IC.poin_single X la P0 x X.Γ.one_mem hvan, IW.lact_one X, hP0x, hchi1]
    simp
  have hpn : X.pnorm la (poin X la P0) x = 1 := by
    rw [IC.pnorm_orth X la _ hx, hPx, norm_one]
  refine ⟨poin X la P0, hSS, by rw [hPx]; exact one_ne_zero, ?_⟩

  have hA : MeasurableSet (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x) :=
    Metric.isOpen_ball.measurableSet.inter
      ((IW.isOpen_dom X).preimage (IW.cpt_diff X x).continuous).measurableSet
  have hvol : muF X x (Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x) ≤ muF X x0 FF := by
    have h := GlobalTheory.Unfold.lintegral_chart_le_mul_fundSet E r X x0 x FF
      (Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x) 1 (fun _ => 1) hx0 hx hFF hA
      Set.inter_subset_right measurable_const (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (by
        have hsub : {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x,
            ∃ z' ∈ Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x, ∃ b ∈ Bor X.Ψ r,
              lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b} ⊆ {1} := by
          rintro γ ⟨hγ, z, hz, z', hz', b, hb, he⟩
          have h1 : ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) := le_of_lt (by simpa using hz.1)
          have h2 : ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) := le_of_lt (by simpa using hz'.1)
          exact hinj γ hγ z z' h1 h2 b hb he
        have := Set.encard_le_encard hsub
        rw [Set.encard_singleton] at this
        exact_mod_cast this)
    simpa [setLIntegral_one] using h
  have hSb := hS E r X la x x0 FF F P0 hp0 hp0r hx hx0 hFF hinj hFd hP0 hagree
  rw [hpn, one_pow, ENNReal.ofReal_one, one_mul]
  calc ENNReal.ofReal (Real.exp (-((CH + CS + 1) * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))))
        * ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(muF X x0)
      ≤ ENNReal.ofReal (Real.exp (-((CH + CS + 1) * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))))
        * (ENNReal.ofReal (Real.exp (CS * ((X.Ψ.card : ℝ) * r) ^ 8)) *
          (ENNReal.ofReal (Real.exp (CH * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))) * muF X x0 FF)) := by
        gcongr
        exact hSb.trans (mul_le_mul' le_rfl (hbound.trans (mul_le_mul' le_rfl hvol)))
    _ = ENNReal.ofReal (Real.exp (-((CH + CS + 1) * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8)))
          * Real.exp (CS * ((X.Ψ.card : ℝ) * r) ^ 8)
          * Real.exp (CH * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))) * muF X x0 FF := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        ring
    _ ≤ 1 * muF X x0 FF := by
        gcongr
        rw [← Real.exp_add, ← Real.exp_add, ENNReal.ofReal_le_one, Real.exp_le_one_iff]
        nlinarith
    _ = muF X x0 FF := one_mul _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationFactorPairingIsoPullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam.FactorAdj

open AdjComp

def chartPullTwo {X Y Y' Y'' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ' : K → (Y'' ⟶ X)) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (h : Y'' ⟶ Y') (n : Y' ⟶ Y) (hc : ∀ k, φ' k = (h ≫ n) ≫ φ k) :
    ChartPull (LB.LinComb L φ' ε) ((LB.LinComb L φ ε).pull n) h :=
  have le : ∀ j : K → L.ι, LB.wchart L φ' j ≤ h ⁻¹ᵁ ((LB.LinComb L φ ε).pull n).U (fun _ => j) := fun j _ hy =>
    (mem_pull (L := LB.LinComb L φ ε)).2 ((chartPullSame L φ' φ ε (h ≫ n) hc).le j hy)
  { idx := fun j _ => j
    le := le
    g := fun y j j' hj hj' => ((chartPullSame L φ' φ ε (h ≫ n) hc).g y j j' hj hj').trans
      (gm_pull_g (LB.LinComb L φ ε) n h y (fun _ => j) (fun _ => j') (le j hj) (le j' hj')).symm }

theorem exists_pull_lam {S : Scheme.{0}} {T G G' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {L : LB G.left} {L' : LB G'.left} {n : G2 G ⟶ G2 G'} (w : LB.Iso (abelian₂ G L) ((abelian₂ G' L').pull n.left))
    (hw : w.IsGen) (m : T ⟶ G2 G) (x : Fin 2 → (T ⟶ G)) (x' : Fin 2 → (T ⟶ G')) (hx : ∀ i, x i = m ≫ x2 G i)
    (hx' : ∀ i, x' i = (m ≫ n) ≫ x2 G' i) :
    ∃ w' : LB.Iso (cubeLB G x L) (cubeLB G' x' L'), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ T.left) (z : Z) J' J,
      Good L' z J' → Good L z J → adjVal w' p z J' J = lamVal w (p ≫ m.left) z J' J := by
  let a : ChartPull (cubeLB G x L) (abelian₂ G L) m.left := cubePull L m _ _ hx
  let b : ChartPull (cubeLB G' x' L') ((abelian₂ G' L').pull n.left) m.left :=
    chartPullTwo L' _ _ _ m.left n.left (psum_left_pull (m ≫ n) _ _ hx')
  refine ⟨pullIso a b w, pullIso_isGen a b hw, fun Z p z J' J hJ' hJ => ?_⟩
  have mA := Good.mem hJ (fun I : ULift (Finset (Fin 2)) => (psum G x I.down).left) p
  have mB := Good.mem hJ' (fun I : ULift (Finset (Fin 2)) => (psum G' x' I.down).left) p
  refine ((adjVal_of (pullIso a b w) p z J' J _ _ (fun _ => rfl) (fun _ => rfl)).trans
    (gm_pullIso a b w p z (_, _) ⟨mB, mA⟩)).trans ?_
  have e₁ : (fun I : ULift (Finset (Fin 2)) => J (p ≫ (psum G x I.down).left)) =
      fun I => J ((p ≫ m.left) ≫ (psum G (x2 G) I.down).left) := funext fun I => by
    rw [psum_left_pull m _ _ hx I, Category.assoc]
  have e₂ : (fun I : ULift (Finset (Fin 2)) => J' (p ≫ (psum G' x' I.down).left)) =
      fun I => J' ((p ≫ m.left) ≫ n.left ≫ (psum G' (x2 G') I.down).left) := funext fun I => by
    rw [psum_left_pull (m ≫ n) _ _ hx' I, Over.comp_left, Category.assoc, Category.assoc]
  rw [e₁, e₂]
  rfl

theorem exists_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (F : Factor D.toPre D'.toPre), ∃ w : LB.Iso (cubeLB (pol D).B ![fst (pol D').B (pol D).B ≫ F.pr, snd (pol D').B (pol D).B] (pol D).M.L) (cubeLB (pol D').B ![fst (pol D').B (pol D).B ≫ F.o.onB.act F.e, snd (pol D').B (pol D).B ≫ F.inc ≫ F.o.onB.act F.f] (pol D').M.L), w.IsGen ∧ ∀ y y' z J₁ J₂, Good (pol D').M.L z J₁ → Good (pol D).M.L z J₂ → val ((pol D).tau (F.xp y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ (pol D').c y) (toUnit (TK R) ≫ (pol D).c y')).left z J₁ J₂ * val ((pol D').tau ((DistribSMul.toAddMonoidHom D'.toPre.X F.e) y) (((DistribSMul.toAddMonoidHom D'.toPre.X F.f).comp F.xi) y')) (𝟙 _) z J₁ := by
  intro R _ _ I D D' F
  let m : (pol D').B ⊗ (pol D).B ⟶ G2 (pol D).B := lift (fst _ _ ≫ F.pr) (snd _ _)
  let n : G2 (pol D).B ⟶ G2 (pol D').B := lift (fst _ _ ≫ F.inc) (snd _ _ ≫ F.inc ≫ F.o.onB.act F.f)
  let w₀ : LB.Iso (abelian₂ (pol D).B (pol D).M.L) ((abelian₂ (pol D').B (pol D').M.L).pull n.left) := F.w
  obtain ⟨w, gw, hw⟩ := exists_pull_lam w₀ F.w_gen m ![fst (pol D').B (pol D).B ≫ F.pr, snd (pol D').B (pol D).B]
    ![fst (pol D').B (pol D).B ≫ F.o.onB.act F.e, snd (pol D').B (pol D).B ≫ F.inc ≫ F.o.onB.act F.f]
    (fun i => by
      fin_cases i
      · exact (lift_fst _ _).symm
      · exact (lift_snd _ _).symm)
    (fun i => by
      fin_cases i
      · refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg (m ≫ ·) (lift_fst _ _)).trans ?_))
        refine (lift_fst_assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_)
        exact congrArg (fst (pol D').B (pol D).B ≫ ·) F.pr_inc
      · refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg (m ≫ ·) (lift_snd _ _)).trans ?_))
        exact lift_snd_assoc _ _ _)
  refine ⟨w, gw, fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  have hP : (lift (toUnit (TK R) ≫ D.toPre.c (F.xp y)) (toUnit (TK R) ≫ D.toPre.c y')).left =
      (lift (toUnit (TK R) ≫ (pol D').c y) (toUnit (TK R) ≫ (pol D).c y')).left ≫ m.left := by
    refine congrArg (fun q : TK R ⟶ G2 (pol D).B => q.left) (Eq.symm ((comp_lift _ _ _).trans ?_))
    refine congrArg₂ lift ((lift_fst_assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_)) (lift_snd _ _)
    exact congrArg (toUnit (TK R) ≫ ·) (c_xp F y).symm
  have e := F.tau (F.xp y) y' z J₁ J₂ hJ₁ hJ₂
  rw [F.xi_xp, hP] at e
  refine ((GlobalTheory.PolDeg.Wit.exists_tau D.toPre _ _).choose_spec.2 _ _ z J₂ hJ₂).trans (e.trans ?_)
  exact congrArg₂ (· * ·) (hw _ _ z J₁ J₂ hJ₁ hJ₂).symm
    ((GlobalTheory.PolDeg.Wit.exists_tau D'.toPre (F.e • y) (F.f • F.xi y')).choose_spec.2 _ _ z J₁ hJ₁).symm

end GlobalTheory.MumFam.FactorAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfEqualisedProperCoverNormal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MorDescent

theorem restrict_isPullback {R : Type} [CommRing R] {S Y Z Y' : Scheme.{0}} {π : S ⟶ Sp R} {y : Y ⟶ Sp R}
    {p : Z ⟶ Y} {q : Z ⟶ S} (hpb : IsPullback p q y π) (f : Y' ⟶ Y) :
    IsPullback (pullback.snd p f) (pullback.fst p f ≫ q) (f ≫ y) π :=
  IsPullback.paste_vert (IsPullback.of_hasPullback p f).flip hpb

theorem uniq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ (W : Scheme.{0}) (g₁ g₂ : Y ⟶ W), p ≫ g₁ = p ≫ g₂ → g₁ = g₂ := by
  intro R _ _ _ _ S Y Z π y p q hprop hsurj hint hflat hpb W g₁ g₂ he
  have hpS : Surjective p := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hsurj
  have heqz := _root_.GlobalTheory.descend_of_equalised_fibreSquare R S Y Z π y p q hprop hsurj hint hflat hpb
  have hbase : g₁.base = g₂.base := by
    ext x
    obtain ⟨z, rfl⟩ := p.surjective x
    have := congrArg (fun k : Z ⟶ W => k z) he
    simpa only [Scheme.Hom.comp_apply] using this
  refine Scheme.Hom.ext hbase fun U => ?_
  have : Mono (p.app (g₂ ⁻¹ᵁ U)) := ConcreteCategory.mono_of_injective _ (heqz _).1
  rw [← cancel_mono (p.app (g₂ ⁻¹ᵁ U)), ← Scheme.Hom.comp_app, Scheme.Hom.congr_app he.symm,
    Category.assoc, Scheme.Hom.naturality, ← Category.assoc, ← Scheme.Hom.comp_app]
  rfl

theorem exAff : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ (W : Scheme.{0}) [IsAffine W] (h : Z ⟶ W), pullback.fst p p ≫ h = pullback.snd p p ≫ h → ∃ h₀ : Y ⟶ W, p ≫ h₀ = h := by
  intro R _ _ _ _ S Y Z π y p q hprop hsurj hint hflat hpb W _ h hh
  obtain ⟨hinj, hdesc⟩ := _root_.GlobalTheory.descend_of_equalised_fibreSquare R S Y Z π y p q hprop hsurj hint hflat hpb ⊤
  have hmem : ∀ x : Γ(W, ⊤), h.appTop x ∈ (p.app ⊤).hom.range := by
    intro x
    refine hdesc (h.appTop x) fun e => ?_
    have := congrArg (fun k : pullback p p ⟶ W => k.appTop.hom x) hh
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this
    refine this.trans ?_
    change _ = (CommRingCat.Hom.hom ((pullback p p).presheaf.map (𝟙 (Opposite.op (⊤ : (pullback p p).Opens)))))
      ((pullback.snd p p).appTop.hom (h.appTop.hom x))
    rw [CategoryTheory.Functor.map_id]
    rfl
  let φ : Γ(W, ⊤) →+* Γ(Y, ⊤) :=
    (RingEquiv.ofBijective (p.app ⊤).hom.rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), (p.app ⊤).hom.rangeRestrict_surjective⟩).symm.toRingHom.comp
      (h.appTop.hom.codRestrict _ hmem)
  have hφ : CommRingCat.ofHom φ ≫ p.appTop = h.appTop := by
    ext x
    exact congrArg Subtype.val ((RingEquiv.ofBijective (p.app ⊤).hom.rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), (p.app ⊤).hom.rangeRestrict_surjective⟩).apply_symm_apply
      (h.appTop.hom.codRestrict _ hmem x))
  refine ⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ W.isoSpec.inv, ?_⟩
  have h1 : h = Z.toSpecΓ ≫ Spec.map h.appTop ≫ W.isoSpec.inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]
  rw [h1, ← Category.assoc p, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp_assoc, hφ]

theorem descend : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z W : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ h : Z ⟶ W, pullback.fst p p ≫ h = pullback.snd p p ≫ h → ∃! h₀ : Y ⟶ W, p ≫ h₀ = h := by
  intro R _ _ _ _ S Y Z W π y p q hprop hsurj hint hflat hpb h hh
  have hpS : Surjective p := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hsurj
  have hpC : UniversallyClosed p := MorphismProperty.of_isPullback (P := @UniversallyClosed) hpb.flip inferInstance
  have hfib : Function.FactorsThrough h.base.hom p.base.hom := by
    intro a b hab
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := p) a b hab
    have := congrArg (fun k : pullback p p ⟶ W => k z) hh
    simp only [Scheme.Hom.comp_apply, hz1, hz2] at this
    exact this
  have hq : Topology.IsQuotientMap p.base.hom :=
    IsClosedMap.isQuotientMap p.isClosedMap p.base.hom.continuous p.surjective
  let b : Y.carrier ⟶ W.carrier := TopCat.ofHom (hq.lift h.base.hom hfib)
  have hb : ∀ z, b (p z) = h z := fun z => congrArg (fun k : C(Z, W) => k z) (hq.lift_comp h.base.hom hfib)
  let V : W.affineOpens → Y.Opens := fun i => TopologicalSpace.Opens.comap b.hom i.1
  have hV : TopologicalSpace.IsOpenCover V := W.isBasis_affineOpens.isOpenCover.comap b.hom
  let 𝒰 := Y.openCoverOfIsOpenCover V hV
  have hloc : ∀ i, ∃ u : (V i).toScheme ⟶ W, pullback.snd p (V i).ι ≫ u = pullback.fst p (V i).ι ≫ h := by
    intro i
    have hr : Set.range (pullback.fst p (V i).ι ≫ h) ⊆ Set.range i.1.ι := by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, ← hb, ← Scheme.Hom.comp_apply, pullback.condition,
        Scheme.Hom.comp_apply]
      exact ((pullback.snd p (V i).ι) w).2
    let hi := IsOpenImmersion.lift i.1.ι _ hr
    have : IsAffine i.1.toScheme := i.2
    have heq : pullback.fst (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ≫ hi =
        pullback.snd (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ≫ hi := by
      rw [← cancel_mono i.1.ι]
      simp only [Category.assoc, hi, IsOpenImmersion.lift_fac]
      let m : pullback (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ⟶ pullback p p :=
        pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst _ _)
          (by simp only [Category.assoc, pullback.condition, pullback.condition_assoc])
      have e1 : pullback.fst (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ≫ pullback.fst p (V i).ι =
          m ≫ pullback.fst p p := (pullback.lift_fst _ _ _).symm
      have e2 : pullback.snd (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ≫ pullback.fst p (V i).ι =
          m ≫ pullback.snd p p := (pullback.lift_snd _ _ _).symm
      rw [reassoc_of% e1, reassoc_of% e2, hh]
    obtain ⟨u, hu⟩ := exAff R S (V i).toScheme (pullback p (V i).ι) π ((V i).ι ≫ y) (pullback.snd p (V i).ι)
      (pullback.fst p (V i).ι ≫ q) hprop hsurj hint inferInstance (restrict_isPullback hpb _) i.1.toScheme hi heq
    exact ⟨u ≫ i.1.ι, by rw [← Category.assoc, hu, IsOpenImmersion.lift_fac]⟩
  choose u hu using hloc
  have hc : ∀ i j, pullback.fst (V i).ι (V j).ι ≫ u i = pullback.snd (V i).ι (V j).ι ≫ u j := by
    intro i j
    let f := pullback.fst (V i).ι (V j).ι ≫ (V i).ι
    apply uniq R S _ (pullback p f) π (f ≫ y) (pullback.snd p f) (pullback.fst p f ≫ q) hprop hsurj hint
      inferInstance (restrict_isPullback hpb f) W
    let mi : pullback p f ⟶ pullback p (V i).ι := pullback.lift (pullback.fst p f)
      (pullback.snd p f ≫ pullback.fst _ _) (by rw [pullback.condition, Category.assoc])
    let mj : pullback p f ⟶ pullback p (V j).ι := pullback.lift (pullback.fst p f)
      (pullback.snd p f ≫ pullback.snd _ _) (by
        rw [pullback.condition]
        show pullback.snd p f ≫ pullback.fst (V i).ι (V j).ι ≫ (V i).ι = _
        rw [pullback.condition, Category.assoc])
    have ei : pullback.snd p f ≫ pullback.fst (V i).ι (V j).ι = mi ≫ pullback.snd p (V i).ι :=
      (pullback.lift_snd _ _ _).symm
    have ej : pullback.snd p f ≫ pullback.snd (V i).ι (V j).ι = mj ≫ pullback.snd p (V j).ι :=
      (pullback.lift_snd _ _ _).symm
    rw [reassoc_of% ei, reassoc_of% ej, hu, hu, pullback.lift_fst_assoc, pullback.lift_fst_assoc]
  have hglue : p ≫ 𝒰.glueMorphisms u hc = h := by
    refine Scheme.Cover.hom_ext (𝒰.pullback₁ p) _ _ fun i => ?_
    change pullback.fst p (V i).ι ≫ _ = pullback.fst p (V i).ι ≫ _
    rw [← Category.assoc, pullback.condition, Category.assoc]
    change pullback.snd p (V i).ι ≫ 𝒰.f i ≫ _ = _
    exact (congrArg (pullback.snd p (V i).ι ≫ ·) (𝒰.ι_glueMorphisms u hc i)).trans (hu i)
  refine ⟨𝒰.glueMorphisms u hc, hglue, fun g hg => ?_⟩
  exact uniq R S Y Z π y p q hprop hsurj hint hflat hpb W g _ (hg.trans hglue.symm)

end GlobalTheory.MorDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalFirstNeighbourhoodRetractionForms
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers TrivSqZeroExt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm
open GlobalTheory.CrysConn

namespace GlobalTheory.PDForm.Nbhd

open GlobalTheory.SmoothLift

attribute [local instance] opK isCentral_K isTower_K


set_option maxHeartbeats 20000000 in
theorem exists_retraction : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R), ∃ (S : Thick κ t ⥤ Thick κ t) (u v : 𝟭 _ ⟶ S)
    (r1 : ∀ T, (KK κ t).M1.obj (S.obj T) →+ (KK κ t).M1.obj T)
    (r2 : ∀ T, (KK κ t).M2.obj (S.obj T) →+ (KK κ t).M2.obj T)
    (r3 : ∀ T, (KK κ t).M3.obj (S.obj T) →+ (KK κ t).M3.obj T),
    ((∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r1 T' ((KK κ t).M1.map (S.map φ) x) = (KK κ t).M1.map φ (r1 T x)) ∧
      (∀ T x, r1 T ((KK κ t).M1.map (u.app T) x) = 0) ∧ (∀ T x, r1 T ((KK κ t).M1.map (v.app T) x) = x)) ∧
    ((∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r2 T' ((KK κ t).M2.map (S.map φ) x) = (KK κ t).M2.map φ (r2 T x)) ∧
      (∀ T x, r2 T ((KK κ t).M2.map (u.app T) x) = 0) ∧ (∀ T x, r2 T ((KK κ t).M2.map (v.app T) x) = x)) ∧
    (∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r3 T' ((KK κ t).M3.map (S.map φ) x) = (KK κ t).M3.map φ (r3 T x)) ∧
      (∀ T x, r3 T ((KK κ t).M3.map (u.app T) x) = 0) ∧ (∀ T x, r3 T ((KK κ t).M3.map (v.app T) x) = x) := by
  intro R _ I κ X t
  have hr : ∀ T : Thick κ t, ∀ x ∈ rel R T.δ, ∀ y, x * y ∈ rel R T.δ := fun T ↦ (_root_.GlobalTheory.PDForm.rel_two_sided_and_bot.1 R T.B T.J T.δ).1
  have H := fun T : Thick κ t ↦ GlobalTheory.T.exists_formsMap_of_dividedPowerDerivation R T.B T.J T.δ (ER T) (nb T).J (nb T).δ (fstA T) (sndA T)
    (sndA_mul T) (sndA_algebraMap T) (fun n a ha ↦ sndA_dpow T n a ha)
  choose ρ ha hm h0 h1 hrel hone hdeg using H
  have natK : ∀ (j : ℕ) (T T' : Thick κ t) (φ : T ⟶ T') (x : K R (nb T).δ j),
      rK (nb T').δ (ha T') (hrel T') (hdeg T') j (km (SemiHom.of_algHom (nbAlg φ)) (nbF.map φ).dp j x) =
        km (SemiHom.of_algHom φ.φ) φ.dp j (rK (nb T).δ (ha T) (hrel T) (hdeg T) j x) := by
    intro j T T' φ x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx : (x : DR R (ER T)) ∈ ⋀[ER T]^j Ω[ER T⁄R] := x.2
    have hd := hdeg T j _ hx
    let y := hd.choose
    have hy : y ∈ ⋀[T.B]^j Ω[T.B⁄R] := hd.choose_spec.1
    have hρy : ρ T x - y ∈ rel R T.δ := hd.choose_spec.2
    rw [rK_spec (nb T).δ (ha T) (hrel T) (hdeg T) (y := ⟨y, hy⟩) hρy, km_mk]
    have e := add_mem (natAgree hr φ (ρ T) (ρ T') (ha T) (hm T) (h0 T) (h1 T) (ha T') (hm T') (h0 T') (h1 T') x)
      (mDR_mem_rel (SemiHom.of_algHom φ.φ) φ.dp hρy)
    rw [map_sub, sub_add_sub_cancel] at e
    exact rK_spec (nb T').δ (ha T') (hrel T') (hdeg T') (x := (SemiHom.of_algHom (nbAlg φ)).mOm j x)
      (y := (SemiHom.of_algHom φ.φ).mOm j ⟨y, hy⟩) e
  have uK : ∀ (j : ℕ), j ≠ 0 → ∀ (T : Thick κ t) (x : K R T.δ j),
      rK (nb T).δ (ha T) (hrel T) (hdeg T) j (km (SemiHom.of_algHom (inlMap T).φ) (inlMap T).dp j x) = 0 := by
    intro j hj T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e := uAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) x
    rw [algebraMapInv_eq_zero hj x.2, map_zero] at e
    have e' : ρ T ((SemiHom.of_algHom (inlMap T).φ).mDR x) - ((0 : Om R T.B j) : DR R T.B) ∈ rel R T.δ := by
      rw [ZeroMemClass.coe_zero]; exact e
    exact (rK_spec (nb T).δ (ha T) (hrel T) (hdeg T) (x := (SemiHom.of_algHom (inlMap T).φ).mOm j x) e').trans
      (Submodule.Quotient.mk_zero _)
  have vK : ∀ (j : ℕ) (T : Thick κ t) (x : K R T.δ j),
      rK (nb T).δ (ha T) (hrel T) (hdeg T) j (km (SemiHom.of_algHom (difMap T).φ) (difMap T).dp j x) = x := by
    intro j T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact rK_spec (nb T).δ (ha T) (hrel T) (hdeg T) (x := (SemiHom.of_algHom (difMap T).φ).mOm j x) (y := x)
      (vAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) x)
  refine ⟨nbF, uN, vN, fun T ↦ r1 (nb T).δ (ha T) (hrel T) (hone T), fun T ↦ rK (nb T).δ (ha T) (hrel T) (hdeg T) 2,
    fun T ↦ rK (nb T).δ (ha T) (hrel T) (hdeg T) 3, ⟨?_, ?_, ?_⟩, ⟨fun T T' φ x ↦ natK 2 T T' φ x,
      fun T x ↦ uK 2 (by norm_num) T x, fun T x ↦ vK 2 T x⟩, fun T T' φ x ↦ natK 3 T T' φ x,
      fun T x ↦ uK 3 (by norm_num) T x, fun T x ↦ vK 3 T x⟩
  · intro T T' φ x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hd := hone T x
    let ω := hd.choose
    have hω : ρ T (ι1 x) - ι1 ω ∈ rel R T.δ := hd.choose_spec
    have e := add_mem (natAgree hr φ (ρ T) (ρ T') (ha T) (hm T) (h0 T) (h1 T) (ha T') (hm T') (h0 T') (h1 T') (ι1 x))
      (mDR_mem_rel (SemiHom.of_algHom φ.φ) φ.dp hω)
    rw [map_sub, sub_add_sub_cancel, SemiHom.mDR_ι, SemiHom.mDR_ι] at e
    have l := divPowerCompatOneForm_retraction_spec (nb T).δ (ha T) (hrel T) (hone T) (x := x) hω
    exact (divPowerCompatOneForm_retraction_spec (nb T').δ (ha T') (hrel T') (hone T') (x := (SemiHom.of_algHom (nbAlg φ)).m1 x)
      (ω := (SemiHom.of_algHom φ.φ).m1 ω) e).trans (congrArg (km1 (SemiHom.of_algHom φ.φ) φ.dp) l).symm
  · intro T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e := uAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) (ι1 x)
    have z : ExteriorAlgebra.algebraMapInv (ι1 x) = 0 := by simp [ExteriorAlgebra.algebraMapInv]
    rw [z, map_zero, SemiHom.mDR_ι] at e
    have e' : ρ T (ι1 ((SemiHom.of_algHom (inlMap T).φ).m1 x)) - ι1 (0 : Ω[T.B⁄R]) ∈ rel R T.δ := by
      rw [map_zero]; exact e
    exact (divPowerCompatOneForm_retraction_spec (nb T).δ (ha T) (hrel T) (hone T) (x := (SemiHom.of_algHom (inlMap T).φ).m1 x) e').trans
      (Submodule.Quotient.mk_zero _)
  · intro T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e := vAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) (ι1 x)
    rw [SemiHom.mDR_ι] at e
    exact divPowerCompatOneForm_retraction_spec (nb T).δ (ha T) (hrel T) (hone T) (x := (SemiHom.of_algHom (difMap T).φ).m1 x) (ω := x) e

end GlobalTheory.PDForm.Nbhd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalStabiliserMulMemBigCellInertStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diagonalStabiliser_mul_mem_bigCell_inert : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ p * g ∈ GlobalTheory.DblVac.KD σ W v ∧ GlobalTheory.DblVac.BigCell W v (p * g) := by
  first | exact @GlobalTheory.DblVac.exists_diag_mul_bigCell | exact GlobalTheory.DblVac.exists_diag_mul_bigCell | (intros; apply GlobalTheory.DblVac.exists_diag_mul_bigCell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerMatrixActionThetaCompactificati
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem GlobalTheory.Poinc.Sep.exists_isAct : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), ∃ act, IsAct X₁ act := by
  intro g n F W Z i X₁
  obtain ⟨c, hc, pr, h1, h2, h3⟩ := X₁.sharp
  choose act hact using fun a : Matrix (Fin 8) (Fin 8) ℤ =>
    (h2 X₁.ρ.P.A fun u => (List.ofFn fun v => pr v ^ a u v).prod).exists
  exact ⟨act, c, hc, pr, h1, h2, h3, hact⟩
end

