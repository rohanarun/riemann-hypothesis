module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapOfOfPtIdent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1070
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0977
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0955
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0458
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelElementAtBadPrimesIntegralAndNear
public import Formalism.LocalToGlobal.Columns.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsScalarScale
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.HeightCounting
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SerVec

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {v₀ v₁ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem evW_scale {j : Fin D.R.m} {c : D.what₂.Tau → ℂ}
    (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) (x : S.WL ((j : ℕ) + 1)) :
    evW YS v₁ j x = (∏ τ, c τ) • evW YS v₀ j x := by
  change (Rl.HW j (sg0 D A3.A)).e _ (v₁ j _) = (∏ τ, c τ) • (Rl.HW j (sg0 D A3.A)).e _ (v₀ j _)
  rw [show v₁ j (sg0 D A3.A) = fun τ => c τ • v₀ j (sg0 D A3.A) τ from funext h]
  exact MultilinearMap.map_smul_univ _ _ _

theorem realRd_scale {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) {j : Fin D.R.m} (b : Bool) {C : ℂ} (hC : C ≠ 0)
    (h : ∀ x, evW YS v₁ j x = C • evW YS v₀ j x) (ν : ℂ) :
    realRd YS v₁ hρ i j b (C * ν) = realRd YS v₀ hρ i j b ν := by
  have key : ∀ x, evK YS v₁ hρ i j b x = C • evK YS v₀ hρ i j b x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, smul_zero]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]
    | tmul a f => rw [evK_tmul, evK_tmul, h, smul_comm]
  refine LinearMap.ext fun f => ?_
  change (C * ν)⁻¹ • evK YS v₁ hρ i j b _ = ν⁻¹ • evK YS v₀ hρ i j b _
  refine (congrArg _ (key _)).trans ?_
  rw [smul_smul, mul_inv, mul_right_comm, inv_mul_cancel₀ hC, one_mul]

theorem isScale_scale {j : Fin D.R.m} {c : D.what₂.Tau → ℂ}
    (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) (B : GlobalTheory.ExportSeries.Base (Vc D j) (Wc D j)) {s : ℂ}
    (hs : IsScale Rl v₀ B s) : IsScale Rl v₁ B ((∏ τ, c τ) * s) := by
  obtain ⟨gramR, c0R, c0L, ht, u, hu, hF⟩ := hs
  refine ⟨gramR, c0R, c0L, ht, fun τ => c τ • u τ, fun τ => ?_, fun F => ?_⟩
  · rw [h, ← hu]; rfl
  · rw [MultilinearMap.map_smul_univ, map_smul, mul_smul, ← hF]
    exact map_smul (GlobalTheory.ExportSeries.harmFn (Wc D j).rank B.w B.F.BS) _ _

theorem isNorm_scale {j : Fin D.R.m} {c : D.what₂.Tau → ℂ} (hc : ∀ τ, c τ ≠ 0)
    (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) (B : GlobalTheory.ExportSeries.Base (Vc D j) (Wc D j)) {ν : ℂ}
    (hν : IsNorm Rl v₀ B ν) : IsNorm Rl v₁ B ((∏ τ, c τ) * ν) := by
  obtain ⟨h0, s, hs, n, hn, he⟩ := hν
  refine ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun τ _ => hc τ) h0, _, isScale_scale h B hs, n, hn, ?_⟩
  rw [mul_pow, he, ← mul_pow, mul_left_comm]

theorem scale_symm {j : Fin D.R.m} {c : D.what₂.Tau → ℂ} (hc : ∀ τ, c τ ≠ 0)
    (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) (τ : D.what₂.Tau) :
    v₀ j (sg0 D A3.A) τ = (c τ)⁻¹ • v₁ j (sg0 D A3.A) τ := by
  rw [h, smul_smul, inv_mul_cancel₀ (hc τ), one_smul]

theorem isScalar_scale {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) {j : Fin D.R.m} (b : Bool) {c : D.what₂.Tau → ℂ}
    (hc : ∀ τ, c τ ≠ 0) (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) {ν : ℂ}
    (hν : IsScalar YS v₀ hρ i j b ν) : IsScalar YS v₁ hρ i j b ((∏ τ, c τ) * ν) := by
  have hC : (∏ τ, c τ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => hc τ
  have hc' : ∀ τ, (c τ)⁻¹ ≠ 0 := fun τ => inv_ne_zero (hc τ)
  have h' := scale_symm hc h
  refine ⟨mul_ne_zero hC hν.ne, fun ⟨ν', h1⟩ => isNorm_scale hc h _ (hν.norm ⟨_, isNorm_scale hc' h' _ h1⟩), fun ⟨ν', h1, h2⟩ => ?_⟩
  rw [realRd_scale YS hρ i b hC (evW_scale YS h)]
  refine hν.rat ⟨_, isNorm_scale hc' h' _ h1, ?_⟩
  rw [realRd_scale YS hρ i b (Finset.prod_ne_zero_iff.2 fun τ _ => hc' τ) (evW_scale YS h')]
  exact h2

theorem exists_cell {ρ : Setup D.ntw} {hρ : ρ.Good} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} {rd rd' : Rd ρ D.nexp i j b}
    (e : rd' = rd) (t : CellTie hρ D.nexp rd) : ∃ t' : CellTie hρ D.nexp rd', t'.rdV = t.rdV := by
  subst e
  exact ⟨t, rfl⟩

theorem serAt_scale {c : Fin D.R.m → D.what₂.Tau → ℂ} (hc : ∀ j τ, c j τ ≠ 0)
    (h : ∀ j τ, v₁ j (sg0 D A3.A) τ = c j τ • v₀ j (sg0 D A3.A) τ)
    (hv : ∀ j, FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₁ j _)) {Xe : Formalism.L2.NExpTied D}
    {PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV} {cf : Formalism.L2.Host.CharFrame D}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} (Z : SerAt YS v₀ Xe PV cf Pq) :
    Nonempty (SerAt YS v₁ Xe PV cf Pq) := by
  have e : ∀ i j b, realRd YS v₁ Z.ex.good i j b ((∏ τ, c j τ) * Z.ex.ν i j b) = realRd YS v₀ Z.ex.good i j b (Z.ex.ν i j b) :=
    fun i j b => realRd_scale YS _ i b (Finset.prod_ne_zero_iff.2 fun τ _ => hc j τ) (evW_scale YS (h j)) _
  choose t ht using fun i j b => exists_cell (e i j b) (Z.ex.tie i j b)
  refine ⟨{ ex :=
              { ρ := Z.ex.ρ
                good := Z.ex.good
                pin := Z.ex.pin
                vec := hv
                ν := fun i j b => (∏ τ, c j τ) * Z.ex.ν i j b
                scalar := fun i j b => isScalar_scale YS _ i b (hc j) (h j) (Z.ex.scalar i j b)
                tie := t
                hecke := fun i j b => by rw [e]; exact Z.ex.hecke i j b
                univ := Z.ex.univ }
            bad := Z.bad
            ch := Z.ch
            join := fun i j b k Q ψ hA hT => ?_
            sup := Z.sup
            off := Z.off
            lam := Z.lam
            lam_ok := Z.lam_ok
            lam_teich := Z.lam_teich
            lam_C := Z.lam_C
            lam_q := Z.lam_q
            lam_tie := Z.lam_tie }⟩
  obtain ⟨ω, h1, h2⟩ := Z.join i j b k Q ψ hA hT
  refine ⟨ω, h1, fun f g => ?_⟩
  rw [← h2 f g, ← ht i j b]

theorem serAt_vec : ∀ {D : D7} (X : RealSide D) (g₀ g₁ : GlobalTheory.RealGeo.GeoHalf X.core X.R.toRealDat fun _ => 1) {S : NX.RatDat D.ntw} (YS : NX.NExpRealS X.R X.cG S) (Xe : Formalism.L2.NExpTied D) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV) (cf : Formalism.L2.Host.CharFrame D) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host), SerAt YS g₀.v₀ Xe PV cf Pq → Nonempty (SerAt YS g₁.v₀ Xe PV cf Pq) := by
  intro D X g₀ g₁ S YS Xe PV cf Pq Z
  have hL : ∀ j, FWT.ExtLine (X.R.MW j (sg0 D X.A3.A)) := fun j =>
    GlobalTheory.HolLowOnce.extLine_of_holShape D _ _ _
      (GlobalTheory.DefLift.holShape_fixed D X.Γ X.Pl0 X.T X.A3.A _ X.R.toRealDat X.char.models.order j).1
  choose c hc h using fun j τ => hL j _ _ (g₀.fw.hv₀ j _).1 (g₁.fw.hv₀ j _).1 τ
  exact serAt_scale YS (fun j τ h0 => by simpa [h0] using hc j τ) h (fun j => g₁.fw.hv₀ j _) Z

end GlobalTheory.SerVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsCompatibleOtherLaterStagesOfSameChoices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

theorem frame_eq_of_map_eq {D : D7} {V : HSp D} {n : ℕ} (P Q : principalLevelFrame.RowPsi V n) (h : P.ψ = Q.ψ) : P = Q := by
  cases P; cases Q; cases h; rfl


set_option maxHeartbeats 8000000 in
theorem lfT_of_same : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → ∀ (Φ : Type) (rep : Φ → _) (Mt : C.Tup → ℕ → Hs) (l : LfD B.O (B.embLL.comp B.OtoLL) C.Tup Φ Mt) jL (t : LfT y F rep (Mt := Mt) jL l) jL', HEq jL' jL → ∃ t' : @LfT b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by with_unfolding_all exact (rep :))) Mt jL' l, letI := alg b iK; HEq t'.eW t.eW ∧ HEq t'.jMt t.jMt := by
  intro B C a b G _ _ Pl0 T Ks _ _ iK A R F y y' hs Φ rep Mt l jL t jL' hj
  obtain ⟨tup', tupT', _, _, _, _, _, ⟨ψY, _, _, _⟩, PW', ιW', _, _, _, _⟩ := y'
  obtain ⟨h1, h2, h3, h4⟩ := hs
  obtain rfl : tup' = (by with_unfolding_all exact (y.tup :)) := eq_of_heq h1
  obtain rfl : tupT' = (by with_unfolding_all exact (y.tupT :)) := eq_of_heq h2
  obtain rfl : ψY = (by with_unfolding_all exact (y.PY.ψ :)) := eq_of_heq h3
  have e4 : (fun i => (PW' i).ψ) = (by with_unfolding_all exact ((fun i => (y.PW i).ψ) :)) := eq_of_heq h4
  obtain rfl : PW' = fun i => rowPsi b (y.PW i) :=
    funext fun i => frame_eq_of_map_eq _ _ ((by with_unfolding_all exact ((congrFun e4 i) :)))
  obtain rfl : jL' = (by with_unfolding_all exact (jL :)) := eq_of_heq hj
  letI := alg b iK
  refine ⟨{
    eW := (by with_unfolding_all exact (t.eW :))
    eW_range := fun i => (by with_unfolding_all exact (((t.eW_range i).trans (by rw [wat_eq b R])) :))
    eW_norm := (by with_unfolding_all exact (t.eW_norm :))
    eW_lat := (by with_unfolding_all exact (t.eW_lat :))
    jMj := (by with_unfolding_all exact (t.jMj :))
    jMj_read := (by with_unfolding_all exact (t.jMj_read :))
    jMj_inj := (by with_unfolding_all exact (t.jMj_inj :))
    jMj_range := fun i => (by with_unfolding_all exact (((t.jMj_range i).trans (congrFun (lift_Wc b F y.tupT y.hm y.hTop y.hinj) i)) :))
    jMj_ip := (by with_unfolding_all exact (t.jMj_ip :))
    jMt := (by with_unfolding_all exact (t.jMt :))
    jMt_inj := (by with_unfolding_all exact (t.jMt_inj :))
    jMt_range := (by with_unfolding_all exact (t.jMt_range :))
    jMt_ip := (by with_unfolding_all exact (t.jMt_ip :))
    theta := fun μ hμ i x h w hw1 he hw2 => by
      have hw1' : ((by with_unfolding_all exact (w :)) : (y.L F).AmbW i) ∈ (toLiftReal R F y.tupT y.hm y.hTop y.hinj).MultW i := by
        rw [lift_MultW b F y.tupT y.hm y.hTop y.hinj]; exact (by with_unfolding_all exact (hw1 :))
      have hw2' : (y.L F).eW i ∘ₗ ((by with_unfolding_all exact (w :)) : (y.L F).AmbW i) ∈ (toLiftReal R F y.tupT y.hm y.hTop y.hinj).Wc i := by
        rw [lift_Wc b F y.tupT y.hm y.hTop y.hinj]; exact (by with_unfolding_all exact (hw2 :))
      exact (by with_unfolding_all exact ((t.theta ((μ)) ((hμ)) ((i)) ((x)) ((h)) ((w)) hw1' ((he)) hw2') : _))
    junk := (by with_unfolding_all exact (t.junk :))
    out := (by with_unfolding_all exact (t.out :))
    isot := fun i π v => by
      unfold Hd.prtW
      rw [isotL_eq a b]
      exact (t.isot i π v)
    disj := fun i π π' hne => by
      unfold Hd.prtW
      rw [isotL_eq a b]
      exact (t.disj i π π' hne)
    read := (by with_unfolding_all exact (t.read :)) }, (by with_unfolding_all exact ((HEq.refl t.eW) :)), (by with_unfolding_all exact ((HEq.refl t.jMt) :))⟩

end GlobalTheory.Mem.R3.Rw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsSpanOfClassSumsSpan
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.LiftSpan

open _root_.Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.OneMapTuples GlobalTheory.OneMapAll GlobalTheory.FieldBC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}




end GlobalTheory.LiftSpan

namespace GlobalTheory.LiftSpan

open _root_.Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.OneMapTuples GlobalTheory.OneMapAll

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


section Guard

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}


set_option maxHeartbeats 1000000 in
theorem lam_geo_mem_span {O : OMDat T.toCore R i Unit fun _ => A.μ0} (hP : O.Pins κ v₀ ι x₀) (hspan : ClassSumsSpan O κ)
    {lam : AutQ (Wc D i) → ℂ} {z : G} {c0 : ℂ} (hid : PtIdent O κ lam z c0) :
    ∀ f ∈ cuspOver O κ, (fun q => lam q * geo O (fun _ => 1) z f q) ∈ Submodule.span ℂ (Set.range (liftQ R i v₀ A.μ0)) := by
  obtain ⟨ζ, -, hζ, h⟩ := hid ()
  intro f hf
  have hf' := hspan hf
  clear hf
  induction hf' using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨hg, x, hx, hgx⟩ := hg
    obtain ⟨y, hy⟩ := lift_of_plc hP hx
    have e : (fun q => lam q * geo O (fun _ => 1) z g q) = (c0 / ζ) • liftQ R i v₀ A.μ0 y := by
      funext q
      rw [Pi.smul_apply, smul_eq_mul, ← hy, div_mul_eq_mul_div, eq_div_iff (ne_zero_of_root hζ),
        h x hx g ((mem_cusp _ _ _ _ _ _).1 hg).1 hgx q]
      show lam q * (1 * rdQ O z g q) * _ = _
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  | zero =>
    have e : (fun q => lam q * geo O (fun _ => 1) z 0 q) = 0 := funext fun q => by
      have := geo_smul O (fun _ => 1) z 0 0 q
      rw [zero_smul] at this
      rw [this]
      simp
    rw [e]
    exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    convert Submodule.add_mem _ hf hg using 1
    funext q
    rw [geo_add, mul_add, Pi.add_apply]
  | smul a f _ hf =>
    convert Submodule.smul_mem _ (a : ℂ) hf using 1
    funext q
    rw [geo_smul, mul_left_comm, Pi.smul_apply, smul_eq_mul]


set_option maxHeartbeats 1000000 in
theorem liftsSpan_of_ptIdent {O : OMDat T.toCore R i Unit fun _ => A.μ0} (hP : O.Pins κ v₀ ι x₀) (hspan : ClassSumsSpan O κ)
    {O' : OMDat T.toCore R i T0 id} (hP' : O'.Pins κ v₀ ι x₀) (hlev : O'.lev = O.lev) (hex : ClsEx O' κ)
    {lam : AutQ (Wc D i) → ℂ} {z : G} {c0 c1 : ℂ} (hc1 : c1 ≠ 0) (hid : PtIdent O κ lam z c0) (hid' : PtIdent O' κ lam z c1) :
    LiftsSpan R i v₀ := by
  intro t y
  have e2 : O'.lev2 = O.lev2 := by funext g; simp only [OMDat.lev2, hlev]
  obtain ⟨x, hx, e⟩ := plc_of_lift hP' t y
  obtain ⟨f, hf, hfx, -⟩ := hex t x hx
  obtain ⟨s, -, -, h⟩ := hid' t
  have hf' := ((mem_cusp _ _ _ _ _ _).1 hf).1
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O'.hle).2 _ (T.U ((i : ℕ) + 1)) _ _ f hf
  have hs : ∀ k, fs k ∈ sec _ T.Q.c (wtA κ) (Vc D i).rank := fun k => ((mem_cusp _ _ _ _ _ _).1 (hfs k)).1
  have key : liftQ R i v₀ t y = ∑ k, (s / c1 * (as k : ℂ)) •
      fun q => lam q * geo O (fun _ => 1) z (GlobalTheory.FieldBC.rulBC O.hle (fs k)) q := by
    funext q
    have h1 : c1 * O'.thAd t x q = s * lam q * rdQ O' z f q := h x hx f hf' hfx q
    have h2 : 1 * rdQ O' z f q = _ := geo_of_isBC O' hP'.act.1 (fun _ => 1) z hf' hs hBC q
    rw [phi_eq O' O (fun _ _ => 1), e2, one_mul] at h2
    have h3 : ∀ k, geo O (fun _ => 1) z (GlobalTheory.FieldBC.rulBC O.hle (fs k)) q =
        O.phi (fun _ => 1) (actLev T.Q.c O.lev2 z (fs k)) q.out := fun k => by
      have hs1 : ∀ k', ![fs k] k' ∈ sec _ T.Q.c (wtA κ) (Vc D i).rank := fun k' => by
        rw [Subsingleton.elim k' 0]; exact hs k
      rw [geo_of_isBC O hP.act.1 _ z (GlobalTheory.FieldBCModel.rulBC_mem_sec O.hle (hs k)) hs1
        (GlobalTheory.FieldBCModel.isBC_rulBC O.hle (hs k).1)]
      simp only [Fin.sum_univ_one, Matrix.cons_val_zero, OneMemClass.coe_one, one_mul]
    refine mul_left_cancel₀ hc1 ?_
    rw [show liftQ R i v₀ t y = O'.thAd t x from e.symm, h1, h2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  rw [key]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (lam_geo_mem_span hP hspan hid _
    (((GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ _ _ O.hle _ (T.U ((i : ℕ) + 1)) _ _ _ (hs k)).2).2 (hfs k)))

end Guard


end GlobalTheory.LiftSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultREqReL
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Top.Bl

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 4000000 in
theorem multR_eq_reL {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
    {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
    (R : RealDat a.D A Ks) (F : Face a.D A) :
    MultR R F = (by with_unfolding_all exact ((letI := alg (reL a Z) iK; MultR (real (reL a Z) R) (face (reL a Z) F)) :)) := (congrArg (fun m ↦ m R.θ (R.MY 0) (JR R F) (chiR R F)) (mult_eq (reL a Z) a))


set_option maxHeartbeats 4000000 in
theorem mvSee : MvSee := by
  intro B C a Z G' _ _ Pl0 T A Ks _ _ iK R F X h t hs
  obtain ⟨h1, h2, σ, red, hA, ⟨hr, hB⟩, hC⟩ := hs
  have hB' := cast (congrArg (fun E : Submodule ℂ (MMap (MP R)) => ∀ k ∈ X.B.I.Kset, ∀ T ∈ E, ∀ (v : (MP R).Vec)
    (g : GA a.D (Yc a.D 0)), (T : MMap (MP R)) v (g * kap X h t k) =
      actL (Yc a.D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red k))) ((T : MMap (MP R)) v) g) (multR_eq_reL a Z R F)) hB
  letI := alg (reL a Z) iK
  refine ⟨?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h1 :))
  · exact (by with_unfolding_all exact (h2 :))
  · refine ⟨(by with_unfolding_all exact (σ :)), (by with_unfolding_all exact (red :)), ?_, ⟨?_, ?_⟩, ?_⟩
    · exact (by with_unfolding_all exact (hA :))
    · exact (by with_unfolding_all exact (hr :))
    · exact (by with_unfolding_all exact (hB' :))
    · exact (by with_unfolding_all exact (hC :))

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvEvHolds
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Top.Bl

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 4000000 in
theorem ep_eq_reL {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
    {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
    (R : RealDat a.D A Ks) (F : Face a.D A) :
    EP R F = (by with_unfolding_all exact ((letI := alg (reL a Z) iK; EP (real (reL a Z) R) (face (reL a Z) F)) :)) := (congrFun (eeat_eq (reL a Z) R) (R.levR F true))


set_option maxHeartbeats 4000000 in
theorem mvEv_holds : MvEv := by
  intro B C a Z G' _ _ Pl0 T A Ks _ _ iK R F X h G t c hj
  exact (by with_unfolding_all exact ((cast (congrArg (fun E : Submodule ℂ (MMap (MP R)) =>
    EvalTieT (MP R) R.ν0 R.fd0 E X G (iotaX X h).toMulEquiv t c) (ep_eq_reL a Z R F)) hj) :))

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvRowJ
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Top.Bl

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 4000000 in
theorem mvRowJ : MvRowJ := by
  intro B C a Z G' _ _ Pl0 T A Ks _ _ iK R X h G t eE j hj
  exact (by with_unfolding_all exact (hj :))

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportedUnitaryAdelicIntegralWithInverseStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supported_unitary_adelic_integral_with_inverse : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) {n : ℕ} (u : GL (Fin n) (AfE F E)), u ∈ Formalism.L2.Herm.UstdAf hc n → ∀ (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)), Formalism.L2.Col.IsOver v P → (∀ v', v' ≠ v → bc (prV (E := E) v') u = 1) → ∀ g ∈ Formalism.L2.Col.GLint E n P, (∀ r s, adAt F P ((u : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g.toLinearMap r s)) → ∀ i j, (u : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E ∧ ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E := by
  first | exact @GlobalTheory.Mem.Col2.AdT.IntSplit.int_of_supported | exact GlobalTheory.Mem.Col2.AdT.IntSplit.int_of_supported | (intros; apply GlobalTheory.Mem.Col2.AdT.IntSplit.int_of_supported <;> assumption)
end

