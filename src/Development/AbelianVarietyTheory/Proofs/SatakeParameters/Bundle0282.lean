module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0277
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
public import Formalism.LocalToGlobal.Columns.Bundle0035
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
public import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PNeatB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0159
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaJetIntegralityTypePrimeOfSplitTableBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0175
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.SharpRestriction.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLattices
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0262

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumEquivariantRationalUnitaryStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepDatum_equivariant_rationalUnitary : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m), t.m2 < i → ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG (E := t.X.E) (n := D.R.N (i + 1)) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  first | exact @GlobalTheory.TopRat.xiPt_top_smul | exact GlobalTheory.TopRat.xiPt_top_smul | (intros; apply GlobalTheory.TopRat.xiPt_top_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumFixedCongruentFrameChangeTwistPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepDatum_fixed_congruentFrameChange_twistPrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) {m2 : ℕ}, R.m = m2 + 2 → cst.Ok → ∀ (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  2 * cst.M ≤ cst.D P →
  ∀ (κ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1)))
    (κ' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))),
  κ ∈ GLint X.E (R.N (m2 + 1)) P.1 →
  (∀ w ∈ stdAt X.E (R.N (m2 + 1)) P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E (R.N (m2 + 1)) P.1) →
  κ' ∈ GLint X.E (R.N (m2 + 1 + 1)) P.1 →
  (∀ w ∈ stdAt X.E (R.N (m2 + 1 + 1)) P.1, ((qOf P.1 : X.E) ^ (2 * cst.M))⁻¹ • (κ' w - w) ∈ stdAt X.E (R.N (m2 + 1 + 1)) P.1) →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y'' : Sp X.E (R.N (m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y'' l)) →
  topDat Ch sel mu cst (m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat Ch sel mu cst (m2 + 1) P y y'' := by
  intro X Pr R Ch sel S mu cst m2 hm hc P hP hD κ κ' hκ hκc hκ' hκ'c y y'' hy''
  exact GlobalTheory.TopFrameQM.topDat_frames_qM Ch sel mu cst hm hc P hP hD κ κ' hκ hκc hκ' hκ'c y y'' hy''
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorLevelValuesTypePrime
section
noncomputable section

namespace GlobalTheory.TwTop

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem locAt_vG : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (x x₁ : UA D (t.m2 + 1) (Nat.le_of_succ_le hi)) (x' x₁' : UA D (t.m2 + 1 + 1) hi)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' →
    ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs → ∀ g z g' z', A.cplRel β P g z →
      InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 g →
      TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P g' z' →
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 g' →
    ∀ Z, z' * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z *
        rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g : t.X.Eˣ) : t.X.E) *
        rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g' : t.X.Eˣ) : t.X.E) =
      z * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P hP g z g' z' hC hF hT hF' Z
  have hD : (t.cst μ).D P = 1 := (t.idx_ok μ).depthG P hP
  have hDt : topDep t.sel (t.tup μ) (t.cst μ) P = 1 := by unfold topDep; simp [hP]
  obtain ⟨Gg, rfl, hsrc⟩ := _root_.GlobalTheory.TopLawG.locTopG_source hPin.fields.ok t.pr_ok hPin.sel (t.idx_ok μ) _ P hP g z hC.1
  obtain ⟨Gt, rfl, htgt⟩ := _root_.GlobalTheory.TwTop.topF_target_vG hPin.fields.ok t.pr_ok hPin.sel (t.idx_ok μ) P hP g' z' hT
  obtain ⟨k, hk, hkr⟩ := _root_.GlobalTheory.LevFrame.frame_lev A dtU a hPin hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ κ hx p p₁ hp hp₁ P hP (t.cst μ).D hD Gg hF
  obtain ⟨k', hk', hkr'⟩ := _root_.GlobalTheory.LevFrame.frame_lev A dtU a hPin hTie (t.m2 + 1 + 1) hi β' x' x₁' κ' hx' p' p₁' hp' hp₁' P hP _ hDt Gt hF'
  obtain ⟨i0, i1, hdiff⟩ := GlobalTheory.T.coupling_cosets_right_translate_in_frames_type_prime A dtU a hPin hTie (Nat.le_of_succ_le hi) β p p₁ P hP Gg k z hC hkr hk
  have e1 : inFr (frsF t.sel (t.tup μ) p₁ P) (frsG t.sel (t.tup μ) p₁' P) Z =
      (k'⁻¹).1.toLinearMap ∘ₗ (inFr (frsF t.sel (t.tup μ) p P) (frsG t.sel (t.tup μ) p' P) Z ∘ₗ k.1.toLinearMap) := by
    rw [frsG_eq, frsG_eq, hk, hk']
    rfl
  have hs := hsrc k hkr (inFr (frsF t.sel (t.tup μ) p P) (frsG t.sel (t.tup μ) p' P) Z) _ _ i0 hdiff
  have ht := htgt k' hkr' (inFr (frsF t.sel (t.tup μ) p P) (frsG t.sel (t.tup μ) p' P) Z ∘ₗ k.1.toLinearMap) _ i1
  unfold topF
  rw [e1]
  linear_combination rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det Gg.1 : t.X.Eˣ) : t.X.E) * ht + hs

end GlobalTheory.TwTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelMovedPointFramesMatrixSteps
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

open scoped TensorProduct
open GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.MatFrames


set_option maxHeartbeats 1000000 in
theorem frames_mat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ j (hj : j < D.R.m), j ≤ t.m2 → ∀ (β : (St j hj.le).Ch) (x x₁ : UA D j hj.le) (κ : ((St j hj.le).K β).lev.U), x₁.1 = x.1 * κ.1 →
    ∀ p p₁, IsPtAd A a j hj.le β x p → IsPtAd A a j hj.le β x₁ p₁ →
    ∃ (k : GLQ t.X.E (D.R.N j) (SB t μ)) (c : SB t μ → t.X.Kˣ),
      (∀ P, frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * ((k P)⁻¹).1) ∧
      (∀ P, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG j (A.ib j hj β)) ((t.idx μ).levQ j (A.ib j hj β)) P (k P) (c P)) ∧
      ((((St j hj.le).K β).lev.chi κ : ℂˣ) : ℂ) = t.seam.σ₀ (((∏ P, c P : t.X.Kˣ)) : t.X.K) ∧
      ∀ P : SB t μ, IntAtA (F := D.host.F) (seamP t.seam P.1)
        (iA D.host.F D.host.E ((qOf (seamP t.seam P.1) : D.host.E))⁻¹ *
          ((((Matrix.GeneralLinearGroup.det κ.1)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
            iA D.host.F D.host.E (t.seam.iE ((LinearEquiv.det ((k P)⁻¹).1 : t.X.Eˣ) : t.X.E)) - 1))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie j hj hjm β x x₁ κ hx p p₁ hp hp₁
  classical
  have hok := t.idx_ok μ
  obtain ⟨hLe, -, hChi⟩ := hTie.levMid j hj hjm β
  have hLoc : ∀ P : SB t μ, ∃ g z, A.midRel j hj β P g z ∧ InFrame t.seam (A.fb j hj.le β) (t.cst μ).D P κ.1 g := by
    intro P
    have hv : IsOver (HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1)) (seamP t.seam P.1) := by
      unfold IsOver
      rw [HeightOneSpectrum.under_asIdeal]
    have hU := (((St j hj.le).K β).lev.U_eq κ.1).1 κ.2
    exact hLe P _ hv κ.1 hU.1 (hU.2 _)
  choose g z hgz using hLoc
  have hpr : ∀ P, g P ∈ prCat (Pr := t.Pr) (t.cst μ).sharp j P.1 ((t.idx μ).h j (A.ib j hj β) P) := fun P =>
    (exists_midLev_iff t.Ch t.sel (t.tup μ) (t.cst μ) j P _ (g P)).1 ⟨z P, (hgz P).1⟩
  let gg : ∀ P : SB t μ, GLint t.X.E (D.R.N j) P.1 := fun P => ⟨g P, hok.int j _ P (hpr P)⟩
  have hB := fun P => GlobalTheory.T.frames_of_right_translate_point_principal_congruence A a j hj.le β x x₁ κ.1 hx p p₁ hp hp₁ P (gg P) (hgz P).2
  choose C hCp hCc hCf using hB
  have hD : ∀ P : SB t μ, 1 ≤ (t.cst μ).D P := fun P => hok.cst_ok.D_pos P
  have hc : ∀ P : SB t μ, ∃ c : t.X.Kˣ, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG j (A.ib j hj β)) ((t.idx μ).levQ j (A.ib j hj β)) P
      (gg P * C P)⁻¹ c ∧ (c : t.X.K) = (z P)⁻¹ := by
    intro P
    obtain ⟨r, hr, hrx, hz⟩ := (hgz P).1
    by_cases hP : P.1 ∈ t.Pr.vGs
    · have hH : redGL _ P.1 (gg P) ∈ ((t.idx μ).levG j (A.ib j hj β) ⟨P.1, hP⟩).H :=
        (hok.grpG j _ ⟨P.1, hP⟩ _).2 ⟨g P, hpr P, fun y hy => redV_redGL (gg P) hy⟩
      have hlam := hok.chrG j _ ⟨P.1, hP⟩ ⟨_, hH⟩ (g P) r hr hrx (fun y hy => redV_redGL (gg P) hy)
      have hred : redGL _ P.1 (gg P * C P)⁻¹ = (redGL _ P.1 (gg P))⁻¹ := by
        rw [map_inv, map_mul, GlobalTheory.TopStep.redGL_of_prinCong (hD P) (hCp P), mul_one]
      refine ⟨(((t.idx μ).levG j (A.ib j hj β) ⟨P.1, hP⟩).lam ⟨_, hH⟩)⁻¹, ⟨fun hP' => ⟨hred ▸ inv_mem hH, ?_⟩, fun _ hP' => absurd hP hP'⟩, ?_⟩
      · rw [← map_inv]
        congr 1
        exact Subtype.ext hred.symm
      · rw [Units.val_inv_eq_inv_val, hlam, hz]
    · have hQ : P.1 ∈ QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K) := (Finset.mem_union.mp P.2).resolve_left hP
      obtain ⟨r', hr', hr'x, hr'1⟩ := GlobalTheory.T.principal_congruence_subgroup_mem_level_twist_prime hPin.fields.ok t.pr_ok hok (j := j) hjm (A.ib j hj β) P hP (C P) (hCp P)
      have hgH : gg P ∈ ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H := by
        rw [hok.grpQ]
        exact Subgroup.mem_subgroupOf.2 (hpr P)
      have hCH : C P ∈ ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H := by
        rw [hok.grpQ]
        exact Subgroup.mem_subgroupOf.2 ⟨r', hr', hr'x⟩
      have hlg := hok.chrQ j _ ⟨P.1, hQ⟩ ⟨gg P, hgH⟩ r hr hrx
      have hlC := hok.chrQ j _ ⟨P.1, hQ⟩ ⟨C P, hCH⟩ r' hr' hr'x
      have hC1 : ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).lam ⟨C P, hCH⟩ = 1 := Units.ext (hlC.trans hr'1)
      refine ⟨(((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).lam ⟨gg P, hgH⟩)⁻¹,
        ⟨fun hP' => absurd hP' hP, fun hQ' _ => ⟨inv_mem (mul_mem hgH hCH), ?_⟩⟩, ?_⟩
      · have e : (⟨(gg P * C P)⁻¹, inv_mem (mul_mem hgH hCH)⟩ : ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H) =
            ((⟨gg P, hgH⟩ : ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H) * ⟨C P, hCH⟩)⁻¹ := Subtype.ext (by simp)
        rw [e, map_inv, map_mul, hC1, mul_one]
      · rw [Units.val_inv_eq_inv_val, hlg, hz]
  choose c hcL hcz using hc
  refine ⟨fun P => (gg P * C P)⁻¹, c, fun P => ?_, hcL, ?_, fun P => ?_⟩
  · rw [inv_inv]
    exact hCf P
  · have h1 := hChi κ g z hgz
    have h2 : (((∏ P, c P : t.X.Kˣ)) : t.X.K) = (∏ P, z P)⁻¹ := by
      rw [Units.coe_prod, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun P _ => hcz P
    rw [h2, map_inv₀]
    exact eq_inv_of_mul_eq_one_left h1
  · rw [inv_inv]
    exact GlobalTheory.T.det_inv_mul_frame_reading_congruent_one_mod_norm t.seam (A.fb j hj.le β) (t.cst μ).D P (hD P) κ.1 (g P) (C P).1 (hgz P).2 (hCc P)

end GlobalTheory.MatFrames

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalIsometryStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrimeFunctionals_move_rationalIsometry : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → ∀ (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal),
        IsOver v (seamP t.seam P.1) →
        FunMoved t.seam ((St i hi).K β).lev P v h (iotaOf A i hi β P v h) (ratA D.host.F (A.crd i hi) * x₁.1) ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1) := by
  first | exact @GlobalTheory.TwV.funMoved_ptAd_rat | exact GlobalTheory.TwV.funMoved_ptAd_rat | (intros; apply GlobalTheory.TwV.funMoved_ptAd_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrimeStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localisation_eq_stdAt_of_congruentOne_atPrime : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ), 1 ≤ d → ∀ (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (R : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)), M.FG → Submodule.span E (M : Set (Fin N → E)) = ⊤ → CongAt (F := F) P d (y⁻¹ * ratA F R) → Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (latAd y M) = mvL R (stdAt E N P) → Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M = stdAt E N P := by
  first | exact @GlobalTheory.CongStdLoc.localization_eq_stdAt_of_congAt | exact GlobalTheory.CongStdLoc.localization_eq_stdAt_of_congAt | (intros; apply GlobalTheory.CongStdLoc.localization_eq_stdAt_of_congAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledLatticeVectorMemDualBaseLatticeCompletionStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col GlobalTheory.TwU Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledLatticeVector_mem_dualBaseLatticeCompletion : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), IsUnit J.det → ∀ (c : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F) →
    ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    (∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb) → ∀ (v : HeightOneSpectrum (𝓞 F)) (y : Fin N → E),
    y ∈ latCo sp J c a x Lb →
    (fun l => prV (E := E) v (pullV (F := F) (ratA F c * x) y l)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)) := by
  first | exact @GlobalTheory.MemDual.mem_latS_dual_of_latCo | exact GlobalTheory.MemDual.mem_latS_dual_of_latCo | (intros; apply GlobalTheory.MemDual.mem_latS_dual_of_latCo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepPointPulledDualVectorMemLocalBaseLatticeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepPoint_pulledDualVector_mem_localBaseLattice : ∀ {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (l : Fin (D.R.N i) → D.host.E), l ∈ dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (latAd x.1 lev.Lb) →
    (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)) ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) := by
  first | exact @GlobalTheory.ZDual.pullV_dual_mem_latS | exact GlobalTheory.ZDual.pullV_dual_mem_latS | (intros; apply GlobalTheory.ZDual.pullV_dual_mem_latS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaJetIntegralityTypePrimeOfSplitTableBoundStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaJetIntegrality_typePrime_of_splitTableBound : JetSplitAmb → ∀ (D : D7) (EX : ErrX D) (sel : _) (δ : ℂ) (B : Base D D.host.ccK δ) (χ : _) (cD : _), GlobalTheory.ColPeriod.JetLossAll D EX sel B χ cD := by
  first | exact @GlobalTheory.JetsFromTables.jetLossAll_of_jetSplitAmb | exact GlobalTheory.JetsFromTables.jetLossAll_of_jetSplitAmb | (intros; apply GlobalTheory.JetsFromTables.jetLossAll_of_jetSplitAmb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaKernelFunctionAdelicPointsEqPullbackClassKe
section
noncomputable section

namespace GlobalTheory.TwV.SPull

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xiL_scal {V : Type} [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (vol : ℝ)
    (SX SA SB : Finset V) (k : ℂ) (Φ e : V → ℂ) (z : V) :
    xiL H α vol SX SA SB (fun v => k * Φ v) e z = k * xiL H α vol SX SA SB Φ e z := by
  have hS : ∀ x, xiS H α vol SA SB (fun s => k * Φ (s - x)) e = fun w => k * xiS H α vol SA SB (fun s => Φ (s - x)) e w := by
    intro x
    funext w
    unfold xiS Formalism.L2.Th1.H.sumU
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have : hatS H vol SA (fun s => k * Φ (s - x)) y = k * hatS H vol SA (fun s => Φ (s - x)) y := by
      unfold hatS
      simp only [mul_assoc, ← Finset.mul_sum]
      ring
    beta_reduce
    rw [this]
    ring
  unfold xiL
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hS x]
  simp only [Formalism.L2.Th1.H.opU]
  ring

theorem kerTh_scal {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (k : ℂ) (z : TaylorLogMetric.VC D a b) :
    kerTh B χ SS cl N N' (fun x => k * Ξ x) z = k * kerTh B χ SS cl N N' Ξ z := by
  have hon : Formalism.L2.Ker.onV (fun τ => TaylorLogMetric.embT D τ) δ (fun x => k * Ξ x) =
      fun v => k * Formalism.L2.Ker.onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ v := by
    funext v
    unfold Formalism.L2.Ker.onV
    split_ifs <;> simp
  unfold kerTh thC xiV
  rw [hon]
  exact xiL_scal _ _ _ _ _ _ _ _ _ _

theorem kerTh_prop {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ Ξ' : Formalism.L2.Col.HomE D.host.E a b → ℂ) (k k' : ℂ)
    (h : ∀ x, k * Ξ x = k' * Ξ' x) (z : TaylorLogMetric.VC D a b) :
    k * kerTh B χ SS cl N N' Ξ z = k' * kerTh B χ SS cl N N' Ξ' z := by
  rw [← kerTh_scal, ← kerTh_scal, funext h]


set_option maxHeartbeats 1000000 in
theorem kerTh_eq_pull : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)), ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), ∀ (κ : ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.U) (κ' : ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.U), x.1 = ratA D.host.F γ * ((St i (Nat.le_of_succ_le hi)).y c).1 * κ.1 → x'.1 = ratA D.host.F γ' * ((St (i + 1) hi).y c').1 * κ'.1 → ∀ z, muT (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.chi κ : ℂˣ) : ℂ) * kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.Lb) (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.Lb) (Xi i hi ((St i (Nat.le_of_succ_le hi)).chOf c) ((St (i + 1) hi).chOf c') x x') z = muT (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.chi κ' : ℂˣ) : ℂ) * TaylorLogMetric.pull D t.B.tor (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi))).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)).toLinearMap) (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap) ((t.rd u μ).Th t.seam t.amb i c c') z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hA Xi muT law i hi c c' x x' γ hγ γ' hγ' κ κ' hx hx' z
  obtain ⟨hδ, hLat, hVec, hEq⟩ := _root_.GlobalTheory.TieBase.base_data t
  obtain ⟨hl, hSS⟩ := _root_.GlobalTheory.BadPrimes.lev_pos_and_noConj A dtU a hP hA
  have hu := _root_.GlobalTheory.TwV.ratIsometry_unitary A dtU a hP hA i (Nat.le_of_succ_le hi) γ hγ
  have hu' := _root_.GlobalTheory.TwV.ratIsometry_unitary A dtU a hP hA (i + 1) hi γ' hγ'
  have hN := _root_.GlobalTheory.TwV.latK_lev_rat A dtU a hP hA i (Nat.le_of_succ_le hi) c x γ hγ κ hx
  have hN' := _root_.GlobalTheory.TwV.latK_lev_rat A dtU a hP hA (i + 1) hi c' x' γ' hγ' κ' hx'
  have hd := _root_.GlobalTheory.TwV.adelicDatum_at_translates A dtU a hP hA Xi muT law i hi c c' x x' γ hγ γ' hγ' κ κ' hx hx' hu'
  have hc := _root_.GlobalTheory.TwV.datLoc_classes A dtU a hP hA Xi muT law i hi c c'
  have hth := _root_.GlobalTheory.TwV.th_eq_kerTh A dtU a hP hA Xi muT law i hi c c'
  have hmv := GlobalTheory.TwU.KerMove.kerTh_move D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok hδ t.χ_ok hLat hVec hEq (ssRec t u μ) (t.rd u μ).lev hl hSS
    _ _ _ _ _ (_root_.GlobalTheory.TwV.adm_seam_lat_rd_pair t u μ i (i + 1) c c') hc _ _ hu hu'
  rw [hth, ← hmv, hN, hN']
  exact kerTh_prop _ _ _ _ _ _ _ _ _ _ hd z

end GlobalTheory.TwV.SPull

end
end

