module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0017
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.RtUnitaryOf
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStarStableIdealAbsorbingMinors
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryFixingActsOnComplementFrame
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St


set_option maxHeartbeats 1000000 in
theorem unitary_fix_acts_on_complement_frame : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ γ₀ : GL (Fin X.B.I.n) X.B.I.E, γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J → (∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x) → ∃ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, (y₀.map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * y₀ = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm ∧ ∀ j, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i) := by
  intro D X u wt hw γ₀ hγ hfix
  obtain ⟨Q, Qi, G', h1, h2, hq, he, hf, hz, hG', hD⟩ := _root_.GlobalTheory.St.qFrame_basis_gram D X u wt hw
  have hU : ((γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (starRingEnd X.B.I.E))ᵀ * X.B.I.J *
      (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J := hγ
  have hcol : ∀ b, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ (fun i => Q i (Sum.inr b)) =
      fun i => Q i (Sum.inr b) := by
    intro b
    rcases b with a | a | ⟨⟩
    · have e : (fun i => Q i (Sum.inr (Sum.inl a))) = X.eR a := funext (he a)
      rw [e]; exact hfix _ (Or.inl (Or.inl ⟨a, rfl⟩))
    · have e : (fun i => Q i (Sum.inr (Sum.inr (Sum.inl a)))) = X.fR a := funext (hf a)
      rw [e]; exact hfix _ (Or.inl (Or.inr ⟨a, rfl⟩))
    · have e : (fun i => Q i (Sum.inr (Sum.inr (Sum.inr ())))) = X.zR u := funext hz
      rw [e]; exact hfix _ (Or.inr rfl)
  obtain ⟨y, hy, hγQ⟩ := (GlobalTheory.unitary_stabiliser_orthogonal_summand X.B.I.E (starRingEnd X.B.I.E) _ _ _
    X.B.I.J _ G' Q Qi h1 h2 hD hG').2 _ hU hcol
  refine ⟨y, hy, fun j => ?_⟩
  have hQ : (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * Q = Q * (Matrix.fromBlocks y (0 : Matrix (Fin (D.R.N 0)) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E) (0 : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin (D.R.N 0)) X.B.I.E) (1 : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E)) := by
    rw [hγQ, Matrix.mul_assoc _ Qi Q, h2, Matrix.mul_one]
  funext i
  have e := congrFun (congrFun hQ i) (Sum.inl j)
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type] at e
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁,
    Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, hq] at e
  rw [Finset.sum_apply]
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [e]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.St
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryFixingMemRationalStabiliser
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem rat_unitary_fixing_mem_gam : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (γ₀ : GL (Fin X.B.I.n) X.B.I.E), γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J → (∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x) → ∃ γ : Gam X u, (∀ v, uMat ((γ : X.B.I.GA).1 v) = (X.B.I.P v)⁻¹ * (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v) ∧ X.B.I.fmat (γ : X.B.I.GA).2 = (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) := by
  intro D X u γ₀ hγ₀ hfix
  have hs : (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)).comp (starRingEnd X.B.I.E) =
      (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)).comp (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) := by
    ext e
    exact (PI.UnitaryGroupMassFormula.InHHClassFin.rt_sig X.B.I e).symm
  have hm := Formalism.UG.P.bc_mem _ _ _ hs X.B.I.J γ₀ hγ₀
  let g : X.B.I.Gf := ⟨_, hm⟩
  have hg : X.B.I.fmat g = (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map
      (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) :=
    Formalism.UG.P.bc_coe _ γ₀
  have hinf : (fun v => PI.UnitaryGroupMassFormula.InHHClassFin.rtReal X.B.I γ₀ hγ₀ v) ∈ Hinf X u := by
    intro v y hy
    have hP : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (X.B.I.P_unit v))
    show uMat (PI.UnitaryGroupMassFormula.InHHClassFin.rtReal X.B.I γ₀ hγ₀ v) *ᵥ
        ((X.B.I.P v)⁻¹ *ᵥ fun i => X.B.I.φ v (y i)) = (X.B.I.P v)⁻¹ *ᵥ fun i => X.B.I.φ v (y i)
    rw [PI.UnitaryGroupMassFormula.InHHClassFin.rt_uMat, Matrix.mulVec_mulVec, Matrix.mul_assoc _ (X.B.I.P v), hP,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    exact (RingHom.map_mulVec (X.B.I.φ v) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) y i).symm.trans
      (congrArg (X.B.I.φ v) (congrFun (hfix y hy) i))
  have hfin : g ∈ Hfin X u := by
    intro y hy
    rw [hg]
    funext i
    exact (RingHom.map_mulVec (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))
      (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) y i).symm.trans
      (congrArg _ (congrFun (hfix y hy) i))
  refine ⟨⟨(fun v => PI.UnitaryGroupMassFormula.InHHClassFin.rtReal X.B.I γ₀ hγ₀ v, g), ?_⟩, ?_, ?_⟩
  · show _ ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ⊓ (Hinf X u).prod (Hfin X u)
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_prod.2 ⟨hinf, hfin⟩⟩
    exact ⟨γ₀, hγ₀, fun v => PI.UnitaryGroupMassFormula.InHHClassFin.rt_uMat X.B.I γ₀ hγ₀ v, hg⟩
  · intro v
    exact PI.UnitaryGroupMassFormula.InHHClassFin.rt_uMat X.B.I γ₀ hγ₀ v
  · exact hg

end GlobalTheory.St
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlacesFrameMatrixEqRationalOfRational
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.St


set_option maxHeartbeats 1000000 in
theorem sTil_eq_atInf_of_rational : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ (s : X.B.I.Ginf) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E), (∀ v, uMat (s v) = (X.B.I.P v)⁻¹ * γ₀.map (X.B.I.φ v) * X.B.I.P v) → (∀ j, γ₀ *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i)) → sTil X wt s = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (y₀.map X.ιE) := by
  intro D X u wt hW s γ₀ y₀ hs hy
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hQq, -, -, -, hG', hblk⟩ := _root_.GlobalTheory.St.qFrame_basis_gram D X u wt hW
  funext τ
  set v := X.pl.symm τ with hv
  set φ := X.B.I.φ v with hφ
  set G := (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm with hGdef

  have hgram : gramQ X wt v = G.map φ := by
    ext a b
    have h1 := congrFun (congrFun hblk (Sum.inl a)) (Sum.inl b)
    rw [Matrix.fromBlocks_apply₁₁] at h1
    rw [Matrix.map_apply, ← h1]
    simp only [gramQ, Matrix.of_apply, rvV]
    have := PI.ScPiFrameW.hJ_rv X.B.I v (X.crd (qFr wt a)) (X.crd (qFr wt b))
    refine this.trans ?_
    congr 1
    simp only [Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hQq, Finset.sum_mul]
    rw [Finset.sum_comm]

  have hdetG : G.det ≠ 0 := by
    have hJu : IsUnit X.B.I.J.det := isUnit_iff_ne_zero.mpr X.B.I.J_det
    have hJinv : X.B.I.J * X.B.I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJu
    have hR : Matrix.fromBlocks G 0 0 G' *
        (Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ) = 1 := by
      rw [← hblk]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q Qi, hQQi, Matrix.one_mul, ← Matrix.mul_assoc X.B.I.J, hJinv, Matrix.one_mul,
        ← Matrix.transpose_mul, ← Matrix.map_mul, hQiQ, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.transpose_one]
    have hd := congrArg Matrix.det hR
    rw [Matrix.det_mul, Matrix.det_one, Matrix.det_fromBlocks_zero₂₁] at hd
    exact left_ne_zero_of_mul (left_ne_zero_of_mul_eq_one hd)
  have hdetQ : IsUnit (gramQ X wt v).det := by
    have hm : (G.map φ).det = φ G.det := (RingHom.map_det φ G).symm
    rw [hgram, hm, isUnit_iff_ne_zero, map_ne_zero]; exact hdetG

  have hvec : ∀ x, uMat (s v) *ᵥ rv X.B.I v x = rv X.B.I v (γ₀ *ᵥ x) := by
    intro x
    have hu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (X.B.I.P_unit v)
    have hinv : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    rw [hs v]
    simp only [rv]
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc _ (X.B.I.P v), hinv, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    congr 1
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul, φ]
  have hlin : ∀ b, rv X.B.I v (γ₀ *ᵥ X.crd (qFr wt b)) = ∑ i, φ (y₀ i b) • rvV X v (qFr wt i) := by
    intro b
    rw [hy b]
    simp only [rvV, rv]
    simp_rw [← Matrix.mulVec_smul]
    rw [← Matrix.mulVec_sum]
    congr 1
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Finset.sum_apply, map_sum, map_mul, φ]
  have hM : (Matrix.of fun a b => hJ (X.B.I.ε v) (rvV X v (qFr wt a))
      (uMat (s v) *ᵥ rvV X v (qFr wt b))) = gramQ X wt v * y₀.map φ := by
    ext a b
    rw [Matrix.of_apply, show rvV X v (qFr wt b) = rv X.B.I v (X.crd (qFr wt b)) from rfl, hvec, hlin,
      Matrix.mul_apply]
    simp only [hJ, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, gramQ,
      Matrix.of_apply, Matrix.map_apply, smul_eq_mul, rvV]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hfin : y₀.map φ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (y₀.map X.ιE) τ := by
    ext a b
    simp only [Formalism.L2.Forms.atInf, Matrix.map_apply, φ, X.φ_eq, hv, Equiv.apply_symm_apply]
    rfl
  show (gramQ X wt v)⁻¹ * _ = _
  rw [hM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetQ, Matrix.one_mul, hfin]

end GlobalTheory.St
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantTermNormsGeOneAndBounded
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.PairsLab

theorem norms_of_relevant : ∀ (Cg cb Cw cT CT C0 CH C' Cl : ℝ), 0 ≤ CH → ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X)
    (u : D.what₂.Word), HostC → NFExC → LabC → TermC → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 →
    ∀ t ∈ relSet Y u, 1 ≤ k2Del D (jT t) (labT t) ∧ 1 ≤ DbL D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 ∧
      DbL D (jT t) (labT t) ≤ (Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2) ^ D.R.rS := by
  intro Cg cb Cw cT CT C0 CH C' Cl hCH D large₂ X Y u hHost hNF hLab hTerm hH t ht
  have hS : Std D large₂ := ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hH⟩
  obtain ⟨hK, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := hHost D large₂ hS
  obtain ⟨N, hN, hNj, hNT⟩ := hNF D large₂ X Y u hS t ht
  have hT : N.IsTerm (gS D) t.lam := hTerm D large₂ X Y u hS t N hN
  obtain ⟨-, -, hDel, hDb, -⟩ := hLab D large₂ X Y u hS t N hN
  obtain ⟨𝔠, -, hDb1, hDel1, -⟩ := GlobalTheory.DegCnt.Absorb.exists_absorbing_ideal D.host.E (VS D).V (HV D) hK D.R.rS N (gS D)
    t.lam (by omega) hT
  have hPF : PFHost D := PFHost_of_data D hH.1.2.1
  have hC : 2 * (CH + 1) ≤ 2 * (CH + 1) := le_rfl
  have hup := (delta_pos_le_height_sq hPF large₂ hCH hC t ht).2
  have hb := two_le_scale_b D large₂
  have hHb : (1 : ℝ) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f := by
    unfold Hb
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hS1 := one_le_sigma_product (D := D) (H1C large₂ CH) (jT t) (labT t)
  have hA : (1 : ℝ) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 :=
    one_le_mul_of_one_le_of_one_le hHb (one_le_pow₀ hS1)
  refine ⟨hDel ▸ hDel1, hDb ▸ hDb1, hup, ?_⟩
  have hcard : (k2ends D (jT t) (labT t)).card ≤ D.R.rS := by
    unfold k2ends
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Nat.card_Icc]
    unfold jT
    omega
  calc DbL D (jT t) (labT t)
      ≤ ∏ _l ∈ k2ends D (jT t) (labT t),
          Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 := by
        unfold DbL
        refine Finset.prod_le_prod₀ (fun l _ => ?_) (fun l hl => localNorm_le_height_sq hPF large₂ hCH hC t l hl)
        unfold Nloc
        exact_mod_cast FractionalIdeal.absNorm_nonneg _
    _ = _ ^ (k2ends D (jT t) (labT t)).card := Finset.prod_const _
    _ ≤ _ := pow_le_pow_right₀ hA hcard

end GlobalTheory.TypeAsm.PairsLab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReproducingFormulaFixedVectorModerateGrowth
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.ReproducingFixed

theorem two_mul_rank_le {n : ℕ} (ε : Fin n → Bool) : 2 * rkR ε ≤ n := by
  unfold rkR
  set A := univ.filter fun a => ε a = true
  set A' := univ.filter fun a => ε a = false
  have h1 := Finset.card_union_add_card_inter A A'
  have h2 : A ∩ A' = ∅ := by
    ext a
    simp [A, A']
  have h3 := Finset.card_le_univ (A ∪ A')
  rw [h2, Finset.card_empty] at h1
  rw [Fintype.card_fin] at h3
  omega

theorem weight_condition (B : RowsAut) (h s : ℝ) (hn : 1 ≤ B.I.n) (hb : HBig B 40 h)
    (hs : s ≤ 2 * (B.I.n : ℝ) ^ 2) (v : InfinitePlace B.I.F) :
    rkR (B.I.ε v) = 0 ∨ 8 * Real.sqrt (rkR (B.I.ε v)) * (s + 4 * B.I.n * rkR (B.I.ε v)) < h := by
  by_cases hq : rkR (B.I.ε v) = 0
  · exact Or.inl hq
  right
  have h2 := two_mul_rank_le (B.I.ε v)
  have hq1 : (1 : ℝ) ≤ (rkR (B.I.ε v) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
  have h2r : 2 * (rkR (B.I.ε v) : ℝ) ≤ B.I.n := by exact_mod_cast h2
  have hnr : (1 : ℝ) ≤ B.I.n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt (rkR (B.I.ε v)) := Real.sqrt_pos.mpr (by linarith)
  have hbv := hb v
  unfold HBig at hbv
  have key : s + 4 * B.I.n * rkR (B.I.ε v) ≤ 4 * (B.I.n : ℝ) ^ 2 := by nlinarith
  have hle : 8 * Real.sqrt (rkR (B.I.ε v)) * (s + 4 * B.I.n * rkR (B.I.ε v)) ≤
      32 * (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v)) := by nlinarith
  have hpos : 0 < (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v)) := by positivity
  linarith

theorem inv_tau_pow_le (I : AutInst) (hn : 1 ≤ I.n) (x g : I.GA) (hg : g.2 ∈ I.Kset) :
    (tau1 I (x * g))⁻¹ ^ (2 * I.n ^ 2 * I.f) ≤
      (tau1 I x)⁻¹ ^ (2 * I.n ^ 2 * I.f) * Real.exp (2 * (I.n : ℝ) ^ 2 * dSum I g.1) := by
  have ha := GlobalTheory.TauLipschitz.trunc_pos I hn x
  have hb := GlobalTheory.TauLipschitz.trunc_pos I hn (x * g)
  have hl := GlobalTheory.TauLipschitz.log_trunc_le I hn x g hg
  have hf : (0 : ℝ) < I.f := by
    have : 0 < I.f := by
      unfold AutInst.f
      exact Module.finrank_pos
    exact_mod_cast this
  set D := dSum I g.1
  have h1 : tau1 I x * Real.exp (-(D / I.f)) ≤ tau1 I (x * g) := by
    have := Real.exp_le_exp.mpr hl
    rw [Real.exp_log hb, Real.exp_sub, Real.exp_log ha] at this
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact this
  have h2 : (tau1 I (x * g))⁻¹ ≤ (tau1 I x)⁻¹ * Real.exp (D / I.f) := by
    have hpos : 0 < tau1 I x * Real.exp (-(D / I.f)) := mul_pos ha (Real.exp_pos _)
    calc (tau1 I (x * g))⁻¹ ≤ (tau1 I x * Real.exp (-(D / I.f)))⁻¹ := inv_anti₀ hpos h1
      _ = (tau1 I x)⁻¹ * Real.exp (D / I.f) := by rw [mul_inv, Real.exp_neg, inv_inv]
  have h3 := pow_le_pow_left₀ (inv_nonneg.mpr hb.le) h2 (2 * I.n ^ 2 * I.f)
  have h4 : ((2 * I.n ^ 2 * I.f : ℕ) : ℝ) * (D / I.f) = 2 * (I.n : ℝ) ^ 2 * D := by
    push_cast
    field_simp
  calc _ ≤ _ := h3
    _ = (tau1 I x)⁻¹ ^ (2 * I.n ^ 2 * I.f) * Real.exp (2 * (I.n : ℝ) ^ 2 * D) := by
      rw [mul_pow, ← Real.exp_nat_mul, h4]

theorem reproducing_fixed : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 40 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ) (C : ℝ), T y = y → IsContRep B y f → (∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)) → (∃ Φ : B.I.GA → ℝ, Integrable Φ (B.I.muA B.μf) ∧ ∀ x g, ‖phe B d g * f (x * g)‖ ≤ (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g) ∧ ∀ x, f x = ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf) := by
  intro B d h hd hn hl hb T hT y f C hy hf hC
  have hcr := hf
  unfold IsContRep at hf
  obtain ⟨hfc, hfinv, -⟩ := hf
  obtain ⟨hphc, hphle, hphint⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl
  have hwc := fun v => weight_condition B h (2 * (B.I.n : ℝ) ^ 2) hn hb le_rfl v
  have hint1 : Integrable (fun g => majPh B d h g * Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g)) (muInf B.I) :=
    hphint (2 * (B.I.n : ℝ) ^ 2) (by positivity) hwc
  obtain ⟨hτpos, hτc, -, -⟩ := GlobalTheory.TauLipschitz.tauLip B.I hn
  have hadm := B.e_adm
  unfold AutInst.IsAdmIdem at hadm
  obtain ⟨-, -, -, -, he_supp, -, -⟩ := hadm
  have hre := B.Re_spec
  unfold AutInst.IsRConvF at hre
  have hmu : B.I.muA B.μf = (muInf B.I).prod B.μf := rfl
  have hmaj0 : ∀ g, 0 ≤ majPh B d h g := fun g => (norm_nonneg _).trans (hphle g)
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : B.I.GA → ℝ, Φ = fun g => max C 0 *
      (majPh B d h g.1 * Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1) * ‖B.e g.2‖) := ⟨_, rfl⟩
  have hΦg : ∀ g, Φ g = max C 0 *
      (majPh B d h g.1 * Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1) * ‖B.e g.2‖) := fun g => by rw [hΦdef]
  have hΦ0 : ∀ g, 0 ≤ Φ g := fun g => by
    rw [hΦg]
    exact mul_nonneg (le_max_right _ _)
      (mul_nonneg (mul_nonneg (hmaj0 _) (Real.exp_pos _).le) (norm_nonneg _))
  have hΦint : Integrable Φ (B.I.muA B.μf) := by
    rw [hΦdef, hmu]
    have hre1 : Integrable B.e B.μf := hre.1
    exact (hint1.mul_prod hre1.norm).const_mul _
  have hW0 : ∀ x, 0 ≤ (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) := fun x => pow_nonneg (inv_nonneg.mpr (hτpos x).le) _
  have hbound : ∀ x g, ‖phe B d g * f (x * g)‖ ≤ (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g := by
    intro x g
    rw [show phe B d g = ph B d g.1 * B.e g.2 from rfl]
    by_cases he : B.e g.2 = 0
    · rw [he, mul_zero, zero_mul, norm_zero]
      exact mul_nonneg (hW0 x) (hΦ0 g)
    · have h2 := inv_tau_pow_le B.I hn x g (he_supp g.2 he)
      have h3 : ‖f (x * g)‖ ≤ max C 0 * ((tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) *
          Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1)) :=
        (hC (x * g)).trans ((mul_le_mul_of_nonneg_right (le_max_left C 0) (hW0 _)).trans
          (mul_le_mul_of_nonneg_left h2 (le_max_right C 0)))
      rw [norm_mul, norm_mul, hΦg]
      calc ‖ph B d g.1‖ * ‖B.e g.2‖ * ‖f (x * g)‖
          ≤ majPh B d h g.1 * ‖B.e g.2‖ * (max C 0 * ((tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) *
              Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1))) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (hphle g.1) (norm_nonneg _)) h3 (norm_nonneg _)
              (mul_nonneg (hmaj0 _) (norm_nonneg _))
        _ = _ := by ring
  obtain ⟨hext1, hext2, -, -⟩ := GlobalTheory.ExtContRep.ext_ae_eq_contRep B y f hcr
  have hrc := (GlobalTheory.ConvKernel.rconv_eq_integral B (phe B d) T hT y).2
  rw [hy] at hrc
  haveI : SecondCountableTopology B.I.Gf := (GlobalTheory.CongTop.adelic_topology B.I).2.2.1
  haveI : FirstCountableTopology B.I.Ginf := inferInstance
  have hshift : ∀ x : B.I.GA, ∀ᵐ g ∂(B.I.muA B.μf), B.I.ext y (x * g) = f (x * g) := by
    intro x
    have hmap := (GlobalTheory.AdelicUnimod.adelic_unimodular B.I B.μf).1 x
    have hm : AEMeasurable (fun g => x * g) (B.I.muA B.μf) :=
      (continuous_const.mul continuous_id).aemeasurable
    rw [← hmap] at hext1
    exact ae_of_ae_map hm hext1
  have hyF : (y : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund]
      fun x => ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf) := by
    refine hrc.trans (Filter.Eventually.of_forall fun x => ?_)
    exact integral_congr_ae ((hshift x).mono fun g hg => by simp only [hg])
  have hFc : Continuous fun x => ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf) := by
    rw [continuous_iff_continuousAt]
    intro x0
    have hcw : Continuous fun x => (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) :=
      (hτc.inv₀ fun x => (hτpos x).ne').pow _
    have hev : ∀ᶠ x in nhds x0, (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) < (tau1 B.I x0)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) + 1 :=
      hcw.continuousAt.eventually_lt continuousAt_const (lt_add_one _)
    refine continuousAt_of_dominated (bound := fun g => ((tau1 B.I x0)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) + 1) * Φ g)
      ?_ ?_ (hΦint.const_mul _) ?_
    · exact Filter.Eventually.of_forall fun x =>
        hT.1.aestronglyMeasurable.mul (hfc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards [hev] with x hx
      exact Filter.Eventually.of_forall fun g =>
        (hbound x g).trans (mul_le_mul_of_nonneg_right hx.le (hΦ0 g))
    · exact Filter.Eventually.of_forall fun g =>
        (continuous_const.mul (hfc.comp (continuous_id.mul continuous_const))).continuousAt
  have hcrF : IsContRep B y fun x => ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf) := by
    unfold IsContRep
    refine ⟨hFc, fun γ hγ x => ?_, hyF⟩
    simp only [mul_assoc, hfinv γ hγ]
  have hFeq := hext2 _ hcrF
  exact ⟨⟨Φ, hΦint, hbound⟩, fun x => (congrFun hFeq x).symm⟩

end GlobalTheory.ReproducingFixed
end

