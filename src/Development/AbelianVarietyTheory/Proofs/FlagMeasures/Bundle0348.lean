module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselTorusElementProperties
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0346
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalOfUnipotentFibreIntegralsVanish
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0240
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0302
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ProjRows
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsBij
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RegUnitary
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0003
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0005
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0001
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0025
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSublatticeLiftsModuloFixingUnipotent
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0344
public import Formalism.LocalToGlobal.Divisibility.Bundle0004
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.GroupLattices.JointServices.LevelOperatorFixesImage

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselEnergyNormalisedFrameChange
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA

theorem lintegral_comp_scale {r : ℕ} (s : Fin r → ℝ) (hs : ∀ a, 0 < s a)
    (G : (Fin r → ℂ) × ℂ → ENNReal) :
    ∫⁻ p : (Fin r → ℂ) × ℂ, G (fun a => (s a : ℂ) * p.1 a, p.2) =
      ENNReal.ofReal (∏ a, (s a ^ 2)⁻¹) * ∫⁻ p, G p := by
  let f : (Fin r → ℂ) →ₗ[ℝ] (Fin r → ℂ) :=
    LinearMap.pi fun i => ((s i • LinearMap.id : ℂ →ₗ[ℝ] ℂ)).comp (LinearMap.proj i)
  let T : ((Fin r → ℂ) × ℂ) →ₗ[ℝ] ((Fin r → ℂ) × ℂ) := f.prodMap LinearMap.id
  have hdet : LinearMap.det T = ∏ a, s a ^ 2 := by
    simp only [T, f, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_smul, LinearMap.det_id,
      Complex.finrank_real_complex, mul_one]
  have hpos : 0 < ∏ a, s a ^ 2 := Finset.prod_pos fun a _ => pow_pos (hs a) 2
  have hne : LinearMap.det T ≠ 0 := hdet ▸ hpos.ne'
  haveI : (volume : Measure ((Fin r → ℂ) × ℂ)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ((Fin r → ℂ) × ℂ)) hne
  let e : ((Fin r → ℂ) × ℂ) ≃ᵐ ((Fin r → ℂ) × ℂ) :=
    (T.equivOfDetNeZero hne).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : (e : _ → _) = T := rfl
  have h := lintegral_map_equiv (μ := (volume : Measure ((Fin r → ℂ) × ℂ))) G e
  rw [he, hmap, lintegral_smul_measure, hdet, abs_of_pos (inv_pos.2 hpos), smul_eq_mul] at h
  rw [Finset.prod_inv_distrib, h]
  refine lintegral_congr fun p => ?_
  congr 1

theorem bcWeight_scale (k r : ℕ) (T T' : ℝ) (s : Fin r → ℝ) (hs : ∀ a, 0 < s a) (p : (Fin r → ℂ) × ℂ) :
    bcWeight k r T T' p = (∏ a, (s a ^ (2 * (Mdim k r a - 2)))⁻¹) *
      bcWeight k r T T' (fun a => (s a : ℂ) * p.1 a, p.2) := by
  unfold bcWeight
  split_ifs with h
  · rw [← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    have := (hs a).ne'
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hs a), mul_pow]
    field_simp
  · simp

theorem gamLev_inv_eq (k r : ℕ) (t : ℝ) (ht : 0 < t) :
    (D.GamLev k r t⁻¹ 1 0)⁻¹ = (∏ a : Fin r, ((t ^ (2 * (r - a.val))) ^ (2 * (Mdim k r a - 2)))⁻¹) *
      ∏ a : Fin r, ((t ^ (2 * (r - a.val))) ^ 2)⁻¹ := by
  unfold D.GamLev
  rw [Finset.prod_Ioc_succ_top (Nat.zero_le r), ← Finset.prod_mul_distrib]
  have h1 : Finset.Ioc 0 r = Finset.Ico 1 (r + 1) := by ext; simp; omega
  rw [h1, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel, Finset.prod_range]
  have h0 : ((r : ℤ) + 1 - ((r + 1 : ℕ) : ℤ)) = 0 := by push_cast; ring
  rw [h0]
  simp only [mul_zero, zero_mul, neg_zero, zpow_zero, div_one, mul_one]
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  obtain ⟨d, hd⟩ : ∃ d, r = a.val + (d + 1) := ⟨r - a.val - 1, by have := a.isLt; omega⟩
  have h2 : r - a.val = d + 1 := by omega
  have h3 : Mdim k r a - 2 = 2 * d + k + 1 := by unfold Mdim; omega
  have h4 : 4 * ((r : ℤ) + 1 - ((1 + a.val : ℕ) : ℤ)) * (C.Mlev k r (1 + a.val) - 1) =
      ((2 * (d + 1) * (2 * (2 * d + k + 1)) + 2 * (d + 1) * 2 : ℕ) : ℤ) := by
    unfold C.Mlev
    have : (r : ℤ) = a.val + (d + 1) := by exact_mod_cast hd
    push_cast
    rw [this]; ring
  rw [h4, h2, h3, _root_.inv_zpow', neg_neg, zpow_natCast, ← pow_mul, ← pow_mul, pow_add, mul_inv]

theorem energy_change_of_frame : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Bs : B.RealPlaceData k r L.Wp L.Wq) (cN : ℝ) (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)), 1 ≤ k → IsStdOf L μsec Bs → IsRatioN k r cN → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → ∫⁻ p : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') p * Formalism.MainNotions.S.hsNormSq (L.J F (bigCell k r p.1 (μsec p.2)))) = ENNReal.ofReal (lamN L cN ^ 4 / D.GamLev k r ‖cStd / L.c‖⁻¹ 1 0) * B.normSq Bs (conjF (cStd / L.c) F) := by
  intro k r L μsec Bs cN F _ hstd hrat hc h0 htop
  have hJ := _root_.GlobalTheory.ThA.besselJ_changeFrame k r L μsec Bs cN F hstd hrat hc h0 htop
  have hα : cStd / L.c ≠ 0 := div_ne_zero (by simp [cStd]) hc
  set α := cStd / L.c with hαdef
  have hB := (_root_.GlobalTheory.ThA.TorusElt.torusElt k r α hα).2.2.2
  have ht : 0 < ‖α‖ := norm_pos_iff.2 hα
  obtain ⟨hz, hz', -, -, -, -, -, hμ⟩ := hstd
  let s : Fin r → ℝ := fun a => ‖α‖ ^ (2 * (r - a.val))
  have hs : ∀ a, 0 < s a := fun a => pow_pos ht _
  let G : (Fin r → ℂ) × ℂ → ENNReal := fun p =>
    ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') p *
      ‖B.hsVec (B.JF Bs (conjF α F) (B.gq Bs p))‖ ^ 2)
  have hG : B.normSq Bs (conjF α F) = ∫⁻ p, G p := by
    simp only [B.normSq, jNormSq, hz, hz', G]
  let A : ℝ := lamN L cN ^ 4 * ∏ a, (s a ^ (2 * (Mdim k r a - 2)))⁻¹
  have hA : 0 ≤ A := mul_nonneg (by positivity)
    (Finset.prod_nonneg fun a _ => inv_nonneg.2 (pow_pos (hs a) _).le)
  have hhs : ∀ X : L.Wq →L[ℂ] L.Wp, Formalism.MainNotions.S.hsNormSq X = ‖B.hsVec X‖ ^ 2 := by
    intro X
    rw [PiLp.norm_sq_eq_of_L2]
    unfold Formalism.MainNotions.S.hsNormSq Formalism.MainNotions.S.hsInner
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hpt : ∀ p : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') p *
      Formalism.MainNotions.S.hsNormSq (L.J F (bigCell k r p.1 (μsec p.2)))) =
      ENNReal.ofReal A * G (fun a => (s a : ℂ) * p.1 a, p.2) := by
    intro p
    simp only [G]
    rw [← ENNReal.ofReal_mul hA, hJ, hB, hhs, bcWeight_scale k r _ _ s hs p]
    congr 1
    have hsm : ∀ (c : ℂ) (X : L.Wq →L[ℂ] L.Wp), B.hsVec (c • X) = c • B.hsVec X := fun _ _ => rfl
    rw [hsm, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    simp only [B.gq, hμ, A, s]
    ring
  rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_comp_scale s hs G,
    hG, ← mul_assoc, ← ENNReal.ofReal_mul hA, div_eq_mul_inv, gamLev_inv_eq k r _ ht]
  simp only [A, s, mul_assoc]

end GlobalTheory.ThA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryIsometricOfRepresentatives
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.St

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem colDict_isometric_of_reps :
    ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) → ∀ (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (cs : Formalism.L2.SG.TermOp.ColSys X u what₂) (hinj : Function.Injective (Formalism.L2.SG.TermOp.sharp hK cs)), Formalism.L2.SG.TermOp.ColReps hK cs → ColDictIsom X Tr hK cs hinj := by
  intro D X u F Tr hK hsig hL hS what₂ cs hinj hreps T T'
  obtain ⟨hcls, hwt⟩ := _root_.GlobalTheory.ColClass.classes_and_weight D X u F Tr hK hsig hL
  have hwt1 := hwt hS
  obtain ⟨hψ, hπ, heq, -, -⟩ := GlobalTheory.St.cols_sharp_dictionary D X u hK
  have key := GlobalTheory.sum_inner_classReps_indep (Gam X u) (Hinf X u) (Hfin X u) (iotaI X u) (iotaF X u)
    (Ku X u hK) (psiK X u hK) (X.Vpi u) (piRep X u) hπ hψ cs.Cl ((D.mem u).C.cls 0) cs.h Tr.hc hreps hcls
    (shP X u (toCu X hK T').1) (shP X u (toCu X hK T).1) (heq _) (heq _)
  have hsh : ∀ (S : Formalism.L2.SG.PackageTie2.ColT hinj) ρ, (Formalism.L2.SG.PackageTie2.shT hinj S).ofLp ρ = shP X u (toCu X hK S).1 (cs.h ρ) := fun S ρ => rfl
  show inner ℂ (Formalism.L2.SG.PackageTie2.shT hinj T') (Formalism.L2.SG.PackageTie2.shT hinj T) = _
  rw [PiLp.inner_apply]
  simp only [hsh]
  rw [key]
  have hd : ∀ (S : Formalism.L2.SG.PackageTie2.ColT hinj) c, colDictL X Tr hK (toCu X hK S) c = fun z => Tr.J (shP X u (toCu X hK S).1 (Tr.hc c)) (F.val0.eY z) := fun S c => rfl
  have hterm : ∀ c, (D.fm u).ipV 0 c (colDictL X Tr hK (toCu X hK T) c) (colDictL X Tr hK (toCu X hK T') c) = ⟪shP X u (toCu X hK T').1 (Tr.hc c), shP X u (toCu X hK T).1 (Tr.hc c)⟫_ℂ := by
    intro c
    rw [hd, hd]
    exact Tr.J_isom c _ _
  unfold Formalism.BasicNotions.MemberForms.ipC
  simp only [hwt1, one_mul, hterm]

end GlobalTheory.St

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConvolutionRangeCuspidalOfLowestKType
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem range_cuspidal_of_lowKType : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ y : B.I.L2 B.μf B.fund, (∀ f : B.I.GA → ℂ, IsContRep B (T y) f → ∀ W, B.I.IsIsot W → ∀ ν : Measure B.I.GA, B.I.IsNQuotMeas W ν → ∀ x, ∫ m, f (m * x) ∂ν = 0) ∧ B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T y)) := by
  intro B d h hD hK hh hL hB hF T hT y
  have hv := _root_.GlobalTheory.RealFibre.integral_phe_eq_zero_of_isKTypeOf B d h hD hK hL hh
  exact _root_.GlobalTheory.CuspCore.cusp_of_fibre_vanish B d h hD hv hL hB hF T hT y

end GlobalTheory.Dec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalFrame
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Dec.CuspFrame

theorem one_mem_Kg (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨?_, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
  · simp [AutInst.Kset]
  · simp [AutInst.fmat]

theorem re_fixed (B : RowsAut) : ∀ k ∈ B.I.Kg B.g, (B.R (1, k)).comp B.Re = B.Re := by
  intro k hk
  obtain ⟨h1, hm, hn, -, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  have pm : ∀ a b : B.I.Gf, B.R (1, a * b) = B.R (1, a) * B.R (1, b) := fun a b => by
    have := hm (1, a) (1, b)
    rwa [Prod.mk_mul_mk, mul_one] at this
  have ir : ∀ (a : B.I.Gf) (x z : B.I.L2 B.μf B.fund), ⟪x, B.R (1, a) z⟫_ℂ = ⟪B.R (1, a⁻¹) x, z⟫_ℂ :=
    fun a x z => by
      have hback : B.R (1, a) (B.R (1, a⁻¹) x) = x := by
        have hident : B.R (1, 1) = 1 := h1
        have h := congrArg (fun S : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => S x)
          (pm a a⁻¹)
        simpa [hident, mul_apply_eq_comp] using h.symm
      let U : B.I.L2 B.μf B.fund →ₗᵢ[ℂ] B.I.L2 B.μf B.fund :=
        ⟨(B.R (1, a)).toLinearMap, hn (1, a)⟩
      calc
        ⟪x, B.R (1, a) z⟫_ℂ = ⟪U (B.R (1, a⁻¹) x), U z⟫_ℂ := by
          change ⟪x, B.R (1, a) z⟫_ℂ = ⟪B.R (1, a) (B.R (1, a⁻¹) x), B.R (1, a) z⟫_ℂ
          rw [hback]
        _ = ⟪B.R (1, a⁻¹) x, z⟫_ℂ := U.inner_map_map _ _
  have he : ∀ x, B.e (k * x) = B.e x := fun x => by
    have := B.e_adm.2.2.2.2.2.1 x k hk 1 (one_mem_Kg B.I B.g)
    rwa [mul_one] at this
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply, ir k, B.Re_spec.2, B.Re_spec.2,
    ← MeasureTheory.integral_mul_left_eq_self (fun g => B.e g * ⟪x, B.R (1, g) y⟫_ℂ) k]
  congr 1
  ext g
  rw [he, pm, mul_apply_eq_comp, ir k x]

end GlobalTheory.Dec.CuspFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DEqFinrankHHX
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.RowsCount


open _root_.Formalism _root_.Formalism.L2 Formalism.L2.SG in
theorem projRowsR : Formalism.L2.SG.ProjRows.ProjRowsR :=
  Formalism.L2.SG.ProjRows.projRowsR_of schur_orthogonality_idempotent convolution_projection isConvIdempotent_pi
    Formalism.L2.SG.Pf.regular_representation_unitary


open _root_.Formalism _root_.Formalism.L2 Formalism.L2.SG in
theorem unimodGf : Formalism.L2.SG.Pf.UnimodGf := fun I μf _ _ =>
  (PI.WAU.adUnimod_of PI.WAU.kg_subgroup PI.WAU.maximal_compact_isCompact PI.WAU.compact_countable
    PI.adelic_index_eq) I μf inferInstance

theorem D_eq_finrank_HHX : ∀ (D : D7) (X : HidaSetting D),
    Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → X.B.D = Module.finrank ℂ (HHX X) := by
  intro D X h
  exact (Formalism.L2.SG.RowsDef.RowsAut.D_eq_finrank_HH (Formalism.L2.SG.Pf.rows_bijective projRowsR unimodGf) X.B _
    (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (GlobalTheory.LowestVectorDegree.isFdeg_fdegOf_lowest D X) (fun v => (X.low v).1)
    (GlobalTheory.ProdFactor.integrable_phLoc_of_integrable_ph D X h) X.Rph X.Rph_spec).1

end GlobalTheory.RowsCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSublatticeLiftsModuloFixingUnipotentStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sublattice_lifts_modulo_fixing_unipotent : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → IsSplit D F0 Λ → ∀ (P : LatW D) (s : ℕ) (Q : ℝ), SubOK D (L0X D Λ (lf D F0)) P s Q → ∃ reps : Finset (P →ₗ[𝓞 D.host.E] (hS D).V), (reps.card : ℝ) ≤ NT D u ^ (2 * D.R.rS) * Q ^ D.R.rS ∧ (∀ φ ∈ reps, ∀ p, φ p ∈ XLam Λ (lf D F0)) ∧ ∀ φ : P →ₗ[𝓞 D.host.E] (hS D).V, (∀ p, φ p ∈ XLam Λ (lf D F0)) → ∃ φ₀ ∈ reps, ∃ n ∈ N1 D Λ (lf D F0), ∀ p : P, n (D.sp.iXY 0 (p : (D.sp.X 0).V) + φ p) = D.sp.iXY 0 (p : (D.sp.X 0).V) + φ₀ p := by
  first | exact @GlobalTheory.LoopC.Lifts.main | exact GlobalTheory.LoopC.Lifts.main | (intros; apply GlobalTheory.LoopC.Lifts.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteDimensionalHHX
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.RowsFiniteDim

theorem finiteDimensional_HHX : Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (X : HidaSetting D),
    Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → FiniteDimensional ℂ (HHX X) := by
  intro hHC D X h
  exact hHC X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec X.B.e X.B.Re X.B.e_adm.1
    X.B.e_adm.2.2.2.2.1 X.B.Re_spec
    X.B.H X.B.σ (fun v => fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) X.B.w
    (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (fun v => GlobalTheory.LowestVectorDegree.isFdeg_fdegOf_lowest D X v) (fun v => (X.low v).1)
    (GlobalTheory.ProdFactor.integrable_phLoc_of_integrable_ph D X h) X.Rph X.Rph_spec

end GlobalTheory.RowsFiniteDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapFibreMeasureLocalUnitaryInvariant
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalFibreInvariant

theorem fibre_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (S : HermR (Fv F v) σ a) (g : HA (Fv F v) σ J), (fib S).map (fun X => g • X) = fib S := by
  intro F E _ _ _ _ _ σ hCM n J hJ v a μ ν hμ hν fib hfib S g
  obtain ⟨-, -, -, h4, -, -, -, -, ha⟩ := GlobalTheory.LocalUnitaryTop.top_facts F E σ hCM n J hJ v
  obtain ⟨-, hact⟩ := ha a
  haveI := h4
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hc : ∀ k : HA (Fv F v) σ J,
      Continuous (fun X : Fin a → Fin n → Fv F v ⊗[F] E => k • X) :=
    fun k => hact.comp (Continuous.prodMk continuous_const continuous_id)
  let T : (Fin a → Fin n → Fv F v ⊗[F] E) ≃ₜ (Fin a → Fin n → Fv F v ⊗[F] E) :=
    { toFun := fun X => g • X
      invFun := fun X => g⁻¹ • X
      left_inv := fun X => inv_smul_smul g X
      right_inv := fun X => smul_inv_smul g X
      continuous_toFun := hc g
      continuous_invFun := hc g⁻¹ }
  let Tm := T.toMeasurableEquiv
  have hTm : ∀ X, Tm X = g • X := fun X => rfl
  have hgram : ∀ X : Fin a → Fin n → Fv F v ⊗[F] E,
      gramR (Fv F v) σ J (g • X) = gramR (Fv F v) σ J X := by
    intro X
    funext i j
    exact hR_lin g (X i) (X j)
  have hli : ∀ (k : HA (Fv F v) σ J) (X : Fin a → Fin n → Fv F v ⊗[F] E),
      LinearIndependent (Fv F v ⊗[F] E) X → LinearIndependent (Fv F v ⊗[F] E) (k • X) := by
    intro k X hX
    have hinj : Function.Injective (lin (Fv F v) σ J k) :=
      Function.LeftInverse.injective (g := lin (Fv F v) σ J k⁻¹) (fun x => lin_inv_lin (g := k) (x := x))
    exact hX.map' (lin (Fv F v) σ J k) (LinearMap.ker_eq_bot.mpr hinj)
  have hpre : ∀ b : HermR (Fv F v) σ a,
      Tm ⁻¹' (gramR (Fv F v) σ J ⁻¹' {Subtype.val b} ∩ {X | LinearIndependent (Fv F v ⊗[F] E) X}) =
        gramR (Fv F v) σ J ⁻¹' {Subtype.val b} ∩ {X | LinearIndependent (Fv F v ⊗[F] E) X} := by
    intro b
    ext X
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, hTm, hgram]
    refine and_congr_right fun _ => ⟨fun h => ?_, hli g X⟩
    have := hli g⁻¹ _ h
    rwa [inv_smul_smul] at this
  have hU : Tm ⁻¹' {X | LinearIndependent (Fv F v ⊗[F] E) X} =
      {X | LinearIndependent (Fv F v ⊗[F] E) X} := by
    ext X
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hTm]
    refine ⟨fun h => ?_, hli g X⟩
    have := hli g⁻¹ _ h
    rwa [inv_smul_smul] at this
  have hμT : μ.map Tm = μ := _root_.GlobalTheory.LocalUnitaryHaar.haar_tuple_invariant F E σ hCM n J hJ v a μ hμ g
  let fib' : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E) := fun b => (fib b).map Tm
  have hfib' : IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib' := by
    refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
    · show (fib b).map Tm _ = 0
      rw [Tm.map_apply, Set.preimage_compl, hpre]
      exact hfib.1 b
    · have e1 : ∀ b, ∫⁻ x, φ x ∂(fib' b) = ∫⁻ x, φ (Tm x) ∂(fib b) := fun b =>
        lintegral_map_equiv φ Tm (μ := fib b)
      simp only [e1]
      rw [← hfib.2.1 (fun x => φ (Tm x)) (hφ.comp Tm.measurable)]
      conv_lhs => rw [← hμT]
      rw [Tm.restrict_map, lintegral_map_equiv, hU]
    · have h3 := hfib.2.2 (φ ∘ Tm) (hφc.comp T.continuous) (hφs.comp_homeomorph T) (by
        show tsupport (φ ∘ T) ⊆ _
        rw [tsupport_comp_eq_preimage φ T]
        intro X hX
        have : Tm X ∈ {X | LinearIndependent (Fv F v ⊗[F] E) X} := hφU hX
        rw [← Set.mem_preimage, hU] at this
        exact this)
      refine ⟨fun b hb => (integrable_map_equiv Tm φ).mpr (h3.1 b hb), ?_⟩
      refine h3.2.congr fun b _ => ?_
      exact MeasureTheory.integral_map_equiv Tm φ
  have hu := GlobalTheory.LocalFibreUnique.fibre_family_unique F E σ hCM n J hJ v a μ ν hμ hν fib hfib fib' hfib'
  show (fib S).map Tm = fib S
  exact (congrFun hu S).symm

end GlobalTheory.LocalFibreInvariant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtDerivedActionMaxCompactAverageStatement
section
open MeasureTheory Matrix Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_derived_action_max_compact_average : ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ) (v : H) (D : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ → GlobalTheory.KFinAvg.IsHaarKH k r μ → Continuous φ → Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v → (∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y) → Formalism.MainNotions.S.InLieHpk k r X → HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v) ∂μ)) (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v) ∂μ) 0 := by
  first | exact @GlobalTheory.KFinAvg.hasDerivAt_exp_integral_dsigW | exact GlobalTheory.KFinAvg.hasDerivAt_exp_integral_dsigW | (intros; apply GlobalTheory.KFinAvg.hasDerivAt_exp_integral_dsigW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralTranslateFamilyIsKFiniteHermitianStatement
section
open MeasureTheory Matrix Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_translate_family_isKFinite_hermitian : ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ → GlobalTheory.KFinAvg.IsHaarKH k r μ → ∀ (N : ℕ) (b : Fin N → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ), (∀ j, Continuous (b j)) → (∀ (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (j : Fin N), ∃ d : Fin N → ℂ, ∀ g, b j (a * g) = ∑ i, d i * b i g) → ∀ (c : Fin N → ℂ) (v : H), PI.UpqRep.IsKFinHpk (k := k) (r := r) σ (∫ g, (∑ j, c j * b j g) • σ g v ∂μ) := by
  first | exact @GlobalTheory.KFinAvg.isKFinHpk_integral_translates | exact GlobalTheory.KFinAvg.isKFinHpk_integral_translates | (intros; apply GlobalTheory.KFinAvg.isKFinHpk_integral_translates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.JExistsAll
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem jExists_all : ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), JExists D F := by
  intro D F X u wt hw
  obtain ⟨J, hJ, -⟩ := _root_.GlobalTheory.St.coefficient_map_exists_onto D X u (F u) wt hw
  exact ⟨J, hJ⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveRowsMapBijectiveColumnLevel
section
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField

namespace GlobalTheory

theorem prim_rows_surjective : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → ∀ (Zs : DefSub A3.fam3.amb3) (S1 : IndefData (A3.side3 F.P1 F.ψ1 Zs)), (R.toCx3 F).zs = Zs → HEq ((R.toCx3 F).data F.cr true) S1 → Function.Surjective ((A3.side3 F.P1 F.ψ1 Zs).Pq A3.A.μ0).mulVec ∧ Function.Surjective (S1.ι A3.A.μ0).mulVec := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hsep hW hP Zs S1 hz hS
  subst hz
  have hS' := eq_of_heq hS
  subst hS'
  have hR := complex_data_conditions_base_level_of_primitive_links hok hsep hW hP
  exact ⟨(hR.wf true).Pq_surj _, (CxData.rowMat_bij _ _ true (hR.what₂ true).1 (hR.ratMu true) _).2⟩

end GlobalTheory
end

