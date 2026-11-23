module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1603
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2096
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientBoundOfHyp
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SumSize GlobalTheory.FunObj.AaCoef
open GlobalTheory.RowClaim GlobalTheory.ArchTens ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.ArchTens.VolSize

theorem abs_zpow_le {q : ℕ} (hq : q ≠ 0) {z : ℤ} {A : ℝ} (h : |(z : ℝ)| ≤ A) :
    |(((q : ℚ) ^ z : ℚ) : ℝ)| ≤ Real.exp (A * Real.log q) := by
  have h0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have e : (((q : ℚ) ^ z : ℚ) : ℝ) = Real.exp ((z : ℝ) * Real.log q) := by
    rw [← Real.log_zpow, Real.exp_log (zpow_pos h0 z)]
    push_cast
    rfl
  rw [e, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ((le_abs_self _).trans h) (Real.log_natCast_nonneg _))

theorem prod_zpow_sum {q : ℚ} (hq : q ≠ 0) {ι : Type} (s : Finset ι) (z : ι → ℤ) : ∏ i ∈ s, q ^ z i = q ^ ∑ i ∈ s, z i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem coef_le_of_chosen {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {P : Pl D.host.E} (hP : P ∈ G.pl.W0)
    (hl : P ∈ locPl G t) {β : CosFam G t} (hβ : β ∈ S.supp t Φ) :
    |((S.term t Φ β ⟨P, hl⟩).coef : ℝ)| ≤
      Real.exp ((D.R.m : ℝ) ^ 3 * bigN D * cosExp G P * Real.log (resCard (Kw P) : ℕ)) := by
  classical
  have hs : 1 ≤ (locGrid G t P).s := one_le_sLen
  have hkeep : keepAt G P = false := by simp [keepAt, hP]
  have hdep : depthAt G P = cosExp G P := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨h1, h2⟩ := depthAt_w G hv
    rw [h1, h2]
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := ((Good.locGrid_isGood hL G W t hde hc).1 P hl).square 0 hm 0 hm
  haveI := (isUnitVol_unitVol P).1
  have hT := isTensor_Tflip hL W S.B t Φ hde hc hl
  rw [hdep] at hT
  have hO := oneCoset hs (psiAt W P) (unitVol P) (givenLevel G t P) (Tflip W S.B t Φ P) (unifAt P) (cosExp G P) D.R.m_even
    (isUnif_unifAt P) h00.cond hT (fun j hj _ => givenLevel_KO G t P hj)
  have hb := hβ ⟨P, hl⟩
  have hb' : β ⟨P, hl⟩ ∈ unfSupport (psiAt W P) (unitVol P) false
      (Reps.through hs (givenLevel G t P) (stair (locGrid G t P) (unifAt P) (cosExp G P))) (Tflip W S.B t Φ P) := by
    have : keepAt G (⟨P, hl⟩ : locPl G t).1 = false := hkeep
    rw [this] at hb
    exact hb
  have hβ' := funext (hO _ hb')
  have hz : ∀ i : Fin ((locGrid G t P).m - 2), ∃ z : ℤ,
      invVol (conjLevel hs (givenLevel G t P) ((repsAt G t P).elt (β ⟨P, hl⟩)) (j := i + 1) (by omega)) =
        (resCard (Kw P) : ℚ) ^ z ∧ |z| ≤ (bigN D : ℤ) * ((D.R.m : ℤ) * ((cosExp G P : ℤ) * (D.R.m : ℤ))) := fun i =>
    factor_stair G t P hs (cosExp G P) _ (Nat.succ_pos _) _ (by
      rw [hβ']
      exact through_elt _ (by omega))
  choose z hz hzb using hz
  have hq : resCard (Kw P) ≠ 0 := resCard_ne P
  have e : (S.term t Φ β ⟨P, hl⟩).coef = (resCard (Kw P) : ℚ) ^ (∑ i, z i) := by
    rw [← prod_zpow_sum (by exact_mod_cast hq)]
    refine Eq.trans ?_ (Finset.prod_congr rfl fun i _ => hz i)
    rfl
  rw [e]
  refine abs_zpow_le hq ?_
  have hm2 : (((locGrid G t P).m - 2 : ℕ) : ℤ) ≤ D.R.m := by
    have : (locGrid G t P).m - 2 ≤ D.R.m := by show D.R.m - 2 ≤ D.R.m; omega
    exact_mod_cast this
  have key : |∑ i, z i| ≤ (D.R.m : ℤ) ^ 3 * bigN D * cosExp G P :=
    calc |∑ i, z i| ≤ ∑ i, |z i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin ((locGrid G t P).m - 2), (bigN D : ℤ) * ((D.R.m : ℤ) * ((cosExp G P : ℤ) * (D.R.m : ℤ))) :=
        Finset.sum_le_sum fun i _ => hzb i
      _ = (((locGrid G t P).m - 2 : ℕ) : ℤ) * ((bigN D : ℤ) * ((D.R.m : ℤ) * ((cosExp G P : ℤ) * (D.R.m : ℤ)))) := by simp
      _ ≤ (D.R.m : ℤ) * ((bigN D : ℤ) * ((D.R.m : ℤ) * ((cosExp G P : ℤ) * (D.R.m : ℤ)))) :=
        mul_le_mul_of_nonneg_right hm2 (by positivity)
      _ = _ := by ring
  exact_mod_cast key

theorem exponent_le (P : Pl D.host.E) {C : ℝ} (hC : 2 ≤ C) :
    (D.R.m : ℝ) ^ 3 * bigN D * cosExp G P * Real.log (resCard (Kw P) : ℕ) ≤
      C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz G P := by
  have h1 := log_absNorm_le P
  have hS := placeSz_nonneg G P
  have hmN : (D.R.m : ℝ) ≤ bigN D := by exact_mod_cast m_le_bigN
  rw [ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw]
  have h2 : (cosExp G P : ℝ) * Real.log (Ideal.absNorm P.asIdeal : ℕ) ≤ C * placeSz G P :=
    calc (cosExp G P : ℝ) * Real.log (Ideal.absNorm P.asIdeal : ℕ)
        ≤ (cosExp G P : ℝ) * (2 * Real.log (Ideal.absNorm (P.under (𝓞 D.host.F)).asIdeal)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ = 2 * placeSz G P := by rw [placeSz]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC hS
  have h3 : (D.R.m : ℝ) ^ 3 * bigN D ≤ (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 :=
    calc (D.R.m : ℝ) ^ 3 * bigN D = (D.R.m : ℝ) ^ 2 * bigN D * D.R.m := by ring
      _ ≤ (D.R.m : ℝ) ^ 2 * bigN D * bigN D := mul_le_mul_of_nonneg_left hmN (by positivity)
      _ = _ := by ring
  calc _ = ((D.R.m : ℝ) ^ 3 * bigN D) * ((cosExp G P : ℝ) * Real.log (Ideal.absNorm P.asIdeal : ℕ)) := by ring
    _ ≤ ((D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2) * (C * placeSz G P) :=
      mul_le_mul h3 h2 (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)) (by positivity)
    _ = _ := by ring

end GlobalTheory.ArchTens.VolSize

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstOneMemCuspFormsDefiniteBottom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section
namespace GlobalTheory.BottomCusp

theorem isAniso_neg {D : D7} {A : HSp D} (h : IsAniso A) : IsAniso (GlobalTheory.Grid.neg A) := by
  rintro r C ⟨hr, hC, h0⟩
  refine h r C ⟨hr, hC, ?_⟩
  have e : (GlobalTheory.Grid.neg A).gram = -A.gram := GlobalTheory.Grid.neg_gram A
  rw [e, Matrix.mul_neg, Matrix.neg_mul] at h0
  exact neg_eq_zero.1 h0

theorem const_one_mem_cuspForms_of_anisotropic {D : D7} {V : HSp D} (h : IsAniso V) (θ : GlobalTheory.Mem.Th.InfF D) (A : CptF V) :
    (fun _ => (1 : ℂ)) ∈ A0 θ V A :=
  GlobalTheory.Cusp.mem_cuspForms.2 ⟨⟨isAutFunSm_const θ V 1, fun r C hC => absurd hC (h r C)⟩, .of_invariant fun _ _ _ => rfl⟩

theorem one_mem_A0_of_isBottomTri : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ cA : CptF (GlobalTheory.Grid.neg A), HidaSetting W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s A'.rank cA → (fun _ => (1 : ℂ)) ∈ A0 W.θ (GlobalTheory.Grid.neg A) cA := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j A A' WW X hX t cA _
  exact const_one_mem_cuspForms_of_anisotropic (isAniso_neg (GlobalTheory.Mem.ColAd.isAniso_of_gram hX.std.1)) W.θ cA

end GlobalTheory.BottomCusp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPhaseAt
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeUChar

open IsDedekindDomain

variable {D : D7}

def finIdl (D : D7) : (AE D)ˣ →* (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
  Units.map ((GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp (finPart D)).toMonoidHom

def finY (D : D7) : (AE D)ˣ →* (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ :=
  (Units.map (GlobalTheory.BotFormula.toFinE D).symm.toRingHom.toMonoidHom).comp (finIdl D)

theorem coe_finIdl (x : (AE D)ˣ) : ((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
    FiniteAdeleRing (𝓞 D.host.E) D.host.E) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) := rfl

theorem coe_finY (x : (AE D)ˣ) : ((finY D x : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) =
    (GlobalTheory.BotFormula.toFinE D).symm (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D))) := rfl

def finChar {N : ℕ} (c : HeckeU D N) : (AE D)ˣ →* Circle where
  toFun x := ⟨((c.f (finY D x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (c.unitary _)⟩
  map_one' := Circle.ext (by
    change ((c.f (finY D 1) : ℂˣ) : ℂ) = 1
    rw [map_one, map_one, Units.val_one])
  map_mul' x y := Circle.ext (by
    change ((c.f (finY D (x * y)) : ℂˣ) : ℂ) = ((c.f (finY D x) : ℂˣ) : ℂ) * ((c.f (finY D y) : ℂˣ) : ℂ)
    rw [map_mul, map_mul, Units.val_mul])

theorem coe_finChar {N : ℕ} (c : HeckeU D N) (x : (AE D)ˣ) :
    ((finChar c x : Circle) : ℂ) = ((c.f (finY D x) : ℂˣ) : ℂ) := rfl

def phaseAt (θ : InfFam D) (τ : D.what₂.Tau) : (AE D)ˣ →* Circle :=
  GlobalTheory.ChrEqUnique.phase.comp (Units.map ((θ τ).comp (infPart D)).toMonoidHom)

def infChar (θ : InfFam D) (n : D.what₂.Tau → ℤ) : (AE D)ˣ →* Circle := ∏ τ, phaseAt θ τ ^ n τ

theorem coe_infChar (θ : InfFam D) (n : D.what₂.Tau → ℤ) (x : (AE D)ˣ) :
    ((infChar θ n x : Circle) : ℂ) =
      ∏ τ, (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ n τ := by
  have h : ∀ s : Finset D.what₂.Tau, (((∏ τ ∈ s, phaseAt θ τ ^ n τ : (AE D)ˣ →* Circle) x : Circle) : ℂ) =
      ∏ τ ∈ s, ((phaseAt θ τ x : Circle) : ℂ) ^ n τ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, MonoidHom.mul_apply, Circle.coe_mul, ih,
        MonoidHom.zpow_apply, Circle.coe_zpow]
  exact h Finset.univ

def chi {N : ℕ} (c : HeckeU D N) (θ : InfFam D) (e : ℤ) : (AE D)ˣ →* Circle := (finChar c * infChar θ c.n) ^ e

theorem continuous_phaseAt {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) : Continuous (phaseAt θ τ) :=
  GlobalTheory.ChrEqUnique.continuous_phase.comp (Continuous.units_map _ (GlobalTheory.FockCompare.continuous_comp hθ τ))

theorem continuous_infChar {θ : InfFam D} (hθ : IsInfFam θ) (n : D.what₂.Tau → ℤ) : Continuous (infChar θ n) := by
  have h : ∀ s : Finset D.what₂.Tau,
      Continuous (((∏ τ ∈ s, phaseAt θ τ ^ n τ : (AE D)ˣ →* Circle)) : (AE D)ˣ → Circle) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      change Continuous (fun _ : (AE D)ˣ => (1 : Circle))
      exact continuous_const
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact ((continuous_phaseAt hθ a).zpow (n a)).mul ih
  exact h Finset.univ

theorem finY_incA (a : D.host.Eˣ) :
    finY D (Units.map (incA D).toMonoidHom a) = Units.map (Formalism.MainNotions.StandardLatticesGL3.inc D).toMonoidHom a := by
  refine Units.ext ?_
  rw [coe_finY, RingEquiv.symm_apply_eq]
  change GlobalTheory.LFun.toFinAd D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ (a : D.host.E)) =
    GlobalTheory.LFun.toFinAd ℚ D.host.E ((1 : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) ⊗ₜ (a : D.host.E))
  rw [GlobalTheory.LFun.toFinAd_tmul, GlobalTheory.LFun.toFinAd_tmul, map_one, map_one]

theorem finY_mul_conj (x y : (AE D)ˣ) (h : (y : AE D) = x * cA D x) :
    finY D y = finY D x * Formalism.MainNotions.StandardLatticesGL3.sgU D (finY D x) := by
  refine Units.ext ?_
  apply (GlobalTheory.BotFormula.toFinE D).injective
  rw [Units.val_mul, map_mul]
  change GlobalTheory.BotFormula.toFinE D ((GlobalTheory.BotFormula.toFinE D).symm _) = GlobalTheory.BotFormula.toFinE D ((GlobalTheory.BotFormula.toFinE D).symm _) *
    GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D ((GlobalTheory.BotFormula.toFinE D).symm _))
  rw [GlobalTheory.BotFormula.toFinE_sgA, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, coe_finIdl, coe_finIdl, h,
    RingHom.map_mul, map_mul]
  apply congrArg (fun z => GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) * z)
  have e1 : finPart D (cA D (x : AE D)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) :=
    GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig (x : AE D)
  rw [e1, GlobalTheory.DefU.ClassFin.finAdEquiv_sigR D.sp.cm.sig (D.host.conj : D.host.E ≃+* D.host.E)
    (fun z => Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D z)]

end GlobalTheory.HeckeUChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosineCountOfHyp
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SumSize GlobalTheory.SumCount

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CosCount

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem cosFam_apply_eq_of_mem_supp {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {P : Pl D.host.E} (hP : P ∈ G.pl.W0)
    (hl : P ∈ locPl G t) {β β' : CosFam G t} (hβ : β ∈ S.supp t Φ) (hβ' : β' ∈ S.supp t Φ) :
    β ⟨P, hl⟩ = β' ⟨P, hl⟩ := by
  classical
  have hs : 1 ≤ (locGrid G t P).s := one_le_sLen
  have hkeep : keepAt G P = false := by simp [keepAt, hP]
  have hdep : depthAt G P = cosExp G P := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨h1, h2⟩ := depthAt_w G hv
    rw [h1, h2]
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := ((Good.locGrid_isGood hL G W t hde hc).1 P hl).square 0 hm 0 hm
  haveI := (isUnitVol_unitVol P).1
  have hT := isTensor_Tflip hL W S.B t Φ hde hc hl
  rw [hdep] at hT
  have hO := oneCoset hs (psiAt W P) (unitVol P) (givenLevel G t P) (Tflip W S.B t Φ P) (unifAt P) (cosExp G P) D.R.m_even
    (isUnif_unifAt P) h00.cond hT (fun j hj _ => ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.givenLevel_KO G t P hj)
  have hk : keepAt G (⟨P, hl⟩ : locPl G t).1 = false := hkeep
  have hb := hβ ⟨P, hl⟩
  have hb2 := hβ' ⟨P, hl⟩
  rw [hk] at hb hb2
  exact funext fun i => (hO _ hb i).trans (hO _ hb2 i).symm

theorem supp_subsingleton {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) (hQ : L.Q t = ∅) : (S.supp t Φ).Subsingleton := by
  classical
  intro β hβ β' hβ'
  have hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP; rw [hQ] at hP; exact absurd hP (Finset.notMem_empty _)
  funext ⟨P, hl⟩
  have hP : P ∈ G.pl.W0 := by
    rcases Finset.mem_union.1 hl with h | h
    · exact h
    · rw [hQ] at h; exact absurd h (Finset.notMem_empty _)
  exact cosFam_apply_eq_of_mem_supp hL S t Φ hde hc hP hl hβ hβ'

end GlobalTheory.CosCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFrobeniusSemilinearBijective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

open KaehlerDifferential DividedPowers GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm

namespace GlobalTheory.SmoothLift

private theorem crystallineSmoothLift_natural_local :
    ∃ e₁ : ∀ D : Data, CatCoh.H1 (O D.κ D.t) ≃ₗ[D.R] HH1 D.s,
      ∀ (D D' : Data) (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (h : φ ≫ D.s = D'.s ≫ spMap σ)
        (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∀ c,
        IsPull1 h (e₁ D c) (e₁ D' (m.pull1 c)) := by
  let Λ : ∀ D : Data, Lift D := fun D ↦ Classical.choice (_root_.GlobalTheory.SmoothLift.LiftEx.nonempty_lift D)
  obtain ⟨hr1, -⟩ := _root_.GlobalTheory.PDForm.rel_total_zero
  have E1 : ∀ D : Data, ∃ e : CatCoh.H1 (O D.κ D.t) ≃ₗ[D.R] HH1 D.s, ∀ c h, e c = h ↔ (Λ D).Rel1 c h := fun D ↦
    exists_linearEquiv_of_rel _ (hr1 D (Λ D)).1 (hr1 D (Λ D)).2.1 (hr1 D (Λ D)).2.2
      (_root_.GlobalTheory.PDForm.rel_add_smul D (Λ D)).1 (_root_.GlobalTheory.PDForm.rel_add_smul D (Λ D)).2.1
  choose e₁ he₁ using E1
  refine ⟨e₁, ?_⟩
  intro D D' σ φ φ₀ h m hc c
  exact _root_.GlobalTheory.PDForm.LiftNat.main.1 D D' (Λ D) (Λ D') σ φ φ₀ h m hc c _ _
    ((he₁ D c _).1 rfl) ((he₁ D' _ _).1 rfl)

end GlobalTheory.SmoothLift

namespace GlobalTheory.CrysFlatBC

open GlobalTheory.SmoothLift

theorem bijective_liftSemi_pull1 : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D] [Module.Flat R D] (π : D →+* R) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : R, π (algebraMap R D a) = a) → ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (t : X ⟶ Sp D) (φ : X ⟶ X), Smooth s → IsSeparated s → QuasiCompact s → t = s ≫ spMap π → φ = 𝟙 X → ∀ m : IsMor (dp0 R) s κ t (algebraMap R D) φ, Function.Bijective (liftSemi m.pull1) := by
  intro R D _ _ _ _ π κ hκ hπ X s t φ hs hs' hs'' ht hφ m
  subst hφ ht
  obtain ⟨e₁, n⟩ := GlobalTheory.SmoothLift.crystallineSmoothLift_natural_local
  have hb : spMap π ≫ spMap (algebraMap R D) = 𝟙 _ := by
    rw [← Cris.spMap_comp, show π.comp (algebraMap R D) = RingHom.id R from RingHom.ext hπ, Cris.spMap_id]
  obtain ⟨X', q, s', H⟩ : ∃ (X' : Scheme.{0}) (q : X' ⟶ X) (s' : X' ⟶ Sp D),
      IsPullback q s' s (spMap (algebraMap R D)) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  let i : X ⟶ X' := H.lift (𝟙 X) (s ≫ spMap π) (by rw [Category.assoc, hb]; simp)
  have hiq : i ≫ q = 𝟙 X := H.lift_fst _ _ _
  have his : i ≫ s' = s ≫ spMap π := H.lift_snd _ _ _
  have hp : IsPullback i s s' (spMap π) :=
    IsPullback.of_right (by rw [hiq, hb]; exact IsPullback.id_horiz s) his H
  have k1 : Smooth s' := MorphismProperty.of_isPullback (P := @Smooth) H hs
  have k2 : IsSeparated s' := MorphismProperty.of_isPullback (P := @IsSeparated) H hs'
  have k3 : QuasiCompact s' := MorphismProperty.of_isPullback (P := @QuasiCompact) H hs''
  let D₀ := Data.self s hs hs' hs''
  let D' := Data.ofQuot κ hκ π (fun a ↦ ⟨_, hπ a⟩) rfl s' s i k1 k2 k3 hp _ rfl
  have w : 𝟙 X ≫ 𝟙 X = i ≫ q := by rw [hiq, Category.id_comp]
  have key := n D₀ D' (algebraMap R D) q (𝟙 X) H.w m w
  obtain ⟨e, e', he⟩ : ∃ (e : Cris.H1 (dp0 R) s ≃ₗ[R] HH1 s) (e' : Cris.H1 κ (s ≫ spMap π) ≃ₗ[D] HH1 s'),
      ∀ c, IsPull1 H.w (e c) (e' (m.pull1 c)) := ⟨e₁ D₀, e₁ D', key⟩
  exact (_root_.GlobalTheory.BaseChangeIso.main R D (Cris.H1 (dp0 R) s) (HH1 s) (Cris.H1 κ (s ≫ spMap π)) (HH1 s')
    e.toLinearMap e'.toLinearMap m.pull1 (pullHH1 H.w) e.bijective e'.bijective fun c ↦ (he c).eq_pullHH1).2
    (_root_.GlobalTheory.Div.HypFlatBaseChange.main R D X X' s s' q H hs' hs'')

end GlobalTheory.CrysFlatBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToH1StructureSurjectiveAbelian
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

theorem toH1O_surjective_of_abelian : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Function.Surjective (toH1O (A.hom ≫ 𝟙 _)) := by
  intro hH R _ A _ g hab hdim
  rw [Category.comp_id]
  have hsm : Smooth A.hom := hab.smooth
  have hsep : IsSeparated A.hom := by haveI := hab.proper; infer_instance
  have hqc : QuasiCompact A.hom := by haveI := hab.proper; infer_instance
  have hcmp := GlobalTheory.Published.CrystallineSmoothLift.bijective_cechDeRhamComparison_degreeOne
    GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations A.hom hsm hsep hqc
  have hsurj : Function.Surjective (GlobalTheory.CechDR.toHO1 A.hom) := (hH R A g hab hdim).2.2.2.2.1.2.2
  intro u
  obtain ⟨h, hh⟩ := hsurj (GlobalTheory.CechDR.cmpO A.hom u)
  obtain ⟨c, rfl⟩ := hcmp.2 h
  refine ⟨c, GlobalTheory.CechDR.cmpO_injective R A.left A.hom ?_⟩
  rw [← GlobalTheory.CechDR.structureSheaf_comparison_comm, hh]

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqNsmulOfActs
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo

theorem actG_mem_laHat {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {N : ℕ} {g : G.GAf}
    (hg : g ∈ L.KN N) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) : L.actG g v ∈ LaHat D := by
  obtain ⟨w, hw, e⟩ := hg.1 v hv
  rw [e]
  exact add_mem hv (nsmul_mem hw N)

end GlobalTheory.LKGeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledSemiAbelianCoverFiniteExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_labelledSemiAbelianCover_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))) (lab : Labels D₁.toPre A), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) ∧ OneTrait D₁.toPre A lab ∧ GalEqN n lab := by
  first | exact @GlobalTheory.Mum.exists_desc_labels | exact GlobalTheory.Mum.exists_desc_labels | (intros; apply GlobalTheory.Mum.exists_desc_labels <;> assumption)
end

