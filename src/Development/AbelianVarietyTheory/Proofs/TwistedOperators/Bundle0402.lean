module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0324
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertValuesIffInertLabelsCarriedEigensystems
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1420
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0058
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0746
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0005
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyThetaGeneratorTransport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsCompareByLevelMatchingEvaluation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeEval
section SlopeTestRemainingChoices
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem postOn_eq_of_mem (R : RealDat D A Ks) (F : Face D A) {S : MMap (MP R)} (hS : S ∈ EP R F) :
    postOn (MP R) R.e0 S = S :=
  sub_eq_zero.mp (LinearMap.mem_ker.mp hS.2)

theorem rg_fix (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp X) (φ : L2X X) (h2 : star (Gd.Rg (star φ)) = φ) :
    Gd.Rg (star φ) = star φ :=
  calc Gd.Rg (star φ) = star (star (Gd.Rg (star φ))) := (star_star _).symm
    _ = star φ := by rw [h2]

theorem ev_sub (R : RealDat D A Ks) (v₀ : (MP R).Vec) (S S' : MMap (MP R)) (y : GA D (Yc D 0)) :
    ev (MP R) v₀ (S - S') y = ev (MP R) v₀ S y - ev (MP R) v₀ S' y := by
  simp [ev_apply]
  rfl

end SlopeTestRemainingChoices

theorem evalTieT_of_levelMatch : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (Gd : GoodOp X) (t : GA D (Yc D 0)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → RowLevelMatchAt R F X h t → ∃ c' : ℝ, EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd (iotaX X h).toMulEquiv t c' := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hHost hE Gd t ht hConj hRow
  obtain ⟨c, hc, hsm⟩ := _root_.GlobalTheory.SeeInt.conjModel_of_setting hDS R F X h hLev hGrp hMod hHost hE
  let v₀ : (MP R).Vec := fun τ => ⟨(c τ).symm (X.B.w (X.pl.symm τ)), hsm τ⟩
  have hv₀ : ∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ) := fun τ => by
    simp [v₀]
  have hnorm : ∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1 := fun τ => by
    show ‖(c τ).symm (X.B.w (X.pl.symm τ))‖ = 1
    rw [LinearIsometryEquiv.norm_map]
    exact (X.low _).1
  have hne : ∀ τ, (v₀ τ : (MP R).H τ) ≠ 0 := fun τ h0 => by
    have := hnorm τ
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨σ, red, hA, -, -⟩ := id hRow
  obtain ⟨c0, hc0, hN⟩ := _root_.GlobalTheory.EvalNormTransfer.evalTranslate_norm R F X h hLev hGrp hMod t ht
  refine ⟨c0, Formalism.IndefR.AutomorphicEvaluation.evalTieT_of _ _ _ _ X Gd _ t c0 v₀ hnorm ?_ ?_ ?_⟩
  · intro S hS
    obtain ⟨hmem, hint, -⟩ := hN v₀ hnorm S hS
    have hHH := _root_.GlobalTheory.RowEvalHH.conj_eval_mem_HH R F X h hLev hGrp hMod hHost hE t c v₀ ht hA hc hv₀ S hS _ hmem.coeFn_toLp
    have h1 := _root_.GlobalTheory.GoodProjEval.goodOp_star_ev R F X h hLev hGrp hMod Gd t v₀ hRow S hS.1 _ hmem.coeFn_toLp
    rw [postOn_eq_of_mem R F hS] at h1
    have hfix : Gd.Rg (star (hmem.toLp _)) = star (hmem.toLp _) :=
      rg_fix X Gd _ (Lp.ext (h1.trans hmem.coeFn_toLp.symm))
    refine ⟨⟨hmem.toLp _, Submodule.mem_inf.mpr ⟨hHH, LinearMap.mem_ker.mpr (sub_eq_zero.mpr hfix)⟩⟩,
      hmem.coeFn_toLp, ?_⟩
    show ‖(hmem.toLp _ : L2X X)‖ ^ 2 = _
    rw [Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp hmem]
    exact hint
  · intro Φ
    have hF : star (Φ : L2X X) ∈ goodSub X Gd := Φ.2
    have hfix : Gd.Rg (star (Φ : L2X X)) = star (Φ : L2X X) :=
      sub_eq_zero.mp (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hF).2)
    obtain ⟨S, hSM, hSF⟩ := _root_.GlobalTheory.ConjRowMult.conj_row_eq_eval_mult hDS R F X h hLev hGrp hMod hHost hE t c v₀ ht hConj hc hv₀ (Φ : L2X X)
      (Submodule.mem_inf.mp hF).1
    have h1 := _root_.GlobalTheory.GoodProjEval.goodOp_star_ev R F X h hLev hGrp hMod Gd t v₀ hRow S hSM _ hSF
    rw [hfix, star_star] at h1
    have hz := _root_.GlobalTheory.TranslatedEvalInj.eq_zero R F X h hLev hGrp hMod t v₀ hne S hSM _ rfl (by
      filter_upwards [h1, hSF] with x h1x h2x
      refine (ev_sub R v₀ _ _ _).trans ?_
      exact sub_eq_zero.mpr (h1x.symm.trans h2x))
    exact ⟨S, ⟨hSM, LinearMap.mem_ker.mpr hz⟩, hSF⟩
  · intro S hS h0
    obtain ⟨-, hint, hzero⟩ := hN v₀ hnorm S hS
    have hI : ∫ x, ‖(fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) x‖ ^ 2 ∂(muX X) = 0 := by
      refine (integral_congr_ae ?_).trans (integral_zero _ _)
      filter_upwards [h0] with x hx
      have : ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t) = 0 := hx
      simp [this]
    rw [hI] at hint
    have hre : (ipM (MP R) R.ν0 R.fd0 S S).re = 0 := by
      rcases mul_eq_zero.mp hint.symm with h' | h'
      · exact absurd h' hc0.ne'
      · exact h'
    exact hzero hre

end GlobalTheory.SeeEval
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeEigenvaluesEqOfDualEnlargingLabelsSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.Hk3.LabDetRows

open GlobalTheory.Hk3 GlobalTheory.Hk3.LabDet

theorem dual_eq_of_split : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ SF, GlobalTheory.Hk3.IsSF R SF → ∀ (c c' : Pl D.host.E → List ℤ → ℂ), GlobalTheory.Hk3.EEc R SF c ≠ ⊥ → GlobalTheory.Hk3.EEc R SF c' ≠ ⊥ → (∀ P, GlobalTheory.Hk3.Good R A.μ0 P → Formalism.DivisionValues.conjPl P ≠ P → ∀ k ≤ (Yc D 0).rank, c P (dualLab (splitLab (Yc D 0).rank k)) = c' P (dualLab (splitLab (Yc D 0).rank k))) → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → Formalism.DivisionValues.conjPl P ≠ P → ∀ d, GlobalTheory.Hk3.IsLab (Yc D 0) P d → c P (dualLab d) = c' P (dualLab d) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF c c' hc hc' hs P hP hcP
  obtain ⟨-, hgood, hoff, -⟩ := _root_.GlobalTheory.GoodPrimes.good_primes R F hC.lev
  obtain ⟨n, hβ⟩ := hC.lev.βY 0 (by have := D.R.two_le_m; omega)
  have hlev := fun (P : Pl D.host.E) (hP : Good R A.μ0 P) =>
    _root_.GlobalTheory.LevOp.level_operators (Yc D 0) (R.βY 0) (R.ΛY 0) ((D.host.g 0 * D.host.g 1) ^ n) (R.dat0 R.triv) hβ P
      (by
        rw [Nat.cast_pow]
        exact fun h => (hgood A.μ0 P hP).1 (P.isPrime.mem_of_pow_mem _ h))
      (by
        intro PP hPP
        refine hP PP (hPP.imp id ?_)
        intro h
        exact absurd h (Finset.notMem_empty _))
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  obtain ⟨x', hx', hx0'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc'
  have inj : Function.Injective R.HE.e := hC.models.HE.1
  have hu : R.HE.e x ≠ 0 := fun h => hx0 (inj (by rw [h, map_zero]))
  have hu' : R.HE.e x' ≠ 0 := fun h => hx0' (inj (by rw [h, map_zero]))
  have hp := (LabDet.mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_comap.1 hx)
  have hp' := (LabDet.mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_comap.1 hx')
  have hP' : Good R A.μ0 (Formalism.DivisionValues.conjPl P) := (hgood _ P hP).2.1
  have hcc : Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl P) = P := Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl P
  exact eq_of_split (rRep (R.MY 0)) P hcP _ _ hu hu'
    (fun k hk => mult_lev _ _ _ _ _ hp.1 k ((hlev P hP).1 k hk).1 ((hlev P hP).1 k hk).2)
    (fun k hk => mult_lev _ _ _ _ _ hp'.1 k ((hlev P hP).1 k hk).1 ((hlev P hP).1 k hk).2)
    (fun d => c P (dualLab d)) (fun d => c' P (dualLab d))
    (fun d => c (Formalism.DivisionValues.conjPl P) (dualLab d)) (fun d => c' (Formalism.DivisionValues.conjPl P) (dualLab d))
    (fun d hd => by
      rw [opOf_single, sum_rRep]
      exact hp.2 _ _ _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩))
    (fun d hd => by
      rw [opOf_single, sum_rRep]
      exact hp'.2 _ _ _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩))
    (fun d hd => by
      rw [opOf_single, sum_rRep]
      exact hp.2 _ _ _ (((hlev _ hP').2.1 SF d _).2 ⟨(hoff SF hSF _).2 hP', sphOp_rep hd⟩))
    (fun d hd => by
      rw [opOf_single, sum_rRep]
      exact hp'.2 _ _ _ (((hlev _ hP').2.1 SF d _).2 ⟨(hoff SF hSF _).2 hP', sphOp_rep hd⟩))
    (hs P hP hcP) (hs _ hP' (by rw [hcc]; exact fun h => hcP h.symm))

end GlobalTheory.Hk3.LabDetRows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelEqOfUnipotentFrameChange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option autoImplicit false

namespace GlobalTheory.HeckeInj

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HeckeEx MonoidalCategory CartesianMonoidalCategory MonObj

theorem smul_sum_sub_mem_span {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (cf : Fin n → ℂ) (bv : Fin n → V)
    (s : ℂ) (i : Fin n) (h1 : cf i = 1) (h0 : ∀ j, i < j → cf j = 0) :
    s • ∑ j, cf j • bv j - s • bv i ∈ Submodule.span ℂ (bv '' {j | j < i}) := by
  classical
  have e1 : s • ∑ j, cf j • bv j - s • bv i = ∑ j, (s * (cf j - if j = i then 1 else 0)) • bv j := by
    simp only [mul_sub, sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
    congr 1
    simp
  rw [e1]
  refine Submodule.sum_mem _ fun j _ => ?_
  rcases lt_trichotomy j i with hj | rfl | hj
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · simp [h1]
  · simp [h0 j hj, hj.ne']

theorem exists_lift_pair {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {σ' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (F : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FamilyUnif Xo σ' ty)
    (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ))
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod (F.Di i) ty P) (hP' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod (F.Di j) ty P')
    {p : ℕ} (hp : p.Prime)
    {y y₁ y₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Xo.X} (hy : y = F.u i P) (hy₁ : y₁ = F.u j P') (hy₂ : y₂ = F.u j P')
    (C C' : Subgroup (Over.mk y ⟶ Xo.univ.t.G))
    (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y₁)
    (ψp : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y₁ ⟶ Xo.univ.t.G))
    (ψ' : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y₂)
    (ψp' : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y₂ ⟶ Xo.univ.t.G))
    (hC : ∀ a ∈ C, a ^ p ^ 2 = 1) (hC' : ∀ a ∈ C', a ^ p ^ 2 = 1)
    (hI : Formalism.L2.Pj.IsHkIsog p y y₁ C ψ ψp) (hI' : Formalism.L2.Pj.IsHkIsog p y y₂ C' ψ' ψp') :
    ∃ (gam gam' : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h h' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧
      (∀ a b, (F.Di j).EF (gam' a) (gam' b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam' a) = h' (P a)) ∧
      (∀ (w : Fin g → ℂ) (v : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ pullback Xo.univ.t.G.hom y),
        v ≫ pullback.snd _ _ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => (F.ex i P z).left) w (v ≫ pullback.fst _ _) →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => (F.ex j P' z).left) (h w) (v ≫ ψ ≫ pullback.fst _ _) ∧
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => (F.ex j P' z).left) (h' w) (v ≫ ψ' ≫ pullback.fst _ _)) ∧
      (h = h' → C = C') := by
  subst hy hy₁ hy₂
  obtain ⟨gam, h, h1, h2, -, h4⟩ :=
    GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog _ H Dw l Xo σ' g ty F i j P P' p C ψ ψp hP hP' hp hC hI
  obtain ⟨gam', h', h1', h2', -, h4'⟩ :=
    GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog _ H Dw l Xo σ' g ty F i j P P' p C' ψ' ψp' hP hP' hp hC' hI'
  refine ⟨gam, gam', h, h', h1, h2, h1', h2', fun w v hvs hd => ?_, fun hh => ?_⟩
  · have hfst : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ pullback.fst _ _ = (F.ex i P z).left := fun z =>
      pullback.lift_fst _ _ _
    have d0 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => fibPt Xo.univ.t.G (F.ex i P z)) w v := by
      refine FibreDeriv.isDerivAt0_of_isPullback (IsPullback.of_hasPullback Xo.univ.t.G.hom (F.u i P))
        (fun z => pullback.lift_snd _ _ _) ?_ hvs ?_
      · convert ExpChain.isHolTo_ex F i P hP using 2 with z
        exact hfst z
      · convert hd using 2 with z
        exact hfst z
    refine ⟨?_, ?_⟩
    · have d1 := FibreDeriv.isDerivAt0_comp d0 (ψ ≫ pullback.fst _ _)
      have e1 : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ ψ ≫ pullback.fst _ _ = (F.ex j P' (h z)).left :=
        fun z => by
          rw [← Category.assoc, hI.2.2.1, h4]
          exact pullback.lift_fst _ _ _
      simp only [e1] at d1
      exact (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F j P' hP') h.toLinearMap w _).1 d1
    · have d1 := FibreDeriv.isDerivAt0_comp d0 (ψ' ≫ pullback.fst _ _)
      have e1 : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ ψ' ≫ pullback.fst _ _ = (F.ex j P' (h' z)).left :=
        fun z => by
          rw [← Category.assoc, hI'.2.2.1, h4']
          exact pullback.lift_fst _ _ _
      simp only [e1] at d1
      exact (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F j P' hP') h'.toLinearMap w _).1 d1
  · rw [← hI.2.2.2.2.2.1, ← hI'.2.2.2.2.2.1]
    congr 1
    refine MonoidHom.ext fun x => ?_
    obtain ⟨z, rfl⟩ := F.ex_onto i P hP x
    rw [← h4, ← h4', hh]

end GlobalTheory.HeckeInj

namespace GlobalTheory.HeckeInj

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HeckeEx MonoidalCategory CartesianMonoidalCategory MonObj


set_option maxHeartbeats 1000000 in
theorem eq_of_hkRelFr_frBor : ∀ {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U →
    ∀ (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P p → ∀ (k : U.Comp) (x : (U.X k).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ (C C' : hkKer (Xo := Xo) P p i (CAt σ) (U.un k x)) (z z' w : FrPt Xo c (CAt σ)) (t t' : Ix Dw → (CAt σ)ˣ),
        hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) (CAt σ) (U.un k x) C z →
        hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) (CAt σ) (U.un k x) C' z' →
        (∀ j, j ≠ none → t j = 1) → (∀ j, j ≠ none → t' j = 1) → FrBor t w z → FrBor t' w z' → C = C' := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hU P p i hHP k x C C' z z' w t t' hz hz' ht ht' hB hB'
  obtain ⟨-, -, hall, -, -, g, e, F, ik, φ, -, hpt⟩ := hU
  obtain ⟨Pm, -, per, hPx, hv, -⟩ := hpt k x
  obtain ⟨k'', x'', t'', hB''⟩ := hall w
  obtain ⟨Pm'', -, per'', hPx'', hv'', -⟩ := hpt k'' x''
  obtain ⟨ψ, ψp, hI, hL, -⟩ := hz
  obtain ⟨ψ', ψp', hI', hL', -⟩ := hz'
  have hpp : p.Prime := hHP.2.2.2.1
  have hwx : w.x = F.u (ik k'') Pm'' := hB''.1.trans hPx''
  obtain ⟨gam, gam', h, h', hiso, hh, hiso', hh', hder, hker⟩ :=
    exists_lift_pair F (ik k) (ik k'') Pm Pm'' per per'' hpp hPx (hB.1.trans hwx) (hB'.1.trans hwx) C.1 C'.1
      ψ ψp ψ' ψp' (fun a ha => GlobalTheory.HkPts.pow_eq_one hHP.2.2.2.2 C.2 ha)
      (fun a ha => GlobalTheory.HkPts.pow_eq_one hHP.2.2.2.2 C'.2 ha) hI hI'
  choose c'' hc''1 hc''2 hc''3 using hB''.2.1
  let bv : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ) := fun τ j =>
    ∑ i, Formalism.L2.Pj.toC (c'' τ j i) • (Pi.single (e.symm ⟨τ, i⟩) 1 : Fin g → ℂ)
  have hdw : ∀ τ j, IsDerivAt0 (fun z => (F.ex (ik k'') Pm'' z).left) (bv τ j) (w.u τ j) := fun τ j =>
    (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ Pm'' per'' _ ((U.un k'' x'').u τ) _ (hv'' τ) (c'' τ j)
      (w.u τ j)).1 (hPx'' ▸ hc''3 τ j)
  have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ Pm'' per''
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
  have e1 : spMap (epsMul (1 : ℂ)) = 𝟙 _ := by
    have e0 : epsMul (1 : ℂ) = RingHom.id _ := by
      apply RingHom.ext
      intro a
      ext <;> simp [epsMul]
    rw [e0]
    first | rfl | exact Spec.map_id _ | simp [spMap] | (rw [CommRingCat.ofHom_id]; exact Spec.map_id _)
  letI : Field (Formalism.L2.Pj.CAt σ) := inferInstanceAs (Field ℂ)
  have col : ∀ (zz : Formalism.L2.Pj.FrPt Xo c (Formalism.L2.Pj.CAt σ)) (tt : Formalism.L2.Pj.Ix Dw → (Formalism.L2.Pj.CAt σ)ˣ)
      (ψ0 : pullback Xo.univ.t.G.hom (U.un k x).x ⟶ pullback Xo.univ.t.G.hom zz.x)
      (h0 : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ τ j, Formalism.L2.Pj.IsLieImageH p ψ0 ((U.un k x).u τ j) (zz.u τ j)) →
      (∀ (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ pullback Xo.univ.t.G.hom (U.un k x).x),
        v ≫ pullback.snd _ _ = spMap (algebraMap ℂ (DualNumber ℂ)) →
        IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) w (v ≫ pullback.fst _ _) →
        IsDerivAt0 (fun z => (F.ex (ik k'') Pm'' z).left) (h0 w) (v ≫ ψ0 ≫ pullback.fst _ _)) →
      (∀ j, j ≠ none → tt j = 1) → Formalism.L2.Pj.FrBor tt w zz →
      ∀ τ m, h0 (Pi.single (e.symm ⟨τ, m⟩) 1) - (p : ℂ) • bv τ m ∈
        Submodule.span ℂ (bv τ '' {j | j < m}) := by
    intro zz tt ψ0 h0 hL0 hder0 ht0 hB0 τ m
    choose cf hcf1 hcf2 hcf3 using hB0.2.1
    obtain ⟨wv, hw1, hw2, hw3⟩ := hL0 τ m
    have d2 := hder0 (Pi.single (e.symm ⟨τ, m⟩) 1) wv hw2 (by have q := hv τ m; rw [← hw1] at q; exact q)
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ Pm'' per'' _ (w.u τ) _ (hdw τ) (cf τ m)
      (zz.u τ m)).1 (hwx ▸ hcf3 τ m)
    have d3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul d1 (p : ℂ)
    have e3 : spMap (epsMul (p : ℂ)) ≫ zz.u τ m = wv ≫ ψ0 ≫ pullback.fst _ _ := by
      rw [hw3]
      refine (spMap_epsMul_comp (p : ℂ) ((p : ℂ)⁻¹) _).trans ?_
      rw [inv_mul_cancel₀ hp0, e1]
      exact Category.id_comp _
    rw [e3] at d3
    rw [(tn.2.2 _ (tn.1 _ _ d2)).unique d2 d3]
    refine smul_sum_sub_mem_span (fun j => Formalism.L2.Pj.toC (cf τ m j)) (bv τ) _ m ?_ fun j hj => ?_
    · show Formalism.L2.Pj.toC (cf τ m m) = 1
      rw [hcf1 τ m, ht0 _ (by simp)]
      rfl
    · show Formalism.L2.Pj.toC (cf τ m j) = 0
      rw [hcf2 τ m j hj]
      rfl
  obtain ⟨Hm, -, hpos, hHm⟩ := per''.2.2.2.2
  have hform : ∀ x y, hermForm Hm (h x) (h y) = hermForm Hm (h' x) (h' y) :=
    _root_.GlobalTheory.hermForm_eq_of_im_eq_on_spanning_lattice Pm per.2.2.2.1 Hm h.toLinearMap h'.toLinearMap fun a b => by
      simp only [LinearEquiv.coe_coe]
      rw [← hh, ← hh, ← hh', ← hh', hHm, hHm, hiso, hiso']
  have hhh := _root_.GlobalTheory.FlagEq.eq_of_flag_of_hermForm e Hm hpos h h' hform bv (p : ℂ) hp0
    (col z t ψ h hL (fun w v a b => (hder w v a b).1) ht hB)
    (col z' t' ψ' h' hL' (fun w v a b => (hder w v a b).2) ht' hB')
  exact Subtype.ext (hker hhh)

end GlobalTheory.HeckeInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelSumEqCardTorsionMulTrace
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelSum

theorem sum_ker_eq_card_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x x' : Sp Ω ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (p n : ℕ) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ ((p : ℤ) ^ 2))) (s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x))) (e : Fin n ≃ transKer Xo.univ.t.G Ψ), IsHeckeIsog p (transKer Xo.univ.t.G Ψ) Ψ → IsThGen x' s' → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ p s s' → IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ _ β → IsMulPull Xo.univ.t.G Xo.univ.t.PP p s s₁ → ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → (Nat.card {a : Over.mk x ⟶ Xo.univ.t.G // a ∈ transKer Xo.univ.t.G Ψ ∧ a ^ p = 1} : Z.presheaf.stalk z) * sv Xo.univ.t.G Xo.univ.t.PP s' (r ≫ Ψ) z J = ∑ j, ((val β (r ≫ (translT Xo.univ.t.G (e j).1).left) z J)⁻¹).val * sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ (translT Xo.univ.t.G (e j).1).left) z J := by
  intro E _ _ _ H Dw l Xo Ω _ _ x x' Ψ p n s s' β s₁ e hΨ _ hs' hβ hs Z r z J hJ
  have hG := abelianSchemeLaws_all.1.globalFns
  have hA := GlobalTheory.HeckePoint.isAbelianScheme_of_proper Xo.univ.t Xo.univ.proper
  obtain ⟨β', s₂, n', c, hβ', hs₂, hc, hv⟩ := isThetaTrace_iff.1 hs'
  obtain rfl := hs.unique hG hA hs₂
  have hst : ∀ a ∈ transKer Xo.univ.t.G Ψ, a ≫ Xo.univ.t.act.act H.w0 ∈ transKer Xo.univ.t.G Ψ := by
    intro a ha
    have := Xo.univ.t.act.hom H.w0
    refine (hΨ.2.2.2.1 _).1 ?_
    have h1 : (lift (𝟙 (Over.mk x)) a).left ≫ Ψ =
        (lift (𝟙 (Over.mk x')) (1 : Over.mk x' ⟶ Xo.univ.t.G)).left := (hΨ.2.2.2.1 a).2 ha
    show (lift (𝟙 (Over.mk x)) (a ≫ Xo.univ.t.act.act H.w0)).left ≫ Ψ =
      (lift (𝟙 (Over.mk x')) (1 : Over.mk x' ⟶ Xo.univ.t.G)).left
    rw [← lift_whiskerLeft, Over.comp_left, Category.assoc, hΨ.2.1.2.2 H.w0, reassoc_of% h1, ← Over.comp_left,
      lift_whiskerLeft, MonObj.one_comp]
  let Φ : (Over.mk x ⟶ Xo.univ.t.G) → Z.presheaf.stalk z := fun b =>
    ((val β (r ≫ (translT Xo.univ.t.G b).left) z J)⁻¹).val *
      sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ (translT Xo.univ.t.G b).left) z J
  have hΦ : ∀ a ∈ transKer Xo.univ.t.G Ψ, a ^ p = 1 → ∀ b, Φ (a * b) = Φ b := fun a ha hp b =>
    GlobalTheory.ThetaTransport.term_transl hΨ.2.1 hβ.2.1 hs hst r z hJ a ha hp b
  have h1 : sv Xo.univ.t.G Xo.univ.t.PP s' (r ≫ Ψ) z J = ∑ i, Φ (c i) :=
    (hv Z r z J hJ).trans (Finset.sum_congr rfl fun i _ => by
      simp only [Φ]; rw [hβ'.val_unique hG hA hβ _ z hJ])
  have : Finite (transKer Xo.univ.t.G Ψ) := Finite.of_equiv _ e
  letI := Fintype.ofFinite (transKer Xo.univ.t.G Ψ)
  let T := {a : Over.mk x ⟶ Xo.univ.t.G // a ∈ transKer Xo.univ.t.G Ψ ∧ a ^ p = 1}
  have : Finite T := Finite.of_injective (fun q : T => (⟨q.1, q.2.1⟩ : transKer Xo.univ.t.G Ψ))
    (fun a b h => Subtype.ext (congrArg (fun q : transKer Xo.univ.t.G Ψ => q.1) h))
  letI := Fintype.ofFinite T
  have bij : Function.Bijective fun q : T × Fin n' =>
      (⟨q.1.1 * c q.2, (transKer Xo.univ.t.G Ψ).mul_mem q.1.2.1 (hc.1 _)⟩ : transKer Xo.univ.t.G Ψ) := by
    constructor
    · rintro ⟨a, i⟩ ⟨b, j⟩ h
      have h' : a.1 * c i = b.1 * c j := congrArg Subtype.val h
      obtain rfl : i = j := (hc.2 _ ((transKer Xo.univ.t.G Ψ).mul_mem a.2.1 (hc.1 i))).unique
        (by simpa using a.2.2) (by rw [h']; simpa using b.2.2)
      exact Prod.ext (Subtype.ext (mul_right_cancel h')) rfl
    · intro d
      obtain ⟨i, hi, -⟩ := hc.2 d d.2
      exact ⟨(⟨d * (c i)⁻¹, (transKer Xo.univ.t.G Ψ).mul_mem d.2 ((transKer Xo.univ.t.G Ψ).inv_mem (hc.1 i)), hi⟩, i),
        Subtype.ext (by simp)⟩
  have h2 : ∑ j, Φ (e j).1 = ∑ d : transKer Xo.univ.t.G Ψ, Φ d.1 := Equiv.sum_comp e (fun d => Φ d.1)
  have h3 : ∑ d : transKer Xo.univ.t.G Ψ, Φ d.1 = ∑ q : T × Fin n', Φ (q.1.1 * c q.2) :=
    (Fintype.sum_bijective _ bij _ _ fun q => rfl).symm
  have h4 : ∑ q : T × Fin n', Φ (q.1.1 * c q.2) = ∑ q : T × Fin n', Φ (c q.2) :=
    Finset.sum_congr rfl fun q _ => hΦ _ q.1.2.1 q.1.2.2 _
  show _ = ∑ j, Φ (e j).1
  rw [h2, h3, h4, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [h1, Nat.card_eq_fintype_card]

end GlobalTheory.KernelSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSymmetricPositionLevelFirstSpaceIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead

theorem mem_levS_dat0_PsharpSym_iff : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (β : GL (Fin (Yc D 0).rank) (EAf D)) (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (κ : GA D (Yc D 0)), (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) ↔ κ ∈ GfC (Yc D 0) ∧ finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram ∧ finE (Yc D 0) κ ∈ St β ∧ ∀ PP ∈ Lc.Pg, upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) ∧ (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) → levChi (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) κ = ∏ PP ∈ Lc.Pg, ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) (upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ))))) := by
  intro D T Lc β ψ0 κ
  have hH : ∀ g : G0 Lc.Pg D.R.r, g ∈ (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0).H ↔
      ∀ PP : ↥Lc.Pg, g PP ∈ unipSym (kP PP.1) D.R.r D.R.rS D.R.k := by
    intro g
    show g ∈ Subgroup.pi Set.univ _ ↔ _
    rw [Subgroup.mem_pi]
    simp
  refine ⟨?_, fun hκ => ?_⟩
  · rw [GlobalTheory.SeeConjReord.mem_levelSubgroup_principalDatum_iff, hH]
    simp only [GlobalTheory.SeeConjReord.r0]
    constructor
    · rintro ⟨⟨h0, h1, h2⟩, h3⟩
      exact ⟨h0, h1, h2, fun PP hPP => h3 ⟨PP, hPP⟩⟩
    · rintro ⟨h0, h1, h2, h3⟩
      exact ⟨⟨h0, h1, h2⟩, fun PP => h3 PP.1 PP.2⟩
  · have hm := ((GlobalTheory.SeeConjReord.mem_levelSubgroup_principalDatum_iff Lc _ β κ).1 hκ).2
    rw [GlobalTheory.SeeConjReord.principalRowLevelCharacter_trivial, extendOne_of_mem _ hm]
    letI : IsOneApply ((PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0).H →* ℂˣ) := ⟨fun _ => rfl⟩
    letI : IsMulApply ((PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0).H →* ℂˣ) := ⟨fun _ _ _ => rfl⟩
    erw [prod_apply, Units.coe_prod]
    rw [← Finset.prod_coe_sort Lc.Pg]
    rfl

end GlobalTheory.SeeConjRead
end
end

