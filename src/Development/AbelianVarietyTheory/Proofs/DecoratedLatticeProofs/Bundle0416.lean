module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramified
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumStabilizerSplittingCharacters
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0171
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0152
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0422
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalCongruenceFixesDefiniteStepVector
section
noncomputable section

namespace GlobalTheory.SmallFix

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isDetRoot_one (V : HSp D) : IsDetRoot V (1 : GA D V) (1 : (AE D)ˣ) := by
  show ((1 : (AE D)ˣ) : AE D) = _
  rw [map_one, Units.val_one]
  simp

theorem suppPl_one (ε : AF D.host.F) (V : HSp D) : SuppPl ε V (1 : GA D V) := fun i j => by
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]

theorem suppAt_one (e : AE D) (V : HSp D) : Formalism.L2.Theta.SuppAt e V (1 : GA D V) := fun i j => by
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]

theorem inert_one {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {χS : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS 1 om)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hη : ∃ η, IsEtaTilde D η)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : NonSplitAt D v ε) (g : GA D S) (hg : SuppPl ε S g)
    (hst : ∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔
      actO S T g 1 u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True))
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f) :
    om (g, 1) f = f := by
  obtain ⟨η, hη⟩ := hη
  have hψ := hW.std
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨om₀, h0, hv, -⟩ := _root_.GlobalTheory.WeilProduct.exists_weilDatum_etaTilde D ψ hψ S T θ hθ ΛS ΛT hS hT η hη
  obtain ⟨om₁, h1, htw⟩ := _root_.GlobalTheory.WeilChange.exists_weilDatum_twist D ψ hψ S T _ _ ((η ^ S.rank)⁻¹ * χS) ((η ^ T.rank)⁻¹ * 1) om₀ h0
    (GlobalTheory.VacInert.hecke_quot hW.hecS h0.hecS) (GlobalTheory.VacInert.hecke_quot hW.hecT h0.hecT)
    (GlobalTheory.VacInert.resEta_quot hW.resS h0.resS) (GlobalTheory.VacInert.resEta_quot hW.resT h0.resT)
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at h1
  obtain ⟨x, hx, xi, -, x1, x2⟩ := GlobalTheory.VacInert.exists_unit_root hε S g hg
  have hlat : ∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v) ↔
      actO S T g 1 u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v) := fun u => by
    rw [GlobalTheory.VecInvInert.mem_place_iff hε.1, GlobalTheory.VecInvInert.mem_place_iff hε.1, ← hst, ← GlobalTheory.FinWeilO.actO_smul,
      (GlobalTheory.VecInvInert.act_injective g 1).eq_iff]
  have hfix : ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v),
      heisO ψ S T u f = f := fun u hu => by
    obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hε
    have e1 : 2 • (a • u) = u := by
      rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.VecInvInert.idem_smul_eq hε.1 hu]
    have e2 := hvac.1 (a • u)
      (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u (GlobalTheory.PlaceModel.latO_le_top _ hu))
    rwa [e1] at e2
  rw [_root_.GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ S T χS 1 om om₁ hW h1 _ f hf, htw g 1 x 1 hx (isDetRoot_one T), LinearMap.smul_apply,
    hv v ε hε g 1 hg (suppPl_one ε T) hlat f hf hfix]
  simp [hη.2.1 x xi x1 x2]

theorem local_one {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {χS : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS 1 om)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hη : ∃ η, IsEtaTilde D η)
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} (frS : IsFrame βS ΛS) (frT : IsFrame βT ΛT)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) (g : GA D S) (hg : Stab S βS g)
    (sg : SuppPl ε S g) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f) :
    om (g, 1) f = f := by
  have hlat := mem_latO_iff frS frT (h := (1 : GA D T)) hg.2 (Stab.one T βT).2
  by_cases hsp : ∃ e', IsSplitIdem D e' ∧ e' + cA D e' = algebraMap (AF D.host.F) (AE D) ε
  · obtain ⟨e', he', hb⟩ := hsp
    have := _root_.GlobalTheory.VecInv.om_latVac_split D ψ S T ΛS ΛT χS 1 om hW hS hT e' he' g 1 (fun i j => by rw [hb]; exact sg i j)
      (suppAt_one e' T) hlat _ _ (isDetAt_detAt e' he'.1 S g) (isDetAt_detAt e' he'.1 T 1) f hf hvac
    rw [this, splitFacO, map_one, map_one, MonoidHom.one_apply, inv_one, one_mul, Circle.coe_one, one_smul]
  · exact inert_one hW hS hT hη ⟨hε, hsp⟩ g sg hlat f hf hvac

theorem vac_one {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {χS : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS 1 om)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hη : ∃ η, IsEtaTilde D η)
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} (frS : IsFrame βS ΛS) (frT : IsFrame βT ΛT)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f)
    (g : GA D S) (hg : Stab S βS g) : om (g, 1) f = f := by
  let H : Subgroup (GA D S × GA D T) :=
    { carrier := {p | om (p.1, 1) f = f}
      one_mem' := by
        change om ((1 : GA D S), (1 : GA D T)) f = f
        rw [Prod.mk_one_one, map_one, Module.End.one_apply]
      mul_mem' := fun {p q} hp hq => by
        change om ((p * q).1, (1 : GA D T)) f = f
        have e : ((p * q).1, (1 : GA D T)) = (p.1, (1 : GA D T)) * (q.1, 1) := Prod.ext rfl (mul_one 1).symm
        have hq' : om (q.1, 1) f = f := hq
        have hp' : om (p.1, 1) f = f := hp
        rw [e, map_mul, Module.End.mul_apply, hq', hp']
      inv_mem' := fun {p} hp => by
        change om (p⁻¹.1, (1 : GA D T)) f = f
        have hp' : om (p.1, 1) f = f := hp
        have e : (p⁻¹.1, (1 : GA D T)) = (p.1, (1 : GA D T))⁻¹ := Prod.ext rfl inv_one.symm
        rw [e]
        calc om (p.1, (1 : GA D T))⁻¹ f = om (p.1, (1 : GA D T))⁻¹ (om (p.1, 1) f) := by rw [hp']
          _ = f := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hcl : IsClosed (H : Set (GA D S × GA D T)) := by
    have : (H : Set (GA D S × GA D T)) = ⋂ w, {p | om (p.1, 1) f w = f w} := by
      ext p
      rw [Set.mem_iInter]
      exact funext_iff
    rw [this]
    exact isClosed_iInter fun w => isClosed_eq
      ((hW.om_cont f hf w).comp (continuous_fst.prodMk continuous_const)) continuous_const
  exact GlobalTheory.T.mem_closedSubgroup_of_localStabilizerPairs D S T βS βT H hcl (fun v ε hε g' h' hg' _ sg' _ =>
    local_one hW hS hT hη frS frT hε g' hg' sg' f hf hvac) g 1 hg (Stab.one T βT)

end GlobalTheory.SmallFix

end

noncomputable section

namespace GlobalTheory.SmallFix

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW


set_option maxHeartbeats 1000000 in
open Classical in
theorem prin_fixes_stepVec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ (βH : GL (Fin H.rank) (Formalism.IndefR.Lev.EAf D)) (f₀ f : WO A H → ℂ), Formalism.L2.DIV.IsFrame βH (frameLat H) → IsStepVecOf ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) ∅ (fun _ => 1) f₀ f → IsThetaFunO ψ A H f → ∀ κ ∈ prin A β Z, om (κ, 1) f = f := by
  intro D ψ θ A H χA om sA sH hθ hη hW cA' cH hrk β Z hPl βH f₀ f hfrH hv hthf κ hκ
  obtain ⟨hf, e, he, hΘ⟩ := hv
  have dA := frameLat_isSelfDualC A
  have dH := frameLat_isSelfDualC H
  have hlev : Formalism.IndefR.Lev.finE A κ ∈ Formalism.L2.DIV.lev D.sp.cm A.gram β (prinDat A Z) := hκ.2
  have sg : Formalism.IndefR.Lev.finE A κ ∈ Formalism.L2.DIV.St β := Formalism.L2.DIV.parLev_St hlev.1
  have sh : Formalism.IndefR.Lev.finE H 1 ∈ Formalism.L2.DIV.St βH := by rw [map_one]; exact Subgroup.one_mem _
  have h1 : om (κ, 1) f₀ = (1 : ℂ) • f₀ := by
    rw [one_smul]
    exact GlobalTheory.SmallFix.vac_one hW dA dH hη hPl.frame hfrH f₀ hf.2.theta hf.2.lat κ ⟨hκ.1, sg⟩
  have hoG := _root_.GlobalTheory.ChainOnto.RightMove.omegaG_mul_right D A.rank H.rank (prinDat A Z) (fun _ => 1)
    (fun PP => Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE A κ)) (fun PP hP => Formalism.L2.DIV.parLev_g hlev.1 hP) hlev.2
  have h2 := _root_.GlobalTheory.ThetaMove.om_theta_eq_smul D ψ A H χA 1 om hW e _ f₀ _ f
    (_root_.GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std A H (frameLat A) (frameLat H) dA dH e (GlobalTheory.PlaceDatum.idemSum_mul_self he)
      (GlobalTheory.PlaceDatum.infPart_idemSum he) f₀ hf.2.theta) hΘ κ 1
    (_root_.GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D A H (frameLat A) (frameLat H) β βH dA dH hPl.frame hfrH κ 1 sg sh) 1 1 one_ne_zero h1 (fun x => by
      obtain ⟨i1, i2⟩ := _root_.GlobalTheory.FrameRed.frMapO_actO_int_red D A H β βH κ 1 sg sh x
      have i0 : Formalism.IndefR.Datum.IsHalf e (actO A H κ⁻¹ 1⁻¹ x) ↔ Formalism.IndefR.Datum.IsHalf e x :=
        ⟨fun H' => GlobalTheory.AdelicLatMove.actO_actO_inv A H κ 1 x ▸ GlobalTheory.SplitHecke.isHalf_actO κ 1 H',
          fun H' => GlobalTheory.SplitHecke.isHalf_actO _ _ H'⟩
      by_cases hx : Formalism.IndefR.Datum.IsHalf e x ∧ Formalism.IndefR.Datum.IsIntM (frMapO A H β βH x)
      · beta_reduce
        rw [if_pos hx, if_pos ⟨i0.2 hx.1, i1.2 hx.2⟩, funext (i2 hx.2), GlobalTheory.ChainOnto.StepLevLaw.omegaQ_empty,
          GlobalTheory.ChainOnto.StepLevLaw.omegaQ_empty, mul_one, mul_one]
        simp only [map_one, Formalism.L2.DIV.redFn_one, inv_one, Units.val_one, Matrix.one_mul]
        rw [hoG]
        congr 1
        rw [show (prinDat A Z).s = 0 from rfl, Finset.range_zero]
        simp only [Finset.prod_empty, Finset.prod_const_one, MonoidHom.one_apply, inv_one, mul_one]
        exact (congrArg Units.val (show (prinDat A Z).P.chi _ = 1 from rfl)).trans Units.val_one
      · beta_reduce
        rw [if_neg hx, if_neg fun H' => hx ⟨i0.1 H'.1, i1.1 H'.2⟩, mul_zero])
  rw [h2, mul_one, one_smul]

end GlobalTheory.SmallFix

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReadingVectorFixedByClassStabiliserCharacter
section
noncomputable section

namespace GlobalTheory.AdForm.StabInv

section Pair
open Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.ColAd Matrix

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem lT_fnOf (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) (u : ι → GL (Fin n) ℂ) (P : Pol ℂ ι n) :
    lT G u (fnOf G (shiftOf lam) 1 P) = fnOf G (shiftOf lam) 1 (rhoP lam (invTrK u⁻¹) P) := by
  funext y
  have e1 : ∀ τ, ((invTrK u⁻¹ τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ = (u τ : Matrix (Fin n) (Fin n) ℂ) := fun τ => by
    rw [invTrK_coe, Matrix.transpose_transpose, Pi.inv_apply, inv_inv]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lT_apply, fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul, frL, rhoP, MonoidHom.coe_mk,
    OneHom.coe_mk, actP, trAct, detTwK, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_mul, MvPolynomial.smul_eval,
    Formalism.GradedWeylDivisibility.blockAct, eval_aeval_poly, e1, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  have e2 : ∀ τ, detPow ℂ n (invTrK u⁻¹ τ) (lam τ).detShift = (u τ : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift :=
    fun τ => by rw [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, e1]
  simp only [e2, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, shiftOf, Matrix.mul_apply]
  ring

theorem eq_smul_of_pair (G G' : ι → Matrix (Fin n) (Fin n) ℂ) (lam lam' : ι → DomWeight n) (hl : lam = lam') (o : Frames G')
    (ho : ∀ τ, o.1 τ = 1) (k k' : ι → GL (Fin n) ℂ) (hk : k = k') {w : Pol ℂ ι n} (hw : w ∈ VV ℂ lam) (c : ℂ)
    (h : ∀ φ ∈ ValC G lam', ∃ φ' : Frames G → ℂ, lT G k φ' = φ ∧
      pairB lam (polOf G' (shiftOf lam) o φ') w = c * pairB lam (polOf G' (shiftOf lam) o φ) w) :
    w = c • rhoP lam k' w := by
  subst hl hk
  have hp : ∀ P, polOf G' (shiftOf lam) o (fnOf G (shiftOf lam) 1 P) = P := fun P => by
    have e : (fun τ => (o.1 τ)⁻¹) = 1 := funext fun τ => by rw [ho τ]; exact inv_one
    have := polOf_fnOf G' (shiftOf lam) o P
    rw [e] at this
    exact this
  have hm : w - c • rhoP lam k w ∈ VV ℂ lam := sub_mem hw (Submodule.smul_mem _ _ (polyAction_mem_VV lam k hw))
  have h0 := (pairingBNondegenerate_holds ℂ ι n lam).2 ⟨_, hm⟩ fun P => by
    obtain ⟨φ', e1, e2⟩ := h (lT G k (fnOf G (shiftOf lam) 1 P.1))
      (lT_mem G lam k ⟨P.1, by simpa [MvPolynomial.map_id] using map_mem_CSpan (RingHom.id ℂ) lam _ P.2, rfl⟩)
    have e3 : φ' = fnOf G (shiftOf lam) 1 P.1 := by
      have := congrArg (lT G k⁻¹) e1
      rwa [← lT_mul, ← lT_mul, mul_inv_cancel, lT_one, lT_one] at this
    rw [e3, lT_fnOf, hp, hp] at e2
    have e4 := pairingBInvariantK_holds ℂ ι n lam k⁻¹ P.1 (rhoP lam k w)
    have e5 : actP lam k⁻¹ (rhoP lam k w) = w := by
      show (rhoP lam k⁻¹ * rhoP lam k) w = w
      rw [← map_mul, inv_mul_cancel, map_one]; rfl
    rw [e5] at e4
    rw [pairBK_apply]
    show pairB lam P.1 (w - c • rhoP lam k w) = 0
    rw [map_sub, map_smul, e2, ← e4, smul_eq_mul]
    exact sub_self _
  exact sub_eq_zero.1 (congrArg Subtype.val h0)

end Pair

section Law
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
  Formalism.L2.Forms GlobalTheory.Core.Rk GlobalTheory.Core.Rk.Top GlobalTheory.Core.Rk.TopOnto
open GlobalTheory.Mem.ColAd GlobalTheory.Core.Rk.TopLift GlobalTheory.Core.Rk.Top.Model GlobalTheory.PointAtPlaceHom Formalism.MainNotions.StandardLattice Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} {θ : InfFam D} {S : D.what₂.Tau → SPar} {M : DSModel D.sp.X' S}
  {j : SmT M →ₗ[ℂ] (FrP D → ℂ)} {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ}


set_option maxHeartbeats 1000000 in
theorem coset_law_moved (hθ : IsInfFam θ) (hj : IsJ u M j) {b : GA D D.sp.X'} (hb : b ∈ GfC D.sp.X') {γ : GA D D.sp.X'}
    (hγ : γ ∈ GQ D.sp.X') {k h h' : GA D D.sp.X'} {κ x x'} (hk : HasMat k κ) (hJ : b⁻¹ * k * b ∈ J) (hh : HasMat h x)
    (hh' : HasMat h' x') (e : x' = (finPt γ).1 * x * κ) (v : SmT M) :
    ∃ v' : SmT M, lT _ (infPt θ γ) (j v') = j v ∧
      ∀ T ∈ MultT θ M J χ, T v' (h' * b) = χ (b⁻¹ * k * b) * T v (h * b) := by
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ D.sp.X'
  obtain ⟨f, hf, a, ha, rfl⟩ := R.2.2.2.2.2.2.1 γ
  obtain ⟨v', e1, e2⟩ := real_translate (J := J) (χ := χ) hθ hj a ha v
  have e3 : h' = f * h * k := by
    refine hasMat_pt hh' ?_
    have := hasMat_finPt (mul_mem (mul_mem hf hh.1) hk.1)
    rwa [finPt_mul, finPt_mul, finPt_of_hasMat hh, finPt_of_hasMat hk, ← finPt_mul_inf f ha, ← e] at this
  refine ⟨v', by rw [map_mul (infPt θ), infPt_of_fin θ hf, one_mul, e1], fun T hT => ?_⟩
  have e4 : h' * b * a = f * a * (h * b * (b⁻¹ * k * b)) := by
    have e5 : h * b * (b⁻¹ * k * b) = h * k * b := by group
    rw [e5, e3, mul_assoc f a, comm_of_mem _ ha (mul_mem (mul_mem hh.1 hk.1) hb)]
    simp only [mul_assoc]
  rw [e2 T hT, e4, multT_rel' (h * b * (b⁻¹ * k * b)) (f * a * (h * b * (b⁻¹ * k * b))) 1 (fun m hm w => by
    rw [one_mul]; exact (hm.aut w).left _ hγ _) hT, one_mul,
    multT_rel' (h * b) (h * b * (b⁻¹ * k * b)) (χ (b⁻¹ * k * b)) (fun m hm w => hm.lev w _ hJ (h * b)) hT]

end Law

section Chi
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem chi_eq_chr {B : Base} {X : PreX B.toPre} (I : TC B X) (a : I.ι) {Lb U chi y lat st} (hR : I.ReadsP a Lb U chi y lat st)
    (c : (I.stX a).Cl) (s : (I.stX a).Stab c) (κ : U)
    (e' : y c = bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1) * y c * κ.1) :
    ((chi κ : ℂˣ) : ℂ) = B.embLL (((I.stX a).chr c.1 s.1 : B.LLˣ) : B.LL) := by
  let κ0 : (I.stX a).G c.1 := (1, s.1.2.1, s.1.2.2)
  have hgam : (I.stX a).gam c.1 κ0 = 1 := map_one (ufGL B.fields.E (B.R.N B.R.m - 1))
  have hp := GlobalTheory.Mem.Col2.TilX.isPtOf_rat (hR.pt c) (s.1.1)⁻¹
  have hact : ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
      GLG (E := B.fields.E) (n := B.R.N B.R.m - 1) (SG := (B.primes X).vGs) × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) •
      ((I.stX a).rep c).1.1 := by
    have e1 : FrmG.incl _ _ s.1 • ((I.stX a).rep c).1.1 = ((I.stX a).rep c).1.1 :=
      congrArg (fun d : (I.stX a).D c.1 => d.1.1) s.2
    conv_rhs => rw [← e1]
    refine Eq.trans ?_ (smul_smul _ _ _).symm
    have e2 : FrmG.incl _ _ κ0 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
        GLG (E := B.fields.E) (n := B.R.N B.R.m - 1) (SG := (B.primes X).vGs) × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) *
        FrmG.incl _ _ s.1 := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact (inv_mul_cancel _).symm
      · exact (one_mul _).symm
      · exact (one_mul _).symm
    exact congrArg (fun t => t • ((I.stX a).rep c).1.1) e2
  have hyk : y c * κ.1 = ratAd B.host.F (s.1.1)⁻¹ * y c := by
    have e3 : ratAd B.host.F (s.1.1)⁻¹ =
        (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1))⁻¹ := by
      unfold ratAd
      rw [map_inv, map_inv]
      rfl
    rw [e3]
    conv_rhs => rw [e']
    group
  have hq : PtOf (y c * κ.1) ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 := by
    rw [hyk, hact]
    exact hp
  exact hR.chr c κ κ0 hgam hq

theorem sgT_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    (I.perIn u a).sgT = (Formalism.L2.Forms.sgT (D := I.rec7 l Z) u : B.fields.Tau → DomWeight (B.R.N B.R.m - 1)) := by
  funext τ
  obtain ⟨a, ha⟩ := B.R.t_odd
  have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (a + 1) := by
    rw [ha, show B.R.m * (2 * a + 1 + 1) = 2 * (B.R.m * (a + 1)) by ring]; omega
  have e2 : (B.R.t + 1) / 2 = a + 1 := by omega
  show GlobalTheory.Mem.Col2.shW (B.wts.sgW τ) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))) =
    Formalism.L2.Forms.shW (B.wts.sgW τ) ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ)
  rw [e1, e2]
  unfold GlobalTheory.Mem.Col2.shW Formalism.L2.Forms.shW
  congr 1

theorem star_eq_inv {H K : Type} [Group H] [Finite H] [Field K] (φ : H →* Kˣ) (σ : K →+* ℂ) (s : H) :
    star (σ (φ s : K)) = (σ (φ s : K))⁻¹ := by
  have e : σ (φ s : K) ^ Nat.card H = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one, map_one]
  exact (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one e Nat.card_pos.ne')).symm

end Chi

section Main
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.TopLift GlobalTheory.Core.Rk.TopOnto GlobalTheory.Core.Rk.Top.Model


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem reading_stab_inv : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ : ℕ → ℂ), PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (a : I.ι), ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → ∀ f : CXP R P t, ∀ (c : (I.stX a).Cl) (w : Formalism.L2.DIV.Pol ℂ (I.rec7 l Z).what₂.Tau (B.R.N B.R.m - 1)), w ∈ Formalism.L2.DIV.VV ℂ (I.perIn u a).sgT → (∀ v h, GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 → f.1 v (h * g.bT) = Formalism.L2.DIV.pairB (I.perIn u a).sgT (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT) (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (j v)) w) → ∀ s : (I.stX a).Stab c, w = (B.embLL ((I.stX a).chr c.1 s.1 : B.LL))⁻¹ • Formalism.L2.DIV.rhoP (I.perIn u a).sgT (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) ((I.stX a).gam c.1 s.1)) w := by
  intro B X I hI hP l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ hX j hj P t a bad K hR hb hL f c w hw hf s
  have hθ : IsInfFam R.θ := hX.inf
  have hst : (K.stabI c s).1 = (I.stX a).gam c.1 s.1 := hR.stab c s
  obtain ⟨κ₀, hκ₀, e0⟩ := (K.stabI_range c (K.stabI c s)).1 ⟨s, rfl⟩
  let κ : K.lev.U := ⟨κ₀, hκ₀⟩⁻¹
  have e1 : (K.y c).1 = Formalism.UG.bc (Formalism.UG.inclE (F := (I.rec7 l Z).host.F)
      (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (K.stabI c s).1 * (K.y c).1 * κ.1 := by
    rw [← e0]
    show _ = (K.y c).1 * κ₀ * (K.y c).1⁻¹ * (K.y c).1 * κ₀⁻¹
    group
  have e2 := chi_eq_chr I a hR c s κ (by
    have h0 := e1
    rw [hst] at h0
    exact h0)
  haveI : Finite ((I.stX a).Stab c) := ((I.fm l u a).stabPFin c : Finite _)
  have e3 := star_eq_inv (((I.stX a).chr c.1).comp (Subgroup.subtype _ : (I.stX a).Stab c →* _)) B.embLL s
  obtain ⟨γ, hγ, e4, e5⟩ := exists_ratPt hθ (rankP (I.rec7 l Z)) (K.stabI c s).1 (K.stabI c s).2
  obtain ⟨k, hk⟩ := hasMat_exists (D := I.rec7 l Z) ⟨κ.1, ((K.lev.U_eq _).1 κ.2).1⟩
  obtain ⟨h, hh⟩ := hasMat_exists (D := I.rec7 l Z) (K.y c)
  have e6 : levChi _ R.βX (datXP R P t) (g.bT⁻¹ * k * g.bT) = (B.embLL ((I.stX a).chr c.1 s.1 : B.LL))⁻¹ :=
    (hL.2 k κ hk).trans ((congrArg star e2).trans e3)
  refine eq_smul_of_pair (gramC (gramP (I.rec7 l Z)) (embT (I.rec7 l Z))) _ _ _ (sgT_eq I l Z u a)
    (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (fun _ => rfl) (infPt R.θ γ) _ ?_ hw _ fun φ hφ => ?_
  · funext τ
    refine Units.ext ((e5 τ).trans ?_)
    rw [hst]
    ext p q
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  · obtain ⟨v, rfl⟩ := (hj.range ▸ hφ : φ ∈ LinearMap.range j)
    obtain ⟨v', e7, e8⟩ := coset_law_moved (χ := levChi _ R.βX (datXP R P t)) hθ hj hb hγ hk ((hL.1 k).2 ⟨κ, hk⟩) hh hh
      (e1.trans (congrArg (· * (K.y c).1 * κ.1) e4.symm)) v
    refine ⟨j v', e7, ?_⟩
    have e9 := e8 f.1 f.2
    rw [hf v' h hh, hf v h hh, e6] at e9
    exact e9

end Main

end GlobalTheory.AdForm.StabInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhat
section
noncomputable section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

namespace GlobalTheory.SchSchwartzAll

theorem sch_sub {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {A B : HSp D} {ν : Measure (WO A B)}
    {𝓨 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓨) {f f' : WO (dblSp A) B → ℂ}
    (hf : IsThetaFunO ψ (dblSp A) B f) (hf' : IsThetaFunO ψ (dblSp A) B f') :
    sch ψ A B ν 𝓨 (f - f') = sch ψ A B ν 𝓨 f - sch ψ A B ν 𝓨 f' := by
  funext x
  have h1 := (dblDec A).integrableOn_mixS hψ hν hf x 0
  have h2 := (dblDec A).integrableOn_mixS hψ hν hf' x 0
  refine Eq.trans ?_ (integral_sub h1 h2)
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [HypDec.integrandS_eq, Pi.sub_apply, mul_sub]

theorem schSchwartz : ∀ D : D7, SchSchwartz D := by
  intro D ψ hψ θ hθ A B ν 𝓨 hν
  refine ⟨fun f hf => (_root_.GlobalTheory.SchwartzIff.isSchwartzBruhat_iff_mem_schwartzA D θ hθ _ _ _).1 (GlobalTheory.T.isSchwartzBruhat_doubledPairSchrodingerFunction D ψ hψ A B ν 𝓨 hν f hf),
    fun φ hφ => _root_.GlobalTheory.SchwOnto.schw_onto D ψ hψ A B ν 𝓨 hν φ ((_root_.GlobalTheory.SchwartzIff.isSchwartzBruhat_iff_mem_schwartzA D θ hθ _ _ _).2 hφ), fun f f' hf hf' h => ?_⟩
  refine sub_eq_zero.1 (_root_.GlobalTheory.Core.Rk.SchwInj.eq_zero_of_sch_eq_zero D ψ hψ A B ν 𝓨 hν (f - f') (GlobalTheory.OrientedHeis.theta_sub hf hf') ?_)
  rw [sch_sub hψ.1.1 hν hf hf', h, sub_self]

end GlobalTheory.SchSchwartzAll

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointIdempotentsOrthogonalSumPlaces
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PutIn

theorem orth_and_eq_eSum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (J : List ι) (P : Pl D → Prop), Places p J P → ∀ (Pset : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e Pset → (∃ eq : ι ≃ Pset, ∀ i, Formalism.L2.NTheta.IsIdemAt (p i).e (eq i).1) → (∀ i j, i ≠ j → (p i).e * (p j).e = 0) ∧ e = GlobalTheory.FinPl.PutIn.eSum p J := by
  intro D k _ _ _ _ ι p J P hP Pset e he hq
  classical
  obtain ⟨q, hq⟩ := hq
  refine ⟨fun i j hij => ?_, ?_⟩
  · refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (p i).split (p j).split).resolve_left fun h => hij ?_
    exact q.injective (Subtype.ext (GlobalTheory.PlaceVec.isIdemAt_inj (hq i) (h ▸ hq j)))
  · obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
    haveI : Fintype ι := Fintype.ofList J hP.all
    have h1 : ∀ i, es (q i).1 = (p i).e := fun i =>
      GlobalTheory.SplitHeckeAdj.idem_unique D.sp.X' (hq i) (hes _ (q i).2)
    have h2 : J.toFinset = Finset.univ := Finset.eq_univ_of_forall fun i => List.mem_toFinset.2 (hP.all i)
    rw [eSum, ← List.sum_toFinset _ hP.nodup, h2, ← Finset.sum_coe_sort Pset es, ← Equiv.sum_comp q]
    exact Finset.sum_congr rfl fun i _ => h1 i

end GlobalTheory.FinPl.PutIn

end
end

