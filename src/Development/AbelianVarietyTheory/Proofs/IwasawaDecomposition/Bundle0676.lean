module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyGrid
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0645
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0671
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCharactersAgreeOverEnlargedBase
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.LevExt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gridCharacter_eq_reference_at_base_tuple {D : D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {t : T} (h : L.Is t) (j : ℕ) : L.mu t j = L.mu0 j := by
  have hx := h.xi t
  rw [h.xi_base] at hx
  have e : L.xi t = 1 := MonoidHom.ext (GlobalTheory.ChrEqUnique.eq_one_of_chrEq hx)
  show L.mu0 j * L.xi t = L.mu0 j
  rw [e, mul_one]

theorem Q_eq_empty {D : D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {t : T} (h : L.Is t) : L.Q t = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
  have h1 := (h.Q_ram t PP).2 (Or.inl hPP)
  rw [h.xi_base] at h1
  exact h1 fun _ _ => rfl

theorem isRes_unique' {D : D7} {χ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} {c c' : (kP P)ˣ →* ℂˣ}
    (h : IsRes χ P c) (h' : IsRes χ P c') : c = c' := by
  refine MonoidHom.ext fun u => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  haveI : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h0
    have h1 : a = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
    apply u.ne_zero
    rw [← ha, h1, map_zero]
  rw [h a (Units.mk0 _ ha0) u rfl ha.symm, h' a (Units.mk0 _ ha0) u rfl ha.symm]

section Gen

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}

theorem idc_heq (hP : B'.toPre = B.toPre) {c : (AE a.D)ˣ →* Circle} {c' : (AE a'.D)ˣ →* Circle}
    {χ : Formalism.L2.Host.HChar a.D.host.E} {χ' : Formalism.L2.Host.HChar a'.D.host.E} (hχ : HEq χ' χ) (h : ChrEq c χ)
    (h' : ChrEq c' χ') : HEq c' c := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (χ')) ((by with_unfolding_all exact ((χ) :))) (χ') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (χ')) (χ') (((χ))) (((hχ)))).symm : _))
  clear (hχ)
  subst e))
  have e : @Eq ((AE a.D)ˣ →* Circle) ((by with_unfolding_all exact (c' :))) c := GlobalTheory.ChrEqUnique.idc_unique a.D _ c χ ((by with_unfolding_all exact (h' :))) h
  exact (by with_unfolding_all exact ((heq_of_eq e) :))

theorem res_heq (hP : B'.toPre = B.toPre) {χ : Formalism.L2.Host.HChar a.D.host.E} {χ' : Formalism.L2.Host.HChar a'.D.host.E} (hχ : HEq χ' χ)
    {PP : Pl a.D.host.E} {PP' : Pl a'.D.host.E} (hPP : HEq PP' PP) {c : (kP PP)ˣ →* ℂˣ} {c' : (kP PP')ˣ →* ℂˣ}
    (h : IsRes χ PP c⁻¹) (h' : IsRes χ' PP' c'⁻¹) : HEq c' c := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (χ')) ((by with_unfolding_all exact ((χ) :))) (χ') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (χ')) (χ') (((χ))) (((hχ)))).symm : _))
  clear (hχ)
  subst e))
  ( (
  have e : @Eq (type_of% (PP')) ((by with_unfolding_all exact ((PP) :))) (PP') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (PP')) (PP') (((PP))) (((hPP)))).symm : _))
  clear (hPP)
  subst e))
  have e : ((by with_unfolding_all exact (c' :)) : (kP PP)ˣ →* ℂˣ)⁻¹ = c⁻¹ := isRes_unique' (D := a.D) ((by with_unfolding_all exact (h' :))) h
  have e' : @Eq ((kP PP)ˣ →* ℂˣ) ((by with_unfolding_all exact (c' :))) c := inv_inj.1 e
  exact (by with_unfolding_all exact ((heq_of_eq e') :))

theorem hermitianCodeCharFrame_referenceCharacter_heq (hP : B'.toPre = B.toPre) {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} (hf : HEq f' f) {i : Fin a.D.R.m}
    {i' : Fin a'.D.R.m} (h : (i : ℕ) = i') : HEq ((Top.Fr.at a'.st f').mu0 i') ((Top.Fr.at a.st f).mu0 i) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((f) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((f))) (((hf)))).symm : _))
  clear (hf)
  subst e))
  have e : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i' := (by with_unfolding_all exact ((Fin.ext h : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i') :))
  clear h
  subst e
  exact (by with_unfolding_all exact ((HEq.refl ((Top.Fr.at a.st f).mu0 i)) :))

theorem frat_eta_heq (hP : B'.toPre = B.toPre) {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} (hf : HEq f' f) :
    HEq (Top.Fr.at a'.st f').eta (Top.Fr.at a.st f).eta := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((f) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((f))) (((hf)))).symm : _))
  clear (hf)
  subst e))
  exact (by with_unfolding_all exact ((HEq.refl (Top.Fr.at a.st f).eta) :))

theorem mem_vGs (hP : B'.toPre = B.toPre) {px : PreX B.toPre} {px' : PreX B'.toPre} (hpx : HEq px' px)
    {PP : Pl a.D.host.E} {PP' : Pl a'.D.host.E} (hPP : HEq PP' PP) (h : PP ∈ (B.primes px).vGs) : PP' ∈ (B'.primes px').vGs := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (px')) ((by with_unfolding_all exact ((px) :))) (px') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (px')) (px') (((px))) (((hpx)))).symm : _))
  clear (hpx)
  subst e))
  ( (
  have e : @Eq (type_of% (PP')) ((by with_unfolding_all exact ((PP) :))) (PP') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (PP')) (PP') (((PP))) (((hPP)))).symm : _))
  clear (hPP)
  subst e))
  exact (by with_unfolding_all exact (h :))

end Gen

end GlobalTheory.Mem.R3.Rw.LevExt


open GlobalTheory.Mem.R3.Rw.LevExt in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.R3.Rw.LevExt.levSame_of_levOf : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh → LevSame z Wt' R' := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hf hpx hL'
  have hP : B'.toPre = B.toPre := hE.1
  have hC : z.R.toLevCh.C = Top.Fr.at (w.st Z) f := z.lev.C.trans (by rw [w.C_eq])
  have hC' : R'.toLevCh.C = Top.Fr.at (w'.st Z') f' := hL'.C.trans (by rw [w'.C_eq])
  have hmu0 : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
      HEq (R'.toLevCh.C.mu0 i') (z.R.toLevCh.C.mu0 i) := by
    intro i i' h
    rw [hC, hC']
    exact hermitianCodeCharFrame_referenceCharacter_heq (a := Z) (a' := Z') hP hf h
  have heta : HEq R'.toLevCh.C.eta z.R.toLevCh.C.eta := by
    rw [hC, hC']
    exact frat_eta_heq (a := Z) (a' := Z') hP hf
  have hs := z.lev.is
  have hs' := hL'.is
  refine ⟨fun i i' h => ⟨?_, fun PP' PP hPP hm => ?_⟩, ?_, Q_eq_empty hs', Q_eq_empty hs⟩
  · rw [gridCharacter_eq_reference_at_base_tuple hs', gridCharacter_eq_reference_at_base_tuple hs]
    exact idc_heq (a := Z) (a' := Z') hP (hmu0 i i' h) (hs.mu0 i) (hs'.mu0 i')
  · have hm0 : PP ∈ (B.primes w.px).vGs := by
      have e := z.lev.Pg
      rw [← e]
      exact hm
    have hm' : PP' ∈ R'.toLevCh.Pg := by
      rw [hL'.Pg]
      exact mem_vGs (a := Z) (a' := Z') hP hpx hPP hm0
    exact res_heq (a := Z) (a' := Z') hP (hmu0 i i' h) hPP (hs.chi i PP hm) (hs'.chi i' PP' hm')
  · exact idc_heq (a := Z) (a' := Z') hP heta hs.eta hs'.eta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormLvlOp
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CenTranslate

section Act
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem extV_act (hr : R.grp_red_L) (hj : R.models_jV) (hc : R.models_cV) (i : Fin D.R.m) (t : T0) (g : G)
    (κ : GA D (Vc D i)) (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ) (u : (A.fam.L i t).S.Forms)
    (h : GA D (Vc D i)) :
    R.extV i t (R.jV i t ((A.fam.L i t).r g u)) h =
      (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t (R.jV i t u) (h * κ) := by
  have hT := GlobalTheory.RationalFormsAction.isTranslate_act_V R hr hj i t g u
  have hq : (finHom (Vc D i)).rangeRestrict κ ∈ (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := by
    have h1 := hκ.2.1
    exact ⟨h1, trivial⟩
  let q : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := ⟨_, hq⟩
  have hl : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.LiftsTo (Vc D i) (R.βV i) (R.datVt i t) q (R.eG g) := hκ.2.2
  have e := hT.2 q hl ((finHom (Vc D i)).rangeRestrict h)
  have hk : (R.cV i).ρ κ⁻¹ = 1 := (hc i).1 _ (inv_mem hκ.1)
  have hρ : (R.cV i).ρ (h * κ)⁻¹ = (R.cV i).ρ h⁻¹ := by
    rw [mul_inv_rev, MonoidHom.map_mul, hk, one_mul]
  have hrr : (finHom (Vc D i)).rangeRestrict (h * κ) = (finHom (Vc D i)).rangeRestrict h * (q : Bridge.Gf (Vc D i)) := map_mul _ _ _
  show (R.cV i).ρ h⁻¹ ((R.HV i t).e (R.jV i t ((A.fam.L i t).r g u)) ((finHom (Vc D i)).rangeRestrict h)) =
      (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ •
        (R.cV i).ρ (h * κ)⁻¹ ((R.HV i t).e (R.jV i t u) ((finHom (Vc D i)).rangeRestrict (h * κ)))
  have hch : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q : ℂˣ) : ℂ) :=
    congrArg Units.val ((congrArg (levFn (R.βV i) (flagL (R.datVt i t))) (finE_eq (Vc D i) κ)).trans
      (GlobalTheory.LiftEquivariance.ch_eq q).symm)
  refine (congrArg ((R.cV i).ρ h⁻¹) e).trans ?_
  refine (LinearMap.map_smul _ _ _).trans ?_
  exact congrArg₂ (fun (a : ℂ) w => a • w) ((Units.val_inv_eq_inv_val _).trans (congrArg (·⁻¹) hch.symm))
    (congrArg₂ (fun (f : Module.End ℂ (R.cV i).W) w => f w) hρ.symm (congrArg ((R.HV i t).e (R.jV i t u)) hrr.symm))
end Act

section Read
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D}

theorem liftForm_lvlOp (hOk : A3.A.fam.Ok 1) (i : Fin D.R.m) (t : T) (a : MonoidAlgebra D.what₂.LL G) (ha : ∀ b, b * a = a * b)
    (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL) :
    liftForm A3.A F.P0 F.ψ0 i t (((A3.A.fam.L i t).S.lvlOp (A3.A.fam.L i t).r (A3.A.fam.lvlA F.P0 F.ψ0).P
          (A3.A.fam.lvlA F.P0 F.ψ0).ψ a).mulVec x) =
      ∑ g, a.coeff g • (A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x) :=
  GlobalTheory.ClassSumIdentity.lvlE_lvlOp hOk.conj (A3.A.fam.L i t).S ((hOk.lifts i t).hpos _) (A3.A.fam.L i t).r (hOk.lifts i t).act
    _ _ a ha x

theorem read_rat (hB : R.BaseW F) (hOk : A3.A.fam.Ok 1) (Y : R3.Read (A3 := A3) R F X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (hC : CenRead Y cG) (i : Fin D.R.m) (t : T) (ht : Used0 D (Y.tup t)) (κ : G → GA D (Vc D i))
    (hκ : ∀ g, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) (κ g))
    (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (a : MonoidAlgebra D.what₂.LL G) (ha : ∀ b, b * a = a * b)
    (hza : ∀ g, D.what₂.embLL (a.coeff g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g))
    (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL) (h : GA D (Vc D i)) :
    (Y.IL.jMt (Y.tup t) ht i (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) z
        (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x)))).1 h =
      ∑ g : G, ((z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g) *
        (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) •
        (Y.IL.jMt (Y.tup t) ht i (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x))).1 (h * κ g) := by
  have e1 := congrArg (fun y => (Y.IL.jMt (Y.tup t) ht i y).1 h) (hC i t z a hza x)
  refine e1.trans ?_
  refine (congrFun (Y.mtRead i t ht _) h).trans ?_
  refine Eq.trans ?_ (Finset.sum_congr rfl fun g _ =>
    congrArg (fun w => ((z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g) *
        (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) • w) (congrFun (Y.mtRead i t ht x) (h * κ g)).symm)
  have e2 := liftForm_lvlOp (F := F) hOk i t a ha x
  refine (congrArg (fun v => R.extV i t (R.jV i t v) h) e2).trans ?_
  have e3 := map_sum (R.jV i t) (fun g => a.coeff g • (A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x)) Finset.univ
  have e4 := map_sum (R.extV i t) (fun g => (R.jV i t) (a.coeff g • (A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x))) Finset.univ
  refine (congrArg (fun f => f h) ((congrArg (R.extV i t) e3).trans e4)).trans ?_
  refine (Finset.sum_apply h _ _).trans ?_
  refine Finset.sum_congr rfl fun g _ => ?_
  have e5 := map_smulₛₗ (R.jV i t) (a.coeff g) ((A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x))
  have e6 := LinearMap.map_smul (R.extV i t) (D.what₂.embLL (a.coeff g)) (R.jV i t ((A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x)))
  refine (congrArg (fun f => f h) ((congrArg (R.extV i t) e5).trans e6)).trans ?_
  refine (Pi.smul_apply (D.what₂.embLL (a.coeff g)) (R.extV i t (R.jV i t ((A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x)))) h).trans ?_
  have e7 := extV_act hB.grp.red_L hB.models.jV hB.models.cV i t g (κ g) (hκ g) (liftForm A3.A F.P0 F.ψ0 i t x) h
  refine (congrArg (fun w => D.what₂.embLL (a.coeff g) • w) e7).trans ?_
  refine (smul_smul _ _ _).trans ?_
  exact congrArg (fun c : ℂ => (c * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) •
    R.extV i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) (h * κ g)) (hza g)

end Read

theorem sum_reindex {G H W : Type} [Group G] [Fintype G] [Group H] [Fintype H] [AddCommGroup W] [Module ℂ W] (e : G ≃* H)
    (c : H → ℂ) (ch : G → ℂ) (w : G → W) :
    ∑ g, (c (e g) * ch g) • w g = ∑ g₀, c g₀ • (ch (e.symm g₀) • w (e.symm g₀)) :=
  Fintype.sum_equiv e.toEquiv _ _ fun g => by simp [smul_smul]

theorem main : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A3.A Ks) (F : Face D A3.A) (X0 : BaseLevelRowSide D) (Y : R3.Read (A3 := A3) R F X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), R.BaseW F → A3.A.fam.Ok 1 → CenRead Y cG → ∀ (i : Fin D.R.m) (t : T) (ht : Used0 D (Y.tup t)) (κ : G → GA D (Vc D i)), (∀ g, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) (κ g)) → ∀ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (y : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1)) (h : GA D (Vc D i)), (Y.IL.jMt (Y.tup t) ht i (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) z y)).1 h = ∑ g : G, ((z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g) * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) • (Y.IL.jMt (Y.tup t) ht i y).1 (h * κ g) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F X0 Y cG hB hOk hC i t ht κ hκ z y h
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv G (R.eG.trans cG).toEquiv
  let ad : GA D (Vc D i) → D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.cV i).W := fun h' =>
    { toFun := fun y' => (Y.IL.jMt (Y.tup t) ht i y').1 h'
      map_add' := fun y₁ y₂ => by rw [map_add (f := _)]; rfl
      map_smul' := fun c y₁ => by rw [map_smul]; rfl }
  let ch : G → ℂ := fun g => (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹
  have key : ∀ (g₁ : G0g D.nd) (y' : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1)),
      ad h (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) ⟨GlobalTheory.CenLocAt.avgC g₁, GlobalTheory.CenLocAt.avgC_mem g₁⟩ y') =
        ∑ g : G, ((GlobalTheory.CenLocAt.avgC g₁).coeff ((R.eG.trans cG) g) * ch g) • ad (h * κ g) y' := by
    intro g₁
    have tie : ∀ g, D.what₂.embLL ((GlobalTheory.CenLocAt.avgK D.what₂.LL ((R.eG.trans cG).symm g₁)).coeff g) =
        (GlobalTheory.CenLocAt.avgC g₁).coeff ((R.eG.trans cG) g) := fun g => by
      rw [GlobalTheory.CenLocAt.avgK_coeff D.what₂.embLL (R.eG.trans cG), MulEquiv.apply_symm_apply]
    let F1 : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.cV i).W :=
      (ad h).comp (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) ⟨GlobalTheory.CenLocAt.avgC g₁, GlobalTheory.CenLocAt.avgC_mem g₁⟩)
    let F2 : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.cV i).W :=
      ∑ g : G, ((GlobalTheory.CenLocAt.avgC g₁).coeff ((R.eG.trans cG) g) * ch g) • ad (h * κ g)
    have hb := (D.what₂.jMt_basis (Y.tup t) ((i : ℕ) + 1)
      (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (Y.tup t) ((i : ℕ) + 1)))).2
    have hF : F1 = F2 := by
      refine LinearMap.ext_on_range hb (fun b => ?_)
      obtain ⟨x', hx'⟩ := (Y.eMt i t).surjective (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (Y.tup t) ((i : ℕ) + 1)) b)
      rw [← hx']
      refine (read_rat hB hOk Y cG hC i t ht κ hκ ⟨_, GlobalTheory.CenLocAt.avgC_mem g₁⟩ _ (GlobalTheory.CenLocAt.avgK_comm _ _) tie x' h).trans ?_
      simp only [F2, LinearMap.sum_apply, LinearMap.smul_apply]
      rfl
    intro y'
    have := LinearMap.congr_fun hF y'
    simpa only [F1, F2, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply] using this
  let Φ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) →ₗ[ℂ] (R.cV i).W :=
    { toFun := fun z' => ad h (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) z' y)
      map_add' := fun z₁ z₂ => by simp only [map_add (f := _), LinearMap.add_apply]
      map_smul' := fun c z₁ => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hl := GlobalTheory.CenLocAt.lin_center Φ (fun g₀ => ch ((R.eG.trans cG).symm g₀) • ad (h * κ ((R.eG.trans cG).symm g₀)) y)
    (fun g₁ => (key g₁ y).trans (sum_reindex _ _ _ _)) z
  exact hl.trans (sum_reindex (R.eG.trans cG) _ ch (fun g => ad (h * κ g) y)).symm

end GlobalTheory.CenTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaLiftGridDataUnitGapAllStates
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HeightCounting.Up

theorem nonempty_gridData_allSt : ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => Nonempty (GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩) := by
  intro cDep
  unfold AllSt StepW Step
  refine EvG.imp _root_.GlobalTheory.HeightCounting.Up.sizes_host_at_record fun K _ _ _ _ H => large₂.mono (fun B f T _ h hk _ _ w _ P x => ?_) H
  obtain ⟨-, -, -, -, -, -, w0, hP⟩ := h hk T w x.o.Z
  refine GlobalTheory.HeightCounting.Up.ListModel.nonempty_grid w x.o.Z x.m.z ⟨1, cDep, K.s.b⟩ fun k e => ?_
  have hd := hP.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hd
  fin_cases k
  · exact hd.1 (Or.inr (Or.inr (Or.inr e.symm)))
  · exact hd.2.1 (Or.inr (Or.inr e.symm))

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedReadingsRelatedLocalizedAdelicData
section
noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem yRel_of_pin : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (L : LocAll (lay0 (Dof x))) (m : Moved (oL x L)), m.z = datL x L → m.Coh → ∀ (s : Side0 (oL x L)) (r : ReadPk m s), r.Pin →
      ∀ Y : YT x L s.p0, HEq Y r.Y → YRel L Y := by
  intro K B f T w P x L m hz hC s r hP Y hY
  have hR := CopyRead.repOf_heq x.coh x.r x.pin hC r hP
  obtain ⟨z, intersectionNumber_baseChange, exAt, inGeo, Xg, tr, core, eta, W1, y, tup, t, tA⟩ := m
  dsimp only at hz
  subst hz
  obtain ⟨rY, rZ, rtup, rtupT, rPY, rPW, rjA, rjA0, reMt⟩ := r
  dsimp only at hY
  cases hY
  refine ⟨(by with_unfolding_all exact (hR :)), ?_, ?_⟩
  · intro i y
    have heW := hP.eW
    have hf : HEq t.lf.eW x.m.t.lf.eW := hC.eW.trans x.coh.eW.symm
    have h3 : @Eq (type_of% t.lf.eW) t.lf.eW ((by with_unfolding_all exact (x.m.t.lf.eW :))) :=
      @eq_of_heq (type_of% t.lf.eW) t.lf.eW ((by with_unfolding_all exact (x.m.t.lf.eW :))) ((by with_unfolding_all exact (hf :)))
    with_unfolding_all
      exact (heW i y).trans ((heq_of_eq (congrArg (fun g => g i y) h3)).trans (x.pin.eW i y).symm)
  · intro μ h i y
    have hjMt := hP.jMt
    have hf : HEq t.lf.jMt x.m.t.lf.jMt := hC.jMt.trans x.coh.jMt.symm
    have h3 : @Eq (type_of% t.lf.jMt) t.lf.jMt ((by with_unfolding_all exact (x.m.t.lf.jMt :))) :=
      @eq_of_heq (type_of% t.lf.jMt) t.lf.jMt ((by with_unfolding_all exact (x.m.t.lf.jMt :))) ((by with_unfolding_all exact (hf :)))
    exact (by with_unfolding_all exact (((hjMt μ h i y).trans ((heq_of_eq (congrArg (fun g => g μ i y) h3)).trans (x.pin.jMt μ h i y).symm)) :))

end GlobalTheory.HeightCounting.Fin3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RawPackEqPow
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeightCounting.Rigid

theorem exists_frob (hc : GlobalTheory.TwSys.Cheb) (D : D7) (i : D.ntw.Tw) (Q : Finset (PlE D.host)) {p : ℕ} (hp : p ≠ 0)
    (γ : D.ntw.RCG i Q) :
    ∃ w, w ∉ Q ∧ w ∉ placesOver D.host.E p ∧ ∃ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
      Formalism.ConjugateSelfDual.IsPlaceOver B w ∧ Formalism.ConjugateSelfDual.IsFrob B (Formalism.ConjugateSelfDual.normV w) σ ∧ D.ntw.art i Q σ = γ := by
  classical
  obtain ⟨g, rfl⟩ := D.ntw.art_surj i Q γ
  obtain ⟨w, hwA, -, -, B, hB, -, σ, hσ, hU⟩ := hc D.host.E D.nd.Om (D.ntw.art i Q).ker (D.ntw.art_cont i Q) inferInstance g
    (Q ∪ (placesOver_finite_av D.host.E p hp).toFinset)
  refine ⟨w, fun h => hwA (Finset.mem_union_left _ h),
    fun h => hwA (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h)), B, σ, hB, hσ, ?_⟩
  rwa [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hU

theorem pow_of_tied (hc : GlobalTheory.TwSys.Cheb) {D : D7} (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C)
    (v : D.what₂.places.Pl) (ψ : D.ntw.RCG (C.twI v) (C.Q v) →* (D.ntw.Ok (C.twI v) (C.k' v))ˣ)
    (ι : TwChar.RootIso D (C.twI v) (C.k' v))
    (hF : TwChar.FrobPick (C.twI v) (C.Q v) (C.k' v) ψ ι (tp.psi v)) (hT : PsiChoiceCompatible D cf C tp)
    (htw : TwistedAt D v) (hk : 1 ≤ C.k' v)
    (hL : ∀ z : ℂ, z ^ D.what₂.places.resChar v ^ C.k' v = 1 → ∃ x : D.what₂.LL, D.what₂.embLL x = z) :
    ∃ a : ℕ, a.Coprime (D.ntw.l (C.twI v)) ∧ C.psi' v = ψ ^ a := by
  haveI : NeZero (D.ntw.l (C.twI v) ^ C.k' v) := ⟨pow_ne_zero _ (D.ntw.lPrime _).out.ne_zero⟩
  have hL' : ∀ z : ℂ, z ^ (D.ntw.l (C.twI v) ^ C.k' v) = 1 → ∃ x : D.what₂.LL, D.what₂.embLL x = z := fun z hz =>
    hL z (by rw [← C.twI_l v]; exact hz)
  let j : D.ntw.Ok (C.twI v) (C.k' v) →+* FractionRing (C.Oe v) :=
    (algebraMap (C.Oe v) (FractionRing (C.Oe v))).comp (algebraMap (D.ntw.Ok (C.twI v) (C.k' v)) (C.Oe v))
  have hj : Function.Injective j := (IsFractionRing.injective (C.Oe v) (FractionRing (C.Oe v))).comp (C.Oe_inj v)
  obtain ⟨a, ha, hax⟩ := TwChar.exists_exponent ι (D.ntw.zk_prim _ _) D.what₂.embLL hL' (C.embW v) j hj
  refine ⟨a, Nat.Coprime.coprime_dvd_right (dvd_pow_self _ (by omega)) ha, MonoidHom.ext fun γ => Units.ext ?_⟩
  have hp : D.what₂.places.resChar v ≠ 0 := by rw [← C.twI_l v]; exact (D.ntw.lPrime _).out.ne_zero
  obtain ⟨w, hwQ, hwl, B, σ, hB, hσ, rfl⟩ := exists_frob hc D (C.twI v) (C.Q v) hp γ
  obtain ⟨u, hu, hχ⟩ := hF w hwQ B hB σ hσ
  obtain ⟨x, hx⟩ := hL' ((ι u : ℂˣ) : ℂ) (by rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 (ι u).2, Units.val_one])
  have h1 := hT v htw w hwQ hwl B σ hB hσ x (by rw [hχ, inv_inv]; exact hx)
  have h2 := hax u x hx
  have h3 := hj (h1.symm.trans h2)
  rw [MonoidHom.pow_apply, ← hu]
  exact h3


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem transfer {D₁ D₂ : D7} (h : SameExport D₁ D₂) (p : TwPack D₁) (A : Finset (PlE D₁.host))
    (ι : TwChar.RootIso D₁ p.1 p.2.2.1) (χ : HChar D₁.host.E) (hO : BlochKatoReduction.Gen.PsiOk p.1 A p.2.1 p.2.2.1 p.2.2.2)
    (hF : TwChar.FrobPick p.1 p.2.1 p.2.2.1 p.2.2.2 ι χ) (i₂ : D₂.ntw.Tw) (Q₂ : Finset (PlE D₂.host)) (k₂ : ℕ)
    (χ₂ : HChar D₂.host.E) (hi : HEq i₂ p.1) (hQ : HEq Q₂ p.2.1) (hk : k₂ = p.2.2.1) (hχ : HEq χ₂ χ) :
    ∃ (ψ₂ : D₂.ntw.RCG i₂ Q₂ →* (D₂.ntw.Ok i₂ k₂)ˣ) (ι₂ : TwChar.RootIso D₂ i₂ k₂) (A₂ : Finset (PlE D₂.host)),
      BlochKatoReduction.Gen.PsiOk i₂ A₂ Q₂ k₂ ψ₂ ∧ TwChar.FrobPick i₂ Q₂ k₂ ψ₂ ι₂ χ₂ ∧ D₂.ntw.l i₂ = D₁.ntw.l p.1 ∧
      ∀ a : ℤ, HEq (⟨i₂, Q₂, k₂, ψ₂ ^ a⟩ : TwPack D₂) (GlobalTheory.HeightCounting.twPackPow D₁ a p) := by
  obtain ⟨h1, h2, -, -, -⟩ := h
  obtain ⟨i, Q, k, ψ⟩ := p
  dsimp only at hi hQ hk hO hF ι ⊢
  subst hk
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  cases D₁; cases D₂
  dsimp only at a1 a2 a3
  subst a1; subst a2; subst a3
  cases ‹NData _ _ _›; cases ‹NData _ _ _›
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases ‹@NTw _ _ _ _ _ _ _›; cases ‹@NTw _ _ _ _ _ _ _›
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  subst hi; subst hQ; subst hχ
  exact ⟨ψ, ι, A, hO, hF, rfl, fun _ => HEq.rfl⟩

end GlobalTheory.HeightCounting.Rigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsFiniteGroupActionEqFlagLevelRightTranslaStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowFormsFiniteGroupAction_eq_flagLevelRightTranslation : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      ∃ a : Bridge.ActTie (Bridge.ratF X.toD7.sp.X') P (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q (levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch ((famR X I hX U Xg tr).A.leftGroupActionRight t),
        ∀ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
          eG (a.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)) := by
  first | exact @GlobalTheory.Mem.R3.RowAct.act_tie | exact GlobalTheory.Mem.R3.RowAct.act_tie | (intros; apply GlobalTheory.Mem.R3.RowAct.act_tie <;> assumption)
end

