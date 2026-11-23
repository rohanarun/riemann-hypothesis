module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0001
public import Formalism.LocalRingCardinality.HostCls
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeOfMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenStageFunctionRowArrowEqHalfExtension
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.CosetRow


open Classical in
theorem givenFn_right_eq_extFn {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}
    (hL : L.Is μ₀) (B : Frames G) (t : T) (Φ : G.Datum) {e e₀ : AE D} (he : IsIdemSum e (locPl G t))
    (he₀ : IsIdemSum e₀ G.pl.W0)
    (hAA : ∀ w ∈ L.Q t, w ∉ G.pl.W0 → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) (i : Fin D.R.m) :
    GlobalTheory.FlipStart.givenFn B t Φ e (.right i 0) = GlobalTheory.CosetRow.extFn e₀ (e - e₀)
      (latO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0)) (G.latS (.chi (i : ℕ) 0) : Set _)
        (G.latT (.chi (i : ℕ) 0) : Set _) fun _ => True) (cosInd e₀ (Φ i)) := by
  have hsub : G.pl.W0 ⊆ locPl G t := Finset.subset_union_left
  obtain ⟨he₁, h01⟩ := _root_.GlobalTheory.IdemSubDiff.isIdemSum_sdiff he he₀ hsub
  have hee : e₀ + (e - e₀) = e := add_sub_cancel e₀ e
  have h0 := GlobalTheory.PlaceDatum.idemSum_mul_self he₀
  have h1 := GlobalTheory.PlaceDatum.idemSum_mul_self he₁
  obtain ⟨-, c0, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he₀
  obtain ⟨-, c1, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he₁
  have hAA' : ∀ w ∈ locPl G t \ G.pl.W0, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := fun w hw => by
    rw [Finset.mem_sdiff] at hw
    exact hAA w ((Finset.mem_union.1 hw.1).resolve_left hw.2) hw.2

  have hmap : ∀ (a : AE D) (w : Pl D.host.E), cpt (D := D) w (toEAf D a) = 1 →
      ∀ x : WO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0)),
      (a • x).map (cpt (D := D) w ∘ toEAf D) = x.map (cpt (D := D) w ∘ toEAf D) := fun a w ha x => by
    ext p q
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Function.comp_apply, RingHom.map_mul, ha, one_mul]
  funext x
  unfold GlobalTheory.FlipStart.givenFn GlobalTheory.CosetRow.extFn
  rw [hee]
  by_cases hx : IsHalf e x
  swap
  · rw [if_neg hx, if_neg hx]
  rw [if_pos hx, if_pos hx]

  have hfac : ∀ w, givenDatum t w B Φ (edgeOf (.right i 0)) (locArg B t w (.right i 0) x) =
      if B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0)) ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩
        (x.map (cpt (D := D) w ∘ toEAf D)) ∈ cosetSet t w B i.2 (Φ i) then 1 else 0 := fun w => by
    have hh : (i : ℕ) < D.R.m ∧ 0 ≤ D.R.m := ⟨i.2, Nat.zero_le _⟩
    have hla : locArg B t w (.right i 0) x = B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0))
        ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩ (x.map (cpt (D := D) w ∘ toEAf D)) := by
      exact dif_pos hh
    rw [hla]
    simp only [edgeOf, givenDatum, dif_pos i.2, Set.indicator_apply, Pi.one_apply, Fin.eta]
  rw [Finset.prod_congr rfl fun w _ => hfac w, ← Finset.prod_sdiff hsub, Finset.prod_boole, Finset.prod_boole]
  have hx0 : IsHalf e₀ (e₀ • x) := fun p q => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h0]
  have hx1 : IsHalf (e - e₀) ((e - e₀) • x) := fun p q => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h1]
  have k0 : cosInd e₀ (Φ i) (e₀ • x) = if ∀ w ∈ G.pl.W0, B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0))
      ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩ (x.map (cpt (D := D) w ∘ toEAf D)) ∈ cosetSet t w B i.2 (Φ i)
      then 1 else 0 := by
    unfold cosInd
    rw [Set.indicator_apply, Pi.one_apply]
    refine if_congr ?_ rfl rfl
    rw [GlobalTheory.FunObj.Comparison₂.mem_cosSet_iff_cosetSet B t hL he₀ i.2 (Φ i) hx0]
    exact forall₂_congr fun w hw => by rw [hmap e₀ w (c0 w hw)]
  have k1 : halfInd (e - e₀) (latO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0)) (G.latS (.chi (i : ℕ) 0) : Set _)
        (G.latT (.chi (i : ℕ) 0) : Set _) fun _ => True) ((e - e₀) • x) = if ∀ w ∈ locPl G t \ G.pl.W0,
      B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0))
      ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩ (x.map (cpt (D := D) w ∘ toEAf D)) ∈ cosetSet t w B i.2 (Φ i)
      then 1 else 0 := by
    unfold halfInd
    refine if_congr ?_ rfl rfl
    rw [and_iff_left hx1, GlobalTheory.T.mem_completedGridArrowLattice_iff_integral_frameMatrix hL B t he₁ hAA' i _ hx1]
    refine forall₂_congr fun w hw => ?_
    rw [hmap _ w (c1 w hw), GlobalTheory.FunObj.Comparison₂.cosetSet_of_notMem B t w hL (Finset.mem_sdiff.1 hw).2 i.2 (Φ i)]
    rfl
  rw [k0, k1, mul_comm]

end GlobalTheory.CosetRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodVOfGoodL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
open Formalism.IndefR.CxPass Formalism.IndefR.CxPass.LevelOperators

namespace GlobalTheory.GoodModelVec

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 4000000 in
theorem actL_coord (R : RealDat D A Ks) (hr : R.grp_red_L) (hj : R.models_jV) (i : Fin D.R.m) (hc : (R.cV i).Is) (t : T0)
    (g : G) (x : (A.fam.L i t).S.Forms) (ℓ : (R.cV i).W →ₗ[ℂ] ℂ) :
    actL (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) (fun h => ℓ (R.extV i t (R.jV i t x) h)) =
      fun h => ℓ (R.extV i t (R.jV i t ((A.fam.L i t).r g x)) h) := by
  have hT := GlobalTheory.RationalFormsAction.isTranslate_act_V R hr hj i t g x
  have hk : ∃ κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ := by
    obtain ⟨κ, h1, -⟩ := GlobalTheory.LiftEquivariance.exists_adelic_lift hT
    exact ⟨κ, h1⟩
  funext h
  refine (GlobalTheory.SecLift.actL_apply hk _ h).trans ?_
  have hs := hk.choose_spec
  have e1 := finE_eq (Vc D i) hk.choose
  have hq : (finHom (Vc D i)).rangeRestrict hk.choose ∈ (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := by
    show Formalism.UG.bc (swapAE D) (finHom (Vc D i) hk.choose) ∈ lev _ _ _ _
    rw [← e1]
    exact ⟨hs.2.1, Subgroup.mem_top _⟩
  have hl : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.LiftsTo (Vc D i) (R.βV i) (R.datVt i t) ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩ (R.eG g) := by
    show rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) (finHom (Vc D i) hk.choose)) = R.eG g
    rw [← e1]; exact hs.2.2
  have hT2 : ∀ u, (R.HV i t).e ((R.jV i t) (((A.fam.L i t).r g) x)) u =
      ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩)⁻¹ : ℂˣ) : ℂ) •
        (R.HV i t).e ((R.jV i t) x) (u * (finHom (Vc D i)).rangeRestrict hk.choose) := hT.2 _ hl
  have h2 := GlobalTheory.SecLift.coord_translate (R.cV i) hc hs.1 _ hT2 ℓ h
  have ec := GlobalTheory.LiftEquivariance.ch_eq (V := Vc D i) (β := R.βV i) (L := R.datVt i t) ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩
  have e2 : levFn (R.βV i) (flagL (R.datVt i t)) (Formalism.UG.bc (swapAE D) ((finHom (Vc D i)) hk.choose)) =
      levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) hk.choose) := by rw [e1]
  have hc' : ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩ : ℂˣ)) : ℂ) =
      levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) hk.choose := congrArg Units.val (ec.trans e2)
  rw [Units.val_inv_eq_inv_val, hc'] at h2
  exact h2.symm


set_option maxHeartbeats 4000000 in
theorem goodV_of_fix (R : RealDat D A Ks) (hr : R.grp_red_L) (hj : R.models_jV) (i : Fin D.R.m) (hc : (R.cV i).Is)
    (x : (A.fam.L i A.μ0).S.Forms) (hx : opF (A.fam.L i A.μ0).r (idemOf A.X) x = x) :
    GlobalTheory.LiftRows.GoodV R i (R.jV i A.μ0 x) := by
  intro ℓ
  let Φ : (R.HV i A.μ0).H →ₗ[ℂ] (GA D (Vc D i) → ℂ) := ℓ.compLeft (GA D (Vc D i)) ∘ₗ R.extV i A.μ0
  have hΦ : ∀ y, Φ y = fun h => ℓ (R.extV i A.μ0 y h) := fun _ => rfl
  have key : ∀ g, Φ (R.jV i A.μ0 ((A.fam.L i A.μ0).r g x)) =
      actL (Vc D i) (R.βV i) (R.datVt i A.μ0) (R.eG g) (Φ (R.jV i A.μ0 x)) := fun g =>
    (actL_coord R hr hj i hc A.μ0 g x ℓ).symm
  have hs : ∀ a, RealDat.eC (A := A) (sg0 D A) a = D.what₂.embLL ((idemOf A.X).coeff a) := fun a => by
    show sg0 D A _ = _
    rw [sg0, sgAt_mk D.what₂.embLL R.hv0]
  have e1 : Φ (R.jV i A.μ0 (opF (A.fam.L i A.μ0).r (idemOf A.X) x)) =
      gaL (Vc D i) (R.βV i) (R.datVt i A.μ0) R.eG (RealDat.eC (A := A) (sg0 D A)) (Φ (R.jV i A.μ0 x)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [opF, gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, LinearMap.map_smulₛₗ, key, hs, RingHom.id_apply]
    rfl
  rw [← hΦ, ← e1, hx]

noncomputable def goodSub (R : RealDat D A Ks) (i : Fin D.R.m) : Submodule ℂ (R.HV i A.μ0).H :=
  ⨅ ℓ : (R.cV i).W →ₗ[ℂ] ℂ, LinearMap.ker
    (gaL (Vc D i) (R.βV i) (R.datVt i A.μ0) R.eG (RealDat.eC (A := A) (sg0 D A)) ∘ₗ (ℓ.compLeft (GA D (Vc D i)) ∘ₗ R.extV i A.μ0) -
      ℓ.compLeft (GA D (Vc D i)) ∘ₗ R.extV i A.μ0)

theorem mem_goodSub (R : RealDat D A Ks) (i : Fin D.R.m) (y : (R.HV i A.μ0).H) :
    y ∈ goodSub R i ↔ GlobalTheory.LiftRows.GoodV R i y := by
  simp only [goodSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

end GlobalTheory.GoodModelVec


open GlobalTheory.GoodModelVec in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.goodV_of_goodL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ (j : Fin D.R.m) (y : (R.toCx3 F).FLC j A3.A.fam.μ0), y ∈ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j → GoodV R.toRealDat j (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hC _ _ _ j y hy
  have hM := hC.base.models
  have hr := hC.base.grp.red_L
  have hfix : ∀ x ∈ BlockGood.goodR (A3.fam3.F.L j A3.A.fam.μ0) (A3.fam3.F.lvlA F.P0 F.ψ0),
      opF (A3.A.fam.L j A3.A.fam.μ0).r (idemOf A3.A.X) x = x := by
    intro x hx
    rw [goodR_eq] at hx
    obtain ⟨z, rfl⟩ := hx
    have hid := opF_goodAt_idem (A3.A.fam.L j A3.A.fam.μ0).r A3.A.X hok.ok2.irr ⊥ 1
    rw [goodAt_bot] at hid
    show opF _ (idemOf A3.A.X) (opF _ (idemOf A3.A.X * lvlIdem F.P0 F.ψ0⁻¹) z) = opF _ (idemOf A3.A.X * lvlIdem F.P0 F.ψ0⁻¹) z
    rw [opF_mul, LinearMap.comp_apply]
    exact LinearMap.congr_fun hid _
  have hy' : y ∈ Submodule.span ℂ ((R.toCx3 F).jL j A3.A.fam.μ0 ''
      (BlockGood.goodR (A3.fam3.F.L j A3.A.fam.μ0) (A3.fam3.F.lvlA F.P0 F.ψ0) : Set _)) := hy
  rw [← mem_goodSub]
  clear hy
  induction hy' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    exact (mem_goodSub _ _ _).2 (goodV_of_fix R.toRealDat hr hM.jV j (hM.cV j) x (hfix x hx))
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ (Links.cj (twAt D.what₂.embLL A3.A.v0) c) ha
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridExistenceOfFunctoriality
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.RowEx.GridExPf

open _root_.Formalism.L2.Col GlobalTheory.GridPlaces

variable {D : D7}

theorem under_conjugatePrime_ne_of_class {p : ℕ} (hp : p.Prime) (hcl : D.host.cls p = .splitK) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : (p : 𝓞 D.host.E) ∈ P.asIdeal) : (conjPrime₂ P).under (𝓞 D.host.K) ≠ P.under (𝓞 D.host.K) := by
  intro h
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨h2, hd, hj⟩ : p ≠ 2 ∧ p ≠ D.host.d ∧ jacobiSym (-(D.host.d : ℤ)) p = 1 := by
    obtain ⟨h1, -, h3, h4⟩ := (primeClass_eq_splitK_iff D.host.toHostRaw).1 hcl
    exact ⟨UpperTheory.Small.ne_two D.host h1, h3, h4⟩
  obtain ⟨s, hs⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  obtain ⟨s, rfl⟩ := ZMod.intCast_surjective s
  obtain ⟨m, hm⟩ : (p : ℤ) ∣ s * s + D.host.d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hs ⊢
    rw [← hs]; ring
  have hsq := D.host.sqrtMinusD_sq
  have hint : IsIntegral ℤ D.host.sqrtMinusD := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hsq]
    have := (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := (D.host.d : ℤ))).neg
    simpa using this
  let b : 𝓞 D.host.K := ⟨⟨D.host.sqrtMinusD, IntermediateField.mem_adjoin_simple_self ℚ _⟩,
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ D.host.K D.host.E) Subtype.val_injective).1 hint⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = algebraMap (𝓞 D.host.K) (𝓞 D.host.E) b := ⟨_, rfl⟩
  have hβ1 : (β : D.host.E) = D.host.sqrtMinusD := by rw [hβ]; rfl
  have hβ2 : β * β = -(D.host.d : 𝓞 D.host.E) := RingOfIntegers.ext (by simpa [hβ1, sq] using hsq)
  have hβ3 : cO D.host.E β = -β := RingOfIntegers.ext (by
    show star (β : D.host.E) = ((-β : 𝓞 D.host.E) : D.host.E)
    rw [bridge_star_holds D.R D.host, hβ1, D.host.conj_sqrtMinusD, ← hβ1]
    simp)
  have key : ∀ t : ℤ, (t : 𝓞 D.host.E) + β ∈ P.asIdeal ↔ (t : 𝓞 D.host.E) - β ∈ P.asIdeal := by
    intro t
    have h1 : (t : 𝓞 D.host.K) + b ∈ ((conjPrime₂ P).under (𝓞 D.host.K)).asIdeal ↔
        (t : 𝓞 D.host.K) + b ∈ (P.under (𝓞 D.host.K)).asIdeal := by rw [h]
    have h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((t : 𝓞 D.host.K) + b) = t + β := by
      rw [map_add (f := _), map_intCast, hβ]
    have h4 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((t : 𝓞 D.host.K) + b) ∈ (conjPrime₂ P).asIdeal ↔
      algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((t : 𝓞 D.host.K) + b) ∈ P.asIdeal := h1
    rw [h3, mem_conjP, map_add (f := _), map_intCast, hβ3, ← sub_eq_add_neg] at h4
    exact h4.symm
  have hprod : ((s : 𝓞 D.host.E) + β) * (s - β) ∈ P.asIdeal := by
    have e : ((s : 𝓞 D.host.E) + β) * (s - β) = (p : 𝓞 D.host.E) * m := by
      have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hm
      push_cast at this
      linear_combination this - hβ2
    rw [e]
    exact Ideal.mul_mem_right _ _ hP
  have ha : (s : 𝓞 D.host.E) + β ∈ P.asIdeal := (P.isPrime.mem_or_mem hprod).elim id (key s).2
  have hb := (key s).1 ha
  have h5 : (2 : 𝓞 D.host.E) * β ∈ P.asIdeal := by
    have := sub_mem ha hb
    rwa [show (s : 𝓞 D.host.E) + β - (s - β) = 2 * β by ring] at this
  rcases P.isPrime.mem_or_mem h5 with h6 | h6
  · exact h2 (prime_eq_of_mem P hp Nat.prime_two hP (by exact_mod_cast h6))
  · have h7 := neg_mem (Ideal.mul_mem_left _ β h6)
    rw [hβ2, neg_neg] at h7
    exact hd (prime_eq_of_mem P hp D.host.hyp.2.1 hP h7)

theorem exists_places_of_cls (T : Type) (L : LevCh D T) (μ0 : T) (hL : L.Is μ0)
    (hg : ∀ k, D.host.cls (D.host.g k) = .splitK) (hde : D.host.cls D.host.pde = .splitK)
    (hde' : D.host.cls D.host.pde' = .splitK) (hq : ∀ k, q0 D ≠ D.host.g k)
    (hQ : ∀ t, ∀ PP ∈ L.Q t, ((q0 D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) : ∃ P : Places L, P.v0 ∉ S1 D := by
  classical
  choose 𝔭 h𝔭 using exists_primes L hL
  obtain ⟨hq0, hq1, -⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
  have hq2 : q0 D % LevelStarExponents.condE D = 1 := by
    have h1 : 1 < LevelStarExponents.condE D := by
      have := D.host.qd_big
      have hA : 0 < D.host.QS := D.host.QS_pos
      have hq' : 2 ≤ D.host.q := by omega
      have hd' : 1 ≤ D.host.d := by omega
      show 1 < D.host.QS * D.host.q * D.host.d
      calc 1 < 1 * 2 * 1 := by norm_num
        _ ≤ D.host.QS * D.host.q * D.host.d := Nat.mul_le_mul (Nat.mul_le_mul hA hq') hd'
    rw [← Nat.mod_mod_of_dvd _ (dvd_mul_left _ (Formalism.MainNotions.rPrAv D)), hq1, Nat.mod_eq_of_lt h1]
  have hq3 : D.host.cls (q0 D) = .splitK := GlobalTheory.Mem.cls_eq_splitK_of_cond D.host hq2
  obtain ⟨v0, hv0⟩ := exists_place D.host.F hq0
  have hw : ∀ v : HeightOneSpectrum (𝓞 D.host.F), ∃ w : HeightOneSpectrum (𝓞 D.host.E), ∀ p : ℕ, p.Prime →
      (p : 𝓞 D.host.F) ∈ v.asIdeal → w.under (𝓞 D.host.F) = v ∧ w.under (𝓞 D.host.K) = 𝔭 p := by
    intro v
    by_cases h : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.F) ∈ v.asIdeal
    · obtain ⟨p, hp, hv⟩ := h
      obtain ⟨w, hw⟩ := exists_over_both hp v hv (𝔭 p) (h𝔭 p hp).1
      exact ⟨w, fun p' hp' hv' => prime_eq_of_mem v hp hp' hv hv' ▸ hw⟩
    · obtain ⟨w, -⟩ := exists_place D.host.E hq0
      exact ⟨w, fun p hp hv => absurd ⟨p, hp, hv⟩ h⟩
  choose w hw using hw
  have hS : ∀ v ∈ insert v0 (S1 D), ∃ p : ℕ, p.Prime ∧ D.host.cls p = .splitK ∧ (p : 𝓞 D.host.F) ∈ v.asIdeal := by
    intro v hv
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact ⟨_, hq0, hq3, hv0⟩
    · rcases (S1_mem_OmF D).1 hv with h | h | h | h
      · exact ⟨_, D.host.g_prime 0, hg 0, h⟩
      · exact ⟨_, D.host.g_prime 1, hg 1, h⟩
      · exact ⟨_, D.host.pde_prime, hde, h⟩
      · exact ⟨_, D.host.pde'_prime, hde', h⟩
  have hde2 : ∀ p : ℕ, p = D.host.pde ∨ p = D.host.pde' → p.Prime ∧ D.host.cls p = .splitK := by
    rintro p (rfl | rfl)
    · exact ⟨D.host.pde_prime, hde⟩
    · exact ⟨D.host.pde'_prime, hde'⟩
  refine ⟨⟨v0, hv0, w, fun v hv => ?_, fun v hv => ?_, fun v k hv => ?_, fun p hp => ⟨𝔭 p, fun v hv => ?_⟩,
    fun t P hP hS1 => ?_, fun t P hP h => ?_⟩, fun h => ?_⟩
  · obtain ⟨p, hp, -, h⟩ := hS v (by convert hv)
    exact (hw v p hp h).1
  · obtain ⟨p, hp, hc, h⟩ := hS v (by convert hv)
    refine GlobalTheory.MovedIdem.exists_isIdemAt (w v) fun e => under_conjugatePrime_ne_of_class hp hc (w v)
      ((natCast_mem_under (M := D.host.F) (w v) p).1 (by rw [(hw v p hp h).1]; exact h)) ?_
    rw [show conjPrime₂ (w v) = w v from HeightOneSpectrum.ext ((conjIdeal_asIdeal (w v)).symm.trans e)]
  · exact (hL.Pg _).2 ⟨k, (hw v _ (D.host.g_prime k) hv).2.trans ((h𝔭 _ (D.host.g_prime k)).2.1 k rfl)⟩
  · exact (hw v p (hde2 p hp).1 hv).2
  · obtain ⟨q, hq', hqP, hne⟩ := exists_prime_mem (hL.Q_pl t) hP
    have hqv := (natCast_mem_under (M := D.host.F) P q).2 hqP
    have h1 : q = D.host.pde ∨ q = D.host.pde' := by
      rcases (S1_mem_OmF D).1 hS1 with h | h | h | h
      · exact absurd (prime_eq_of_mem _ hq' (D.host.g_prime 0) hqv h) (hne 0)
      · exact absurd (prime_eq_of_mem _ hq' (D.host.g_prime 1) hqv h) (hne 1)
      · exact Or.inl (prime_eq_of_mem _ hq' D.host.pde_prime hqv h)
      · exact Or.inr (prime_eq_of_mem _ hq' D.host.pde'_prime hqv h)
    obtain ⟨h2, h3⟩ := hw _ q hq' hqv
    rcases eq_or_eq_conjP h2 with h | h
    · exact h.symm
    · exfalso
      apply under_conjugatePrime_ne_of_class hq' (hde2 q h1).2 P hqP
      rw [← h, h3, (h𝔭 q hq').2.2 h1 t P hP hqP]
  · exact hQ t P hP ((natCast_mem_under (M := D.host.F) P _).1 (h ▸ hv0))
  · rcases (S1_mem_OmF D).1 h with h | h | h | h
    · exact hq 0 (prime_eq_of_mem _ hq0 (D.host.g_prime 0) hv0 h)
    · exact hq 1 (prime_eq_of_mem _ hq0 (D.host.g_prime 1) hv0 h)
    · exact (leastSplitAuxiliaryPrime_ne_typePrimes D).1 (prime_eq_of_mem _ hq0 D.host.pde_prime hv0 h)
    · exact (leastSplitAuxiliaryPrime_ne_typePrimes D).2 (prime_eq_of_mem _ hq0 D.host.pde'_prime hv0 h)

theorem leastSplitAuxiliaryPrime_ne_typePrime_of_sizes {large₂ : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (k : Fin 2) : q0 D ≠ D.host.g k := by
  intro e
  have h1 : Real.log (q0 D) ≤ large₂.sc.L := hs.2.2.2.2.2.2.2.2.1
  have h2 := (hs.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k k).1
  have hq : (0 : ℝ) < q0 D := by exact_mod_cast (leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos
  have h3 : (q0 D : ℝ) ≤ large₂.sc.b := (Real.log_le_iff_le_exp hq).1 h1
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hk : (2 : ℝ) ≤ D.R.k := by have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 2 ≤ D.R.k)
  have h4 : (D.R.k : ℝ) * large₂.sc.b ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := le_self_pow₀ (by nlinarith) (by norm_num)
  rw [← e] at h2
  nlinarith

end GlobalTheory.RowEx.GridExPf

namespace GlobalTheory.RowEx

open GlobalTheory.RowEx.GridExPf

end GlobalTheory.RowEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFockVectorDownwardArrow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DownFock

theorem isThetaFunO_fock_down : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (ρ : RealMatch W)
    (t : T) (i j : ℕ), i ≤ D.R.m → j < D.R.m → ∀ {e : AE D}, IsIdemSum e (locPl G t) →
    ∀ {φ f : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ}, IsLocVec W (.mu t i j) e (vacOf ρ (.down t i j)) φ f →
    ∀ Q : PolF D (G.pT (.mu t i j)).rank (G.pS (.mu t i j)).rank,
      IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) (W.fock (.mu t i j) f Q) := by
  intro D T L sc G W ρ t i j hi hj e _he φ f hf Q
  have hv : IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.mu t i j)) (G.onT W.cart (.mu t i j))
      (G.latS (.mu t i j) : Set _) (G.latT (.mu t i j) : Set _) (ρ.vT i j) := ρ.vT_is t i j hi hj
  have hf' : IsThetaFunO W.ψ _ _ f :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hf.2 hv.2.theta
  exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hf' Q

end GlobalTheory.DownFock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFockVectorRightwardArrow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowFock

theorem isThetaFunO_fock_right : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {G' : GridData R.toLevCh sc} {W : G'.Weil}, W.Over R → ∀ (ρ : RealMatch W), RealMatch.Over R ρ → ∀ (t : T) (i j : ℕ), i < D.R.m → j ≤ D.R.m → ∀ e, IsIdemSum e (locPl G' t) → ∀ φ f, IsLocVec W (.chi i j) e (vacOf ρ (.right i j)) φ f → ∀ Q : PolF D (G'.pT (.chi i j)).rank (G'.pS (.chi i j)).rank, IsThetaFunO W.ψ (G'.pS (.chi i j)) (G'.pT (.chi i j)) (W.fock (.chi i j) f Q) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W _ ρ _ t i j hi hj e _ φ f hf Q
  have h₀ : IsThetaFunO W.ψ (G'.pS (.chi i j)) (G'.pT (.chi i j)) (vacOf ρ (.right i j)) :=
    (ρ.vX_is i j hi hj).2.theta
  have hfθ : IsThetaFunO W.ψ (G'.pS (.chi i j)) (G'.pT (.chi i j)) f :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hf.2 h₀
  exact GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hfθ Q

end GlobalTheory.RowFock
end

