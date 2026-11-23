module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
public import Development.AutomorphicArithmetic.CharacterBoxes.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0007
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0008
public import Formalism.LocalToGlobal.FiniteTOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.Bundle0002
public import Formalism.LocalToGlobal.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Lean

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleRationalFormLiftsAlgebraicEnlarged
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.RatExt

open Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Mem.R3.Rw.LiftExt

private theorem comb_gen {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E'] (Y : HMod E) (X : HMod E')
    (g : Y.H →ₗ[ℂ] X.H) (hinj : Function.Injective Y.e) (v : Y.H) {n : ℕ} (s : Fin n → ℂ) (u : Fin n → Y.H)
    (hv : HEq (Y.e v) (∑ k, s k • Y.e (u k))) (p : Fin n → X.H) (hp : ∀ k, HEq (p k) (g (u k))) : ∑ k, s k • p k = g v := by
  have e : v = ∑ k, s k • u k := hinj (by rw [eq_of_heq hv, map_sum]; simp only [map_smul])
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_smul, eq_of_heq (hp k)]

section Comparison₂

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}
  {V W : HSp a.D} {V' W' : HSp a'.D} {S : a.D.what₂.Tau → SPar} {S' : a'.D.what₂.Tau → SPar} {M : DSModel W S} {M' : DSModel W' S'}

private theorem comb_of (hP : B'.toPre = B.toPre) (hV : HEq V' V) (hW : HEq W' W) (h : DSTie M' M) {c : CoefA V} {c' : CoefA V'}
    (c1 : HEq c'.W c.W) (c2 : HEq c'.ρ c.ρ) (c3 : HEq c'.nW c.nW) (c4 : HEq c'.iW c.iW)
    {Y : HMod (Bridge.Gf V → c.W)} {Y' : HMod (Bridge.Gf V' → c'.W)} (hY : HEq Y' Y)
    {X : HMod (MMap M)} {X' : HMod (MMap M')} (hX : HEq X' X) {g : Y.H →ₗ[ℂ] X.H} {g' : Y'.H →ₗ[ℂ] X'.H} (hg : HEq g' g)
    (hinj : Function.Injective Y.e) (v : Y'.H) {n : ℕ} (s : Fin n → ℂ) (u : Fin n → Y.H)
    (hv : HEq (Y'.e v) (∑ k, s k • Y.e (u k))) (p : Fin n → X'.H) (hp : ∀ k, HEq (p k) (g (u k))) : ∑ k, s k • p k = g' v := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (W')) ((by with_unfolding_all exact ((W) :))) (W') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (W')) (W') (((W))) (((hW)))).symm : _))
  clear (hW)
  subst e))
  obtain ⟨H', s', l', ε', f', _, _, _, _⟩ := M'
  rename_i n' i' _ _ _ _
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  dsimp only at h1 h2 h3 h4 h5 h6 h7
  ( (
  have e : @Eq (type_of% (H')) ((by with_unfolding_all exact ((M.H) :))) (H') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (H')) (H') (((M.H))) (((h1)))).symm : _))
  clear (h1)
  subst e))
  ( (
  have e : @Eq (type_of% (n')) ((by with_unfolding_all exact ((M.nacg) :))) (n') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (n')) (n') (((M.nacg))) (((h2)))).symm : _))
  clear (h2)
  subst e))
  ( (
  have e : @Eq (type_of% (i')) ((by with_unfolding_all exact ((M.ips) :))) (i') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (i')) (i') (((M.ips))) (((h3)))).symm : _))
  clear (h3)
  subst e))
  ( (
  have e : @Eq (type_of% (s')) ((by with_unfolding_all exact ((M.σ) :))) (s') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (s')) (s') (((M.σ))) (((h4)))).symm : _))
  clear (h4)
  subst e))
  ( (
  have e : @Eq (type_of% (l')) ((by with_unfolding_all exact ((M.lam) :))) (l') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (l')) (l') (((M.lam))) (((h5)))).symm : _))
  clear (h5)
  subst e))
  ( (
  have e : @Eq (type_of% (ε')) ((by with_unfolding_all exact ((M.ε) :))) (ε') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ε')) (ε') (((M.ε))) (((h6)))).symm : _))
  clear (h6)
  subst e))
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((M.fr) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((M.fr))) (((h7)))).symm : _))
  clear (h7)
  subst e))
  ( (
  have e : @Eq (type_of% (V')) ((by with_unfolding_all exact ((V) :))) (V') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (V')) (V') (((V))) (((hV)))).symm : _))
  clear (hV)
  subst e))
  obtain ⟨W₁, ρ₁⟩ := c'
  rename_i nW' iW' _
  dsimp only at c1 c2 c3 c4
  ( (
  have e : @Eq (type_of% (W₁)) ((by with_unfolding_all exact ((c.W) :))) (W₁) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (W₁)) (W₁) (((c.W))) (((c1)))).symm : _))
  clear (c1)
  subst e))
  ( (
  have e : @Eq (type_of% (nW')) ((by with_unfolding_all exact ((c.nW) :))) (nW') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (nW')) (nW') (((c.nW))) (((c3)))).symm : _))
  clear (c3)
  subst e))
  ( (
  have e : @Eq (type_of% (iW')) ((by with_unfolding_all exact ((c.iW) :))) (iW') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (iW')) (iW') (((c.iW))) (((c4)))).symm : _))
  clear (c4)
  subst e))
  ( (
  have e : @Eq (type_of% (ρ₁)) ((by with_unfolding_all exact ((c.ρ) :))) (ρ₁) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ρ₁)) (ρ₁) (((c.ρ))) (((c2)))).symm : _))
  clear (c2)
  subst e))
  ( (
  have e : @Eq (type_of% (Y')) ((by with_unfolding_all exact ((Y) :))) (Y') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (Y')) (Y') (((Y))) (((hY)))).symm : _))
  clear (hY)
  subst e))
  ( (
  have e : @Eq (type_of% (X')) ((by with_unfolding_all exact ((X) :))) (X') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (X')) (X') (((X))) (((hX)))).symm : _))
  clear (hX)
  subst e))
  ( (
  have e : @Eq (type_of% (g')) ((by with_unfolding_all exact ((g) :))) (g') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (g')) (g') (((g))) (((hg)))).symm : _))
  clear (hg)
  subst e))
  exact (by with_unfolding_all exact ((comb_gen Y X g hinj ((v)) s u ((hv)) ((p)) ((hp))) : _))

end Comparison₂

private theorem apply_eq {m m' : ℕ} (hm : m' = m) {F : Fin m → ℕ} {F' : Fin m' → ℕ} (hF : HEq F' F) {i : Fin m} {i' : Fin m'}
    (h : (i : ℕ) = i') : F i = F' i' := by
  subst hm
  obtain rfl := eq_of_heq hF
  obtain rfl : i = i' := Fin.ext h
  rfl

section Fields

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 T0 Pl0' T0' : Type}
  {A : FamIn a.D.what₂.LL G Pl0 T0 a.D.R.m} {A' : FamIn a'.D.what₂.LL G' Pl0' T0' a'.D.R.m}
  {Ks Ks' : Type} [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' a'.D.what₂.LL]
  {R : RealDat a.D A Ks} {R' : RealDat a'.D A' Ks'}


set_option maxHeartbeats 1000000 in
private theorem rat_of (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i') {t : T0} {t' : T0'}
    (c1 : HEq (R'.cV i').W (R.cV i).W) (c2 : HEq (R'.cV i').ρ (R.cV i).ρ) (c3 : HEq (R'.cV i').nW (R.cV i).nW)
    (c4 : HEq (R'.cV i').iW (R.cV i).iW)
    (hM : DSTie (R'.MW i' a'.D.what₂.embLL) (R.MW i a.D.what₂.embLL)) (hHW : HEq (R'.HW i' a'.D.what₂.embLL) (R.HW i a.D.what₂.embLL))
    (hHV : HEq (R'.HV i' t') (R.HV i t)) (hg : HEq (R'.thG i' t') (R.thG i t)) (hn : HEq R'.nW R.nW)
    (ι : a.D.what₂.LL →+* a'.D.what₂.LL) (hι : ∀ x, a'.D.what₂.embLL (ι x) = a.D.what₂.embLL x)
    (hj : ∀ (σ' : a'.D.what₂.LL →+* ℂ) x x', CrdOver ι x x' → HEq ((R'.FW i').j σ' x') ((R.FW i).j (σ'.comp ι) x))
    (hinj : Function.Injective (R.HV i t).e) (hjV : ∀ x, (R.HV i t).e (R.jV i t x) = R.B.jL i t x) (hr : RatAt R t)
    (x' : A'.fam.amb.FL i' t') {n : ℕ} (b : Fin n → a'.D.what₂.LL) (x : Fin n → A.fam.amb.FL i t)
    (hx : HEq (R'.B.jL i' t' x') (∑ k, a'.D.what₂.embLL (b k) • R.B.jL i t (x k)))
    (v : (R'.HV i' t').H) (hv : (R'.HV i' t').e v = R'.B.jL i' t' x') :
    ∃ y, (R'.FW i').j (sg0 a'.D A') y = R'.thG i' t' v := by
  have s : a.D.what₂.embLL = sg0 a.D A := (sgAt_mk _ R.hv0).symm
  have s' : a'.D.what₂.embLL = sg0 a'.D A' := (sgAt_mk _ R'.hv0).symm
  have hM0 : DSTie (R'.MW i' (sg0 a'.D A')) (R.MW i (sg0 a.D A)) := s ▸ s' ▸ hM
  have hHW0 : HEq (R'.HW i' (sg0 a'.D A')) (R.HW i (sg0 a.D A)) := s ▸ s' ▸ hHW
  have hc : (sg0 a'.D A').comp ι = sg0 a.D A := by
    rw [← s, ← s']; exact RingHom.ext hι
  have hmv : ∀ (σ₁ σ₂ : a.D.what₂.LL →+* ℂ), σ₁ = σ₂ → ∀ y, HEq ((R.FW i).j σ₁ y) ((R.FW i).j σ₂ y) := by
    intro σ₁ σ₂ e y; subst e; exact HEq.rfl
  have hn0 : R.nW i = R'.nW i' := apply_eq (LiftExt.m_eq hP) hn h
  choose y hy using fun k => hr i (x k) (R.jV i t (x k)) (hjV (x k))
  refine ⟨∑ k, b k • GeoFW.crdMap ι hn0 (y k), ?_⟩
  refine ((map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => LinearMap.map_smulₛₗ _ _ _)).trans ?_
  refine comb_of hP (vc_heq hP h) (wc_heq hP h) hM0 c1 c2 c3 c4 hHV hHW0 hg hinj v (fun k => sg0 a'.D A' (b k))
    (fun k => R.jV i t (x k)) ?_ (fun k => (R'.FW i').j (sg0 a'.D A') (GeoFW.crdMap ι hn0 (y k))) fun k => ?_
  · refine (heq_of_eq hv).trans (hx.trans (heq_of_eq ?_))
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (by with_unfolding_all exact ((congrArg₂ (fun (c : ℂ) (q : Bridge.Gf (Vc a.D i) → (R.cV i).W) => c • q) (DFunLike.congr_fun s' (b k)) (hjV (x k)).symm) :))
  · exact ((hj _ _ _ (GeoFW.crdOver_crdMap ι hn0 (y k))).trans (hmv _ _ hc _)).trans (heq_of_eq (hy k))

end Fields

end GlobalTheory.Mem.R3.Rw.RatExt

set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.referenceTuple_rationalForm_lifts_algebraic_enlarged : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → RSide z Wt' R' → JSpan z Wt' R' → RatAt z.R.toRealDat (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) → RatAt R'.toRealDat (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hS hJ hr i' x' v hv
  letI := z.alg
  have hP : B'.toPre = B.toPre := hE.1
  have hm := LiftExt.m_eq (a := Z) (a' := Z') hP
  let i : Fin (w.st Z).toD7.R.m := Fin.cast hm i'
  have h : (i : ℕ) = i' := rfl
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL :=
    (B'.embLL.rangeRestrictFieldEquiv.symm : B'.embLL.fieldRange →+* B'.LL).comp
      (B.embLL.codRestrict B'.embLL.fieldRange fun x => hE.2.2.2 ⟨x, rfl⟩)
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := fun x =>
    congrArg Subtype.val (B'.embLL.rangeRestrictFieldEquiv.apply_symm_apply ⟨B.embLL x, hE.2.2.2 ⟨x, rfl⟩⟩)
  obtain ⟨⟨-, -, -, -, -, hn, -, -, -, -, -, -, h1, -⟩, h2⟩ := hS
  obtain ⟨c1, c2, c3, c4, -, -, -, m1, m2, m3, m4, m5, m6, m7, -, hHW, -, -, hWι⟩ := h1 i i' h
  obtain ⟨-, -, hHV, -, hg, -, -⟩ := h2 i i' h
  obtain ⟨n, b, x, hx⟩ := hJ i i' h x'
  have hb := z.pins.char.base.models
  exact RatExt.rat_of (a := Z) (a' := Z') (R := z.R.toRealDat) (R' := R'.toRealDat) hP h c1 c2 c3 c4
    ⟨m1, m2, m3, m4, m5, m6, m7⟩ hHW hHV hg hn ι hι (fun σ' => ((hWι ι hι).1 σ').2.2.2) (hb.HV i _).1 (hb.jV i _) hr x' b x hx v hv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEqOfCmFieldPlaceEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.SplitByCompl

theorem eq_of_w_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s s' : SplitPlace L),
    s.w = s'.w → s = s' := by
  intro L _ _ _ s s' h
  have hv : s.v = s'.v := HeightOneSpectrum.ext (by rw [← s'.w_under, ← s.w_under, h])
  obtain ⟨v, si⟩ := s
  obtain ⟨v', si'⟩ := s'
  dsimp only at hv
  subst hv
  obtain ⟨i, hi, -, hix⟩ := GlobalTheory.SplitCompl.exists_ringEquiv L ⟨v, si⟩
  obtain ⟨i', hi', -, hix'⟩ := GlobalTheory.SplitCompl.exists_ringEquiv L ⟨v, si'⟩
  dsimp only at hix hix'
  generalize hw : SplitPlace.w ⟨v, si⟩ = w at i hix hi
  generalize hw' : SplitPlace.w ⟨v, si'⟩ = w' at i' hix' hi'
  have hww : w = w' := hw.symm.trans (h.trans hw')
  subst hww
  have e : (i' : v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L) = i :=
    DFunLike.coe_injective ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L) v).equalizer
      hi' hi (funext fun y => by
        have h1 := hix (algebraMap _ L y)
        have h2 := hix' (algebraMap _ L y)
        rw [AlgHom.commutes] at h1 h2
        exact h2.trans h1.symm))
  have e' : ∀ x, i' x = i x := fun x =>
    congrArg (fun f : v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L => f x) e
  have hs : si = si' := AlgHom.ext fun x => i.injective (by rw [hix, ← e', hix'])
  rw [hs]

end GlobalTheory.SplitByCompl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlacesSameRealPlaceNatCastMem
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory

theorem split_places_same_natCast_mem : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s s' : SplitPlace L) (n : ℕ), s.v = s'.v →
    ((n : ℕ) : 𝓞 L) ∈ s.w.asIdeal → ((n : ℕ) : 𝓞 L) ∈ s'.w.asIdeal := by
  intro L _ _ _ s s' n hv hn
  have e : ((n : ℕ) : 𝓞 L) = algebraMap (𝓞 (NumberField.maximalRealSubfield L)) (𝓞 L) (n : 𝓞 (NumberField.maximalRealSubfield L)) := (map_natCast _ n).symm
  rw [e] at hn ⊢
  have h1 : ((n : ℕ) : 𝓞 (NumberField.maximalRealSubfield L)) ∈ s.v.asIdeal := by
    rw [← s.w_under]; exact Ideal.mem_comap.mpr hn
  rw [hv] at h1
  rw [← s'.w_under] at h1
  exact Ideal.mem_comap.mp h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceSquare
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory


set_option maxHeartbeats 4000000 in
open GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.BigTop.Fun in
theorem Mem.LiteralAutomorphy.trSq_holds : GlobalTheory.Mem.LiteralAutomorphy.TrSq := by
  intro X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι h M σ hs
  obtain ⟨⟨hpre, -, -, ⟨f, f', hff, hC, hC'⟩, hbase, hxi, -, -⟩, hg, -, -⟩ := h
  clear S S' W W'
  obtain ⟨B, C₁, W₁, V₁, S₁, N₁, G₁⟩ := X
  obtain ⟨B', C₂, W₂, V₂, S₂, N₂, G₂⟩ := X'
  cases B; cases B'
  dsimp only at hpre
  subst hpre
  obtain rfl := eq_of_heq hff
  have hv0 : G'.pl.v0 = G.pl.v0 := eq_of_heq hg.v0
  have hw : G'.pl.w = G.pl.w := eq_of_heq hg.w
  have hchi : G'.ch.chiH = G.ch.chiH := eq_of_heq hg.chiH
  have hx : L'.xiH μ₀' = L.xiH μ₀ := by have := eq_of_heq (hxi μ₀'); rwa [hbase] at this
  have e_levQ : levQ G'.pl = levQ G.pl := by
    unfold levQ Places.S0 condExp; rw [hv0]; exact (Eq.refl (levQ G.pl))
  have e_condE : SqNum.condE G'.pl = SqNum.condE G.pl := by
    unfold SqNum.condE Places.S0 condExp; rw [hv0, hw]; exact (Eq.refl (SqNum.condE G.pl))
  have e_condF : condF G'.pl = condF G.pl := by
    unfold condF Places.S0 condExp; rw [hv0]; exact (Eq.refl (condF G.pl))
  have hmu : L'.C.mu0 = L.C.mu0 := by rw [hC, hC']; exact (Eq.refl f'.mu0)
  have heta : L'.C.eta = L.C.eta := by rw [hC, hC']; exact (Eq.refl f'.eta)
  have hd1 : L'.C.del = L.C.del := by rw [hC, hC']; exact (Eq.refl f'.del)
  have hd2 : L'.C.del' = L.C.del' := by rw [hC, hC']; exact (Eq.refl f'.del')
  have e_nu : ∀ i j, nuH G' μ₀' i j = nuH G μ₀ i j := by
    intro i j; unfold nuH; rw [hmu, hx, hchi]; exact (Eq.refl (nuH G μ₀ i j))
  have e_beta : ∀ i j, betaH G' i j = betaH G i j := by
    intro i j; unfold betaH; rw [heta, hchi]; exact (Eq.refl (betaH G i j))
  have e_alpha : ∀ i j, alphaH L' μ₀' i j = alphaH L μ₀ i j := by
    intro i j; unfold alphaH; rw [hmu, hx, heta]; exact (Eq.refl (alphaH L μ₀ i j))
  have e_del : ∀ c, delOf L' c = delOf L c := by
    intro c; unfold delOf; rw [hd1, hd2]; exact (Eq.refl (delOf L c))
  have eT : ∀ i j s χ x, IsTor G' i j s χ x ↔ IsTor G i j s χ x := by
    intro i j s χ x; unfold IsTor; rw [e_condF]; exact (Iff.refl (IsTor G i j s χ x))

  let hk1 : ∀ {N : ℕ}, Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) N → Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) N :=
    fun h => { f := ((h.f)), n := ((h.n)), unitary := ((h.unitary)), cont := ((h.cont)), aut := ((h.aut)), norm := ((h.norm)), par := ((h.par)), unr := ((h.unr)) }
  let wt1 : ∀ {δ : ℂ} {a d : ℕ} {e0 : Formalism.MainNotions.TaylorLogMetric.VC (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) a d → ℂ}, Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ a d e0 →
      Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ a d ((e0)) :=
    fun w => { chV := hk1 w.chV, chV' := hk1 w.chV', ep := w.ep, ep' := w.ep', ep_pm := w.ep_pm, nz := ((w.nz)), Om := ((w.Om)), maps := ((w.maps)), add := ((w.add)), smul := ((w.smul)), one := ((w.one)), mul := ((w.mul)), lift := ((w.lift)), inert := ((w.inert)), split := ((w.split)) }
  let pt1 : ∀ {δ t0 : ℂ} {Q : ℕ}, GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ t0 Q → GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ t0 Q :=
    fun P => { a := P.a, d := P.d, a_le := P.a_le, d_even := P.d_even, W := wt1 P.W, crv := ((P.crv)), pt0 := ((P.pt0)), e0 := ((P.e0)), vac := ((P.vac)), n := ((P.n)), wt := ((P.wt)), F := ((P.F)), pres := ((P.pres)), fix := ((P.fix)), J := ((P.J)), J_le := ((P.J_le)), idx_ne := ((P.idx_ne)), idx_le := ((P.idx_le)), eig := ((P.eig)) }

  let hk2 : ∀ {N : ℕ}, Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) N → Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) N :=
    fun h => { f := ((h.f)), n := ((h.n)), unitary := ((h.unitary)), cont := ((h.cont)), aut := ((h.aut)), norm := ((h.norm)), par := ((h.par)), unr := ((h.unr)) }
  let wt2 : ∀ {δ : ℂ} {a d : ℕ} {e0 : Formalism.MainNotions.TaylorLogMetric.VC (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) a d → ℂ}, Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ a d e0 →
      Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ a d ((e0)) :=
    fun w => { chV := hk2 w.chV, chV' := hk2 w.chV', ep := w.ep, ep' := w.ep', ep_pm := w.ep_pm, nz := ((w.nz)), Om := ((w.Om)), maps := ((w.maps)), add := ((w.add)), smul := ((w.smul)), one := ((w.one)), mul := ((w.mul)), lift := ((w.lift)), inert := ((w.inert)), split := ((w.split)) }
  let pt2 : ∀ {δ t0 : ℂ} {Q : ℕ}, GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ t0 Q → GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ t0 Q :=
    fun P => { a := P.a, d := P.d, a_le := P.a_le, d_even := P.d_even, W := wt2 P.W, crv := ((P.crv)), pt0 := ((P.pt0)), e0 := ((P.e0)), vac := ((P.vac)), n := ((P.n)), wt := ((P.wt)), F := ((P.F)), pres := ((P.pres)), fix := ((P.fix)), J := ((P.J)), J_le := ((P.J_le)), idx_ne := ((P.idx_ne)), idx_le := ((P.idx_le)), eig := ((P.eig)) }

  have btr1 : ∀ {δ t0 : ℂ} {Q : ℕ} (i j : Fin (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩).R.m)
      (P P' : GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ t0 Q), IsBottom G μ₀ i j (SqNum.condE G.pl) P P' →
        IsBottom G' μ₀' i j (SqNum.condE G'.pl) (pt1 P) (pt1 P') := by
    intro δ t0 Q i j P P' h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨(h1), ?_, ?_, ?_, ?_, ?_⟩
    · rw [e_beta, e_nu]; exact (h2)
    · rw [e_alpha, e_nu]; exact (h3)
    · rw [e_condE]; exact (h4)
    · rw [e_condE]; exact (h5)
    · rw [e_condE]; exact (h6)

  have btr2 : ∀ {δ t0 : ℂ} {Q : ℕ} (i j : Fin (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩).R.m)
      (P P' : GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ t0 Q), IsBottom G' μ₀' i j (SqNum.condE G'.pl) P P' →
        IsBottom G μ₀ i j (SqNum.condE G.pl) (pt2 P) (pt2 P') := by
    intro δ t0 Q i j P P' h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    rw [e_beta, e_nu] at h2
    rw [e_alpha, e_nu] at h3
    rw [e_condE] at h4 h5 h6
    exact ⟨(h1), (h2), (h3), (h4), (h5), (h6)⟩
  refine ⟨fun hb => ?_, fun i j s c x y h1 h2 h3 h4 => ?_⟩
  · obtain ⟨δ, t0, hb⟩ := hb
    rw [e_levQ] at hb
    obtain ⟨δ', t0', hb'⟩ := hs.norms ⟨δ, t0, fun ij => by
      obtain ⟨P, P', hP, -, -⟩ := hb ((ij))
      exact ⟨pt2 P, pt2 P', btr2 ((ij.1)) ((ij.2)) P P' hP, trivial, trivial⟩⟩
    refine ⟨δ', t0', fun ij => ?_⟩
    rw [e_levQ]
    obtain ⟨P, P', hP, n1, n2⟩ := hb' ((ij))
    exact ⟨pt1 P, pt1 P', btr1 ij.1 ij.2 P P' hP, (n1), (n2)⟩
  · rw [eT, e_nu] at h3
    rw [eT, e_nu, e_del] at h4
    exact hs.toric ((i)) ((j)) s c x y h1 ((h2)) ((h3)) ((h4))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConductorsAvoidExcludedPrimes
section
noncomputable section

namespace GlobalTheory.LowAvoid

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

def lowPre (P : Pre) : Finset ℕ := by
  classical
  exact if h : ∃ X : Stages, X.B.toPre = P then lowAll h.choose.toD7 else ∅

theorem lowAll_congr {s s' : Stages} (h : s.B.toPre = s'.B.toPre) : lowAll s.toD7 = lowAll s'.toD7 := by
  obtain ⟨B, C, W, V, S, N, Gj⟩ := s
  obtain ⟨B', C', W', V', S', N', Gj'⟩ := s'
  cases B
  cases B'
  dsimp only at h
  subst h
  rfl

theorem lowAll_eq_lowPre (s : Stages) : lowAll s.toD7 = lowPre s.B.toPre := by
  have h : ∃ X : Stages, X.B.toPre = s.B.toPre := ⟨s, rfl⟩
  simp only [lowPre, dif_pos h]
  exact lowAll_congr h.choose_spec.symm

theorem prime_of_mem_lowAll (D : D7) {p : ℕ} (hp : p ∈ lowAll D) : p.Prime := by
  simp only [lowAll, lowPr, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with ((rfl | rfl | hp | hp) | rfl | rfl | rfl | rfl)
  · exact Nat.prime_two
  · exact (Formalism.L2.Host.leastSplitAuxiliaryPrimeThetaChain_spec D).1
  · exact Nat.prime_of_mem_primeFactors hp
  · exact Nat.prime_of_mem_primeFactors hp
  · exact D.host.g_prime 0
  · exact D.host.g_prime 1
  · exact D.host.pde_prime
  · exact D.host.pde'_prime

theorem eq_of_mem_placesOver {E : Type} [Field E] [NumberField E] (u : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime)
    (hu : (Ideal.absNorm u.asIdeal).Prime) (h : u ∈ placesOver E p) : Ideal.absNorm u.asIdeal = p := by
  by_contra e
  have h3 : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ∈ u.asIdeal := Ideal.absNorm_mem _
  obtain ⟨a, b, hab⟩ : IsCoprime ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ((p : ℕ) : 𝓞 E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hu hp).2 e)
  exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h3) (Ideal.mul_mem_left _ _ (show ((p : ℕ) : 𝓞 E) ∈ u.asIdeal from h))))

theorem conductors_avoid_lowAll :
    AllSt fun _ _ _ T _ _ x => ∀ v, ∀ u ∈ T.Q v, ∀ p ∈ lowAll (Dof x), u ∉ placesOver (Dof x).host.E p := by
  refine evG_all fun K => ?_
  refine large₂.imp (p := fun B _ T => T.Avoids fun _ => lowPre B.toPre)
    ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun B _ _ _ _ => lowPre B, fun _ _ _ _ _ => ∅, by simp, by simp,
      fun _ _ _ _ _ _ h => h⟩ ?_
  intro B f T _ hA _ _ _ w _ P x v u hu p hp hup
  have hl : lowAll (Dof x) = lowPre B.toPre := lowAll_eq_lowPre (w.st x.o.Z)
  obtain ⟨-, h1, -, -⟩ := (T.psi_tw v).2.2.2 u fun h => ((T.psi_is v).ram u).1 h hu
  have e : Ideal.absNorm u.asIdeal = p := eq_of_mem_placesOver u (prime_of_mem_lowAll _ hp) h1 hup
  exact hA v u hu (by rw [e, ← hl]; exact hp)

end GlobalTheory.LowAvoid

end
end

