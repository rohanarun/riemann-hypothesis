module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemSqOfRamificationIdx
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0667
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0551
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0643
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0426

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
section
noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder RootIso FrobPick)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000

def SatU {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (P : Pre2 K w) : Prop :=
  T = TwDat.untw B T.pl → ∀ v v', OverOne (w.D P.Z₀) v v' → v ∈ P.Wt → v' ∈ P.Wt

section Slot

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ)

end Slot

def ExistsUnlocalizedSaturatedState : Prop := StepW Start fun K _ _ _ w => ∃ (P : Pre2 K w) (x : St P), SatU P ∧ IsEmpty x.o.N.nd.Loc ∧ ∀ j v, x.o.η j v = 0

structure SameGal (D D' : D7) : Prop where
  gal : SameGalois D.nd D'.nd
  pl : HEq D.naut.plGw D'.naut.plGw

structure Carried (D D' : D7) : Prop where
  exp : SameExport D D'
  emb : ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (x : D.LL0) (x' : D'.LL0),
    D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL) →
      HEq (D.ntw.emb0 i x) (D'.ntw.emb0 i' x') ∧ HEq (D.ntw.emb0b i x) (D'.ntw.emb0b i' x')

structure Seed (D : D7) (A : D.ntw.Tw → Finset (PlE D.host)) where
  s : D.what₂.places.Pl → D.ntw.Tw
  reads : ∀ v, ∃ b, ReadsAt (s v) b v
  conj : ∀ v, s (D.what₂.places.conj v) = s v
  same : ∀ v v', TwistedAt D v → TwistedAt D v' → OverOne D v v' → s v' = s v
  xd : ThData D
  all : XdAll xd
  N0 : D.ntw.Tw → ℕ
  S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)
  Q : D.ntw.Tw → Finset (PlE D.host)
  k : D.ntw.Tw → ℕ
  ψ : ∀ i, D.ntw.RCG i (Q i) →* (D.ntw.Ok i (k i))ˣ
  good : ∀ v, TwistedAt D v → TwIn.Ok (⟨twEOf xd, N0, S⟩ : TwIn D) (s v) ∧
    ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l (s v)) →
      IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) (twEOf xd) N0 (s v) (twEps D (s v)) (S (s v)) (A (s v)) (Q (s v)) (k (s v)) (ψ (s v) ^ a)
  sep : ∀ v v', TwistedAt D v → TwistedAt D v' → s v ≠ s v' → Disjoint (Q (s v)) (Q (s v'))

def Seed.pack {D : D7} {A : D.ntw.Tw → Finset (PlE D.host)} (σ : Seed D A) (v : D.what₂.places.Pl) : TwPack D :=
  ⟨σ.s v, σ.Q (σ.s v), σ.k (σ.s v), σ.ψ (σ.s v)⟩

def TwFrom (X : Stages) {A : X.toD7.ntw.Tw → Finset (PlE X.toD7.host)} (σ : Seed X.toD7 A) {B' : Base} (h : Enl X.B B')
    (T' : TwDat B') : Prop :=
  (∀ (v' : B'.places.Pl) (z : ℂ), z ^ B'.places.resChar v' ^ T'.k v' = 1 → ∃ x : B'.LL, B'.embLL x = z) ∧
  ∀ v' : B'.places.Pl,
    (TwistedAt X.toD7 (plUnder h v') →
      HEq (T'.Q v') (σ.Q (σ.s (plUnder h v'))) ∧ T'.k v' = σ.k (σ.s (plUnder h v')) ∧
      ∃ (ι : RootIso X.toD7 (σ.s (plUnder h v')) (σ.k (σ.s (plUnder h v')))) (χ : HChar X.toD7.host.E),
        FrobPick (σ.s (plUnder h v')) _ _ (σ.ψ (σ.s (plUnder h v'))) ι χ ∧ HEq (T'.psi v') χ) ∧
    (¬ TwistedAt X.toD7 (plUnder h v') → T'.psi v' = 1)

def BareK : Prop := StepW Start fun K B' f' _ w' => ∀ (P' : Pre2 K w') (X : Stages) (f : Fr X.B.toPre), B'.toPre = X.B.toPre →
  HEq f' f → GrpTrue X.N f → ∃ x' : St P', IsEmpty x'.o.N.nd.Loc ∧ SameGal X.toD7 (Dof x')

variable (hL : GlobalTheory.Published.LocalLanglandsGL)

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherPlacesGroupContainsChartLevels
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC


set_option maxHeartbeats 4000000 in
theorem further_group_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∃ (W : ∀ v, v ∈ Q → Subgroup (GL (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F))) (ψ : (∀ v : Q, ↥(W v.1 v.2)) →* ℂˣ), (∀ v hv, W v hv ≤ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v Lb0) ∧ (∀ v hv, ∃ n : ℕ, 0 < n ∧ ∀ x, Formalism.L2.Herm.InPrinc (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) v n Lb0 x → x ∈ W v hv) ∧ (∀ β v hv, (K β).lev.Uloc v ≤ (W v hv).map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) ∧ (∀ β v hv, ((((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom).subgroupOf (W v hv)).FiniteIndex) ∧ (∀ β (κ : (K β).lev.U) (z : ∀ v : Q, ↥(W v.1 v.2)), (∀ v : Q, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (z v).1 = bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1) → (∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ψ z) := by
  intro B X I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hfin hoff hchi Lb0 hLb
  classical
  rcases isEmpty_or_nonempty Ch with hE | hNE
  · refine ⟨fun v _ => levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v Lb0, 1, fun v hv => le_rfl,
      fun v hv => ⟨1, one_pos, fun x hx => hx.1⟩, fun β => hE.elim β, fun β => hE.elim β, fun β => hE.elim β⟩
  · obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_character_allCharts_furtherPlaces I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hfin hoff hchi Lb0 hLb
    refine ⟨fun v _ => (⨆ β', ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom), ψ, fun v hv => iSup_le fun β => GlobalTheory.Mem.Col2.TC.chart_Uloc_le_levelVL_base I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hoff hchi Lb0 hLb β v hv, fun v hv => ?_, fun β v hv => ?_, fun β v hv => GlobalTheory.T.chartLocalGroup_finiteIndex_at_furtherPlace I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hoff hchi Lb0 hLb β v hv, hψ⟩
    · obtain ⟨β⟩ := hNE
      obtain ⟨n, hn, hx⟩ := GlobalTheory.Mem.Col2.AdT.LevQ.chart_contains_princ I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hoff hchi Lb0 hLb β v hv
      exact ⟨n, hn, fun x h => le_iSup (fun β' => ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) β (hx x h)⟩
    · intro x hx
      refine ⟨(reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).symm x, le_iSup (fun β' => ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) β ?_, ?_⟩
      · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]; exact hx
      · rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

end GlobalTheory.Mem.Col2.TC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridStaircaseLatticeFirstColumnTransportStages
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.Mem.R3.Tr Formalism.BasicNotions.TH

set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.Mem.GridMove
open GlobalTheory.ChiGrid
variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {T : Type}

def plC {L : Formalism.IndefR.Links.LevCh a.D T} (P : Places L) : Places (levCh b L) where
  v0 := (by with_unfolding_all exact (P.v0 :))
  basePlace_over_qZero := (by with_unfolding_all exact (P.basePlace_over_qZero :))
  w := (by with_unfolding_all exact (P.w :))
  w_over := (by with_unfolding_all exact (P.w_over :))
  w_split := (by with_unfolding_all exact (P.w_split :))
  w_g := (by with_unfolding_all exact (P.w_g :))
  w_de := (by with_unfolding_all exact (P.w_de :))
  w_Q := (by with_unfolding_all exact (P.w_Q :))
  levelPlace_ne_basePlace := (by with_unfolding_all exact (P.levelPlace_ne_basePlace :))

def chC {L : Formalism.IndefR.Links.LevCh a.D T} {P : Places L} {c : ℝ} (X : Chars P c) : Chars (plC b P) c where
  chiH := (by with_unfolding_all exact (X.chiH :))
  chi := (by with_unfolding_all exact (X.chi :))
  chi_eq := (by with_unfolding_all exact (X.chi_eq :))
  triv := (by with_unfolding_all exact (X.triv :))
  inf := (by with_unfolding_all exact (X.inf :))
  unr := (by with_unfolding_all exact (X.unr :))
  lev1 := (by with_unfolding_all exact (X.lev1 :))
  wild := (by with_unfolding_all exact (X.wild :))
  lev0 := (by with_unfolding_all exact (X.lev0 :))

def lsC (X : LSp a.D) : LSp b.D := ⟨(by with_unfolding_all exact (X.sp :)), (by with_unfolding_all exact (X.lat :))⟩

theorem isVC {X : LSp a.D} {ν q : ℕ} (h : X.IsV ν q) : (lsC b X).IsV ν q :=
  ⟨(by with_unfolding_all exact (h.rank :)), (by with_unfolding_all exact (h.sigOK :)), (by with_unfolding_all exact (h.sig :)), (by with_unfolding_all exact (h.sd :))⟩

def adC {A B' : HSp a.D} {c : ℕ} {ε : a.D.host.E} (d : HermitianOrthogonalExtensionData A B' c ε) :
    @HermitianOrthogonalExtensionData b.D ((A)) ((B')) c ((ε)) where
  ι := (by with_unfolding_all exact (d.ι :))
  isom := (by with_unfolding_all exact (d.isom :))
  a := (by with_unfolding_all exact (d.a :))
  gram := (by with_unfolding_all exact (d.gram :))
  perp := (by with_unfolding_all exact (d.perp :))
  rank := (by with_unfolding_all exact (d.rank :))

section V
open scoped nonZeroDivisors
variable {L : Formalism.IndefR.Links.LevCh a.D T} (Vs : ℕ → ℕ → LSp a.D) (Xs : ℕ → LSp a.D)

def gridColumnVertexDecompTransport (P : ℕ → LSp a.D) : ∀ (i : ℕ) (_ : 1 ≤ i) (_ : HermitianOrthogonalExtensionData (P i).sp (vtxOf L Vs i 0).sp (i - 1) (-1)),
    HermitianOrthogonalExtensionData (lsC b (P i)).sp (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) i 0).sp (i - 1) (-1)
  | 0, h, _ => absurd h (by omega)
  | _ + 1, _, d => (adC b d :)

theorem gridStaircaseLattice_firstColumn_transportStages (P : ℕ → LSp a.D) : ∀ (i : ℕ) (h : 1 ≤ i) (d : HermitianOrthogonalExtensionData (P i).sp (vtxOf L Vs i 0).sp (i - 1) (-1))
    (𝔟 : Fin (i - 1) → FractionalIdeal (𝓞 a.D.host.E)⁰ a.D.host.E),
    (vtxOf L Vs i 0).lat = d.lat (P i).lat 𝔟 →
    (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) i 0).lat = (gridColumnVertexDecompTransport b Vs P i h d).lat (lsC b (P i)).lat ((𝔟))
  | 0, h, _, _, _ => absurd h (by omega)
  | _ + 1, _, _, _, e => (e)

def gridInteriorVertexDecompTransport (j : ℕ) : ∀ (n : ℕ) (_ : j + 1 < n) (_ : HermitianOrthogonalExtensionData (Xs (j + 1)).sp (vtxOf L Vs n (j + 1)).sp (n - 1 - (j + 1)) (-1)),
    HermitianOrthogonalExtensionData (lsC b (Xs (j + 1))).sp (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) n (j + 1)).sp (n - 1 - (j + 1)) (-1)
  | 0, h, _ => absurd h (by omega)
  | _ + 1, _, d => (adC b d :)

theorem gridLastRowVertexLattice_transportStages (j : ℕ) : ∀ (n : ℕ) (h : j + 1 < n) (d : HermitianOrthogonalExtensionData (Xs (j + 1)).sp (vtxOf L Vs n (j + 1)).sp (n - 1 - (j + 1)) (-1))
    (𝔟 : Fin (n - 1 - (j + 1)) → FractionalIdeal (𝓞 a.D.host.E)⁰ a.D.host.E),
    (vtxOf L Vs n (j + 1)).lat = d.lat (Xs (j + 1)).lat 𝔟 →
    (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) n (j + 1)).lat = (gridInteriorVertexDecompTransport b Vs Xs j n h d).lat (lsC b (Xs (j + 1))).lat ((𝔟))
  | 0, h, _, _, _ => absurd h (by omega)
  | _ + 1, _, _, _, e => (e)

def gridDiagonalVertexDecompTransport (X0 : LSp a.D) : ∀ (n : ℕ) (_ : 1 ≤ n) (_ : HermitianOrthogonalExtensionData (vtxOf L Vs n n).sp (xOf X0 Xs n).sp 1 1),
    HermitianOrthogonalExtensionData (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) n n).sp (xOf (lsC b X0) (fun j => lsC b (Xs j)) n).sp 1 1
  | 0, h, _ => absurd h (by omega)
  | _ + 1, _, d => (adC b d :)

theorem gridTopVertexLattice_transportStages (X0 : LSp a.D) : ∀ (n : ℕ) (h : 1 ≤ n) (d : HermitianOrthogonalExtensionData (vtxOf L Vs n n).sp (xOf X0 Xs n).sp 1 1),
    (xOf X0 Xs n).lat = d.lat (vtxOf L Vs n n).lat (fun _ => 1) →
    (xOf (lsC b X0) (fun j => lsC b (Xs j)) n).lat = (gridDiagonalVertexDecompTransport b Vs Xs X0 n h d).lat (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) n n).lat (fun _ => 1)
  | 0, h, _, _ => absurd h (by omega)
  | _ + 1, _, _, e => (e)

end V

section W
open scoped nonZeroDivisors
variable {L : Formalism.IndefR.Links.LevCh a.D T}

def vtC {𝔞 𝔞' : FractionalIdeal (𝓞 a.D.host.E)⁰ a.D.host.E} (V : Vertices L 𝔞 𝔞') :
    Vertices (levCh b L) ((𝔞)) ((𝔞')) where
  Vs i j := lsC b (V.Vs i j)
  P i := lsC b (V.P i)
  Xs j := lsC b (V.Xs j)
  V_is i j h1 h2 h3 := (by with_unfolding_all exact ((isVC b (V.V_is i j h1 h2 h3)) :))
  P_is i h := (by with_unfolding_all exact ((isVC b (V.P_is i h)) :))
  X_is j h1 h2 := (by with_unfolding_all exact ((isVC b (V.X_is j h1 h2)) :))
  dec0 := (by with_unfolding_all exact ((adC b V.dec0) :))
  lat0 := (by with_unfolding_all exact (V.lat0 :))
  colDec i h h' := gridColumnVertexDecompTransport b V.Vs V.P i h (V.colDec i h h')
  colLat i h h' := (by with_unfolding_all exact ((gridStaircaseLattice_firstColumn_transportStages b V.Vs V.P i h (V.colDec i h h') _ (V.colLat i h h')) :))
  rowDecS j h := (by with_unfolding_all exact ((gridInteriorVertexDecompTransport b V.Vs V.Xs j a.D.R.m h (V.rowDecS j h)) :))
  rowLat j h := (by with_unfolding_all exact ((gridLastRowVertexLattice_transportStages b V.Vs V.Xs j a.D.R.m h (V.rowDecS j h) _ (V.rowLat j h)) :))
  topDec := (by with_unfolding_all exact ((gridDiagonalVertexDecompTransport b V.Vs V.Xs (V.P a.D.R.m) a.D.R.m (by have := a.D.R.two_le_m; omega) V.topDec) :))
  topLat := (by with_unfolding_all exact ((gridTopVertexLattice_transportStages b V.Vs V.Xs (V.P a.D.R.m) a.D.R.m (by have := a.D.R.two_le_m; omega) V.topDec V.topLat) :))

def gdC {sc : Consts} (G : GridData L sc) : GridData (levCh b L) sc where
  pl := plC b G.pl
  ch := chC b G.ch
  sp := (by with_unfolding_all exact ((vtC b G.sp) :))

end W

section Y
variable {L : Formalism.IndefR.Links.LevCh a.D T}

theorem listPin_upL (S' : SStage B C a.W) (Nn : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (hh : B.Word → ℝ) (c bb : ℝ)
    (h : ListPin a.D L c bb) : ListPin (upL a S' Nn hh).D (levCh (upL a S' Nn hh) L) c bb := by
  obtain ⟨G, h1, h2⟩ := h
  exact ⟨gdC _ G, ⟨(by with_unfolding_all exact (h1.values :)), (by with_unfolding_all exact (h1.roots :))⟩, (by with_unfolding_all exact (h2 :))⟩
end Y


set_option maxHeartbeats 4000000 in
theorem listPin_rowsSame : ∀ (cDep b : ℝ) (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0'), RowsSame t t' → ListPin (w.st Z).toD7 t.r.z.R.toRealDat.toLevCh cDep b → ListPin (w.st (upL Z S' N h)).toD7 t'.r.z.R.toRealDat.toLevCh cDep b := by
  intro cDep b K B f T w Z Wt S' N h p0 t p0' t' hs hp
  cases t' with | mk hX' r' => ?_
  cases r' with | mk z' => ?_
  cases z' with | @mk Xg' tr' core' alg' alg_eq' R' => ?_
  have hXg := hs.Xg
  have htr := hs.tr
  have hcore := hs.core
  have hR := hs.R
  clear hs
  change Xg' = t.r.z.Xg at hXg
  change tr' = t.r.z.tr at htr
  subst hXg htr
  change HEq core' _ at hcore
  have hc := eq_of_heq hcore
  subst hc
  have ha : alg' = GlobalTheory.Mem.R3.Tr.alg (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩)
      ⟨(upL Z S' N h).W, (upL Z S' N h).V, (upL Z S' N h).S, (upL Z S' N h).N, (upL Z S' N h).G⟩ t.r.z.alg := by
    apply Algebra.algebra_ext
    intro r
    apply (w.st (upL Z S' N h)).B.embLL.injective
    exact (by with_unfolding_all exact (((alg_eq' r).trans (t.r.z.alg_eq r).symm) :))
  subst ha
  change HEq R' _ at hR
  have hR2 := eq_of_heq hR
  subst hR2
  exact (by with_unfolding_all exact ((listPin_upL (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) S' N h cDep b hp) :))

end GlobalTheory.Mem.GridMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralPointPolyCovol
section
noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.LieBase

theorem hasChernIntegral_pointPoly_covol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → HasChernIntegral Eb (openPart j) (lieGram e U hj f₀ A₀) (pointPoly H Dw) (GlobalTheory.TrueCx.covol (U.X k)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL
  have h0 := GlobalTheory.T.chernTopForm_negativePart_eq_zero_of_nonneg_on_open Eb (openPart j) (lieGram e U hj f₀ A₀) (pointPoly H Dw)
    (_root_.GlobalTheory.PointFormSign.chernTop_pointPoly_lieGram_nonneg E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL)
  have h1 := _root_.GlobalTheory.BaseVolume.mass_openPart_eq_covol E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL
  have hc := (GlobalTheory.TrueCx.covol_pos (U.X k)).le
  refine ⟨fun ε => ?_, ?_⟩
  · rcases Int.units_eq_one_or ε with rfl | rfl
    · rw [h1]; exact ENNReal.ofReal_ne_top
    · rw [h0]; exact ENNReal.zero_ne_top
  · rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def, h1, h0, ENNReal.toReal_ofReal hc]; simp

end GlobalTheory.LieBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricLieGramIsGoodMumford
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.LieBaseGood

theorem lieGram_isGood : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → IsGood Eb (openPart j) (lieGram e U hj f₀ A₀) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU C X j f f₀ Eb A₀ hj hL y hy
  obtain ⟨ch, a, ha, g, rk, τ₀, B, hP, hHolo, hys, hy0, hpoly, hbd, A, hA, Q, hQ, hcard, hind, hform, horth⟩ :=
    _root_.GlobalTheory.LieBase.HodgeChart.exists_hodge_period_chart E H Dw l Xo c O β Y T F e σ U hσ hU C X j f f₀ Eb A₀ hj hL y hy
  obtain ⟨ρ, hρ, hρ2, c₀, N₀, hb⟩ := _root_.GlobalTheory.HodgeInvGood.inv_hodgeGram_goodBound X.dim a ha g rk τ₀ B hP
  let W : Set (ReciprocityTheory.L2DbarEstimates.V X.dim) :=
    (ch.target ∩ ch.symm ⁻¹' GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j)) ∩
      WithLp.ofLp ⁻¹' GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ
  have hWo : IsOpen W := (ch.isOpen_inter_preimage_symm (GlobalTheory.CxPts.isOpen_ptsIn _)).inter
    ((GlobalTheory.HodgeChartRow.isOpen_punctured ha ρ).preimage (PiLp.continuous_ofLp 2 _))
  let G₀ : ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin g) (Fin g) ℂ :=
    fun u => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹
  let Q' : ∀ τ : E →+* ℂ, ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin (Dw.mult τ)) (Fin g) ℂ := fun τ u => Q τ u.ofLp
  have hdo : Differentiable ℂ (WithLp.ofLp : ReciprocityTheory.L2DbarEstimates.V X.dim → Fin X.dim → ℂ) :=
    (EuclideanSpace.equiv (Fin X.dim) ℂ).differentiable
  have hQ' : ∀ τ i k, DifferentiableOn ℂ (fun u => Q' τ u i k) (Metric.ball 0 1) := by
    intro τ i k
    refine (hQ τ i k).comp hdo.differentiableOn fun u hu k' => ?_
    exact (PiLp.norm_apply_le u k').trans_lt (by simpa using hu)
  have hind' : LinearIndependent ℂ (fun p : Σ τ, Fin (Dw.mult τ) => Q' p.1 0 p.2) := by
    simpa [Q'] using hind
  have hG₀ : ∀ v ∈ W, (G₀ v).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => G₀ u i k) v) ∧
      GlobalTheory.GoodMetric.GoodBound (Finset.univ.map (Fin.castLEEmb ha)) c₀ N₀ G₀ v := by
    intro v hv
    obtain ⟨hpd, hcd, hgb⟩ := hb v hv.2
    refine ⟨?_, hcd, hgb⟩
    exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hpd.det_pos.ne')).ne_zero
  have horth' : ∀ v ∈ W, ∀ τ τ', τ ≠ τ' → Q' τ v * G₀ v * (Q' τ' v)ᴴ = 0 := by
    intro v hv τ τ' hne
    have := horth (ch.symm v) (ch.map_target hv.1.1) hv.1.2 τ τ' hne
    rwa [ch.right_inv hv.1.1] at this
  obtain ⟨r', hr', c', N', hfr⟩ := _root_.GlobalTheory.FrameGood.frame_summands_goodBound X.dim g (Finset.univ.map (Fin.castLEEmb ha)) W G₀ c₀ N₀ (E →+* ℂ)
    Dw.mult Q' 1 hWo one_pos hQ' hcard hind' hG₀ horth'
  refine ⟨ch, Finset.univ.map (Fin.castLEEmb ha), hHolo, hys, ?_, ?_, A, hA, c', N', ?_⟩
  · intro b _
    rw [hy0]
    rfl
  · intro z hz
    rw [hbd z hz]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨Fin.castLE ha i, by simp, hi⟩
    · rintro ⟨b, hb', hb0⟩
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hb'
      exact ⟨i, hb0⟩
  · have h1 : ∀ᶠ z in nhds y, z ∈ ch.source ∧ ch z ∈ Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V X.dim) (min r' ρ) :=
      Filter.Eventually.and (ch.open_source.mem_nhds hys) ((ch.continuousAt hys).preimage_mem_nhds
        (by rw [hy0]; exact Metric.ball_mem_nhds _ (lt_min hr' hρ)))
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with z hz hzO τ
    obtain ⟨hzs, hzb⟩ := hz
    rw [mem_ball_zero_iff] at hzb
    have hzW : ch z ∈ W := by
      refine ⟨⟨ch.map_source hzs, Set.mem_preimage.2 (by rw [ch.left_inv hzs]; exact hzO)⟩, ?_, ?_⟩
      · exact fun k => (PiLp.norm_apply_le _ k).trans_lt (hzb.trans_le (min_le_right _ _))
      · intro i hi
        exact (hbd z hzs).2 ⟨i, hi⟩ hzO
    have hGB := hfr (ch z) hzW (hzb.trans_le (min_le_left _ _)) τ
    refine _root_.GlobalTheory.GoodMetric.goodBound_congr_nhds X.dim _ _ c' N' _ _ (ch z) ?_ hGB
    filter_upwards [hWo.mem_nhds hzW] with u hu
    have := hform (ch.symm u) (ch.map_target hu.1.1) hu.1.2 τ
    rw [ch.right_inv hu.1.1] at this
    exact this.symm

end GlobalTheory.LieBaseGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerThetaStepsPreserveFaceLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.DTheta

theorem stepLev_holds : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → GlobalTheory.Mem.R3.DTheta.StepLev R.toRealDat F.lv2 := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH b t k hk y hy
  have hx0 := (R.ioY t k y).2
  have hT := Formalism.IndefR.Eqv.contAt_of_mem ((mem_multT _ _ _ _ _).1 hx0)
  have hx := hx0
  rw [mem_multT, GlobalTheory.MultMem.mem_mult_iff] at hx ⊢
  refine ⟨hx.aut, hx.cusp, ?_, hx.equiv, hx.cont⟩
  intro v κ hκ g
  obtain ⟨κ', hκ', hω⟩ := GlobalTheory.Mem.R3.DTheta.StepLevLift.stepLev_lift D G Pl0 I0 T A3 Ks R F cG hP hH b t k hk κ hκ
  have hpt := _root_.GlobalTheory.Mem.R3.DTheta.StepLevFock.om_ptY_of_finite D G Pl0 I0 T A3 Ks R F cG hP hH t k hk κ hκ.1 κ' hκ'.1 _ hω
  have hval := GlobalTheory.Mem.R3.DTheta.stepLev_change D G Pl0 I0 T A3 Ks R F cG hP hH b t k hk κ κ' hκ' _ hpt y hy
  set x := (R.ioY t k y).1 with hxdef
  set c0 := levChi (Yc D k) (R.βY k) (R.datYt t k (R.toRealDat.levR F.lv2 b)) κ with hc0
  set c1 := levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) κ' with hc1
  have hne : c1 ≠ 0 := by rw [hc1]; unfold levChi; exact Units.ne_zero _
  let u : MMap (R.MY k) := (LinearMap.funLeft ℂ ℂ (fun h : GA D (Yc D k) => h * κ)).compMultilinearMap
    (PiTensorProduct.lift.symm x) - c0 • PiTensorProduct.lift.symm x
  have hu : Formalism.IndefR.Eqv.ContAt (R.MY k) u := by
    intro τ v' z
    obtain ⟨ℓ₁, s₁, e₁⟩ := hT τ v' (z * κ)
    obtain ⟨ℓ₂, s₂, e₂⟩ := hT τ v' z
    refine ⟨ℓ₁ + (-c0) • ℓ₂, GlobalTheory.MultMem.sobCont_add s₁ (GlobalTheory.MultMem.sobCont_smul _ s₂), fun w => ?_⟩
    simp only [u, LinearMap.add_apply, LinearMap.smul_apply, e₁, e₂, MultilinearMap.sub_apply,
      MultilinearMap.smul_apply, LinearMap.compMultilinearMap_apply, Pi.sub_apply, Pi.smul_apply,
      LinearMap.funLeft_apply, smul_eq_mul]
    ring
  have hz : ∀ φ w, PiTensorProduct.lift u (R.ItY k φ w) = 0 := by
    intro φ w
    have e : PiTensorProduct.lift u = (LinearMap.funLeft ℂ ℂ (fun h : GA D (Yc D k) => h * κ)) ∘ₗ x - c0 • x := by
      apply PiTensorProduct.ext
      ext v'
      simp [u]
    rw [e]
    funext g'
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
      LinearMap.funLeft_apply, smul_eq_mul, Pi.zero_apply]
    rw [hval φ w g']
    field_simp
    ring
  have h0 := GlobalTheory.Mem.R3.StepUniq.eq_zero_of_vanish_it hC.1 hC.2.1 D G Pl0 I0 T A3 Ks R F cG hP hH t k hk u hu hz
  have h1 := congrFun (congrArg (fun U : MMap (R.MY k) => U v) h0) g
  simp only [u, MultilinearMap.sub_apply, MultilinearMap.smul_apply, LinearMap.compMultilinearMap_apply, Pi.sub_apply,
    Pi.smul_apply, LinearMap.funLeft_apply, smul_eq_mul, MultilinearMap.zero_apply, Pi.zero_apply] at h1
  linear_combination h1

end GlobalTheory.Mem.R3.DTheta
end

