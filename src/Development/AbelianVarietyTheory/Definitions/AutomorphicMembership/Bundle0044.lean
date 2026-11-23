module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsChartOfMaximal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0511
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0531
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieAll
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieFin
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.GTiedFOfIsRecCEv
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0008
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.BlockRationalityField
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0014
public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.ColSpanMulUnit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroOfSetting
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocIdOfCompletions
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0186
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad

namespace admitted

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  (z : admitted Y i₀)

def stepLB (b : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : FinLB z.Z.X :=
  match h : letterOf Dw st with
  | some x => (z.line b st x h).L
  | none => FinLB.triv _

theorem stepLB_of_some (b : Bool) {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw} (h : letterOf Dw st = some x) :
    z.stepLB b st = (z.line b st x h).L := by
  unfold stepLB
  split
  · next y hy => obtain rfl : y = x := Option.some.inj (hy.symm.trans h); rfl
  · next hy => exact absurd (hy.symm.trans h) (by simp)

variable (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)

section Step

variable {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw} (h : letterOf Dw st = some x)

def genId : GenIso z.Z (z.line false st x h).L (z.line true st x h).L :=
  (exists_isGenId hp hW z.full (GenId.bdd_step hp st) _ _).choose

end Step

variable (d : ℕ) {r : ℕ} {st : Fin r → ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Fin r → Letter Dw}
  (h : ∀ i, letterOf Dw (st i) = some (x i))

def stepPair : DV.FPair (ithOf hp hW z.Z d) r :=
  fpairOf hp hW d (fun i => (z.line false _ _ (h i)).L) (fun i => (z.line true _ _ (h i)).L) fun i => z.genId hp hW (h i)

def dualPair : DV.FPair (ithOf hp hW z.Z d) r :=
  fpairOf hp hW d (fun i => (z.line false _ _ (h i)).L.dual) (fun i => (z.line true _ _ (h i)).L.dual)
    fun i => NModel.GenIso.dual (z.genId hp hW (h i))

theorem pair_x_eq_LB_false (i : Fin r) : (z.stepPair hp hW d h).x i = z.stepLB false (st i) := (z.stepLB_of_some _ _).symm

theorem dualPair_x_eq_dual_LB_false (i : Fin r) : (z.dualPair hp hW d h).x i = (z.stepLB false (st i)).dual :=
  congrArg FinLB.dual (z.stepLB_of_some _ _).symm

omit hp

variable [Fact p.Prime]

include hW

end admitted

section Ranks

variable {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j) {p : ℕ} [Fact p.Prime] (jc : DV.KW p →+* ℂ)

theorem comp_cEmb (τ : DV.Emb D p) : jc.comp (DV.cEmb D τ) = conjEmb (jc.comp τ) :=
  RingHom.ext fun x => Formalism.MainNotions.WeightFamilies.emb_conj D (jc.comp τ) x

theorem mult_comp (τ : DV.Emb D p) : S.Dw.mult (jc.comp τ) = DV.rkOf (DV.PsiOf D jc) N j τ := by
  have h₁ := S.p_eq
  have h₂ := S.rank_eq
  by_cases h : τ ∈ DV.PsiOf D jc
  · obtain ⟨t, ht⟩ := id h
    rw [DV.rkOf, if_pos h, ht, Datum.mult, if_pos (A.cm t), h₁]
  · obtain ⟨t, ht⟩ : DV.cEmb D τ ∈ DV.PsiOf D jc := by_contra fun h' => h ((cm_type_meets_conjugate_pair p jc τ).2 h')
    have h₃ := GlobalTheory.Proof.LetterConjugation.mult_add S.Dw (jc.comp τ)
    rw [← comp_cEmb, ht, Datum.mult.eq_1 _ (DV.tauEmb D t), if_pos (A.cm t)] at h₃
    rw [DV.rkOf, if_neg h]
    omega

theorem mult_conj_comp (τ : DV.Emb D p) : S.Dw.mult (conjEmb (jc.comp τ)) = N - DV.rkOf (DV.PsiOf D jc) N j τ := by
  have h₁ := GlobalTheory.Proof.LetterConjugation.mult_add S.Dw (jc.comp τ)
  have h₂ := S.rank_eq
  rw [mult_comp] at h₁
  omega

theorem length_letters : (letters S.Dw).length = D.R.f * N := by
  have h := GlobalTheory.Proof.LetterConjugation.two_mul_length S.Dw
  rw [GlobalTheory.Proof.LetterConjugation.finrank_host, S.rank_eq, mul_assoc] at h
  omega

theorem letterOf_lie (τ : DV.Emb D p) (i : Fin (DV.rkOf (DV.PsiOf D jc) N j τ)) :
    letterOf S.Dw (.inl (jc.comp τ, i)) = some ⟨jc.comp τ, i.cast (mult_comp S jc τ).symm⟩ :=
  dif_pos (i.cast (mult_comp S jc τ).symm).2

theorem letterOf_om (τ : DV.Emb D p) (i : Fin (N - DV.rkOf (DV.PsiOf D jc) N j τ)) :
    letterOf S.Dw (.inl (conjEmb (jc.comp τ), i.rev)) =
      some ⟨conjEmb (jc.comp τ), i.rev.cast (mult_conj_comp S jc τ).symm⟩ :=
  dif_pos (i.rev.cast (mult_conj_comp S jc τ).symm).2

theorem letterOf_whole (k : Fin (D.R.f * N)) :
    letterOf S.Dw (.inr k) = some ((letters S.Dw).get (k.cast (length_letters S).symm)) :=
  List.getElem?_eq_getElem (k.cast (length_letters S).symm).2

end Ranks

section Mdl

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime}
  {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (jc : DV.KW p →+* ℂ)

def mdlOf : DV.Mdl D p N (DV.rkOf (DV.PsiOf D jc) N j) where
  Z := ithOf hp hW z.Z (Formalism.DegreeFormula.dimFl D.what₂.Tau N)
  cov := cov z
  cov_pos := cov_pos z
  lvl := z.n
  lie τ := z.stepPair hp hW _ (letterOf_lie S jc τ)
  om τ := z.dualPair hp hW _ (letterOf_om S jc τ)
  lieW := z.stepPair hp hW _ (letterOf_whole S)
  omW := z.dualPair hp hW _ fun k => letterOf_whole S k.rev
  om_dual τ := ⟨Fin.revPerm.trans (finCongr (by rw [← mult_conj_comp S, ← mult_comp S, comp_cEmb])), fun i => by
    rw [admitted.dualPair_x_eq_dual_LB_false, admitted.pair_x_eq_LB_false]
    exact (FinLB.firstChern_dual _).trans
      (congrArg (fun σ => -(admitted.stepLB z false (.inl (σ, i.rev))).c1) (comp_cEmb jc τ).symm)⟩
  dim_eq := rfl
  omW_dual := ⟨Fin.revPerm, fun _ => FinLB.firstChern_dual _⟩

variable {jc} {t : D.what₂.Tau} {τ : DV.Emb D p} (ht : jc.comp τ = DV.tauEmb D t)

include ht

end Mdl

section PiLocalization₂

variable {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j) (κ : Lv A)
  (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ))
  (hj : ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la))

theorem one_add_lt_three {p : ℕ} (hp : p.Prime) : 1 + 1 / ((p : ℝ) - 1) < (3 : ℕ) := by
  have h : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have : 1 / ((p : ℝ) - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  push_cast
  linarith

abbrev AdmPl (p : ℕ) [Fact p.Prime] (la : PlL D p) : Type :=
  AdmAt S κ Fact.out (placeW_over D p la (jC p la) (hj p la)).1

def admissible_representation_factorisation (hA : AdmEx S κ) : AdmSt D N j jC where
  admitted p _ la := AdmPl S κ jC hj p la
  mdl p _ la z := mdlOf z (jC p la)
  Crv _ _ _ z := Crv z
  deg _ _ _ z c x := degRoot z c (DV.tauEmb D x.1) x.2
  ht p _ _ := (hA p Fact.out _ _ 3 (one_add_lt_three Fact.out)).choose

variable (hA : AdmEx S κ) (p : ℕ) [Fact p.Prime] (la : PlL D p)

end PiLocalization₂

section Examples

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)

end Examples

end GlobalTheory.ShFam.Pad
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsEmbeddingOfRingTie
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

namespace GlobalTheory.Mem.LocalPack.Test

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar


section Reduction

open Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags

theorem block_rational : Formalism.L2.G.BlockRationalityField := by
  intro p O Kf _ _ _ _ _ P Tau _ n LL _ h pos G M embLL lam hW hM
  exact blockRatReal P.lam0 h pos G M embLL (fun τ => (lam τ).w) (fun τ => (lam τ).anti) hW hM

variable (D : D7) (sc : Scale)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc 1 (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)
  (H0 : Formalism.L2.Herm.Herm0 (recC D sc 1 Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
  (T : ∀ u : D.what₂.Word, Forms0 (recC D sc 1 Lc I ψ hd) u)
  (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc 1 Lc I ψ hd) B)
  (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
    (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
      (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
  (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
  (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
  (hK : ∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
    lamV (lam u w hg) (D.what₂.embLL z))
  (hPos : ∀ u w hg, (packC D Lc I ψ u w hg).posOK (iK u w hg) (lam u w hg))


set_option maxHeartbeats 32000000 in
include hK hPos in
theorem comparison_statements (hJ : ∀ u, Joint0 H0.lev0 u (T u))
    (h0 : ∀ u, LevelZeroCharacterRational (D := recC D sc 1 Lc I ψ hd) T u)
    (hψ : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      PsiTied (LL := D.what₂.LL) (O := ORec D w (nFr D (D.what₂.places.resChar w)))
        (Kf := KfRec D w (nFr D (D.what₂.places.resChar w)))
        ((T u).cls0).lev (Lc u) (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        ((cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB).embW u w hg) (ψ u w hg)) :
    CmpHyp0P T (gatTiesC D sc 1 Lc I ψ hd) (cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB) := by
  have hpos := fun u w hg v s x => pos_C D sc 1 Lc I ψ hd H0 hL B hBs hB iK lam hK hPos u w hg v s x
  have hs : ∀ u, SameUloc (hermitianLevelZeroOfRecursion D sc 1 Lc I ψ hd H0 hL) T u :=
    fun u => sameUloc_of_joint (hermitianLevelZeroOfRecursion D sc 1 Lc I ψ hd H0 hL) T u (hJ u)
  have N : CmpLeft D sc 1 Lc I ψ hd H0 hL T B hBs hB :=
    { same := hs
      blk := fun u w hg => blkRatRec_of_stmt block_rational _ _ u w hg B
      psi0 := h0
      chi := chi_C D sc 1 Lc I ψ hd H0 hL T B hBs hB hψ
      valInt := valIntRec_of weylLatticeDescent_holds
        (fun u w hg => ex_C_blk D sc 1 Lc I ψ hd H0 hL T B hBs hB u (hs u) w hg
          (blkRatRec_of_stmt block_rational _ _ u w hg B) (h0 u))
        (fun u w hg => frac_of_gatIs _ u w hg (gatIs_recC D sc 1 Lc I ψ hd H0 hL
          (fun u w h => isHyperbolicAt_rec_of_placeIdentification D u w h (I u w h)) u w hg))
        (restExB _)
        (restLatO_of hpos (restLatW_of (D := recC D sc 1 Lc I ψ hd) T (cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB) (fun u => hJ u))
          (restGramW_of (D := recC D sc 1 Lc I ψ hd) T (cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB)))
        (restChi_of (D := recC D sc 1 Lc I ψ hd) T h0) }
  exact N.toHyp0P hpos


end Reduction


end GlobalTheory.Mem.LocalPack.Test
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PositionMv (𝒮 : Slots) : Prop :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj2 (w.D Z)) (x : Wit 𝒮 K w Z O)
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (O' : Obj2 (w.D (Db.setDivZ Z N h))), O' = O.tr N h →
    ∀ (col : ColumnDataSplitPrimes K w (Db.setDivZ Z N h)) (n : NchT w (Db.setDivZ Z N h) x.Wt O'.nch),
    ∃ t : RowsT K w (Db.setDivZ Z N h) x.Wt O'.p0, ObjT O' t ∧
      Nonempty (𝒮.Rx K B f T w (Db.setDivZ Z N h) x.Wt O'.p0 t) ∧
      Nonempty (𝒮.Nx K B f T w (Db.setDivZ Z N h) x.Wt O'.p0 t O'.nch n O'.xd) ∧
      Nonempty (𝒮.Sx K B f T w (Db.setDivZ Z N h) x.Wt O'.p0 t col.toColT) ∧
      Nonempty (𝒮.Ox K B f T w (Db.setDivZ Z N h) x.Wt O' t)

def WitMv (𝒮 : Slots) : Prop :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj2 (w.D Z)) (x : Wit 𝒮 K w Z O)
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), EntC x.ker →
    ∃ x' : Wit 𝒮 K w (Db.setDivZ Z N h) (O.tr N h), EntC x'.ker

end GlobalTheory.Mem.Top.Bl

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
section
noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

abbrev Dof (x : St P) : D7 := (w.st x.o.Z).toD7

abbrev cfOf (x : St P) : CharFrame (Dof x) := TC.cf w.I w.l x.o.Z


open Classical in
def QOf (P : Pre2 K w) (v : B.places.Pl) : Finset (HeightOneSpectrum (𝓞 B.host.E)) := if v ∈ P.Wt then T.Q v else ∅

structure LA (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 where
  a : StA hL (Dof x) (cfOf x) (repOf x.r.Y)
  Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (Dof x).host.E)) → PlE (Dof x).host
  Pq_over : ∀ v, NG.OverPl (Pq v) v
  sel : Set.range Pq = Set.range w.I.sel

structure LI (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends LA hL x where
  mt : InMt x.r.Y (cfOf x) w.I.xi (QOf P)
  rat : InRat x.r.Y x.m.z.cG
  cusp : RowCusp (Dof x) a.A.row

structure SeriesLevel (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends LI hL x where
  b : SeriesState x.m.z.geo a rat mt.ad.PV Pq

structure StrictHenselianAcyclic (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends LI hL x where
  b : ModuliPointsState x.m.z.geo a rat mt.ad.PV Pq

structure LC (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends StrictHenselianAcyclic hL x where
  c : StC mt b T.k T.psi

abbrev AllSt (p : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop) : Prop :=
  StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), p K B f T w P x

variable (hL)

def SMt : Prop := AllSt fun _ _ _ _ w P x => Nonempty (InMt x.r.Y (cfOf x) w.I.xi (QOf P))

structure Kept {D D' : D7} (c : NChoice D) (c' : NChoice D') : Prop where
  gal : GlobalTheory.TwistChoice.SameGalois D.nd D'.nd
  set : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients D.ntw D'.ntw
  forms : GlobalTheory.TwistChoice.SameForms D.nexp D'.nexp
  br : HEq D.ntwbr D'.ntwbr
  twI : HEq c.twI c'.twI
  sd : HEq c.sd c'.sd
  Q : HEq c.Q c'.Q
  k : HEq c.k' c'.k'
  psi : HEq c.psi' c'.psi'

end GlobalTheory.HeightCounting.Up

end
end

