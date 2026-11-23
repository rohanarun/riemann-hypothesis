module

public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0023
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0723
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0759
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0021
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
public import Formalism.LocalToGlobal.HilbertRowConditions.ColumnsFunctionAtSubspaces
public import Formalism.LocalToGlobal.HilbertRowConditions.RowPinMin
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVColPins
section
set_option synthInstance.maxHeartbeats 200000

section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.L2.DIV
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Rows
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
def lamOfCol_alt {T : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex} (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) :
    ∀ (_ : D.what₂.Word) (i : ℕ), D.what₂.Tau → DomWeight (D.R.N i) :=
  fun u i τ =>
    cast (congrArg (fun R : Ranks => DomWeight (R.N i)) K.kerTie.2.1)
      (K.c.W.lamTrue (K.c.wd (cast K.kerTie.2.2.2.2.2.2.2.2.2.2.2.2.1.symm u)) i
        (cast (congrArg Formalism.L2.Col.Fields.Tau K.kerTie.1) (T.ker.seam.iT.symm τ)))
open Classical in
def columnAddCharacter {T : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex} (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) : ∀ PP : Pl K.X.E, AddChar (kP PP) D.what₂.LL :=
  fun PP => if h : PP ∈ K.c.Pr.vGs then K.c.Ch.psi0 ⟨PP, h⟩ else 1
open Classical in
structure ColumnCharactersCompatible {T : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex} (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) : Prop where
  grpTie : HEq P.grp (inferInstance : Group (Formalism.L2.Col.G0 K.X.E K.c.Pr.vGs K.c.Rk.r))
  psTie : HEq P.Ps K.c.Lv.grp ∧ HEq P.ψs K.c.Lv.chr
  pointCharacterEq : HEq P.P0 (P0 K.c.Pr.vGs K.c.Rk.r (_root_.Formalism.L2.DIV.columnAddCharacter K)).H ∧ HEq P.ψ0 (P0 K.c.Pr.vGs K.c.Rk.r (_root_.Formalism.L2.DIV.columnAddCharacter K)).chi
  wOk : K.c.W.Ok
  chOk : K.c.Ch.Ok
  hcTie : ∀ (u : D.what₂.Word) (τ : D.what₂.Tau),
    HEq (K.c.W.hc (K.c.wd (cast K.kerTie.2.2.2.2.2.2.2.2.2.2.2.2.1.symm u))
      (cast (congrArg Formalism.L2.Col.Fields.Tau K.kerTie.1) (T.ker.seam.iT.symm τ))) (D.hcW u τ)
  wtTie : ∃ (sh : D.what₂.Word → ℕ → D.what₂.Tau → ℤ) (n : D.what₂.Word → ℕ → D.what₂.Tau → ℕ),
    Formalism.L2.Ker.KerEntTied.WtTie T.ker (_root_.Formalism.L2.DIV.lamOfCol_alt K) sh n
  xgTie : ∀ χ : Formalism.L2.Col.G0 K.X.E K.c.Pr.vGs K.c.Rk.r → D.what₂.LL,
    χ ∈ K.c.Xg ↔ (fun g => χ (cast K.gEq (P.I.eG.symm g))) ∈ Formalism.L2.Col.XgE K.c.Am.σ₀ D.ntypes.e0
  qNF : ∀ (t : P.A3.fam3.base3.Tup) (j : ℕ) (b : (K.c.Li t).β j)
      (v : ↥(Formalism.L2.Col.uSG K.c.Pr.vGs (Formalism.L2.Col.QE K.c.sel (K.c.mu t : Chr K.X.F K.X.E D.what₂.LL)))),
      v.1 ∉ K.c.Pr.vGs → 1 ≤ j → j + 2 ≤ K.c.Rk.m →
      ∃ (nn : Fin (Formalism.L2.Col.cOf K.c.Rk j) → ℤ) (z : Fin (K.c.Rk.N j) → K.X.E),
        (∀ i, -(j : ℤ) ≤ nn i ∧ nn i ≤ 0) ∧
        (fun l : Fin (K.c.Rk.N j + Formalism.L2.Col.cOf K.c.Rk j) => if h : l.1 < K.c.Rk.N j then z ⟨l.1, h⟩ else 0) ∈
          Formalism.L2.Col.lamYat (Pr := K.c.Pr) (R := K.c.Rk) j v.1 ∧
        (Formalism.L2.Col.lamYat (Pr := K.c.Pr) (R := K.c.Rk) j v.1).map
                  (((K.c.Li t).h j b v).toLinearMap.restrictScalars (𝓞 K.X.E)) =
          (Formalism.L2.Col.lamYat (Pr := K.c.Pr) (R := K.c.Rk) j v.1).map
            ((Matrix.toLin' (nfMat (K.c.Rk.N j) (Formalism.L2.Col.cOf K.c.Rk j) ((Formalism.L2.Col.qOf v.1 : ℕ) : K.X.E) nn z)).restrictScalars
              (𝓞 K.X.E))
  columnEvaluationOk : ∃ hM : (Formalism.L2.Col.rowGSD K.c.W (Formalism.L2.Col.rowTyG K.c.Ch K.c.Lv).inv).Ok, ∀ u : D.what₂.Word,
    ∃ ι : (D.mem u).P.Mt ≃ₗ[ℂ] (Fin ((Formalism.L2.Col.rowGSD K.c.W (Formalism.L2.Col.rowTyG K.c.Ch K.c.Lv).inv).hDim hM) → ℂ),
      (∀ (t : P.A3.fam3.base3.Tup) (ht : P.I.tup t = D.what₂.mu0)
        (hQ : Formalism.L2.Col.QE K.c.sel (K.c.mu t : Chr K.X.F K.X.E D.what₂.LL) = ∅)
        (y : Fin (rDim D P.A3.A P.Ps P.ψs t) → D.what₂.LL),
        ∃ (F' : (Formalism.L2.Col.mtildeKGSD K.c.W K.c.Ch K.c.sel (K.c.mu t)).EqFun)
          (hm : F'.1 ∈ (Formalism.L2.Col.mtildeGSD K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.Lv).EqFun),
          HEq ((Formalism.L2.Col.mtildeKGSD K.c.W K.c.Ch K.c.sel (K.c.mu t)).res
              (Formalism.L2.Col.mtildeKOk K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.hX) F')
            ((P.A3.A.fam.R t).S.basis.equivFun.symm
              (((P.A3.A.fam.R t).S.cutE (P.A3.A.fam.R t).r (lvlIdem (P.A3.A.fam.lvl P.Ps P.ψs).P
                (P.A3.A.fam.lvl P.Ps P.ψs).ψ)).mulVec y)) ∧
          ι ((D.eMt u).symm (ht ▸ P.I.jA t y)) =
            Formalism.L2.Col.zOfRow K.c.W K.c.Ch K.c.sel (K.c.mu t) hQ K.c.Lv K.c.Am.σ₀ hM ⟨F'.1, hm⟩) ∧
      ∀ (t : P.A3.fam3.base3.Tup) (ht : P.I.tup t = D.what₂.mu0)
        (hQ : Formalism.L2.Col.QE K.c.sel (K.c.mu t : Chr K.X.F K.X.E D.what₂.LL) = ∅)
        (F : Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV t) → D.what₂.LL),
        ∃ hm : ((K.c.ev P.Zs t F : Formalism.L2.Col.V0X K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.Xg K.c.Lv) :
            (Formalism.L2.Col.mtildeKGSD K.c.W K.c.Ch K.c.sel (K.c.mu t)).EqFun).1 ∈
            (Formalism.L2.Col.mtildeGSD K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.Lv).EqFun,
          ι ((D.eMt u).symm (ht ▸ P.I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F))) =
            Formalism.L2.Col.zOfRow K.c.W K.c.Ch K.c.sel (K.c.mu t) hQ K.c.Lv K.c.Am.σ₀ hM ⟨_, hm⟩
end Formalism.L2.DIV
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTwOpenExpRel
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting.FitTwExp
set_option maxHeartbeats 8000000 in
theorem exists_twOpen_expRel_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D'), Elem b.D → GlobalTheory.RowTie.ChebSplit b.D.nd → ∃ Tw : TwOpen (withLoc b.L) (chL b.L b.C) (cfL b.L b.cf) (tpL b.L b.tp) (mtL b.L b.M) b.low, ExpRel b.L b.Bs.exp Tw.exp := by
  intro hL D' b hE hC
  obtain ⟨Tw⟩ := _root_.GlobalTheory.HeightCounting.FitTw.nonempty_twOpen_alt b.D b.cf b.jE b.A b.low b.Pq b.S b.hL b.eig b.θ b.Bs b.M b.C b.tp b.ch b.mt hE.star hE.int hE.split hC b.big b.L b.Sp b.Au
  refine ⟨{ Tw with exp := GlobalTheory.HeightCounting.FitTw.expL b.L b.Bs.exp, ch := GlobalTheory.HeightCounting.FitTw.chSideL b.Sp b.ch }, ?_⟩
  exact
    { tau := fun h => h
      pl := fun _ _ _ _ _ _ _ _ _ => rfl
      reads := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => h }
end GlobalTheory.HeightCounting.FitTwExp
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtOfBuilt
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.CoefDuty.ExtBuilt
theorem extOf_built_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ big₀ L₀, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → ∃ big₁, ∀ L₁, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ i₁, ∃ i₀, ExtOf L₀ L₁ i₀ i₁ := by
  intro hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hst hex hsp hCh big₀ L₀ hB₀
  obtain ⟨big₁, hR⟩ := _root_.GlobalTheory.T.side_eigen_level_alt hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hst hex hsp hCh big₀ L₀ hB₀
  refine ⟨big₁, fun L₁ hB₁ i₁ => ?_⟩
  obtain ⟨i₀, hw, hj, e, he⟩ := _root_.GlobalTheory.T.side_eigen_weight_alt hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hst hex hsp hCh big₀ big₁ L₀ L₁ hB₀ hB₁ i₁
  obtain ⟨φ, hφ, hφa⟩ := hR L₁ hB₁ i₀ i₁ hw
  have hZ := _root_.GlobalTheory.T.side_eigen_conductor_alt hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hst hex hsp hCh big₀ big₁ L₀ L₁ hB₀ hB₁ i₀ i₁ hw hj e he
  have hchi := _root_.GlobalTheory.T.side_eigen_character_alt hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hst hex hsp hCh big₀ big₁ L₀ L₁ hB₀ hB₁ i₀ i₁ hw hj φ hφ hφa
  have hl : L₀.lay.fixZ.nd.l i₀ = L₁.lay.fixZ.nd.l i₁ := by
    rw [← L₀.lay.fixZ.nd.w_l, ← L₁.lay.fixZ.nd.w_l, hw]
  have hQ : L₀.lay.fixZ.nd.Q i₀ = L₁.lay.fixZ.nd.Q i₁ := by
    obtain ⟨Sp₀, -, -⟩ := hB₀
    obtain ⟨Sp₁, -, -⟩ := hB₁
    have h0 := Sp₀.Q_eq _ _ i₀ ((L₀.X.locs_mem _ _ i₀).2 ⟨rfl, rfl⟩)
    have h1 := Sp₁.Q_eq _ _ i₁ ((L₁.X.locs_mem _ _ i₁).2 ⟨rfl, rfl⟩)
    rw [Sp₀.Qc_eq] at h0
    rw [Sp₁.Qc_eq] at h1
    exact h0.trans ((congrArg C.Q hw).trans h1.symm)
  have hS : ∀ v, v ∈ L₀.lay.fixZ.nd.S i₀ ↔ v ∈ L₁.lay.fixZ.nd.S i₁ := by
    intro v
    rw [L₀.lay.fixZ.nd.S_def, L₁.lay.fixZ.nd.S_def, hl]
  have hout : ∀ v, SplitOut L₁.lay.fixZ.nd i₁ v ↔ SplitOut L₀.lay.fixZ.nd i₀ v := by
    intro v
    unfold SplitOut
    rw [hl, hQ, hS v]
  have hinj : Function.Injective (iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁) := by
    unfold iotaO
    exact (RingEquiv.injective _).comp ((RingHom.injective _).comp (IsFractionRing.injective _ _))
  have hcyc : ∀ (l l' : ℕ) (_ : l = l') [Fact l.Prime] [Fact l'.Prime] (σ : GE L₁.lay.fixZ.nd),
      HEq (cycZ (F := D.host.E) (Ω := L₀.lay.fixZ.nd.Om) l σ) (cycZ (F := D.host.E) (Ω := L₁.lay.fixZ.nd.Om) l' σ) := by
    intro l l' h _ _ σ
    subst h
    rfl
  refine ⟨i₀, hw, ⟨LocExt.mk hl φ hφ hφa e hout ?_ hZ (MulEquiv.refl _) continuous_id continuous_id
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun σ => hcyc _ _ hl σ) hchi⟩⟩
  intro v k x hv hk1 hk2
  apply hinj
  rw [hφ]
  exact he v k x hv hk1 hk2
end GlobalTheory.CoefDuty.ExtBuilt
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowerMapTieTw
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
namespace GlobalTheory.Mem.Col2.LowerTie
theorem lowerMap_tieTw_alt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (T : _root_.Formalism.L2.TiedDataSKAlt ex) (he : ex.tw = I.tw l l0 Z), I.StdC l Z T.cols → I.StdTw l Z l0 (he ▸ T.tw) → ∀ u a (ha : a ≠ (I.rec7 l Z).what₂.mu0) (h1 : 1 ≤ B.R.m), _root_.Formalism.L2.Rows.LowerMapTieTwAlt T u a ha h1 :=
  fun I hO hP l Z l0 _ _ _ _ _ _ _ _ T he hC hTw u a ha h1 => lowerMap_tw_gen I hO hP l Z l0 T.tw he hC hTw u a ha h1
end GlobalTheory.Mem.Col2.LowerTie
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 1000000
structure HeightCountingBaseData (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) : Type 1 where
  host : HostTied D
  jE : D.host.E →+* Qb
  frame : ∀ x, jE x = host.fr.j x
  A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE
  cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL D A.wdT
  au : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D A.wdT A.au
  row : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR
  fr : OmFrame D
  fr_jE : fr.jE = jE
  pht : PhtOn A.wd fr fun _ _ _ _ => True
  depth : RowDepth D rep
  elem : Elem D
  val : ValLL0 D cf
  labc : LabConj D A.wdT
  zeta : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen
  omax : Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x
section Rows
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F}
  {F : Face3 D A3} {X0 : BaseLevelRowSide D} (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {cf : CharFrame D}
variable {Y cG}
structure SettingsFormsData (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)) (n : InRat Y cG)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 where
  Bs : SideB D cf a.A.row (lowAll D) Pq n.S n.In.hL n.In.eig n.In.θ
  Sb_le : ∀ i, n.In.Sb ⊆ D.ntw.S0 i
  rootsOfUnityRing_le_wittIntegers : ∀ i, OverSet D (D.ntw.S0 i) (insert (D.ntw.l i) (lowAll D))
  lam : ∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z
variable (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1)
structure SeriesData (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)) (n : InRat Y cG) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 extends toSettingsFormsState : _root_.GlobalTheory.HeightCounting.SettingsFormsData a n Pq where
  YS : NExpRealS R cG n.S
  eF : YS.eF = Bs.eF
  fi : ∀ i x, HEq ((YS.fi i).e x) x
  ser : SerAt YS g.v₀ Bs.exp PV cf Pq
  tau : TauTrue Bs.exp
structure ModuliPointsData (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)) (n : InRat Y cG) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 extends toSeriesState : _root_.GlobalTheory.HeightCounting.SeriesData g a n PV Pq where
  geo : Nonempty (GlobalTheory.GeoTie.ThetaTie YS g.fw D.nth)
variable {g}
structure HeightCountingCharacterData {a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)} {n : InRat Y cG} {xi : D.what₂.Tup → HChar D.host.E}
    {Q : D.what₂.places.Pl → Finset (PlE D.host)} (m : InMt Y cf xi Q)
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} (b : _root_.GlobalTheory.HeightCounting.ModuliPointsData g a n m.ad.PV Pq)
    (k : D.what₂.places.Pl → ℕ) (psi : D.what₂.places.Pl → HChar D.host.E) : Type 1 where
  ch : NChoice D
  tp : TupTied D cf ch
  xi_eq : tp.xi = xi
  psi_eq : tp.psi = psi
  Q_eq : ch.Q = Q
  k_eq : ∀ w, TwistedAt D w → ch.k' w = k w
  side : ChoiceSide D cf m.M b.Bs.exp ch tp
  ok : ∀ w, TwistedAt D w → IntegralHeckeForms.TwOK (ch.twI w) (ch.k' w) (ch.Q w) ((ch.psi' w).comp (D.ntw.art (ch.twI w) (ch.Q w)))
  th : EMtTheta Y b.YS ch
structure RealExpansionExtraData {nch : NChoice D} {tp : TupTied D cf nch} {a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp} (r : _root_.GlobalTheory.Mem.Top.Bl.NormRealisationData a R F cG Y)
    (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (xd : ThData D) : Type 1 where
  ad : MtAd Y a.all.gal.mt
  fi : ∀ i x, HEq ((r.nexp.fi i).e x) x
  hecke : NExpHeckeRowX R cG _ r.nexp r.hecke fun _ => LinearMap.id
  cHk : ∀ i b P, ∃ u : (D.ntw.O i)ˣ, r.hecke.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u
  eig : ∃ Sb e, (∀ i, Sb ⊆ D.ntw.S0 i) ∧ HEq a.nt.eig e ∧ EigAd Y Sb e
  ser : SerAt r.nexp g.v₀ a.all.exp ad.PV cf a.Pq
  tau : TauTrue a.all.exp
  geo : Nonempty (GlobalTheory.GeoTie.ThetaTie r.nexp g.fw D.nth)
  ok : ∀ w, TwistedAt D w → IntegralHeckeForms.TwOK (nch.twI w) (nch.k' w) (nch.Q w) ((nch.psi' w).comp (D.ntw.art (nch.twI w) (nch.Q w)))
  th : EMtTheta Y r.nexp nch
  xd : XdAll xd
  large : GlobalTheory.CoefDuty.Large D
  labc : LabConj a.nt.D a.nt.A.wdT
  zeta : ∀ k, haveI : Fact (a.nt.D.host.g k).Prime := ⟨a.nt.D.host.g_prime k⟩
    a.nt.A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k)).gen
  pht : ∃ fr : OmFrame a.nt.D, fr.jE = a.nt.jE ∧ PhtOn a.nt.A.wd fr fun _ _ _ _ => True
end Rows
open GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl in
def defaultExtension (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun _ _ _ _ w Z _ _ t _ _ xd c =>
  _root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st Z).toD7) c.row t.r.z.geo xd
end GlobalTheory.HeightCounting
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowSideDetermined
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
namespace Formalism.L2.Rows
open Formalism.L2.DIV Formalism.L2.Indef
section Joint
variable (D : D7) {Gp : Type} [Group Gp] [Fintype Gp] {Pl0 I0 Ty T : Type}
  (A3 : FamIn3 D.what₂.LL Gp Pl0 I0 Ty T D.R.m)
end Joint
section Bundle
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}
variable {ex : Extra D L hT Gi Gl Kc Y cX}
open Classical in
structure RowSideDeterminedAlt (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) : Prop where
  lowerMap : ∀ u, LowerMapTieS (T.cols.forms u)
  lowerMapTw : ∀ u μ (hμ : μ ≠ D.what₂.mu0) (_hw : ∃ w, μ = D.what₂.muAt w) (h1 : 1 ≤ D.R.m), _root_.Formalism.L2.Rows.LowerMapTieTwAlt T u μ hμ h1
  buDef : Formalism.BasicNotions.Rows.BuDefQ D.what₂
  ambS : ∃ JA : AmbIds D P.A3.A (Formalism.BasicNotions.RowSide.sharp D) ex.amb P.Ps P.ψs P.I.tup,
    AmbTie D P.A3.A (Formalism.BasicNotions.RowSide.sharp D) ex.amb P.Ps P.ψs P.I.tup P.I.jA JA
  faces : ∃ (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs, SPer (Dcf Zs)),
    Dcf P.Zs = P.Dc ∧ HEq (Spf P.Zs) P.Sp
  gamDvd : (∀ (t : P.T) (c : (P.A3.A.fam.R t).S.Cl), Fintype.card ((P.A3.A.fam.R t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) ∧
    ∀ (j : Fin D.R.m) (t : P.T) (c : (P.A3.A.fam.L j t).S.Cl), Fintype.card ((P.A3.A.fam.L j t).S.Gam c) ∣ (D.mem D.u₀).C.DGam
end Bundle
end Formalism.L2.Rows
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsRowPinMin
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2.Rows
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
structure RowPinMinAlt (T : _root_.Formalism.L2.TiedDataSKAlt ex) : Prop where
  lowerMap : ∀ u, LowerMapTieS (T.cols.forms u)
  lowerMapTw : ∀ u μ (hμ : μ ≠ D.what₂.mu0) (_hw : ∃ w, μ = D.what₂.muAt w) (h1 : 1 ≤ D.R.m), _root_.Formalism.L2.Rows.LowerMapTieTwAlt T u μ hμ h1
  buDef : Formalism.BasicNotions.Rows.BuDefQ D.what₂
end Formalism.L2.Rows
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideOf
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open Formalism.L2.Host (CharFrame HChar TupTied)
open GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug
namespace GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace Side
variable {D : D7} {nch : NChoice D} (s : Side D nch)
end Side
section Wit
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}
def sideOf_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (t : RowsT K w Z Wt p0) {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch)
    (c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n) : Side (w.st Z).toD7 nch :=
  { G := _, Pl0 := _, I0 := _, T := _, A3 := _, J := t.r.z.core, R := t.r.z.R, P0 := t.r.z.F.P0, ψ0 := t.r.z.F.ψ0, cG := t.r.z.cG,
    v₀ := t.r.z.geo.v₀, S := _, YS := c.row.nexp, cf := GlobalTheory.Mem.Col2.TC.cf w.I w.l Z, tp := n.tp }
end Wit
def ExponentialNormChoice (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun _ _ _ _ _ _ _ _ t _ n xd c =>
  PLift ((_root_.GlobalTheory.PlugPt.sideOf_alt t n c).Export xd) × PUnit.{2}
structure ExtensionReading (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) : Type 2 where
  rd : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z))
    (t : RowsT K w Z Wt p0) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (xd : ThData (w.D Z)),
    𝒮.Nx K B f T w Z Wt p0 t nch n xd → _root_.GlobalTheory.Mem.Top.Bl.normChoiceOfExtension hL (_root_.GlobalTheory.PlugPt.ExponentialNormChoice hL) K B f T w Z Wt p0 t nch n xd
def HasExponent' {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (E : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) : Prop :=
  ∀ K B f T w Z Wt p0 t nch n xd c, E K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.PlugPt.ExponentialNormChoice hL K B f T w Z Wt p0 t nch n xd c)
def ExtensionReading.of {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (Rx : RPosition) {E : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} (h : _root_.GlobalTheory.PlugPt.HasExponent' E) (Sx : SPosition) (Ox : OComponent₂) :
    _root_.GlobalTheory.PlugPt.ExtensionReading hL ⟨Rx, _root_.GlobalTheory.Mem.Top.Bl.normChoiceOfExtension hL E, Sx, Ox⟩ :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ y => ⟨y.1, Classical.choice (h _ _ _ _ _ _ _ _ _ _ _ _ _ y.2)⟩⟩
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {𝒮 : Slots}
def sideOfWeightedPoint (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) {K : Ctx} (p : WPt 𝒮 K) : Side (p.w.D p.Z) p.O.ex.nch :=
  _root_.GlobalTheory.PlugPt.sideOf_alt p.x.what₂ p.x.n (ν.rd _ _ _ _ _ _ _ _ _ _ _ _ p.x.nx).1
def pinnedPointOfReading (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) : PinT 𝒮 BdPt := fun _ p _ b => ∃ kap lam err, sidePt b = (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).upd kap lam err
end GlobalTheory.PlugPt
end
end
end

