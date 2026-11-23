module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0384
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0028
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0026
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0755
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0226
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
public import Formalism.LocalToGlobal.ClassS
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowLocPin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0022
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0367
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkBCharpolySplits
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.HeightCounting.FormsStep
end GlobalTheory.HeightCounting.FormsStep
namespace GlobalTheory.HeightCounting.FormsStep
theorem hkB_charpoly_splits_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (hst : HkStab D T S In) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host)
      [hfr : Module.Free (T.O i) ↥(BI D T S In i j b)] [hfi : Module.Finite (T.O i) ↥(BI D T S In i j b)], P ∉ T.S0 i →
      ∃ s : Multiset (FractionRing (T.O i)),
        (LinearMap.charpoly (hkB D T S In hst i j b k P)).map
          (algebraMap (T.O i) (FractionRing (T.O i))) = (s.map fun a => X - C a).prod := by
  classical
  intro D cf jE A S In b0 b1 Sx T Sp hSb hstar hst i j b k P hfr hfi hP
  by_cases hc : HkCond D T i j k P
  · have hB : ∀ x ∈ BI D T S In i j b, x ∈ V0T D T S In.rho In.chi In.θ i j b := fun x hx => hx.2
    have hL1 := _root_.GlobalTheory.T.fixed_space_le_iSup_eigenspace_of_goodness D cf jE A S In b0 b1 Sx T Sp hSb hstar i j b k P hc
    let ev : D.what₂.FT → FractionRing (T.O i) := fun σ =>
      algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)
    let sG : Finset D.what₂.FT := Finset.univ.filter fun σ : D.what₂.FT => D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ
    have hle : (⨆ σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ},
        Module.End.eigenspace (hkT D T S In i j b k P) (ev σ)) ≤
        ⨆ r ∈ sG.image ev, Module.End.eigenspace (hkT D T S In i j b k P) r :=
      iSup₂_le fun σ hσ => le_iSup₂_of_le (ev σ) (Finset.mem_image_of_mem ev (by simpa [sG] using hσ)) le_rfl
    obtain ⟨m, hm⟩ := charpoly_restrict_map_eq_prod (BI D T S In i j b) (hkT D T S In i j b k P)
      (fun x hx => hst i j b k P hc x hx) (sG.image ev) (fun x hx => hle (hL1 (hB x hx)))
    refine ⟨m, ?_⟩
    have he : hkB D T S In hst i j b k P = ((hkT D T S In i j b k P).restrictScalars (T.O i)).restrict
        (fun x hx => hst i j b k P hc x hx) := by
      unfold hkB
      rw [dite_eq_left hc]
    rw [he]
    exact hm
  · have he : hkB D T S In hst i j b k P = 1 := by
      unfold hkB
      rw [dite_eq_right hc]
    refine ⟨Multiset.replicate (Module.finrank (T.O i) ↥(BI D T S In i j b)) 1, ?_⟩
    rw [he, LinearMap.charpoly_one, Multiset.map_replicate, Multiset.prod_replicate, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, map_one]
end GlobalTheory.HeightCounting.FormsStep
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreLastStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_through_completion_iso_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ L : G0g D.nd → GAf D.host.E D.R.nV, IsTypeGroupBlockLift D D.R.nV L → ∀ F ∈ D.naut.typeV i PI, ∀ (h : GL (Fin D.R.r) (ZMod (D.host.g k))) (g : G0g D.nd), g ⟨k, v⟩ = h → (∀ kv, kv ≠ ⟨k, v⟩ → g kv = 1) → ∃ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x ∧ IsLiftN h (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) ∧ NG.rt D.host.E D.R.nV (L g) ((P.M.loc i).real F) = NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) := by
  first | exact @_root_.GlobalTheory.LiftOther.main_alt_alt | exact _root_.GlobalTheory.LiftOther.main_alt_alt | (intros; apply _root_.GlobalTheory.LiftOther.main_alt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreSideStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_eigen_frobenius_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 → ∀ c ∈ EigSet (M (D.what₂.muTw w) j h1 h2) (D.what₂.places.resChar w) (C.Q w), ∃ i ∈ L.X.nd.locs j w, ∃ x : L.X.nd.X i, ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) = c v k := by
  first | exact @_root_.GlobalTheory.EigOnto.main_alt_alt | exact _root_.GlobalTheory.EigOnto.main_alt_alt | (intros; apply _root_.GlobalTheory.EigOnto.main_alt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreTailStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_iso_split_place_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ F ∈ D.naut.typeV i PI, ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) = GlobalTheory.BlockType.blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • (P.M.loc i).real F := by
  exact _root_.GlobalTheory.TypeVecEig.main_alt_alt
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerBisStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_weight_direct_sum_alt : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, (∀ a b (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ' → (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w ↔ D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i ρ' w) ∧ (∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ' w → D.naut.wdOf i (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w = D.naut.lpSum (D.naut.wdOf i ρ w) (D.naut.wdOf i ρ' w)) ∧ (∀ τ, (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i ρ' w) → D.naut.jumpsW i (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') τ = D.naut.jumpsW i ρ τ + D.naut.jumpsW i ρ' τ)) := by
  first | exact @_root_.GlobalTheory.SumRepAdd.main_alt_alt | exact _root_.GlobalTheory.SumRepAdd.main_alt_alt | (intros; apply _root_.GlobalTheory.SumRepAdd.main_alt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerTerStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_place_completion_iso_tame_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = GlobalTheory.DimPartsCompare.cPl (D.naut.plGw k v) → IsTame (S i s.w hw).mu → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ Q, ∃ f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), f ≠ 0 ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x f = blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • f := by
  exact _root_.GlobalTheory.TypeBlockConj.main_alt_alt
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}
structure TiedDataSAlt (ex : Extra D L hT Gi Gl K Y cX) where
  host : Host.HostTied D
  level : Host.LevelTied D
  cols : Forms.ColsTiedSym D
  full : Forms.ColsFullS cols
  extra : Forms.ColsExtraTiedS full ex
  provA : TH.ProvA
  theta : Theta.AllTied D ex.th provA
  twIn : TwIn D
  n : _root_.Formalism.L2.NTiedAllAlt D ex.nch twIn
  frameN : Host.SameFrameN host n.gal.fr.jE
  thetaChr : Host.ThetaChrTied D n.cf ex.nch n.tp ex.th
  chrVal : Host.ValLL0 D n.cf
  chrDt : Host.DtTied D n.cf
  chrN : Host.NCharTied D n.cf ex.nch n.tp
  chrGal : Host.NGalChrTied D n.cf ex.nch n.tp
  chrPsi : Host.PsiChoiceCompatible D n.cf ex.nch n.tp
  sameChr : JoinChr.SameChr theta.T thetaChr
  what₂ : Rows.RowsCompatible D host n.cf n.tp
  inK : Y.Lev → ℕ → Prop
  geo : Geo.GeoTiedP Y inK
  tw : Forms.SymmetricTwistedColumnsAtPrimes n.tp cols ex.tw
  emt : Rows.EMtTied D cols tw
  g : G.GroupCompatibilityAll D hT ex.cmp
  herm_eq : g.herm = full.1.to0
  forms_eq : g.forms = fun u => (cols.forms u).to0
def ExtraDataSelfDual (ex : Extra D L hT Gi Gl K Y cX) : Prop := Nonempty (_root_.Formalism.L2.TiedDataSAlt ex)
end
def SecondChernLinkedClass : FamClass := fun {_} Fm =>
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.ExtraDataSelfDual (Fm.ex x hx i)
def LinkedFamiliesFixedValues' : FamClass := Formalism.MainNotions.WithPage _root_.Formalism.L2.SecondChernLinkedClass
def LinkedFamiliesAligned' : FamClass := fun {_} Fm =>
  _root_.Formalism.L2.LinkedFamiliesFixedValues' Fm ∧ Formalism.MainNotions.DIV.Align.SmallFirstModulusBelowScale Fm ∧
    Formalism.MainNotions.TameDistinctF Fm
end Formalism.L2
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NTiedLocTiedOfBuilt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.HeightCounting
theorem nTied_locTied_of_built_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists), _root_.GlobalTheory.HeightCounting.CgCmpAlt hL → ∀ (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D'),
    Nonempty (_root_.GlobalTheory.HeightCounting.NTiedGPlaceholder D') ∧ Nonempty (Formalism.L2.LocTied D') := by
  intro hL hcg D' b
  exact ⟨⟨⟨⟩⟩, locTied_any D'⟩
end GlobalTheory.HeightCounting
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in
structure NAtData (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) :
    Type 1 where
  nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D cf nch tp
  all : _root_.GlobalTheory.HeightCounting.NAllCAlt D nch
  chr_eq : (⟨all.cf, all.tp⟩ : Σ c : CharFrame D, TupTied D c nch) = ⟨cf, tp⟩
  host : HostTied D
  frameN : ∀ x, all.gal.fr.jE x = host.fr.j x
  chrN : NCharTied D cf nch tp
  chrGal : NGalChrTied D cf nch tp
  Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host
  Pq_over : ∀ v, NG.OverPl (Pq v) v
  pq : ∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hadm : NX.AdmTw D i k Q ψ),
    (all.exp.mtV i j b k Q ψ h1 h2 hadm).QP = qpOf D Pq Q ∧ (all.exp.mtV i j b k Q ψ h1 h2 hadm).DP = qpOf D Pq (D.ntw.pD i)
  jE_eq : HEq nt.jE all.gal.fr.jE
  mt_eq : HEq (mtL nt.L nt.M) all.gal.mt
  Pq_eq : HEq nt.Pq Pq
  low : 2 ∈ nt.low ∧ AbsolutelyIrreducibleSpan.q0 D ∈ nt.low ∧ (NumberField.discr D.host.E).natAbs.primeFactors ⊆ nt.low ∧
    (Ideal.absNorm D.host.ccK).primeFactors ⊆ nt.low
  split : GlobalTheory.SplitCoef.OSplit D
  ratIn : RatIn nt.D nt.S
  ratIn_hL : ratIn.hL = nt.hL
  ratIn_eig : ratIn.eig = nt.eig
  ratIn_θ : ratIn.θ = nt.θ
  depth : RowDepth nt.D nt.rep
section Rows
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in
structure NormRealisationData {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D}
    (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) : Type 1 where
  kKs : Ks →+* ↥D.LL0
  hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x
  nexp : NExpRealS R cG (ratDatR R cG kKs hk)
  hecke : NExpRealH R cG (ratDatR R cG kKs hk) nexp
  grp : GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG)
  rowLoc : _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt a.all.gal.lp R.θ Y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
    (fun b => levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (fun _ => R.e0) Y.eFT
  S_eq : HEq (ratL a.nt.L a.nt.S) (ratDatR R cG kKs hk)
  hL_eq : HEq a.nt.hL hecke.hL
  rep_eq : HEq a.nt.rep fun σ : D.what₂.FT => principalLevelFrame.rowRepR R.θ (Y.eFT σ)
end Rows
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
structure NormChoiceCore (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}
    (t : RowsT K w Z Wt p0) {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) : Type 1 where
  a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL (w.D Z) (TC.cf w.I w.l Z) nch n.tp
  row : _root_.GlobalTheory.Mem.Top.Bl.NormRealisationData (D := (w.st Z).toD7) a t.r.z.R t.r.z.F t.r.z.cG t.r.Y
  sel : Set.range a.Pq = Set.range w.I.sel
abbrev NormChoiceExtension (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Type 2 :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
    (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (_ : ThData (w.D Z)),
    _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n → Type 1
def normChoiceOfExtension (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (E : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) : NCondition := fun K B f T w Z Wt p0 t nch n xd =>
  Σ c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n, E K B f T w Z Wt p0 t nch n xd c
end GlobalTheory.Mem.Top.Bl
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PairReadOfJoinStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairRead_of_join_isTrue_unit :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness →
      ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : CharacterChoiceData hL D),
        CharacterChoiceJoin P → ∀ S : Reading P.T, IsFaithfulReading P S → RowUnit S → PairRead S :=
  GlobalTheory.NPin.pairRead_of_join_alt
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PinOfNTrue
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.NPin.exists_character_choice_of_nTrue_split : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D cf C tp), ValLL0 D cf → (∀ σ σ', (nt.rep σ).Iso (nt.rep σ') → σ = σ') → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → ChebSplit D.nd → ∃ P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D, P.cf = cf ∧ P.C = C ∧ HEq P.tp tp ∧ HEq P.rep nt.rep ∧ HEq P.M (mtL nt.L nt.M) := by
  intro hL D cf C tp nt hval hinj hstar hexp hsplit hcheb
  obtain ⟨⟨D0, cf0, jE, A, cg, au, rep, row, low, Pq, S, hLm, eig, θ, Bs, M, C0, tp0, ch, mt, big, L, Sp, Au, ss, heq⟩, pack⟩ := nt
  dsimp only at pack heq hinj ⊢
  subst heq
  cases pack
  obtain ⟨Hk, hHk⟩ := _root_.GlobalTheory.FitHecke.heckeOpen_withLoc_alt D0 cf0 jE A low Pq S hLm eig θ Bs M C0 tp0 ch mt hstar hexp hsplit hcheb big L Sp Au
  obtain ⟨ty⟩ := _root_.GlobalTheory.HeightCounting.typesOpen_withLoc_alt D0 cf0 jE A low Pq S hLm eig θ Bs M C0 tp0 ch mt hstar hexp hsplit hcheb big L Sp Au ss
  obtain ⟨tw⟩ := _root_.GlobalTheory.T.side_multiplicity_character_alt D0 cf0 jE A low Pq S hLm eig θ Bs M C0 tp0 ch mt hstar hexp hsplit hcheb big L Sp Au
  refine ⟨{ cf := cfL L cf0, C := chL L C0, tp := tpL L tp0, chr := tw.chrN, val := hval, Q_eq := ?Q, T := { A.wdT with }, lab := A.lab, cg := { cg with }, M := mtL L M, H := Hk, au := ?au, rep := rep, rep_inj := hinj, row := ?row, locW_eq := fun i i' σ w => (Au.locW i σ w).trans (Au.locW i' σ w).symm, jE := jE, ty := ty, wd := { A.wd with }, wdOf := Au.wdOf }, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  case Q =>
    intro i
    have hm : i ∈ L.X.nd.locs (L.X.nd.j i) (L.X.nd.w i) := (L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
    exact (Sp.Q_eq _ _ i hm).trans (Sp.Qc_eq _ _)
  case au =>
    intro j h1 h2 π s σ h
    rw [hHk]
    exact au j h1 h2 π s σ h
  case row =>
    intro i
    refine ⟨fun σ s τ h => ?_, fun σ v w hvw Dv hα => ?_⟩
    · exact (congrArg (A.wdT.e s.w) (Au.locW i σ s.w)).trans (row.1 σ s τ h)
    · obtain ⟨α, h1, h2⟩ := row.2 σ v w hvw Dv hα
      exact ⟨α, h1, (Au.satW i σ w).trans h2⟩
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtSysFiniteStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_family_local_global_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ w : D.what₂.places.Pl, ∃ (F : Finset (PlE D.host)) (Sy : Finset (PlE D.host → ℕ → ℂ)), ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C → ∀ (i : (withLoc L).nd.Loc) (x : (withLoc L).nd.X i), (withLoc L).nd.w i = w → ∃ c ∈ Sy, ∀ v, v ∉ F → ∀ k, GlobalTheory.CoefDuty.ptSys (withLoc L) i x v k = c v k := by
  first | exact @_root_.GlobalTheory.SysFin.ptSys_finite_alt | exact _root_.GlobalTheory.SysFin.ptSys_finite_alt | (intros; apply _root_.GlobalTheory.SysFin.ptSys_finite_alt <;> assumption)
end
end

