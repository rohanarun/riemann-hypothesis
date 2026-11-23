module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0496
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0081
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0458
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0082
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0474
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0085
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairCentral
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0065
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0087

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeForwardPreservesBase
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.FamTrace.LatFwd
end GlobalTheory.FamTrace.LatFwd
namespace GlobalTheory.FamTrace.LatFwd
set_option maxHeartbeats 4000000 in
theorem lattice_forward_preserves_base_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U → GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun _ => _root_.True) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat row col hc κ hκ y hy hU
  have hs := hA.tr.std.some u
  obtain ⟨k, hk⟩ := hs.ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hlb := hk.lb ()
  have hg : Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _) = 1 :=
    ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hA.tr.ok hA.tr.pins.some l Z).2.2.2 0 (Nat.zero_le _)).1
  have hfg : ((a.g.x 0).L).FG := by
    haveI : Submodule.IsLattice _ (a.g.x 0).L := (ha.x 0 (Nat.zero_le _)).sd.1
    exact Submodule.IsLattice.fg (A := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (a.g.x 0).L
  have hne : X.piT u ≠ 0 := by
    have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := l.pr.piT_cop u
    intro h0
    rw [h0, map_zero, isCoprime_zero_left] at hcop
    exact not_isUnit_zero hcop
  have hne' : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := fun h => hne (by exact_mod_cast h)
  have hσ : ∀ x, Formalism.L2.Forms.sigD (I.rec7 l Z) (Formalism.L2.Forms.sigD (I.rec7 l Z) x) = x := fun x => star_star x
  have hΛ : ∀ x, x ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Lb ↔ ∀ j : Fin _, ∃ r : 𝓞 (I.rec7 l Z).host.E, x j = (r : (I.rec7 l Z).host.E) ∧ (j.1 + 1 = _ → X.piT u ∣ r) :=
    fun x => hlb x
  have hloc : ∀ v, ∀ g ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Uloc v, ∀ i j, g.1 i j ∈ Formalism.UG.tensInt (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (Formalism.UG.intOE (I.rec7 l Z).host.E) (v.adicCompletionIntegers (I.rec7 l Z).host.F).toSubring :=
    fun v g hgv => GlobalTheory.T.unitFormUnitary_integralEntries_of_levelLattice _ _ _ hσ _ _ hg _ hne' _ hΛ v g ((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Uloc_lev v hgv)
  have hyv := (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U_eq y.1).1 hU).2
  have hyinv := finM_inv_eq _ _ κ y.1 hy
  refine GlobalTheory.FinPl.KOpen.moves_of_levelOpen _ _ hfg _ ?_
  clear hs hk hlb row col hc
  have hL : (a.g.x 0).L = GlobalTheory.AdelicU.stdLattice (I.rec7 l Z).host.E ((I.rec7 l Z).sp.X 0).rank := by
    ext z
    rw [(hat.pinX.xs 0 (Nat.zero_le _)).2.2 z]
    simp only [GlobalTheory.AdForm.intVec, Set.mem_setOf_eq, GlobalTheory.AdelicU.stdLattice, Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, LinearMap.mem_range, Algebra.linearMap_apply]
    exact forall_congr' fun k => ⟨fun hk => ⟨⟨_, hk⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe⟩
  rw [GlobalTheory.AdelicU.levelOpen, Subgroup.mem_iInf]
  intro v
  rw [Subgroup.mem_comap, hL]
  have e2 : ∀ i j, (Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y.1)⁻¹).1 i j ∈ Formalism.UG.tensInt (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (Formalism.UG.intOE (I.rec7 l Z).host.E) (v.adicCompletionIntegers (I.rec7 l Z).host.F).toSubring := by
    rw [map_inv]; exact hloc v _ (inv_mem (hyv v))
  exact proj_mem_stabLoc_std _ κ v (GlobalTheory.T.localComponent_integral_of_finiteMatrix_integral _ _ _ _ κ y.1 hy v (hloc v _ (hyv v)))
    (GlobalTheory.T.localComponent_integral_of_finiteMatrix_integral _ _ _ _ κ⁻¹ (y.1)⁻¹ hyinv v e2)
end GlobalTheory.FamTrace.LatFwd
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevAtGEmbAIff
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TraceAtG
end GlobalTheory.TraceAtG
end
noncomputable section
open GlobalTheory.FamTrace
theorem GlobalTheory.TraceAtG.levAtG_embA_iff_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), (_root_.GlobalTheory.FamTrace.LevelAtElement a (embA a.d.B.d a.d.B.o κ) ↔ GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun p => p ∈ a.v.gP) ∧ _root_.GlobalTheory.FamTrace.TraceAtElement a κ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat row col hc κ hκ
  have hmi : ∀ i, 0 + 2 * (I.rec7 l Z).R.rS + 2 = (I.rec7 l Z).R.m := fun i => by
    have h1 := (a.G i).hs
    have h2 := (a.G i).S.odd
    unfold Ranks.rS; omega
  have hbes : ∀ i, (ofSplit (a.G i).q).IsBesFrame a.d.B.lev ((a.G i).sc 0) ((a.G i).FX 0 (Nat.zero_le _))
      ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)) := by
    intro i
    have hm := hmi i
    have key : ∀ Bl : BesLev (I.rec7 l Z) (I.rec7 l Z).R.rS, Bl = (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ hm →
        ∀ (FA : Frame (a.G i).k Bl.A.rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0))
          (F : Frame (a.G i).k Bl.V.rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ⊕ Fin ((a.G i).s + 1))), HEq FA ((a.G i).FX 0 (Nat.zero_le _)) →
          HEq F ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)) → (ofSplit (a.G i).q).IsBesFrame Bl ((a.G i).sc 0) FA F := by
      rintro Bl rfl FA F h1 h2
      cases h1; cases h2
      exact (a.G i).bes 0 _ hm _ _
    exact key _ (ha.bot.1 hm) _ _ HEq.rfl HEq.rfl
  have hmat : ∀ i g, IsMatrixInFrameOfXZero (a.G i) κ g → (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) (embA a.d.B.d a.d.B.o κ)
      (GlobalTheory.RootEx.embX ((a.G i).s + 1) g) := fun i g hg =>
    GlobalTheory.TraceAtG.mat_embA_besFrame (ofSplit (a.G i).q) a.d.B.lev _ _ _ (hbes i) κ g hg
  have huniq : ∀ i x m m', (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) x m →
      (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) x m' → m = m' := by
    intro i x m m' h1 h2
    unfold GLoc.Mat at h1 h2
    rw [h1] at h2
    refine Units.ext ?_
    have := congrArg (fun M => ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).γ * M *
      ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).β) h2
    simp only [← Matrix.mul_assoc, Frame.γβ, Matrix.one_mul] at this
    simpa only [Matrix.mul_assoc, Frame.γβ, Matrix.mul_one] using this
  have hex : ∀ i, ∃ g, IsMatrixInFrameOfXZero (a.G i) κ g := fun i =>
    ⟨coordHom _ (a.G i).q.pr _ _ ((a.G i).FX 0 (Nat.zero_le _)).βγ ((a.G i).FX 0 (Nat.zero_le _)).γβ κ,
      (eq_coordHom_iff _ _ _ _ _ _ κ _).2 rfl⟩
  constructor
  · intro hlev
    have htr : _root_.GlobalTheory.FamTrace.TraceAtElement a κ := fun i g hg => hlev i _ (hmat i g hg)
    refine ⟨?_, htr⟩
    have hsd := (ha.x 0 (Nat.zero_le _)).sd
    have hloc : ∀ i, GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (· = (a.G i).q.v) := by
      intro i
      obtain ⟨g, hg⟩ := hex i
      have hlev0 := htr i g hg
      let β := GlobalTheory.SplitLat.frameOf (a.G i).q ((I.rec7 l Z).sp.X 0) _ ((a.G i).FX 0 (Nat.zero_le _))
      have hIs : β.IsLat (a.g.x 0).L (GlobalTheory.SplitLat.stdLat (a.G i).k _) := fun x => by
        rw [GlobalTheory.SplitLat.mem_std]; exact (a.G i).latX 0 (Nat.zero_le _) x
      have key := _root_.GlobalTheory.FrameMoves.moves_iff_smul _ (a.G i).k (a.G i).q ((I.rec7 l Z).sp.X 0) _ β (a.g.x 0).L _ hsd hIs κ
      refine key.2 ?_
      have hreg := ((Chain.ofType_regular _ _ _ _ _ : ((a.G i).S.T (Fin (I.rec7 l Z).R.t)).Regular).2.2 0
        ((a.G i).s + 1) (Nat.zero_add _)).2.2
      have hst := hreg hlev0
      have hK := GlobalTheory.LevX.mem_KO_of_embX_mem_stabLat (a.G i).S.ϖ
        (stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) (l := (a.G i).s + 1) 0 ((a.G i).s + 1) (Nat.zero_add _)) hst
      have hcoord : coordHom ((I.rec7 l Z).sp.X 0) (a.G i).q.pr β.b β.b' β.bb' β.b'b κ = g :=
        ((eq_coordHom_iff _ _ _ _ _ _ κ g).1 hg).symm
      rw [hcoord]
      exact GlobalTheory.LevX.smul_stdLat_of_mem_KO hK
    intro y hy
    have hlat := ((_root_.GlobalTheory.FinPl.localComponents (I.rec7 l Z) (fun p => p ∈ a.v.gP)).2 ((I.rec7 l Z).sp.X 0)).2.2.2 (a.g.x 0).L
    have hy' : ∀ j, (mt ((I.rec7 l Z).sp.X 0) κ *ᵥ y) j ∈ GlobalTheory.FinPl.idAt (I.rec7 l Z) (fun p => p ∈ a.v.gP) := fun j => by
      simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun t _ => Ideal.mul_mem_left _ _ (hy t)
    have hey : ∀ v e, e ∈ GlobalTheory.FinPl.intAt (I.rec7 l Z) (· = v) → ∀ j, (e • y) j ∈ GlobalTheory.FinPl.idAt (I.rec7 l Z) (· = v) :=
      fun v e he j => by simpa [smul_eq_mul] using Ideal.mul_mem_right (y j) _ he.1
    rw [hlat y hsd.1, hlat _ hsd.1]
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨hy', fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := (ha.gpin.places v).1 hv
      rw [← Matrix.mulVec_smul]
      exact (hloc i _ (hey _ e he)).1 (h2 _ hv e he)
    · rintro ⟨-, h2⟩
      refine ⟨hy, fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := (ha.gpin.places v).1 hv
      have := h2 _ hv e he
      rw [← Matrix.mulVec_smul] at this
      exact (hloc i _ (hey _ e he)).2 this
  · rintro ⟨-, htr⟩ i m hm'
    obtain ⟨g, hg⟩ := hex i
    rw [huniq i _ _ _ hm' (hmat i g hg)]
    exact htr i g hg
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevSphBTCompactOpen
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.TopVol
theorem levSph_bT_compact_open_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT ≤ GfC _ ∧ IsCompact (_root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) ∧ IsOpen (((_root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT).subgroupOf (GfC _) : Subgroup (GfC (I.rec7 l Z).sp.X')) : Set (GfC (I.rec7 l Z).sp.X')) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _
  have hx : a.g.bT ∈ GfC (I.rec7 l Z).sp.X' := ha.top.2.1
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA (I.rec7 l Z).sp.cm.sig (I.rec7 l Z).sp.X'.gram
  have hmem : ∀ h, h ∈ _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT ↔
      a.g.bT⁻¹ * h * a.g.bT ∈ Formalism.IndefR.Lev.levG _ (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.TopVol.datSph_alt W) := fun h => _root_.GlobalTheory.TopVol.mem_level_sphere_iff_conj_mem_levS h
  refine ⟨?_, ?_, ?_⟩
  · intro h hh
    have h1 : a.g.bT⁻¹ * h * a.g.bT ∈ GfC (I.rec7 l Z).sp.X' := ((hmem h).1 hh).1
    have h2 : h = a.g.bT * (a.g.bT⁻¹ * h * a.g.bT) * a.g.bT⁻¹ := by group
    rw [h2]
    exact mul_mem (mul_mem hx h1) (inv_mem hx)
  · have he : (_root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) =
        (fun k => a.g.bT * k * a.g.bT⁻¹) '' (Formalism.IndefR.Lev.levG _ (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.TopVol.datSph_alt W) : Set _) := by
      ext h
      constructor
      · intro hh
        exact ⟨_, (hmem h).1 hh, by group⟩
      · rintro ⟨k, hk, rfl⟩
        refine (hmem _).2 ?_
        have : a.g.bT⁻¹ * (a.g.bT * k * a.g.bT⁻¹) * a.g.bT = k := by group
        rw [this]; exact hk
    rw [he]
    exact (GlobalTheory.ParahoricCompact.isCompact_levG _ _ _).image (by fun_prop)
  · have ho := GlobalTheory.ParahoricCompact.isOpen_comap_lev _ (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.TopVol.datSph_alt W)
    have hc : Continuous fun k : GfC (I.rec7 l Z).sp.X' => a.g.bT⁻¹ * (k : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') * a.g.bT := by
      fun_prop
    convert ho.preimage hc using 1
    ext k
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
    rw [hmem]
    constructor
    · intro hk; exact hk.2
    · intro hk
      exact ⟨(GfC (I.rec7 l Z).sp.X').mul_mem ((GfC (I.rec7 l Z).sp.X').mul_mem ((GfC (I.rec7 l Z).sp.X').inv_mem hx) k.2) hx, hk⟩
end GlobalTheory.TopVol
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelSubgroupAtPlace
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.LevProd
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
theorem step_index_le_s_alt (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (i : Fin J.r) {j : ℕ} (hj : j + 2 ≤ B.R.m) : j ≤ (J.G i).s := by
  have h1 := (J.G i).hs
  change (J.G i).s + 1 + 1 = B.R.m at h1
  omega
def localHomProduct (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →* ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
  Pi.monoidHom fun i => GlobalTheory.LevIdx.locHom (J.G i).q _ ((J.G i).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega))
def levelSubgroupAtPlace (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) (i : Fin J.r) :
    Subgroup (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
  prX (Cgrp (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev j ((J.G i).s - j + 1) (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega)).J
    ((J.E i).rep j ((J.G i).s - j) (Nat.add_sub_cancel' (_root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj)) (α i)))
def quadraticTwistAtPlace (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop := fun v => ∃ i, (J.G i).q.v = v
def relaxedLevelSubgroup (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  (J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J)) ⊓ GfC _ ⊓
    (Subgroup.pi Set.univ fun i => KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)).comap (_root_.GlobalTheory.LevProd.localHomProduct J j hj)
def upperLevelSubgroup (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (j : ℕ) (hj : j + 2 ≤ B.R.m) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  if h : ∃ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.Reads ∧ Nonempty (J.Ch j) then
    _root_.GlobalTheory.LevProd.relaxedLevelSubgroup h.choose_spec.choose j hj h.choose_spec.choose_spec.2.some
  else ⊥
theorem upperLevelSubgroup_le_GfC (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (j : ℕ) (hj : j + 2 ≤ B.R.m) : _root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj ≤ GfC _ := by
  unfold _root_.GlobalTheory.LevProd.upperLevelSubgroup
  split_ifs
  · intro g hg
    exact (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).2
  · exact bot_le
theorem wt_eq_inv_measure_levelSubgroupAtPlace {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) (i : Fin J.r) :
    (J.E i).wt j (α i) = ((((J.E i).m j (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i)).toReal⁻¹ : ℝ) : ℂ) :=
  (J.E i).wt_mid j ((J.G i).s - j) (Nat.add_sub_cancel' (_root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj)) (α i)
end GlobalTheory.LevProd
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftPrincipal
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TieLift
theorem lift_principal_alt : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ g0 : G0 (R2 p).Pg (Fm.D x i).R.r,
    ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc (Fm.D x i) j) ((R2 p).βW j) ((R2 p).datWp j (R2 p).triv) g0 κ' :=
  _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun Fm x hx i p hr hm w hw j g0 =>
    GlobalTheory.GalLift.Transl.lifts (R2 p) j (_root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hr hm.1).1.lev g0
end GlobalTheory.TieLift
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LineIndep
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
set_option maxHeartbeats 1600000
namespace GlobalTheory.LevelLine
section Gen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat ValuativeRel
open GlobalTheory.LocMod (ofSplit MovedTo)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y : Type} [Fintype Y] [DecidableEq Y]
end Gen
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues _root_.Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Matrix
open GlobalTheory.LocMod (ofSplit)
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem single_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.PackageHypotheses W) (r : Fin D.R.rS) (hr : r.1 = 0) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (hP : _root_.GlobalTheory.MiTop.PlacedAlt f B) (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg) :
    ∃ e, Formalism.L2.NTheta.IsIdemAt e PP ∧ ∀ c ∈ idAt D (· = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)),
      (mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ *ᵥ
        (fun i => c * incA D (W.S.X.ιE (W.S.X.eR r (Fin.cast (rank_eq W.S.X W.Q.instEq) i)))) ∈
          latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ↔
        Cond e (2 * D.R.rS + 1) (c * incA D ((W.S.X.B.g : D.host.E) ^ D.R.rS)⁻¹)) := by
  obtain ⟨k, i1, i2, i3, i4, ι, v, o, n, G, pl, hc, hv, ht, -, -, hR, hb⟩ := hP
  obtain ⟨i, hi⟩ := pl.surjective ⟨PP, hPP⟩
  obtain ⟨hq, hqv⟩ := hR.idem i
  rw [hi] at hq hqv
  change (G i).q.v = PP.under _ at hqv
  change Formalism.L2.NTheta.IsIdemAt _ PP at hq
  refine ⟨_, hq, fun c hcv => ?_⟩
  rw [← hqv] at hcv ⊢
  obtain ⟨μ, lam, n1, n2, n3⟩ := hb.norm
  have hξ : -D.host.xi0 ^ (D.R.m / 2) ≠ 0 := neg_ne_zero.2 (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hμ : μ ≠ 0 := left_ne_zero_of_mul (n1 ▸ hξ)
  have h₀ : 0 + 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.rS
    omega
  have hg : ((W.S.X.B.g : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.L2.SG.Pf.modulus_g_ne_zero W.S.X)
  obtain ⟨s, hs, he⟩ := GlobalTheory.LineIdeal.first_vec (_root_.GlobalTheory.MiTop.formsAtZero W u) (W.S.tr u) hW.bot.idE hc.std B hμ n2 r hr
  have hd : B.d.e = (f.c.bes 0 D.R.rS h₀).d.e := eq_of_heq (Sigma.mk.inj (congrArg
    (fun Z : BesLev D D.R.rS => (⟨Z.V.rank, Z.d.e⟩ : Σ n, Matrix (Fin n) (Fin D.R.rS) D.host.E)) (hb.lev h₀))).2
  have hsc := sc_mul (G i) n1 n3 (hb.last i) h₀
  have hT : ((D.mem u).A.T : 𝓞 D.host.E) ∉ PP.asIdeal := fun hT => by
    refine Finset.disjoint_left.1 hv.disj ((ht.gP _).2 ⟨PP, hPP, rfl⟩) ((ht.tP _).2 ?_)
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
    rwa [map_natCast]
  have hTv := val_nat (G i).q hq _ hT
  have hz : star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = star μ * (μ * -((D.mem u).A.T : D.host.E)) := by
    have e : B.d.i₀ *ᵥ vecB B.o B.ζ = μ • GlobalTheory.Core.SBesEx.cY W.S.X W.Q.instEq (W.S.X.zu u) := funext n2
    refine (norm_vec B.lev).trans ?_
    change star (B.d.i₀ *ᵥ vecB B.o B.ζ) ⬝ᵥ (D.sp.Y 0).gram *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = _
    rw [e, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, GlobalTheory.Core.SBesEx.cY_isom D _ _ hW.bot.idE, W.S.X.zu_norm]
    rfl
  have hzu := (G i).hz_unit 0 _ h₀
  have hzu' := hzu
  rw [← hb.lev h₀] at hzu'
  change valuation _ ((G i).q.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ))) = 1 at hzu'
  have hμ1 : valuation _ ((G i).q.pr (incA D μ)) = 1 := by
    have := congrArg (valuation _) hsc
    rwa [map_mul, (G i).sc_unit, one_mul, map_one] at this
  have hμ2 : valuation _ ((G i).q.pr (incA D (star μ))) = 1 := by
    simp only [hz, RingHom.map_mul, RingHom.map_neg, map_natCast, Valuation.map_mul, Valuation.map_neg, hμ1, hTv, mul_one] at hzu'
    exact hzu'
  have hxi : valuation _ (ofSplit (G i).q).xi = 1 := by
    have := congrArg (valuation _) ((G i).sc_step 0)
    rw [map_mul, (G i).sc_unit, (G i).sc_unit, one_mul] at this
    exact this.symm
  obtain ⟨σ, -, hM⟩ := hR.frame i 0 ((G i).s + 1) (Nat.zero_add _)
  obtain ⟨hsd, hfr⟩ := _root_.GlobalTheory.T.selfDual_and_frame_of_pkHyp W hW 0 (by omega)
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> simp
  have H := line_bes (G i).q hq (f.c.B 0 _ h₀) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) hfr hsd (f.g.b 0) _ _ _
    (fun h0 => by simpa [h0] using (G i).sc_unit 0) ((G i).bes 0 _ h₀ _ (Nat.zero_add _)) _ (G i).S.ϖ
    (Matrix.fromBlocks_diagonal _ _) (σ.symm.trans (GlobalTheory.StepData.stdOrd _ _ 0 _ (Nat.zero_add _))) hM r hr
    (incA D (s * μ)⁻¹ * (c * incA D ((W.S.X.B.g : D.host.E) ^ D.R.rS)⁻¹))
    (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hcv))
  have e : (fun i => c * incA D (W.S.X.ιE (W.S.X.eR r (Fin.cast (rank_eq W.S.X W.Q.instEq) i)))) =
      fun l => incA D (s * μ)⁻¹ * (c * incA D ((W.S.X.B.g : D.host.E) ^ D.R.rS)⁻¹) * incA D (B.d.e l r) := by
    funext l
    rw [he, mul_comm (incA D _), mul_assoc, mul_assoc, ← RingHom.map_mul, ← RingHom.map_mul]
    congr 2
    field_simp
  rw [e, hd]
  refine H.trans ?_
  rw [cond_iff (G i).q (G i).S.unif]
  generalize c * incA D ((W.S.X.B.g : D.host.E) ^ D.R.rS)⁻¹ = a
  have hs1 : valuation _ ((G i).q.pr (incA D (s * μ)⁻¹)) = 1 := by
    rw [← RingHom.comp_apply, map_inv₀, map_inv₀, RingHom.comp_apply]
    rcases hs with rfl | rfl <;> simp [hμ1]
  have hs2 : valuation _ ((G i).q.pr (incA D (star (s * μ)⁻¹))) = 1 := by
    rw [star_inv₀, ← RingHom.comp_apply, map_inv₀, map_inv₀, RingHom.comp_apply]
    rcases hs with rfl | rfl <;> simp [hμ2]
  have hϖ : 0 < valuation _ ((G i).S.ϖ : (G i).k) := by simp [zero_lt_iff]
  simp only [Valuation.mem_integer_iff, RingHom.map_mul, GlobalTheory.FinPl.FrameLat.cA_incA, Valuation.map_mul, map_div₀, Valuation.map_neg,
    Valuation.map_pow, Valuation.map_one, hs1, hs2, hxi, hzu, (G i).sc_unit, one_mul, one_pow, div_one, div_le_one₀ hϖ]
theorem line_indep_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (hr : 1 ≤ D.R.rS) u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → _root_.GlobalTheory.MiTop.PlacedAlt f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v) → ∀ c ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = v) ↔ Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f'.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = v)) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u u' f f' B B' hP hP' a₀ a a₀' a' _ _ v ⟨PP, hPP, hv⟩ c hc
  subst hv
  obtain ⟨e, he, h⟩ := _root_.GlobalTheory.LevelLine.single_alt W hW ⟨0, hr⟩ rfl f B hP PP hPP
  obtain ⟨e', he', h'⟩ := _root_.GlobalTheory.LevelLine.single_alt W hW ⟨0, hr⟩ rfl f' B' hP' PP hPP
  obtain rfl := (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D e e' PP PP he he').1 rfl
  exact (h c hc).trans (h' c hc).symm
end GlobalTheory.LevelLine
end
end
end

