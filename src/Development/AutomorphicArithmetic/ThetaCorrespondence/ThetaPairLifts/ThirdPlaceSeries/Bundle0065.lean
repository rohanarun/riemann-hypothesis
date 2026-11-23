module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0527
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0469
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0005
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0014
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0004
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.Bundle0002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GaloisAdmissibleOfRestrictedCmDatum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Formalism.LocalToGlobal.GlobalTheory.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0080
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0266
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ActMemMKStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rho_mem_MK_of_mem_MK : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    ∀ (i : Fin D.R.m) (g : p.P.Gp) f, f ∈ (p.R.toRealDat.FW i).MK → (p.R.toRealDat.FW i).ρ g f ∈ (p.R.toRealDat.FW i).MK := by
  first | exact @_root_.GlobalTheory.TieMK.act_mem_MK_alt | exact _root_.GlobalTheory.TieMK.act_mem_MK_alt | (intros; apply _root_.GlobalTheory.TieMK.act_mem_MK_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdaptFBOfNormalFrames
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.AdaptSplit
open GlobalTheory.FinPl (latV MonoAt PrimAt ColsAt idAt intAt colMul Lat SplitPt)
open GlobalTheory.FinPl.FrameLat
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)
end GlobalTheory.Fam.AdaptSplit
open GlobalTheory.Fam.AdaptSplit in
theorem GlobalTheory.Fam.adaptFB_of_normalFrames_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀))) (o : TDat (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (_root_.GlobalTheory.Fam.pk_z W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP), ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), GlobalTheory.FinPl.AdaptFB (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).ψ ((commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).J j (σ + 1) h) ((commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).B (j + 1 + 1) σ (idx_step h)) (N₁ (j + 1)) ((commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).x (j + 1)).L (N₁ (j + 1 + 1)) (M₁ (j + 1 + 1) σ (idx_step h)) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hT0 hτ hNT hζ hsd hgP htP hdis hPre hOrth hbas FY sc hFr N₁ M₁ hsdN hIntN hsdM hIntM PP hP j σ h
  obtain ⟨hsc, -, hhz, hbes, hjac, -⟩ := hFr PP hP
  have hs := (l PP hP).hs
  have hU := (l PP hP).unit
  rw [← (l PP hP).under]
  have hj1 : j + 1 + (2 * (σ + 1)) = (l PP hP).s + 1 := by omega
  have hj2 : j + 1 + 1 + (2 * σ + 1) = (l PP hP).s + 1 := by omega
  have hJ := hjac j (σ + 1) h (2 * (σ + 1)) hj1
  have hB := hbes (j + 1 + 1) σ (idx_step h) (2 * σ + 1) hj2
  obtain ⟨F₀, hF₀⟩ := GlobalTheory.LocMod.GValProof.core_of_bes _ _ _ _ _ hB
  have hM := hIntM PP hP (j + 1 + 1) σ (idx_step h) (by omega) F₀ hF₀
  have hV := hsdN (j + 1) (by omega)
  have hV₀ := (hIs.x (j + 1) (by omega)).sd
  have hW' := hsdN (j + 1 + 1) (by omega)
  have hLJ := line_jac (l PP hP).q hU _ (hsc _) (hhz _ _ _) hJ hV (hIntN PP hP (j + 1) _ hj1)
  have hLB := line_bes (l PP hP).q hU _ (hsc _) (hhz _ _ _) hB hW' (hIntN PP hP (j + 1 + 1) _ hj2)
  refine ⟨GlobalTheory.FinPl.TamePlaces.tame D _, hV, hV₀, hW', hsdM _ _ _, ?_, ?_, ?_, ?_⟩
  · exact GlobalTheory.JacMono.monoAt_of_jacFrame (l PP hP).q hU _ hV hV₀ (hsc _) (hhz _ _ _) hJ (hIntN PP hP (j + 1) _ hj1)
      ((l PP hP).latX (j + 1) (by omega))
  · exact monoAt_of_besFrame (l PP hP).q hU _ (hsc _) (hhz _ _ _) hB hF₀ hW' (hsdM _ _ _) (hIntN PP hP (j + 1 + 1) _ hj2) hM
  · exact primAt_of_lines (l PP hP).q hU hIs.std _ _ hLJ
  · intro i b hb
    rw [hU.2, hLJ i b hb]
    exact (hLB i b hb).symm
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleJOfRestricted
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalS
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain _root_.GlobalTheory GlobalTheory.StringRepresentationDecomposition UpperTheory.GalC
theorem g3a_of_restricted_general_alt {D : D7} (_ : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (h : DeRhamJumpsDistinctCondition D) : ∀ i r, GoodR D.nd i r → DistinctAbsIrredConstituents D.nd i r := h.2
theorem admJ_of_admPar (D : D7) (L : SizeData₂ D) (h0 : SumRepresentations.tie0 D) (h1 : SumRepresentations.adm1 D) (h2 : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D) (h5 : SumRepresentations.adm5 D)
    (hC : CutRec D) (hW : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D) (hB : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D) (hP : AdmissibleParameterJ.AdmPar L) :
    _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt L :=
  have hG := _root_.UpperTheory.GalS.de_rham_points_weight_jumps_alt D h0 h1 h2 h5 hC
  ⟨hG.1, GlobalTheory.CrysWD.crysIffWD D, hG.2, _root_.GlobalTheory.T.admDict_of_weight_blockChar GlobalTheory.Published.cheb_holds D h2 hW hB, _root_.GlobalTheory.AdmReadBridge.main D, hP⟩
theorem duties_of_large_aux41 (hC : GlobalTheory.TwSys.Cheb) (D : D7) (hL : GlobalTheory.CoefDuty.Large D) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (hg : _root_.UpperTheory.GalS.DeRhamJumpsDistinctCondition D)
    (hRho : AutomorphicSideWildInertia.ResidualIrreducibleGood D) : GlobalTheory.CoefDuty.Duties D :=
  ⟨hL.1, fun i r hr => jc_of_u hr hL.2.1 (_root_.UpperTheory.GalS.g3a_of_restricted_general_alt h41 hg i r hr), _root_.GlobalTheory.DesignFromSize.main hC D hL.2.2, _root_.GlobalTheory.OrthogonalDesignFromSize.main hC D hRho hL.2.2⟩
theorem prvG5_of_admissible_cutRec : LocalFiniteness → LocalTateDuality → LocalEulerChar →
    ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → RbEx D → CutRec D → SumRepresentations.ConclusionG5 D := by
  intro h1 h2 h3 D hA hRb hC
  have hLGC : _root_.GlobalTheory.StringRepresentationDecomposition.LocalGlobalCompatible D := _root_.UpperTheory.GalS.lgc_of_cut'_alt D hA.1.1 hC
  have hEig : EigPd D := _root_.UpperTheory.GalS.eigPd_holds_alt D hA.1.1 hLGC hRb
  have hH : HOneTwo D := _root_.GlobalTheory.HOneTwoLevel.hOneTwo_holds h1 h2 h3 D
  refine _root_.Formalism.MainNotions.SumRepresentations.galois_clause_of_sufficient_alt D hA.1.1 fun i hg r hr w hw => ⟨hLGC i r hr w hw, fun hS => ⟨hRb i hg, fun rb hrb => ?_⟩⟩
  have hS' := (D.nd.S_def i w).1 hS
  have hnr : ¬ (((rb (D.nd.gam0 i w) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).IsRoot
      (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) := by
    have hk : ∀ k, w ∈ placesOver D.host.E (D.host.g k) → D.nd.l i ≠ D.host.g k :=
      fun k hk h => hS'.2 (h ▸ hk)
    rcases hS'.1 with h0 | h0 | h0
    · exact (hA.2.1 i hg rb hrb).2 0 (hk 0 h0) w h0
    · exact (hA.2.1 i hg rb hrb).2 1 (hk 1 h0) w h0
    · exact hEig i hg w hS h0 rb hrb
  exact ⟨hnr, hH i rb w hS hrb hnr⟩
end UpperTheory.GalS
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleSevenRestrict
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalC.Tr
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.NRows
variable {D : D7} {c : CutD D}
theorem admissible_seven_restrict_alt (h : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D) : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt (cut D c) := h
theorem admA_cut (h : _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D) : _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt (cut D c) :=
  ⟨tie0_cut_of_tie0 h.1, hypO_cut h.2.1, fun i => h.2.2.1 i.1, _root_.UpperTheory.GalC.Tr.galois_admissible_of_restricted_cmDatum h.2.2.2.1, fun i => h.2.2.2.2.1 i.1,
    fourthAdmissible_restrictToPoints h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
theorem admissible_cut (h : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D) : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum (cut D c) :=
  ⟨⟨_root_.UpperTheory.GalC.Tr.admA_cut h.1.1, _root_.UpperTheory.GalC.Tr.admissible_seven_restrict_alt h.1.2⟩, rhoBar_cut h.2.1, h.2.2⟩
theorem rsA_cut_of_aux41 (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (h : _root_.GlobalTheory.NRows.RowsAAlt D) : _root_.GlobalTheory.NRows.RowsAAlt (cut D c) :=
  { tieLab := h.tieLab, hecke := h.hecke, tie0 := tie0_cut_of_tie0 h.tie0, a2 := _root_.UpperTheory.GalC.Tr.galois_admissible_of_restricted_cmDatum h.a2, an1 := h.an1, an2 := h.an2
    a5 := h.a5, temp := _root_.UpperTheory.GalC.Tr.admissible_seven_restrict_alt h.temp, g4p := _root_.UpperTheory.GalC.Tr.no_g4_restrict_alt h41 h.g4p, gsp := h.gsp }
theorem rs_cut_of_good_aux41 (hc : c.Good) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (h : _root_.GlobalTheory.NRows.PointConditions' D) : _root_.GlobalTheory.NRows.PointConditions' (cut D c) :=
  { a := _root_.UpperTheory.GalC.Tr.rsA_cut_of_aux41 h41 h.a, b := rowsB_cut h.b, c := rowsC_cut hc h.c
    typeNZ := fun i x hx F hF => h.typeNZ i.1 x.1 ((zg_iff i x).1 hx) F (eigC_eq i x ▸ hF)
    rank := fun L => h.rank (ledBack L) }
theorem admissible_tame_eigenvalues_of_cut (h : _root_.UpperTheory.GalS.AdmissibleResidualTameEigenvalues D) : _root_.UpperTheory.GalS.AdmissibleResidualTameEigenvalues (cut D c) :=
  fun i Sig hx => h i.1 Sig (hx.elim fun x k => ⟨x.1, (par_iff i x Sig).1 k⟩)
end UpperTheory.GalC.Tr
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtPts
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
namespace GlobalTheory.LiftWeightForced
open Formalism.IndefR.IndefiniteWeightData
variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)
end GlobalTheory.LiftWeightForced
namespace GlobalTheory.LiftWeightForced
open Formalism.IndefR.IndefiniteWeightData
variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)
end GlobalTheory.LiftWeightForced
namespace GlobalTheory.LiftWeightForced
open Formalism.IndefR.IndefiniteWeightData
variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)
end GlobalTheory.LiftWeightForced
theorem GlobalTheory.LiftWeightForced.atPts_alt : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ (j : Fin (Fm.D x i).R.m) τ,
    Formalism.IndefR.Bridge.IsLamPrime (D := Fm.D x i)
      (Formalism.IndefR.Bridge.lamLdef (D := Fm.D x i) (Formalism.IndefR.Links.Vc (Fm.D x i) j).rank ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x _ i _ _ _ j τ => GlobalTheory.LiftWeightForced.isLamPrime_lamLdef (Fm.D x i) j τ⟩⟩
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtPtsHLtG
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
namespace GlobalTheory.ExpTie
theorem atPts_h_lt_g_alt : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ =>
    ∀ (j : Fin (Fm.D x i).R.m) a, (GlobalTheory.ExpTie.parOf (Fm.L x i) j).h < ((Fm.D x i).host.g a : ℝ) :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, fun x hx _ i _ _ _ j a => parOf_h_lt_g (Fm.L x i) (Fm.params x hx i) j a⟩⟩⟩
end GlobalTheory.ExpTie
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtPtsImp
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
namespace GlobalTheory.ExpTie
theorem atPts_and_alt {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : _root_.GlobalTheory.BigOn.AtPtsAlt Q) (h' : _root_.GlobalTheory.BigOn.AtPtsAlt Q') : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x hx i p => Q Fm x hx i p ∧ Q' Fm x hx i p :=
  Closed.imp (h.and h') fun Fm _ _ H => by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := H
    exact ⟨max a b, fun x hx hle i p hp hm =>
      ⟨ha x hx ((le_max_left _ _).trans hle) i p hp hm, hb x hx ((le_max_right _ _).trans hle) i p hp hm⟩⟩
theorem atPts_mono {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : _root_.GlobalTheory.BigOn.AtPtsAlt Q) (H : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i),
      Q Fm x hx i p → Q' Fm x hx i p) : _root_.GlobalTheory.BigOn.AtPtsAlt Q' :=
  Closed.imp h fun Fm _ _ ⟨a, ha⟩ => ⟨a, fun x hx hle i p hp hm => H Fm x hx i p (ha x hx hle i p hp hm)⟩
end GlobalTheory.ExpTie
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseLevelIsWhitStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_whittaker_lam_psi_half_unip : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.PointConditions' → ∃ (lam : (p.P.P0.map (p.R.eG.trans p.cG).toMonoidHom) →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), GlobalTheory.BadCount.IsWhit D _ lam ψ ∧ (∀ (g : p.P.P0) (h : (p.R.eG.trans p.cG) g ∈ p.P.P0.map (p.R.eG.trans p.cG).toMonoidHom), ((lam ⟨_, h⟩ : ℂˣ) : ℂ) = D.what₂.embLL ((p.P.ψ0⁻¹ g : D.what₂.LLˣ) : D.what₂.LL)) ∧ HalfUnip p p.P.P0 := by
  first | exact @_root_.GlobalTheory.ShareOn.isWhit_and_eq_embLL_inv_and_halfUnip | exact _root_.GlobalTheory.ShareOn.isWhit_and_eq_embLL_inv_and_halfUnip | (intros; apply _root_.GlobalTheory.ShareOn.isWhit_and_eq_embLL_inv_and_halfUnip <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseLevelRowsEqDimensionStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ind_piece_degree_zero : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), _root_.GlobalTheory.Fc.Ind.summandDegreeZero D O c b := by
  first | exact @_root_.GlobalTheory.Fc.Ind.base_level_rows_eq_dimension_alt | exact _root_.GlobalTheory.Fc.Ind.base_level_rows_eq_dimension_alt | (intros; apply _root_.GlobalTheory.Fc.Ind.base_level_rows_eq_dimension_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotHypMatchStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_hypothesis_matching_central_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → W.Q.Rl.toRealDat.IsModels ∧ IsInfFam W.Q.Rl.θ ∧ IsStdChar D W.Q.Rl.ψ (-1) ∧ (∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) (z * (show GA D (D.sp.Y 0) from W.Q.tS))) ∧ (∀ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.realCharacter W k ≠ 0) ∧ ∀ e : W.Q.Rl.HE.H, W.Q.Rl.HE.e e ∈ W.Q.Rl.toRealDat.EEat (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true) → _root_.GlobalTheory.MiTop.rowFormOfVector W e ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W := by
  first | exact @_root_.GlobalTheory.MiTop.botHyp_match_alt | exact _root_.GlobalTheory.MiTop.botHyp_match_alt | (intros; apply _root_.GlobalTheory.MiTop.botHyp_match_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentralIsomRamifiedStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_colForm_eq_rTrans_of_pin : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ u (d : _root_.GlobalTheory.MiTop.BottomData W u) z, d.Pin z → ∃ R : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u, ∀ φ C C₀, _root_.GlobalTheory.MiTop.IsColumnForm W u C (R φ) → _root_.GlobalTheory.MiTop.IsColumnForm W u C₀ φ → ∀ ξ, d.B.colForm C₀.1 ξ = rTrans d.a⁻¹ (d.B.colForm C.1 ξ) := by
  first | exact @_root_.GlobalTheory.MiTop.exists_linear_isometry_colForm_rTrans_of_pin | exact _root_.GlobalTheory.MiTop.exists_linear_isometry_colForm_rTrans_of_pin | (intros; apply _root_.GlobalTheory.MiTop.exists_linear_isometry_colForm_rTrans_of_pin <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChartZero
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod
namespace GlobalTheory.MiTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
def LevTraceAlt : Prop :=
  ∀ κ ∈ GfC (D.sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) κ = y.1.1 →
    ((y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U ↔
      (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o κ * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W) ∧
    ∀ hy : (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U, (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ) *
      _root_.GlobalTheory.MiTop.realCharacter W ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o κ * (show GA D (D.sp.Y 0) from f.g.b 0)) = 1
structure LocalBottomCompatibility {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (v : VCom f.c) (o : TDat f.c k ι) {n : ℕ} (G : Fin n → GLoc v) : Prop where
  lev : ∀ h₀ : 0 + 2 * D.R.rS + 2 = D.R.m, B.lev = f.c.B 0 D.R.rS h₀
  adapted : B.Adapted (W.S.tr u).wt
  norm : ∃ μ lam : D.host.E, μ * lam = -D.host.xi0 ^ (D.R.m / 2) ∧
    (∀ r, (B.d.i₀ *ᵥ vecB B.o B.ζ) r = μ * W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) ∧
    ∀ j h, v.τ j h *ᵥ o.ζ₀ = lam • (f.c.bes j 0 h).ζ
  last : ∀ i, (G i).z₀ = fun r => (ofSplit (G i).q).pr (o.ζ₀ r)
  lat : ∀ p, p ∉ v.tP → GlobalTheory.FinPl.latV (D.sp.X 0) (f.g.x 0).L (· = p) = GlobalTheory.FinPl.latV (D.sp.X 0)
    ((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Lb.map ((LinearEquiv.funCongrLeft D.host.E D.host.E
      (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 D.host.E))) (· = p)
  trace : _root_.GlobalTheory.MiTop.LevTraceAlt f B
def ChartAtZeroCondition : Prop :=
  ∀ t, ∃ α₀ : (f.t t).Ch 0, (∀ α, α = α₀) ∧ (f.t t).e 0 α₀ = Finsupp.single (f.g.b 0) 1 ∧
    (∀ φ, _root_.GlobalTheory.MiTop.col0_alt f t φ ∈ (f.t t).Ram 0 ∧ ∀ y, (f.t t).rd 0 α₀ (_root_.GlobalTheory.MiTop.col0_alt f t φ) y = (chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) ∧
    ∀ ψ ∈ (f.t t).Ram 0, ∃ φ, ψ = _root_.GlobalTheory.MiTop.col0_alt f t φ
end GlobalTheory.MiTop
end
end
end

