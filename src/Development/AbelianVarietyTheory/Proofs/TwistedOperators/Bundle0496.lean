module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiscreteSeriesModelNegSpaceTransfer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridJoinCubicSizeBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0483
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0486
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0475
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNonzeroRealIntertwinerGridArrow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin.ArrX

theorem vertex_par {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GlobalTheory.Grid.GridPre R) (hS : G.IsSpaces)
    (i j : ℕ) (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : (G.V i j).S = GlobalTheory.Grid.parV D i j := by
  rcases i with _ | i
  · rw [GlobalTheory.Grid.parV_zero D hj]
    show (GlobalTheory.Grid.row0 R j).S = _
    rcases j with _ | j
    · rfl
    · by_cases hlt : j + 1 < D.R.m
      · rw [← GlobalTheory.Grid.nodeY_eq_chainVertexAtRowZero_of_lt R hlt]
        dsimp only [GlobalTheory.Grid.nodeY]
        rw [Nat.min_eq_left hlt.le]
      · rw [← GlobalTheory.Grid.nodeX_eq_chainVertexAtRowZero_of_ge R hlt]
        have hm : j + 1 = D.R.m := by omega
        rw [hm]
  · exact (hS.vert i j hi hj).par

theorem exists_intertwiner : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i < D.R.m → j ≤ D.R.m → ∀ (ω : GlobalTheory.Grid.WRep (G.V (i + 1) j).V (G.V i j).V) (f : WO (G.V (i + 1) j).V (G.V i j).V → ℂ), GlobalTheory.Grid.IsWeil R.ψ true (G.V (i + 1) j).V (G.V i j).V (G.chiAt (D.R.m - i) (rkV D (i + 1) j)) (G.chiAt (D.R.m - i) (rkV D i j)) ω → GlobalTheory.Grid.IsVac R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f → ∃ It : GlobalTheory.Grid.Pol (G.V (i + 1) j) (G.V i j) →ₗ[ℂ] SmT (G.V i j).M →ₗ[ℂ] SmT (G.V (i + 1) j).M, IsItW R.θ (G.V (i + 1) j).M (G.V i j).M ω (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f) It := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDS hHC hHost hSz F hCore hgap G' W hW G hS hC hSp hTh i j hi hj ω f hω hf
  have hθ : IsInfFam R.θ := hCore.models.inf
  obtain ⟨M₁, hcart, honb, hback⟩ := _root_.GlobalTheory.NegModel.exists_negModel_transfer (G.V (i + 1) j).M
  choose aS aT haS haT be de hdat hflip hlow using
    fun τ => GlobalTheory.GridJoin.ArrXPar.arrowX_par hSz hCore G hC i j hi hj τ
  have hSn := vertex_par G hS (i + 1) j hi hj
  have hSo := vertex_par G hS i j hi.le hj
  have hc : cart M₁ = GlobalTheory.Grid.cartS true (G.V (i + 1) j) := funext fun τ => (hcart τ).trans rfl
  have ho : onb M₁ = onb (G.V (i + 1) j).M := funext honb
  have hfin := hf.isFinVec
  have hne : f ≠ 0 := by
    unfold GlobalTheory.Grid.IsVac IsVacO at hf
    obtain ⟨-, ⟨-, -, -, -, ⟨⟨p, hp⟩, hq⟩⟩⟩ := hf
    intro h0
    have h1 := hq p hp
    rw [h0] at h1
    simp [nrm2] at h1
  have hvac : GlobalTheory.Chain.IsVacVec R.ψ R.θ M₁ (G.V i j).M f :=
    ⟨hfin.1, hne, fun τ => by rw [hc]; exact hfin.2 τ⟩
  obtain ⟨It₁, hIt₁⟩ := _root_.GlobalTheory.Chain.RealItLarge.itLarge (GlobalTheory.Grid.sgn true (G.V (i + 1) j).V) (G.V i j).V
    (fun τ => ((G.V (i + 1) j).S τ).image fun x => (x.1, !x.2)) (G.V i j).S M₁ (G.V i j).M R.θ R.ψ
    (GlobalTheory.Grid.sLen D) aS aT hDS hHC hθ
    (fun τ => ⟨be τ, de τ, hdat τ, by rw [hSn]; exact hflip τ, by rw [hSo]; exact hlow τ⟩)
    _ _ (GlobalTheory.Grid.WRep.toSgn true ω) hω (fun τ => ⟨haS τ, haT τ⟩) f hvac
  obtain ⟨It, hIt⟩ := hback (G.V i j).M R.θ hθ ω _ It₁ hIt₁
  have hpt : GlobalTheory.Chain.ptOf R.ψ R.θ M₁ (G.V i j).M f =
      ⇑(GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f) := by
    unfold GlobalTheory.Chain.ptOf GlobalTheory.Grid.fock
    rw [hc, ho]
  exact ⟨It, hpt ▸ hIt⟩

end GlobalTheory.GridJoin.ArrX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealPointStandardSourceUnitaryComponents
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdRealLift

theorem exists_real_point : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (v : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ τ, (v τ)ᴴ * v τ = 1) → ∃ h ∈ GinfC S, ∀ τ, compAt C.θ τ (mt S h) = v τ := by
  intro D S T C v hv
  obtain ⟨L, hL, -⟩ := GlobalTheory.RealLift.exists_real_lift D C.θ S C.inf
  have hu : v ∈ HolDict.UG (gramAt D S) := by
    intro τ
    have hg : gramAt D S τ = 1 := by
      unfold gramAt
      rw [C.m.gS]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    show (v τ)ᴴ * gramAt D S τ * v τ = gramAt D S τ
    rw [hg, Matrix.mul_one]
    exact hv τ
  refine ⟨L v, (hL v hu).1, fun τ => ?_⟩
  rw [← (hL v hu).2 τ]
  clear hL hu hv
  unfold compAt archM
  ext i j
  rfl

end GlobalTheory.StdRealLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitFramePrincipalLevelFiniteGroup
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
namespace GlobalTheory.TrPtFrame

theorem finLoc_locFin_ne {D : D7} (V : HSp D) {u v : HeightOneSpectrum (𝓞 D.host.F)} (h : u ≠ v) (x : Gv V v) :
    finLoc V u (locFin V v x) = 1 := by
  show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram u ((locFin V v x : GfC V) : GA D V) = 1
  rw [coe_locFin]
  exact GlobalTheory.AdelicU.proj_emb_ne _ _ h x

theorem mem_parLev {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    (L : LevDat D.host.E ℂ V.rank) (h : L.r = V.rank) (hQ : L.Q = ∅) {x : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    (hU : x ∈ UA D.sp.cm V.gram) (hS : x ∈ St β) : x ∈ parLev D.sp.cm V.gram β L := by
  rw [Formalism.L2.DIV.mem_parLev]
  refine ⟨hU, hS, fun PP _ => ?_, fun PP hP => ?_⟩
  · rw [Formalism.L2.DIV.mem_blockTri]
    intro i j hij
    exfalso
    simp [Formalism.L2.DIV.blkOf, h] at hij
  · exfalso
    simp [hQ] at hP

theorem upperLeftBlock_apply_of_eq {D : D7} {n r : ℕ} (hr : r ≤ n) (h : r = n) (PP : Pl D.host.E) (g : GL (Fin n) (kP PP)) (i j : Fin r) :
    ((upperLeftBlock hr g : GL (Fin r) (kP PP)) : Matrix (Fin r) (Fin r) (kP PP)) i j = (g : Matrix (Fin n) (Fin n) (kP PP)) (i.cast h) (j.cast h) := by
  subst h
  have hm : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
    rw [Formalism.L2.DIV.mem_blockTri]
    intro a b hab
    exfalso
    simp [Formalism.L2.DIV.blk2] at hab
  rw [Formalism.L2.DIV.upper_block_val_submatrix hr hm, Matrix.submatrix_apply]
  rfl

private theorem finLoc_locFin' {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Gv V v) :
    finLoc V v (locFin V v x) = x := by
  show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v ((locFin V v x : GfC V) : GA D V) = x
  rw [coe_locFin]
  exact GlobalTheory.AdelicU.proj_emb_self _ _ v x

private theorem upperLeftBlock_one {D : D7} {n r : ℕ} (hr : r ≤ n) (PP : Pl D.host.E) :
    (upperLeftBlock hr (1 : GL (Fin n) (kP PP)) : GL (Fin r) (kP PP)) = 1 :=
  Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one (Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) (Formalism.L2.DIV.blkR hr)

theorem exists_splitFrame_levG : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank) (h : L.r = V.rank), IsBaseFrame V β Λ N → L.Q = ∅ → (∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → ∃ (a : GfC V) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ L.Pg) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v) (ρ : ∀ v : S, ResF v.1 ≃+* kP (pl v).1), (∀ v ∉ S, ∀ k ∈ Kv V v, ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ levG V β (flag1L L)) ∧ ∀ (v : S) (k : Kv V v), ∃ g0 : G0 L.Pg L.r, IsLevelLift V β L g0 ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∧ (∀ PP, PP ≠ pl v → g0 PP = 1) ∧ ∀ i j : Fin L.r, (g0 (pl v)).1 i j = ρ v (((s v).red k).1 (i.cast h) (j.cast h)) := by
  intro D V β Λ N L h hB hQ hPg
  classical
  obtain ⟨a, hLat, hSt⟩ := GlobalTheory.FramePointMove.exists_point_carrying_frameLat D V β Λ N hB

  have hStk : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (k : Gv V v), k ∈ Kv V v →
      finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ St β := by
    intro v k hk
    refine (hSt (locFin V v k)).2 fun u => ?_
    by_cases huv : u = v
    · subst huv
      rw [finLoc_locFin']
      exact hk
    · rw [finLoc_locFin_ne V huv k]
      exact Subgroup.one_mem _

  have hinj : ∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP' := by
    intro PP hP PP' hP' he
    by_contra hne
    exact hPg PP hP PP' hP' (GlobalTheory.UnderConj.isConjPl_of_under_eq_of_ne D PP PP' he hne)
  let S : Finset (HeightOneSpectrum (𝓞 D.host.F)) := L.Pg.image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
  let f : L.Pg → S := fun PP => ⟨PP.1.under (𝓞 D.host.F), Finset.mem_image_of_mem _ PP.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro PP PP' he
      exact Subtype.ext (hinj _ PP.2 _ PP'.2 (congrArg Subtype.val he))
    · intro v
      obtain ⟨PP, hP, he⟩ := Finset.mem_image.1 v.2
      exact ⟨⟨PP, hP⟩, Subtype.ext he⟩
  let pl : S ≃ L.Pg := (Equiv.ofBijective f hf).symm
  have hunder : ∀ v : S, (pl v).1.under (𝓞 D.host.F) = v.1 := fun v =>
    congrArg Subtype.val ((Equiv.ofBijective f hf).apply_symm_apply v)
  choose s ρ hsρ using fun v : S =>
    GlobalTheory.SplitPlaceRed.splitRed_frame D V β Λ N a hB hLat v.1 (pl v).1 (hunder v)
      (hPg _ (pl v).2 _ (pl v).2) (fun k => hStk v.1 k.1 k.2)
  refine ⟨a, S, pl, s, ρ, ?_, ?_⟩
  · intro v hv k hk
    have hx := hStk v k hk
    rw [Formalism.IndefR.Lev.levG, Formalism.IndefR.Lev.mem_levA]
    refine ⟨(a * locFin V v k * a⁻¹ : GfC V).2, ?_⟩
    rw [Formalism.L2.DIV.mem_lev]
    refine ⟨mem_parLev (flag1L L) h hQ (GlobalTheory.LevSplit.finE_mem_UA V _) hx, ?_⟩
    have hone : ∀ PP ∈ L.Pg, redFn β PP (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V)) = 1 := by
      intro PP hP
      refine GlobalTheory.PlaceAwayRed.redFn_conj_locFin_eq_one D V β a v PP (fun he => hv ?_) k hx
      rw [← he]
      exact Finset.mem_image_of_mem _ hP
    have hrt : rTup β (flag1L L) (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V)) = rTup β (flag1L L) 1 := by
      funext PP
      simp only [Formalism.L2.DIV.rTup]
      rw [hone PP.1 PP.2, Formalism.L2.DIV.redFn_one]
    rw [hrt, Formalism.L2.DIV.rTup_one]
    exact Subgroup.one_mem _
  · intro v k
    have hx := hStk v.1 k.1 k.2
    refine ⟨rTup β L (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V)),
      ⟨(a * locFin V v k * a⁻¹ : GfC V).2, mem_parLev L h hQ (GlobalTheory.LevSplit.finE_mem_UA V _) hx, rfl⟩, ?_, ?_⟩
    · intro PP hne
      have hu : PP.1.under (𝓞 D.host.F) ≠ v.1 := by
        intro he
        exact hne (Subtype.ext (hinj _ PP.2 _ (pl v).2 (he.trans (hunder v).symm)))
      show upperLeftBlock L.hr (redFn β PP.1 (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V))) = 1
      rw [GlobalTheory.PlaceAwayRed.redFn_conj_locFin_eq_one D V β a v.1 PP.1 hu k.1 hx]
      exact upperLeftBlock_one L.hr PP.1
    · intro i j
      show ((upperLeftBlock L.hr (redFn β (pl v).1 (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V))) :
        GL (Fin L.r) (kP (pl v).1)) : Matrix (Fin L.r) (Fin L.r) (kP (pl v).1)) i j = _
      rw [upperLeftBlock_apply_of_eq L.hr h]
      exact hsρ v k (i.cast h) (j.cast h)

end GlobalTheory.TrPtFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCore
section
namespace I195MixedCoordinates_857711241bb3adcbae71fb38

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_857711241bb3adcbae71fb38

public noncomputable abbrev _root_.I195MixedCoordinates_e9b37737007d4cfbb59b997f.source :=
  @_root_.I195MixedCoordinates_857711241bb3adcbae71fb38.source

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BumpMix

theorem coreA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (H Z T : HSp D) (ρ : ℕ) (dH : HypDec H Z ρ), Z.rank = 0 → ∀ (v : VolM D T.rank ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → ∃ f, IsThetaFunO ψ H T f ∧ ∀ x, (_root_.I195MixedCoordinates_857711241bb3adcbae71fb38.source dH) T ψ v.μ v.𝓕 f x 0 = β x := by
  intro D ψ hψ H Z T ρ dH hZ v β hβ
  exact ⟨poinX ψ dH T β, ⟨_root_.GlobalTheory.BumpMixQuasi.poinX_quasi D ψ hψ H Z T ρ dH hZ β, _root_.GlobalTheory.BumpMixLevel.poinX_heis_level D ψ hψ H Z T ρ dH hZ β hβ,
    _root_.GlobalTheory.BumpMix.poinX_continuous D ψ hψ H Z T ρ dH β hβ, _root_.GlobalTheory.BumpMixSmooth.poinX_smooth D ψ hψ H Z T ρ dH β hβ⟩, _root_.GlobalTheory.BumpMixSum.mixS_poinX D ψ hψ H Z T ρ dH v β hβ⟩

theorem bump_mul_theta_mixS : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (β : Mx D T.rank ρ → ℂ) (g : WO S₀ T → ℂ), IsBump β → IsThetaFunO ψ S₀ T g → ∃ Φ, IsThetaFunO ψ S T Φ ∧ ∀ x, (_root_.I195MixedCoordinates_857711241bb3adcbae71fb38.source d) T ψ v.μ v.𝓕 Φ x = β x • g := by
  intro D ψ hψ S S₀ T ρ d v β g hβ hg
  let P : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral ρ
  let dH : HypDec (GlobalTheory.Doubling.dblSp P) (GlobalTheory.Core.Rk.SWLaw.zeroSp D) ρ := GlobalTheory.Core.Rk.SWLaw.dblDec P
  have hZ : (GlobalTheory.Core.Rk.SWLaw.zeroSp D).rank = 0 := rfl
  obtain ⟨fH, hfH, hmix⟩ := coreA D ψ hψ _ _ T ρ dH hZ v β hβ
  refine ⟨_, isThetaFunO_prod 1 d.i₀ 1 (GlobalTheory.TowerSurj.embMat d dH) (GlobalTheory.TowerSurj.symplOH_split d dH T hZ) hg hfH,
    fun x => ?_⟩
  funext w₀
  have hz : ∀ z : WO (GlobalTheory.Core.Rk.SWLaw.zeroSp D) T, z = 0 := fun z => Matrix.ext fun _ j => by
    haveI : IsEmpty (Fin (GlobalTheory.Core.Rk.SWLaw.zeroSp D).rank) := by rw [hZ]; infer_instance
    exact isEmptyElim j
  have e2 : ∀ a : Mx D T.rank ρ, sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀) =
      dH.extY T a + dH.extX T x + dH.ext0 T 0 := by
    intro a
    have hX : sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀) ⬝ dH.jX = x := by
      rw [sandwich_apply, rat_one, Matrix.one_mul, GlobalTheory.TowerSurj.mul_embMat_jX, coord_jX]
    have hY : sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀) ⬝ dH.jY = a := by
      rw [sandwich_apply, rat_one, Matrix.one_mul, GlobalTheory.TowerSurj.mul_embMat_jY, coord_jY]
    have h0 := hz (sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀) ⬝ dH.j0)
    rw [eq_coords dH (sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀)), hX, hY, h0]
    abel
  have e1 : ∀ a : Mx D T.rank ρ, sandwich (rat 1) (rat d.i₀) (d.extY T a + d.extX T x + d.ext0 T w₀) = w₀ := by
    intro a
    rw [sandwich_apply, rat_one, Matrix.one_mul]
    exact witt_extension_sum_mul_middle_coordinate d x a w₀
  have key : ∀ a : Mx D T.rank ρ,
      heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀)
        (fun w => g (sandwich (rat 1) (rat d.i₀) w) * fH (sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) w)))) 0 =
      g w₀ * heisO ψ _ T (dH.extY T a) (heisO ψ _ T (dH.extX T x) (heisO ψ _ T (dH.ext0 T 0) fH)) 0 := by
    intro a
    rw [d.integrandS_eq, dH.integrandS_eq, symplOH_Y_X, symplOH_Y_X]
    show _ * (g _ * fH _) = _
    rw [e1, e2]
    ring
  have h2 : ∫ a in v.𝓕, heisO ψ _ T (dH.extY T a) (heisO ψ _ T (dH.extX T x) (heisO ψ _ T (dH.ext0 T 0) fH)) 0 ∂v.μ =
      β x := hmix x
  change ∫ a in v.𝓕, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀)
        (fun w => g (sandwich (rat 1) (rat d.i₀) w) * fH (sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) w)))) 0 ∂v.μ = β x * g w₀
  rw [show (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀)
        (fun w => g (sandwich (rat 1) (rat d.i₀) w) * fH (sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) w)))) 0) =
      fun a => g w₀ * heisO ψ _ T (dH.extY T a) (heisO ψ _ T (dH.extX T x) (heisO ψ _ T (dH.ext0 T 0) fH)) 0 from funext key,
    integral_const_mul, h2, mul_comm]

end GlobalTheory.BumpMix

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryCoordinateOfRationalPointDefiniteVe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets

namespace GlobalTheory.RatMoveJets

theorem exists_unitary_ratCoord {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (hX : DefNode D.R.m X) (r : FinPt G X) (hr : GlobalTheory.MovedKappaEx.RatFin (G.V X) r) :
    ∃ U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E, GlobalTheory.RatMoveJets.RatCoord (G.V X) (S.N.fr X) r U := by
  obtain ⟨γ, hγ, hf⟩ := hr
  obtain ⟨γ', h1, h2⟩ := id hγ
  have hG : star γ'.1 * (G.V X).gram * γ'.1 = (G.V X).gram := h1
  have hmt : Formalism.L2.Theta.mt (G.V X) γ = γ'.1.map (incA D) := congrArg Units.val h2.symm
  set F := (S.N.fr X).1 with hFdef
  set Fi := ((S.N.fr X)⁻¹ : GL (Fin (G.V X).rank) D.host.E).1 with hFidef
  have hF : star F * (G.V X).gram * F = 1 := S.N.fr_on X hX
  have e1 : Fi * F = 1 := by rw [hFdef, hFidef]; exact Units.inv_mul _
  have e2 : F * Fi = 1 := by rw [hFdef, hFidef]; exact Units.mul_inv _
  have hGram : star Fi * Fi = (G.V X).gram := by
    have : star Fi * (star F * (G.V X).gram * F) * Fi = (G.V X).gram := by
      calc star Fi * (star F * (G.V X).gram * F) * Fi = star (F * Fi) * (G.V X).gram * (F * Fi) := by
            rw [star_mul]; simp only [Matrix.mul_assoc]
        _ = (G.V X).gram := by rw [e2, star_one, Matrix.one_mul, Matrix.mul_one]
    rw [hF, Matrix.mul_one] at this
    exact this
  have hU : star (Fi * γ'.1 * F) * (Fi * γ'.1 * F) = 1 := by
    calc star (Fi * γ'.1 * F) * (Fi * γ'.1 * F) = star F * (star γ'.1 * (star Fi * Fi) * γ'.1) * F := by
          simp only [star_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hGram, hG]; exact hF
  refine ⟨⟨Fi * γ'.1 * F, Matrix.mem_unitaryGroup_iff'.2 hU⟩, γ, hγ, hf, ?_⟩
  rw [hmt]
  congr 1
  change γ'.1 = F * (Fi * γ'.1 * F) * Fi
  simp only [← Matrix.mul_assoc, e2, Matrix.one_mul]
  rw [Matrix.mul_assoc, e2, Matrix.mul_one]

end GlobalTheory.RatMoveJets
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLevelActionEqInvSmulTranslate
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups GlobalTheory.ThetaProjEquiv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaCommutation

theorem exists_fin_part {D : D7} (V : HSp D) (q : Bridge.Gf V) : ∃ k ∈ GfC V, (finHom V).rangeRestrict k = q := by
  obtain ⟨h, rfl⟩ := (finHom V).rangeRestrict_surjective q
  obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h
  refine ⟨k, hk, Subtype.ext ?_⟩
  show finHom V k = finHom V (a * k)
  rw [map_mul, show finHom V a = 1 from ha, one_mul]

theorem finiteGroupLevelAction_eq_inv_smul_translate {H W : Type} [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {Q : Subgroup H} (ch : Q →* ℂˣ)
    (q : Q) (k : H) (hk : k = q) (c : ℂ) (hc : c = ch q) (f : H → W) (h : H) :
    Bridge.g0Act ch q f h = c⁻¹ • f (h * k) := by
  rw [hk, hc, Bridge.g0Act, Units.val_inv_eq_inv_val]

theorem ch_eq {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) :
    (levEnv V β L).ch q = levFn β (flagL L) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)) := rfl

theorem exists_adelic_lift {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) (g0 : G0 L.Pg L.r) (hq : rTup β L (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)) = g0)
    (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] :
    ∃ k, IsLevelLift V β L g0 k ∧ ∀ (f : Bridge.Gf V → W) h,
      Bridge.g0Act (levEnv V β L).ch q f h = (levChi V β (flagL L) k)⁻¹ • f (h * (finHom V).rangeRestrict k) := by
  obtain ⟨k, hk, e⟩ := exists_fin_part V q.1
  have e1 : finE V k = Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _) :=
    congrArg (fun x : Bridge.Gf V => Formalism.UG.bc (swapAE D) x.1) e
  refine ⟨k, ⟨hk, ?_, ?_⟩, finiteGroupLevelAction_eq_inv_smul_translate _ q _ e _ ?_⟩
  · rw [e1]; exact q.2.1
  · rw [e1]; exact hq
  · exact congrArg Units.val ((congrArg (levFn β (flagL L)) e1).trans (ch_eq V β L q).symm)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem algW_apply (i : Fin D.R.m) (c : G → ℂ) (U : MMap (R.MW i (sg0 D A))) :
    algW R i c U = ∑ g, c g • FWT.actW R i (sg0 D A) g U := by
  refine MultilinearMap.ext fun v => ?_
  show (∑ g, c g • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) (U v) = _
  rw [LinearMap.sum_apply, _root_.sum_apply]
  rfl

theorem map_comb {G H X Y : Type} [Fintype G] [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] (e : H →ₗ[ℂ] X) (he : Function.Injective e) (Θ : H →ₗ[ℂ] Y) (c : G → ℂ) (a : G → X) (b : G → Y) (y : H)
    (hy : e y = ∑ g, c g • a g) (h1 : ∀ g, ∃ z, e z = a g) (h2 : ∀ g z, e z = a g → Θ z = b g) :
    Θ y = ∑ g, c g • b g := by
  choose z hz using h1
  have h3 : y = ∑ g, c g • z g := he (by simp only [hy, map_sum, map_smul, hz])
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h3, map_sum, map_smul, h2 _ _ (hz _)]

end GlobalTheory.ThetaCommutation

end
end

