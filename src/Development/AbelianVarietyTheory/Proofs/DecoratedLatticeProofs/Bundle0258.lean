module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelPairFlipConjugate
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.KernelFlip

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem annih_dag (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (L : AdjLaw ψ S T)
    {aS : Matrix (Fin S.rank) (Fin S.rank) ℂ} {bT : Matrix (Fin T.rank) (Fin T.rank) ℂ} (τ : D.what₂.Tau)
    (hS : IsCartanInv (gramAt D S τ) aS) (hT : IsCartanInv (gramAt D T τ) bT)
    (w : Matrix (Fin S.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    annih (heisO ψ T S) θ τ (cplxO bT aS) w (dag S T f) =
      dag S T (annih (heisO ψ S T) θ τ (cplxO aS bT) (GlobalTheory.FockAdjoint.cdag S T τ w) f) := by
  unfold annih
  rw [GlobalTheory.FockAdjoint.dRho_dag hθ L, GlobalTheory.FockAdjoint.dRho_dag hθ L, GlobalTheory.FockAdjoint.cdag_cplx τ hS hT,
    GlobalTheory.FockAdjoint.dRho_neg' hψ hθ hf]
  funext x
  simp only [dag, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, map_add (f := _), map_mul, map_neg, Complex.conj_I]
  ring

theorem annih_theta (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (annih (heisO ψ S T) θ τ J z f) :=
  GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ z hf)
    (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ (J z) hf))

theorem foldr_theta (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sS : RealMat S) (sT : RealMat T)
    (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g) := by
  induction l with
  | nil => exact hg
  | cons p l ih => exact annih_theta hψ hθ _ _ _ ih

theorem foldr_dag (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (L : AdjLaw ψ S T) (sS : RealMat S) (sT : RealMat T)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (l : List (D.what₂.Tau × Matrix (Fin S.rank) (Fin T.rank) ℂ)) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) :
    l.foldr (fun p f => annih (heisO ψ T S) θ p.1 (cplxO (sT p.1) (sS p.1)) p.2 f) (dag S T g) =
      dag S T ((l.map fun p => (p.1, GlobalTheory.FockAdjoint.cdag S T p.1 p.2)).foldr
        (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldr_cons, List.map_cons]
    rw [ih, annih_dag hψ hθ L p.1 (hS p.1) (hT p.1) _ (foldr_theta hψ hθ sS sT _ hg)]

theorem fock_dag (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (L : AdjLaw ψ S T) (sS : RealMat S) (sT : RealMat T)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) {Φ : WO S T → ℂ}
    (h : IsFockVec ψ θ S T sS sT Φ) : IsFockVec ψ θ T S sT sS (dag S T Φ) := by
  obtain ⟨hth, N, hN⟩ := h
  refine ⟨L.theta Φ hth, N, fun l hl => ?_⟩
  rw [foldr_dag hψ hθ L sS sT hS hT l hth, hN _ (by simpa using hl)]
  funext x
  simp [dag]

theorem coef_dag (hST : AdjLaw ψ S T) (hTS : AdjLaw ψ T S) {X : Type} (x : X → WO T S → ℂ) (x' : X → WO S T → ℂ)
    (hx : ∀ p, x' p = dag T S (x p)) (Φ : WO T S → ℂ) (c : X → ℂ) (h : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsCoef T S x Φ c) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsCoef S T x' (dag T S Φ) fun p => starRingEnd ℂ (c p) := by
  obtain ⟨μ, 𝓕, ⟨hμ, h𝓕, h1⟩, hc⟩ := h
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D S.rank T.rank
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  have : BorelSpace (WO T S) := ⟨rfl⟩
  have : BorelSpace (WO S T) := ⟨rfl⟩
  let eA : WO T S ≃+ WO S T :=
    { toFun := adjO S T
      invFun := adjO T S
      left_inv := fun x => hTS.invol x
      right_inv := fun y => hST.invol y
      map_add' := hST.add }
  let eH : WO T S ≃ₜ WO S T := ⟨eA.toEquiv, hST.cont, hTS.cont⟩
  let eM : WO T S ≃ᵐ WO S T := eH.toMeasurableEquiv
  have hHaar : (μ.map eM).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ eA hST.cont hTS.cont
  have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
  have hmp' : MeasurePreserving eM.symm (μ.map eM) μ := MeasurePreserving.symm eM hmp
  let eG : ratL S T → ratL T S := fun g => ⟨adjO S T g, (hST.rat g).2 g.2⟩
  have hbij : Function.Bijective eG := by
    refine ⟨fun g g' hg => ?_, fun g => ⟨⟨adjO T S g, (hTS.rat g).2 g.2⟩, Subtype.ext (hST.invol g)⟩⟩
    have e := congrArg (fun x : ratL T S => adjO T S (x : WO S T)) hg
    simp only [eG, hTS.invol] at e
    exact Subtype.ext e
  have hF : IsAddFundamentalDomain (ratL T S) (eM.symm ⁻¹' 𝓕) (μ.map eM) := by
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
    show adjO T S (adjO S T g + x) = (g : WO T S) + adjO T S x
    rw [hTS.add, hTS.invol]
  have hpre : eM ⁻¹' (eM.symm ⁻¹' 𝓕) = 𝓕 := by
    ext a; simp
  refine ⟨μ.map eM, eM.symm ⁻¹' 𝓕, ⟨hHaar, hF, ?_⟩, fun p => ?_⟩
  · rw [MeasurableEquiv.map_apply, hpre, h1]
  · show starRingEnd ℂ (c p) = _
    rw [hc p, MeasurableEquiv.restrict_map, hpre, integral_map_equiv, ← integral_conj, hx p]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have ew : eM.symm (eM w) = w := eM.symm_apply_apply w
    show starRingEnd ℂ (x p w * starRingEnd ℂ (Φ w)) =
      dag T S (x p) (eM w) * starRingEnd ℂ (dag T S Φ (eM w))
    simp only [dag]
    have e2 : adjO T S (eM w) = w := hTS.invol w
    rw [e2, map_mul]

end GlobalTheory.KernelFlip


open GlobalTheory.KernelFlip in
theorem GlobalTheory.KernelFlip.kernelPair_flip : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (K₁ K₂ : GA D A → GA D B → ℂ) (c : GA D A → ℂ), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair ψ θ A B χA χB sA sB true (fun _ => True) (fun _ => True) K₁ K₂ c → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair ψ θ A B χA χB sA sB false (fun _ => True) (fun _ => True) K₁ K₂ c := by
  intro D ψ θ A B χA χB sA sB K₁ K₂ c hθ hsA hsB hK
  obtain ⟨om, Φ₁, Φ₂, H, hF₁, hF₂, -, -, hK₁, hK₂, hc⟩ := hK
  have hψ : IsStdChar D ψ (-1) := H.std
  have hBA : AdjLaw ψ B A := _root_.GlobalTheory.AdjLawPf.adjLaw D ψ hψ B A
  have hAB : AdjLaw ψ A B := _root_.GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B
  obtain ⟨om', H', hom'⟩ := GlobalTheory.WeilConj.exists_conj_weilDatum D ψ B A χB χA om H
  have hθK : ∀ (g : GA D A) (h : GA D B) (Φ : WO B A → ℂ),
      starRingEnd ℂ (thetaKO om' g h (dag B A Φ)) = thetaKO om h g Φ := by
    intro g h Φ
    simp only [thetaKO]
    rw [hom' h g Φ]
    simp only [dag]
    rw [GlobalTheory.WeilConj.adjO_zero hBA, Complex.conj_conj]
  refine ⟨om', dag B A Φ₁, dag B A Φ₂, H', fock_dag hψ hθ hBA sB sA hsB hsA hF₁,
    fock_dag hψ hθ hBA sB sA hsB hsA hF₂, trivial, trivial, fun g h => ?_, fun g h => ?_, ?_⟩
  · rw [hθK, hK₁]
  · rw [hθK, hK₂]
  · exact coef_dag hAB hBA (fun g : GA D A => om (1, g) Φ₁) (fun g : GA D A => om' (g, 1) (dag B A Φ₁))
      (fun g => hom' 1 g Φ₁) Φ₂ c hc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleTargetOrthogonalSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.TensorTargetRule

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

variable {D : D7}

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem dagger_resT_symm {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (u : WO S A) (v : WO S B) :
    dagger S T ((d.resT S).symm (u, v)) = (d.resS S).symm (dagger S A u, dagger S B v) := by
  rw [d.resT_symm_apply, d.resS_symm_apply, d.pA_eq, d.pB_eq]
  simp only [dagger, adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, cancel₂ (gA_mul_giA A),
    cancel₂ (gA_mul_giA B), Matrix.one_mul]

theorem dagger_resS_symm {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (u : WO A S) (v : WO B S) :
    dagger T S ((d.resS S).symm (u, v)) = (d.resT S).symm (dagger A S u, dagger B S v) := by
  have h := dagger_resT_symm d S (dagger A S u) (dagger B S v)
  rw [dagger_dagger, dagger_dagger] at h
  rw [← h, dagger_dagger]

theorem resT_dagger {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (y : WO T S) :
    d.resT S (dagger T S y) = (dagger A S (d.resS S y).1, dagger B S (d.resS S y).2) := by
  have h := dagger_resS_symm d S (d.resS S y).1 (d.resS S y).2
  rw [Prod.mk.eta, AddEquiv.symm_apply_apply] at h
  rw [h, AddEquiv.apply_symm_apply]

theorem resS_dagger {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (x : WO S T) :
    d.resS S (dagger S T x) = (dagger S A (d.resT S x).1, dagger S B (d.resT S x).2) := by
  have h := dagger_resT_symm d S (d.resT S x).1 (d.resT S x).2
  rw [Prod.mk.eta, AddEquiv.symm_apply_apply] at h
  rw [h, AddEquiv.apply_symm_apply]

theorem cj_boxT {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (fA : WO S A → ℂ) (fB : WO S B → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) (d.boxT S fA fB) = d.boxS S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger A S) fA) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger B S) fB) := by
  funext y
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, OrthDec.boxT, OrthDec.boxS, resT_dagger, map_mul]

theorem conjAdjoint_cj {S T : HSp D} (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjAdjoint om (h, g) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) (om (g, h) f) :=
  cjEnd_cj (daggerEquiv S T) (om (g, h)) f

theorem cj_mem_span {X Y : Type} (e : Y → X) {s : Set (X → ℂ)} {s' : Set (Y → ℂ)} (h : ∀ g ∈ s, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e g ∈ s')
    {g : X → ℂ} (hg : g ∈ Submodule.span ℂ s) : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e g ∈ Submodule.span ℂ s' := by
  induction hg using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (h x hx)
  | zero =>
    have e0 : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e (0 : X → ℂ) = 0 := by funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    rw [e0]; exact zero_mem _
  | add x y _ _ hx hy =>
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e (x + y) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e x + GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e y := by funext z; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    rw [e1]; exact add_mem hx hy
  | smul c x _ hx =>
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e (c • x) = starRingEnd ℂ c • GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e x := by funext z; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    rw [e1]; exact Submodule.smul_mem _ _ hx

theorem tensorTarget : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (T A B : HSp D) (d : OrthDec T A B) (S : HSp D), GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.TensorTarget ψ d S := by
  intro D ψ hψ T A B d S
  have thd : ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) ↔ IsThetaFunO ψ S T f :=
    fun S T => (_root_.GlobalTheory.AdjointPair.adjoint_clauses D ψ hψ S T).2.2.1
  have src := _root_.GlobalTheory.TensorSrc.tensorSource D ψ hψ T A B d S
  have cc : ∀ f : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S T) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) = f := fun f => cj_cj _ _ (dagger_dagger S T) f
  refine
    { box_theta := fun fA fB hA hB => d.isThetaFunO_boxT hA hB
      box_zero := fun fA fB => d.boxT_zero S fA fB
      heis_box := fun fA fB => ⟨fun u => ?_, fun v => ?_⟩
      slice_theta := fun f hf => ⟨fun v => ?_, fun u => ?_⟩
      dense := fun f hf => ?_
      om_box := ?_
      om_slice := ?_ }
  · rw [d.heisO_boxT, AddEquiv.apply_symm_apply, heisO_zero']
  · rw [d.heisO_boxT, AddEquiv.apply_symm_apply, heisO_zero']
  · have h1 := (src.slice_theta (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) ((thd S T f).2 hf)).1 (dagger S B v)
    rw [← thd S A]
    convert h1 using 1
    funext u
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_resS_symm, dagger_dagger]
  · have h1 := (src.slice_theta (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) ((thd S T f).2 hf)).2 (dagger S A u)
    rw [← thd S B]
    convert h1 using 1
    funext v
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_resS_symm, dagger_dagger]
  · intro ε hε
    obtain ⟨g, hg, hgε⟩ := src.dense _ ((thd S T f).2 hf) ε hε
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S T) g, cj_mem_span _ ?_ hg, fun x => ?_⟩
    · rintro _ ⟨f1, f2, h1, h2, rfl⟩
      refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S A) f1, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S B) f2, (thd A S f1).2 h1, (thd B S f2).2 h2, ?_⟩
      funext x
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, resS_dagger, map_mul]
    · have h := hgε (dagger S T x)
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_dagger] at h ⊢
      rw [← Complex.norm_conj, map_sub, Complex.conj_conj]
      exact h
  · intro χS χA χB omT omA omB hT hA hB g a b fA fB hfA hfB
    have key := src.om_box χA χB χS (conjAdjoint omT) (conjAdjoint omA) (conjAdjoint omB)
      (_root_.GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ S T χS (χA * χB) omT hT) (_root_.GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ S A χS χA omA hA)
      (_root_.GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ S B χS χB omB hB) a b g (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger A S) fA) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger B S) fB)
      ((thd S A fA).2 hfA) ((thd S B fB).2 hfB)
    rw [conjAdjoint_cj, conjAdjoint_cj, ← cj_boxT, ← cj_boxT, conjAdjoint_cj] at key
    have := congrArg (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S T)) key
    rwa [cc, cc] at this
  · intro χS χA χB omT omA omB hT hA hB g a b f hf v
    have key := src.om_slice χA χB χS (conjAdjoint omT) (conjAdjoint omA) (conjAdjoint omB)
      (_root_.GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ S T χS (χA * χB) omT hT) (_root_.GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ S A χS χA omA hA)
      (_root_.GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ S B χS χB omB hB) a b g (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) ((thd S T f).2 hf) (dagger S B v)
    have e1 : (fun u'' => conjAdjoint omB (b, g) (fun v'' => GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f ((d.resS S).symm (u'', v''))) (dagger S B v)) =
        GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger A S) (fun u' => omB (g, b) (fun v' => f ((d.resT S).symm (u', v'))) v) := by
      funext u''
      have hfun : (fun v'' => GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f ((d.resS S).symm (u'', v''))) =
          GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger B S) (fun v' => f ((d.resT S).symm (dagger A S u'', v'))) := by
        funext v''
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_resS_symm]
      rw [hfun, conjAdjoint_cj]
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_dagger]
    obtain ⟨k1, k2⟩ := key
    rw [e1] at k1 k2
    refine ⟨(thd S A _).1 k1, fun u => ?_⟩
    have h := k2 (dagger S A u)
    rw [conjAdjoint_cj, conjAdjoint_cj] at h
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_resS_symm, dagger_dagger] at h
    exact (starRingEnd ℂ).injective h

end GlobalTheory.TensorTargetRule

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationValueAtOriginLeviFactor
section
namespace I195MixedCoordinates_020c054dc3163dabb7fb929c

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

end I195MixedCoordinates_020c054dc3163dabb7fb929c

public noncomputable abbrev _root_.I195MixedCoordinates_34c45ee3f9864caed77cce75.source :=
  @_root_.I195MixedCoordinates_020c054dc3163dabb7fb929c.source

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.LeviOrigin

def diagAt {R : Type*} [CommRing R] (ρ : ℕ) (i : Fin ρ) : R →* Matrix (Fin ρ) (Fin ρ) R where
  toFun t := Matrix.diagonal (Function.update (1 : Fin ρ → R) i t)
  map_one' := by
    have h1 : Function.update (1 : Fin ρ → R) i 1 = 1 := by
      funext j; by_cases h : j = i
      · subst h; simp
      · simp [Function.update_of_ne h]
    show Matrix.diagonal (Function.update (1 : Fin ρ → R) i 1) = 1
    rw [h1]; exact Matrix.diagonal_one
  map_mul' s t := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]

def dgU {R : Type*} [CommRing R] (ρ : ℕ) (i : Fin ρ) : Rˣ →* GL (Fin ρ) R := Units.map (diagAt ρ i)

theorem det_dgU {R : Type*} [CommRing R] (ρ : ℕ) (i : Fin ρ) (t : Rˣ) :
    Matrix.GeneralLinearGroup.det (dgU ρ i t) = t := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal (Function.update (1 : Fin ρ → R) i (t : R))).det = t
  rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

theorem continuous_dgU {R : Type*} [CommRing R] [TopologicalSpace R] (ρ : ℕ) (i : Fin ρ) :
    Continuous (dgU (R := R) ρ i) := by
  apply Continuous.units_map
  show Continuous fun t : R => Matrix.diagonal (Function.update (1 : Fin ρ → R) i t)
  exact Continuous.matrix_diagonal (continuous_const.update i continuous_id)

theorem dgU_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (ρ : ℕ) (i : Fin ρ) (x : Rˣ) :
    dgU ρ i (Units.map f.toMonoidHom x) = Matrix.GeneralLinearGroup.map f (dgU ρ i x) := by
  ext k l
  show Matrix.diagonal (Function.update (1 : Fin ρ → S) i (f x)) k l =
    f (Matrix.diagonal (Function.update (1 : Fin ρ → R) i (x : R)) k l)
  simp only [Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    by_cases h' : k = i
    · subst h'; simp
    · simp [Function.update_of_ne h']
  · simp

theorem dgU_sub_one {R : Type*} [CommRing R] (ρ : ℕ) (i : Fin ρ) (x : Rˣ) (k l : Fin ρ) :
    ((dgU ρ i x).1 - 1) k l = if k = i ∧ l = i then (x : R) - 1 else 0 := by
  show Matrix.diagonal (Function.update (1 : Fin ρ → R) i (x : R)) k l - (1 : Matrix (Fin ρ) (Fin ρ) R) k l = _
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : k = l
  · subst h
    by_cases h' : k = i
    · subst h'; simp
    · simp [Function.update_of_ne h', h']
  · simp [h]
    intro hk hl; exact absurd (hk.trans hl.symm) h

end GlobalTheory.LeviOrigin

theorem GlobalTheory.LeviOrigin.alpha_eq (D : D7) (ρ : ℕ) (α : GL (Fin ρ) (AE D) →* Circle) (χT : (AE D)ˣ →* Circle)
    (hαc : Continuous α) (hαr : ∀ a : GL (Fin ρ) D.host.E, α (Matrix.GeneralLinearGroup.map (incA D) a) = 1)
    (hα1 : ∀ a : GL (Fin ρ) (AE D), Matrix.GeneralLinearGroup.det a = 1 → α a = 1)
    (hχ : IsHeckeChar D χT)
    (hs : ∀ e, IsSplitIdem D e → ∀ a : GL (Fin ρ) (AE D), (∀ i j, (e + cA D e) * (a.1 - 1) i j = (a.1 - 1) i j) →
      α a = (χT (Matrix.GeneralLinearGroup.det a))⁻¹) :
    ∀ a : GL (Fin ρ) (AE D), α a = (χT (Matrix.GeneralLinearGroup.det a))⁻¹ := by
  rcases Nat.eq_zero_or_pos ρ with h0 | hpos
  · intro a
    have hd : Matrix.GeneralLinearGroup.det a = 1 := by
      ext; rw [Matrix.GeneralLinearGroup.val_det_apply]; subst h0; simp
    rw [hα1 a hd, hd, map_one, inv_one]
  obtain ⟨i0⟩ : Nonempty (Fin ρ) := ⟨⟨0, hpos⟩⟩
  have hhec : IsHeckeChar D (α.comp (GlobalTheory.LeviOrigin.dgU ρ i0) * χT) := by
    refine ⟨?_, ?_⟩
    · exact (hαc.comp (GlobalTheory.LeviOrigin.continuous_dgU ρ i0)).mul hχ.1
    · intro x
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, hχ.2 x, mul_one, GlobalTheory.LeviOrigin.dgU_map (incA D) ρ i0 x]
      exact hαr _
  have hν := _root_.GlobalTheory.HeckeSplitAll.heckeChar_eq_one_of_split D _ hhec (by
    intro e he x hx
    have h2 := hs e he (GlobalTheory.LeviOrigin.dgU ρ i0 x) (by
      intro k l
      rw [GlobalTheory.LeviOrigin.dgU_sub_one]
      split_ifs
      · exact hx
      · exact mul_zero _)
    rw [MonoidHom.mul_apply, MonoidHom.comp_apply, h2, GlobalTheory.LeviOrigin.det_dgU, inv_mul_cancel])
  have hdg : ∀ t, α (GlobalTheory.LeviOrigin.dgU ρ i0 t) = (χT t)⁻¹ := by
    intro t
    have := hν t
    rw [MonoidHom.mul_apply, MonoidHom.comp_apply] at this
    exact eq_inv_of_mul_eq_one_left this
  intro a
  have hb : Matrix.GeneralLinearGroup.det (a * (GlobalTheory.LeviOrigin.dgU ρ i0 (Matrix.GeneralLinearGroup.det a))⁻¹) = 1 := by
    rw [map_mul, map_inv, GlobalTheory.LeviOrigin.det_dgU, mul_inv_cancel]
  have h1 := hα1 _ hb
  have h3 : α a = α (a * (GlobalTheory.LeviOrigin.dgU ρ i0 (Matrix.GeneralLinearGroup.det a))⁻¹) *
      α (GlobalTheory.LeviOrigin.dgU ρ i0 (Matrix.GeneralLinearGroup.det a)) := by
    rw [← map_mul, inv_mul_cancel_right]
  rw [h3, h1, one_mul]
  exact hdg _

theorem GlobalTheory.LeviOrigin.value_at_origin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → (∀ g, (_root_.I195MixedCoordinates_020c054dc3163dabb7fb929c.source d) T ψ μ 𝓕 (om (d.emb0 g, 1) f) 0 = om₀ (g, 1) ((_root_.I195MixedCoordinates_020c054dc3163dabb7fb929c.source d) T ψ μ 𝓕 (f) 0)) ∧ (∀ a : GL (Fin ρ) (AE D), Matrix.GeneralLinearGroup.det a = 1 → (_root_.I195MixedCoordinates_020c054dc3163dabb7fb929c.source d) T ψ μ 𝓕 (om (d.levi a, 1) f) 0 = (_root_.I195MixedCoordinates_020c054dc3163dabb7fb929c.source d) T ψ μ 𝓕 (f) 0) ∧ ∀ a : GL (Fin ρ) (AE D), (_root_.I195MixedCoordinates_020c054dc3163dabb7fb929c.source d) T ψ μ 𝓕 (om (d.levi a, 1) f) 0 = ((((χT (Matrix.GeneralLinearGroup.det a))⁻¹ : Circle) : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ)) • (_root_.I195MixedCoordinates_020c054dc3163dabb7fb929c.source d) T ψ μ 𝓕 (f) 0 := by
  intro D ψ S S₀ T ρ d χS χT om om₀ hW hW₀ μ 𝓕 hμ f hf
  obtain ⟨α, ξ, hαc, hαr, hξc, hξr, hmain⟩ := _root_.GlobalTheory.Unf.levi_origin_scalar D ψ S S₀ T ρ d χS χT om om₀ hW hW₀ μ 𝓕 hμ
  have hsp := _root_.GlobalTheory.LeviSplitChar.levi_chars_split D ψ S S₀ T ρ d χS χT om om₀ hW hW₀ μ 𝓕 hμ α ξ hmain

  have hξ : ∀ g, ξ g = 1 :=
    GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D S₀ ξ hξc hξr (fun e he => (hsp e he).1)

  have hα1 : ∀ a : GL (Fin ρ) (AE D), Matrix.GeneralLinearGroup.det a = 1 → α a = 1 :=
    _root_.GlobalTheory.glChar_eq_one_of_det_eq_one D ρ α hαc
  have hα := GlobalTheory.LeviOrigin.alpha_eq D ρ α χT hαc hαr hα1 hW.hecT (fun e he => (hsp e he).2)
  have hhalf : ∀ a : GL (Fin ρ) (AE D), Matrix.GeneralLinearGroup.det a = 1 →
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a = 1 := by
    intro a ha
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod
    rw [ha, MonoidHom.map_one (GlobalTheory.Doubling.absE D.host.F D.host.E)]
    simp
  have hom₀ : ∀ x, om₀ (1, 1) x = x := by
    intro x; rw [← Prod.one_eq_mk, map_one, Module.End.one_apply]
  have key : ∀ a, (_root_.I195MixedCoordinates_020c054dc3163dabb7fb929c.source d) T ψ μ 𝓕 (om (d.levi a, 1) f) 0 = ((((χT (Matrix.GeneralLinearGroup.det a))⁻¹ : Circle) : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ)) • (_root_.I195MixedCoordinates_020c054dc3163dabb7fb929c.source d) T ψ μ 𝓕 (f) 0 := by
    intro a
    have := hmain a 1 f hf
    rw [map_one, mul_one, hξ 1, hom₀, hα a] at this
    simpa using this
  refine ⟨?_, ?_, key⟩
  · intro g
    have := hmain 1 g f hf
    rw [map_one, one_mul, hξ g, map_one, hhalf 1 (map_one _)] at this
    simpa using this
  · intro a ha
    rw [key a, ha, map_one, inv_one, hhalf a ha]
    simp
end
end

