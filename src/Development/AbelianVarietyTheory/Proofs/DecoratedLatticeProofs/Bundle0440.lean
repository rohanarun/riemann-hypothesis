module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardOfInjective
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0458
public import Formalism.LocalToGlobal.BaseRankEqOfRealisation
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0266
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0401
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepInverseCharacterLocalComponentChainTame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.QTw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QTw.StepChar

open _root_.Formalism.L2.Col Formalism.L2.DIV
open Formalism.L2.Host (HChar)

theorem locK_unif {L : Type} [Field L] [NumberField L] (χ : HChar L) (Q : HeightOneSpectrum (𝓞 L)) (hu : χ.UnrAt Q) (k : Lˣ)
    (hk : Q.valuation L (k : L) = WithZero.exp (-1 : ℤ)) : χ.locK Q k = χ.val Q :=
  χ.val_eq hu _ ((Formalism.UG.P.levelaf_valued_algebraMap Q (k : L)).trans hk)

section General

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {σ : X.K →+* ℂ} {e : Fin R.m → X.Tau → ℚ} {m0 : Fin R.m → HChar X.E} {eta ξ : HChar X.E}

theorem g_notMem (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : ∀ k, Pr.g k ∈ S) (P : rowSG Pr sel mu)
    (hP : P.1 ∉ Pr.vGs) (k : Fin 2) : ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal :=
  have hlp := GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P
  GlobalTheory.ColPeriod.natCast_notMem_of_ne (hPr.g_prime k) hlp.1.1 (fun h => hlp.2 hP (h ▸ hg k)) P.1 (Ideal.absNorm_mem _)

theorem res_eq (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : ∀ k, Pr.g k ∈ S) (ht : Ch.Tied σ e m0 eta)
    (h : GlobalTheory.Mem.Col2.Reads σ (mu : Chr X.F X.E X.K) ξ) (j : Fin R.m) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (x : X.Eˣ) (y : 𝓞 X.E) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (hx : (x : X.E) = (y : X.E))
    (hc : (c : 𝓞 X.E ⧸ P.1.asIdeal) = Ideal.Quotient.mk P.1.asIdeal y) :
    σ ((resChar (mu : Chr X.F X.E X.K) P.1 c : X.Kˣ) : X.K) = (((m0 j * ξ).locK P.1 x : ℂˣ) : ℂ) := by
  have hta := GlobalTheory.Mem.ReadTwist.tameAt h fun v => Subgroup.mem_iInf.1 mu.2.1.2 v
  have hu : P.1.valuation X.E (x : X.E) = 1 := by
    rw [hx]
    exact GlobalTheory.NormOneUnit.val_eq_one fun hy => c.ne_zero (hc.trans (Ideal.Quotient.eq_zero_iff_mem.2 hy))
  have e1 : (m0 j * ξ).locK P.1 x = (m0 j).locK P.1 x * ξ.locK P.1 x := rfl
  rw [e1, GlobalTheory.NormOneUnit.locK_unr ((ht.mu0 j).unr _ (g_notMem hX hPr hsel hg P hP)) hu, one_mul,
    GlobalTheory.NormOneUnit.resChar_eq h hta P.1 c y x hx hc.symm]

theorem map_muAt (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : ∀ k, Pr.g k ∈ S) (ht : Ch.Tied σ e m0 eta)
    (h : GlobalTheory.Mem.Col2.Reads σ (mu : Chr X.F X.E X.K) ξ) (j : Fin R.m) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hQ : cst.muq (j.1 + 1) P = (((Ch.muVal j P.1)⁻¹ * (qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ) : X.K)) (a : X.Eˣ) :
    σ (muAt Ch sel mu cst j.1 P (a : X.E)) = (((m0 j * ξ).locK P.1 a : ℂˣ) : ℂ)⁻¹ := by
  classical
  have hlp := GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P
  have hta := GlobalTheory.Mem.ReadTwist.tameAt h fun v => Subgroup.mem_iInf.1 mu.2.1.2 v
  have hq := (GlobalTheory.TwistVal.main X.F X.E X.K σ _ ξ h hta P.1).2 hlp.1.2
  have hg' := g_notMem hX hPr hsel hg P hP
  have hm : ∀ x, (((m0 j * ξ)⁻¹.locK P.1 x : ℂˣ) : ℂ) = (((m0 j * ξ).locK P.1 x : ℂˣ) : ℂ)⁻¹ := fun x => by
    rw [← Units.val_inv_eq_inv_val]
    rfl
  rw [← hm]
  refine GlobalTheory.LocCharComp.locChar_eq_locK X.E X.K σ P.1 (m0 j * ξ)⁻¹ _ _ hlp.1.2 (fun q hq' => ?_) (fun x y c hx hc => ?_) a
  · have e1 : (m0 j * ξ).locK P.1 q = (m0 j).locK P.1 q * ξ.locK P.1 q := rfl
    rw [hm, e1, Units.val_mul, ← hq q hq', hQ, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul,
      map_inv₀, map_inv₀, ht.muVal j P.1 hg', ← locK_unif (m0 j) P.1 ((ht.mu0 j).unr _ hg') q
        (hq' ▸ GlobalTheory.CharVal.val_natCast_of_notMem_sq (Ideal.absNorm_mem _) hlp.1.2), mul_inv]
    rfl
  · rw [hm, if_neg hP, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, res_eq hX hPr hsel hg ht h j P hP x y c hx hc]

end General

theorem comp_eq_muAt_and_tame : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (P : BadPr I a), P.1 ∉ (B.primes X).vGs → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt (D := I.rec7 l Z) q.e P.1 → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt P.1 x) → DenseRange (ofSplit q).pr → ∀ (i : ℕ) (hi : i < B.R.m) (χ : (AE (I.rec7 l Z))ˣ →* Circle), ChrEq (D := I.rec7 l Z) χ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → ∀ μ : kˣ →* ℂˣ, (ofSplit q).IsComp χ⁻¹ μ → (∀ (x : B.fields.E) (u : kˣ), (u : k) = (ofSplit q).pr x → (μ u : ℂ) = B.embLL (Formalism.L2.Col.muAt I.Ch I.sel (I.tup a) (I.cst a) i P x)) ∧ IsTame μ := by
  intro B X I hI l Z a P hP k _ _ _ _ q hq hint hden i hi χ hχ μ hμ
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hμ' : (ofSplit q).IsComp χ μ⁻¹ := fun x b hb => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hμ x b hb, MonoidHom.inv_apply, Circle.coe_inv, inv_inv]
  constructor
  · intro x u hu
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact u.ne_zero (hu.trans (q.pr.comp (incA (I.rec7 l Z))).map_zero)
    have h1 := GlobalTheory.LocMod.SplitHecke.chi_idlU_rat q hq hχ hx0 u hu
    have h2 := map_muAt hX hPr hI.sel_ok hI.g_mem hI.ch_tied (hI.xi_reads a) ⟨i, hi⟩ P hP
      ((hI.idx_ok a).muqQ i hi P hP) (Units.mk0 x hx0)
    have h3 := hμ u (GlobalTheory.LocMod.SplitHecke.idlU q u) rfl
    rw [MonoidHom.inv_apply, Circle.coe_inv, h1] at h3
    exact h3.trans h2.symm
  · have hr : IsRes (D := I.rec7 l Z) (I.C.mu0 ⟨i, hi⟩ * I.xi a) P.1
        ((Units.map (B.embLL : B.fields.K →* ℂ)).comp (resChar (I.tup a : Chr B.fields.F B.fields.E B.fields.K) P.1)) :=
      fun y x c hx hc => Units.ext (res_eq hX hPr hI.sel_ok hI.g_mem hI.ch_tied (hI.xi_reads a) ⟨i, hi⟩ P hP x y c hx hc)
    have ht := (GlobalTheory.LocMod.SplitHecke.tame_and_res (I.rec7 l Z) k q P.1 hq hint hden χ _ _ μ⁻¹ hχ hr hμ').1
    intro x hx
    have := ht x hx
    rwa [MonoidHom.inv_apply, inv_eq_one] at this

end GlobalTheory.QTw.StepChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopReadOfTrueQ
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.Inhab

open GlobalTheory.SymBridge

section Frames

variable {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]

def stdFr (k : Type) [Field k] (e : Y ≃ Fin N) : GlobalTheory.LocMod.Frame k N Y where
  β := (1 : Matrix (Fin N) (Fin N) k).submatrix id e
  γ := (1 : Matrix (Fin N) (Fin N) k).submatrix e id
  βγ := by rw [Matrix.submatrix_mul_equiv, Matrix.one_mul, Matrix.submatrix_id_id]
  γβ := by
    have h := Matrix.submatrix_mul_equiv (1 : Matrix (Fin N) (Fin N) k) (1 : Matrix (Fin N) (Fin N) k) e (Equiv.refl _) e
    rw [Matrix.one_mul, Matrix.submatrix_one_equiv] at h
    exact h

theorem isStdFr_stdFr {pos : Y → ℕ} {e : Y ≃ Fin N} (h : IsOrd pos e) : IsStdFr pos (stdFr k e) := ⟨e, h, rfl⟩

def blockOrd (κ τ l j : ℕ) : (Fin κ ⊕ Fin l) ⊕ Fin j × Fin τ ≃ Fin (κ + l + j * τ) :=
  (Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv

theorem isOrd_xPos (κ τ j : ℕ) : IsOrd (xPos (κ := κ) (τ := τ) (j := j)) (blockOrd κ τ j j) := by
  rintro ((i | i) | ⟨a, b⟩) <;> simp [blockOrd, xPos, finProdFinEquiv]
  ring

theorem isOrd_zPos (κ τ l j : ℕ) : IsOrd (zPos (κ := κ) (τ := τ) (l := l) (j := j)) (blockOrd κ τ l j) := by
  rintro ((i | i) | ⟨a, b⟩) <;> simp [blockOrd, zPos, finProdFinEquiv]
  ring

end Frames

section True

open GlobalTheory.Mem

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}

end True

section Built

open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) {Rc : Formalism.L2.RecT ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} (y : RealIn a.x Rc S)

end Built

end GlobalTheory.Fam.Inhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerSiegelUnipotentAction
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.Unip

theorem trace_algebraMap_mul_gen {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (a : R) (t : S) :
    Algebra.trace R S (algebraMap R S a * t) = a * Algebra.trace R S t := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

theorem trace_mul_smul_gen {R : Type} [CommRing R] {n : ℕ} (s : R) (T b : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (T * (s • b)) = s * Matrix.trace (b * T) := by
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm]

theorem incA_xiZero_mul_inv_eq_algebraMap_neg (D : D7) (μ : D.host.E) (lam : D.host.F)
    (hlam : algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ) :
    incA D D.host.xi0 * incA D μ⁻¹ =
      algebraMap (AF D.host.F) (AE D) (-algebraMap D.host.F (AF D.host.F) lam) := by
  have hxm : D.host.xi0 * μ⁻¹ = -algebraMap D.host.F D.host.E lam := by
    rw [hlam, neg_div, neg_neg, div_eq_mul_inv]
  have hinc : incA D (algebraMap D.host.F D.host.E lam) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) lam) := by
    show (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] AF D.host.F ⊗[D.host.F] D.host.E)
      (algebraMap D.host.F D.host.E lam) = _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply D.host.F (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E)]
  rw [← map_mul, hxm, map_neg, hinc, map_neg]

theorem neg_trHalf_eq (D : D7) (μ : D.host.E) (lam : D.host.F)
    (hlam : algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ) (t : AE D) :
    -(trHalf D (incA D μ⁻¹ * t)) = algebraMap D.host.F (AF D.host.F) lam * halfTr t := by
  have h1 : Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (incA D μ⁻¹ * t)) =
      -algebraMap D.host.F (AF D.host.F) lam * Algebra.trace (AF D.host.F) (AE D) t :=
    (congrArg (Algebra.trace (AF D.host.F) (AE D)) ((mul_assoc _ _ t).symm.trans
      (congrArg (· * t) (incA_xiZero_mul_inv_eq_algebraMap_neg D μ lam hlam)))).trans (trace_algebraMap_mul_gen _ t)
  have h2 : ∀ h a z : AF D.host.F, -(h * (-a * z)) = a * (h * z) := fun h a z => by ring
  exact (congrArg (fun y => -(algebraMap D.host.F (AF D.host.F) (1 / 2) * y)) h1).trans (h2 _ _ _)

theorem chr_eq_shift (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (μ : D.host.E) (lam : D.host.F)
    (hlam : algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ) {n : ℕ} (T b : Mx D n n) (c : skewA D n)
    (hc : c.1 = incA D μ⁻¹ • b) :
    chr ψ T c = shift ψ lam (halfTr (Matrix.trace (b ⬝ T : Mx D n n))) := by
  have h1 : Matrix.trace (T ⬝ c.1 : Mx D n n) = incA D μ⁻¹ * Matrix.trace (b ⬝ T : Mx D n n) :=
    (congrArg (fun y : Mx D n n => Matrix.trace (T ⬝ y : Mx D n n)) hc).trans (trace_mul_smul_gen _ T b)
  exact congrArg ψ ((congrArg (fun y => -(trHalf D y)) h1).trans (neg_trHalf_eq D μ lam hlam _))

theorem transport_unip : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS → ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ → ∀ (g : G D A.rank) (b : Mx D A.rank A.rank), mat g = blk4 1 b 0 1 → ∀ Φ x, (omS g Φ).1 x = shift ψ lam (halfTr (Matrix.trace (b ⬝ GlobalTheory.StdUnn.inner B x x : Mx D A.rank A.rank))) * Φ.1 x := by
  intro D ψ A B χB omh hW ν 𝓨 hν θ hθ μ hμ κ hκ omS hT lam hlam g b hg Φ x
  obtain ⟨c, hc, hgc⟩ := _root_.GlobalTheory.ChartUnip.chart_unip D A μ hμ κ hκ (κ.symm g) b (by rw [MulEquiv.apply_symm_apply]; exact hg)
  obtain ⟨f, hf, hfΦ⟩ := ((_root_.GlobalTheory.SchSchwartzAll.schSchwartz D) ψ hW.std θ hθ A B ν 𝓨 hν).2.1 Φ.1 Φ.2
  have h1 := hT (κ.symm g) f hf Φ hfΦ.symm
  rw [MulEquiv.apply_symm_apply] at h1
  rw [h1, hgc, ((_root_.GlobalTheory.Core.Rk.SchLaws.sch_laws D ψ A B χB omh hW ν 𝓨 hν f hf).2.2.1 c x), hfΦ]
  exact congrArg (· * Φ.1 x) (chr_eq_shift D ψ μ lam hlam _ b c hc)

end GlobalTheory.StdUnn.Unip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleCharacterAtBasePointDetRootRootOfUnity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharRoot

theorem sigR_sigR (D : D7) (w : Formalism.L2.Theta.AE D) :
    sigR (AF D.host.F) D.sp.cm.sig (sigR (AF D.host.F) D.sp.cm.sig w) = w := by
  have hσ : ∀ z : D.host.E, D.sp.cm.sig (D.sp.cm.sig z) = z := fun z => star_star z
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => simp [sigR, hσ]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]

theorem exists_idF_eq_mul_sigR (D : D7) (x : (Formalism.L2.Theta.AE D)ˣ) :
    ∃ t : (AF D.host.F)ˣ, ((idF D t : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = (x : Formalism.L2.Theta.AE D) * sigR (AF D.host.F) D.sp.cm.sig (x : Formalism.L2.Theta.AE D) := by
  have hσ : ∀ z : D.host.E, D.sp.cm.sig (D.sp.cm.sig z) = z := fun z => star_star z
  have htr : ∀ z : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = z + D.sp.cm.sig z := by
    intro z
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add (f := _), hσ, add_comm]
  obtain ⟨t, ht⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr
    (x * Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom x) (by
      rw [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_mul, sigR_sigR, mul_comm])
  refine ⟨t, ?_⟩
  convert congrArg Units.val ht using 1
  · rfl
  · rfl

theorem pow_eq_one_of_isDetRoot (D : D7) (V : HSp D) (g : GA D V) (x : (Formalism.L2.Theta.AE D)ˣ) (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (n : ℕ)
    (hn : 0 < n) (hbase : ∀ t, c (idF D t) ^ n = 1) (hcont : Continuous c) (hR : IsDetRoot V g x)
    (d : (Formalism.L2.Theta.AE D)ˣ) (hd : (d : Formalism.L2.Theta.AE D) = (Formalism.L2.Theta.mt V g).det)
    (hfu : Formalism.L2.Pj.FinUnit d) : ∃ N : ℕ, 0 < N ∧ c x ^ N = 1 := by
  obtain ⟨t, ht⟩ := exists_idF_eq_mul_sigR D x
  have hxx : x * x = d * idF D t := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ht, hd]
    unfold IsDetRoot at hR
    unfold Formalism.L2.Theta.mt
    nth_rewrite 1 [hR]
    ring
  obtain ⟨N, -, -, m, hm, hord⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hcont
  refine ⟨2 * (m * n), by positivity, ?_⟩
  rw [pow_mul, sq, ← map_mul, hxx, map_mul, mul_pow, pow_mul, hord _ hfu, one_pow, one_mul, mul_comm m n, pow_mul, hbase t,
    one_pow]

theorem infPart_det_of_mem_GfC : ∀ (D : D7) (V : HSp D) (g : GA D V), g ∈ GfC V →
    infPart D (Formalism.L2.Theta.mt V g).det = 1 := by
  intro D V g hg
  have h : infHom V g = 1 := hg
  have h2 := congrArg (fun z : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => Matrix.det z.1) h
  simp only [Units.val_one, Matrix.det_one] at h2
  rw [← h2]
  unfold infHom Formalism.L2.Theta.mt Formalism.UG.bc
  rw [RingHom.map_det]
  rfl

theorem finUnit_det_of_carries : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V) (k : GL (Fin n) (EF D)),
    g ∈ GfC V → finM V hn g = k.1 →
    Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat D.host.E n) (Formalism.L2.Col.stdLat D.host.E n) →
    ∃ d : (Formalism.L2.Theta.AE D)ˣ, (d : Formalism.L2.Theta.AE D) = (Formalism.L2.Theta.mt V g).det ∧ Formalism.L2.Pj.FinUnit d := by
  intro D V n hn g k hg hk hc
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.KJStdInt.carries_std_integral D.host.F D.host.E n k hc
  have hu : IsUnit (Formalism.L2.Theta.mt V g).det := by
    unfold Formalism.L2.Theta.mt
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  obtain ⟨f1, f2⟩ := _root_.GlobalTheory.DetIntUnit.det_int_unit D V n hn g k hk h1 h2 hu.unit hu.unit_spec
  refine ⟨hu.unit, hu.unit_spec, ?_, f1, f2⟩
  rw [hu.unit_spec]
  exact infPart_det_of_mem_GfC D V g hg

end GlobalTheory.CharRoot

theorem GlobalTheory.CharRoot.chr_xr_pow_eq_one : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ j, j < B.R.m → ∀ i, i ≤ B.R.m → ∀ β, ∃ n : ℕ, 0 < n ∧ A.chr (j + 1) (A.xr i β) ^ n = 1 := by
  intro B X I hI hP l Z u a Ch₀ A hA j hj i hi β
  have hc : ChrEq (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (A.chr (j + 1)) (I.C.mu0 ⟨j, hj⟩ * I.xi a) := hA.chr ⟨j, hj⟩
  obtain ⟨hG, hF, hR⟩ := hA.kA i hi β
  have hb := hA.base i hi β

  obtain ⟨n, hn, hξ⟩ : ∃ n : ℕ, 0 < n ∧ I.xi a ^ n = 1 := by
    have hx := hI.xi_reads a
    have ht : IsOfFinOrder (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) := (I.tup a).2.1.1.1.2
    obtain ⟨n, hn, hpow⟩ := ht.exists_pow_eq_one
    refine ⟨n, hn, ?_⟩
    apply Subtype.ext
    ext y
    have h1 := hx y
    simp only [SubgroupClass.coe_pow, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, OneMemClass.coe_one, MonoidHom.one_apply, Units.val_one]
    rw [h1, ← map_pow, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hpow]
    simp

  have hpow : ∀ k : ℕ, ChrEq (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (A.chr (j + 1) ^ (k + 1)) ((I.C.mu0 ⟨j, hj⟩ * I.xi a) ^ (k + 1)) := by
    intro k
    induction k with
    | zero => simpa using hc
    | succ k ih =>
      rw [pow_succ (A.chr (j + 1)) (k + 1), pow_succ _ (k + 1)]
      exact GlobalTheory.AdelicLiftCompare.chrEq_mul ih hc
  have hbase : ∀ t, A.chr (j + 1) (idF (I.rec7 l Z) t) ^ n = 1 := by
    intro t
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h1 := hpow k
    rw [mul_pow, hξ, mul_one] at h1
    have h2 := GlobalTheory.GridWeil.triv_base h1 (PsiExist.trivOn_pow (I.C.isMu0 ⟨j, hj⟩).triv (k + 1)) t
    simpa using h2

  have hcar : Formalism.L2.Herm.Carries (A.kb i β) (Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) (Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) := by
    obtain ⟨h1, h2⟩ := hb
    have h := h1.lat
    erw [h2] at h
    exact h
  obtain ⟨d, hd, hfu⟩ := GlobalTheory.CharRoot.finUnit_det_of_carries (I.rec7 l Z) _ _ _ (A.kA i β) (A.kb i β) hG hF hcar
  exact GlobalTheory.CharRoot.pow_eq_one_of_isDetRoot (I.rec7 l Z) _ (A.kA i β) (A.xr i β) (A.chr (j + 1)) n hn hbase hc.1.1 hR d hd hfu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductInverseScalarLawsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistChainLevelProduct_inverse_scalar_laws : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∀ k ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h, ∃ a : ℂ, a ≠ 0 ∧ ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂ → t.om j (1, k) (comb c.ψ _ _ (w.eQ j) Ψ₁) = a⁻¹ • comb c.ψ _ _ (w.eQ j) Ψ₁ ∧ t.om (j + 1) (k, 1) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) = a • comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂ := by
  first | exact @GlobalTheory.QFinLaw.inverse_laws | exact GlobalTheory.QFinLaw.inverse_laws | (intros; apply GlobalTheory.QFinLaw.inverse_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlacesGroupEqProductLocalGroupsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlaces_group_eq_product_local_groups : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ P : (∀ i, GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k) →* GA D (c.V (j + 1)), (∀ (H : Subgroup (GA D (c.V (j + 1)))) y, (∀ i, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) (y i) ∈ H) → P y ∈ H) ∧ (∀ y, P y ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) ∧ ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q), ∃ y, x = P y ∧ ∀ i, x * ((F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) (y i))⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
  first | exact @GlobalTheory.QProd.prod_local | exact GlobalTheory.QProd.prod_local | (intros; apply GlobalTheory.QProd.prod_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaChainStepAdjointScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTw

theorem stepLam_of_ns : ∀ D : D7, SoftQ D → UpParQ D → UpQ D → QOfVal D → UpVal D → StepExactNS D → LFull D → Restore D → StepLam D := by
  intro D h1 h2 h3 h4 h5 h6 h7 h8
  intro hG c w hw k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' m X hX mR hmR φ v hv H₀ hH₀ hκ B hB u₁ hu hq
  obtain ⟨H, -, hH, -, hL, hol⟩ := h7 c hw.com B hB k hk
  obtain ⟨r1, -, r2, r3⟩ := h8 hG c w hw k hk s s' hs hs' p hp
  have hinv := GlobalTheory.ChainTw.invFam_bounded D c w hw k hk.le s hs u₁ B hu hB
  have hns := _root_.GlobalTheory.ChainNS.chainNS_holds D c hw.com c.S subset_rfl B hB hinv k hk
  have hKF : PiTensorProduct.tprod ℂ v ∈ s.KF := Submodule.subset_span ⟨v, hv.1, rfl⟩
  have ex := fun u₂ => h6 hG c w hw k hk s s' hs hs' p hp ipD ip hM m X hX mR hmR φ v hv u₁ u₂ _ hu hq hns _ hol
  simp only [GlobalTheory.ChainTw.Check.const_eq w k p m X mR φ v _ H H₀ (r1 H H₀ hH hH₀) r2 r3] at ex
  have hne : p.up φ (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) ≠ 0 := fun h0 => by
    have e := ex u₁
    rw [h0] at e
    have z : s'.pet 0 0 = 0 := by simp [PiLocalization₂.pet, Lift.pet]
    rw [z] at e
    rcases mul_eq_zero.1 e.symm with e | e
    · exact mul_ne_zero hκ hL ((map_eq_zero _).1 e)
    · have := hM.pos u₁ hu.1
      rw [e] at this
      simp at this
  obtain ⟨v1, v2⟩ := h5 hG c w hw k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' φ _ hKF
  obtain ⟨w₀, hw0, hadj⟩ := v1 ⟨u₁, hne⟩
  refine ⟨w₀, hw0, hadj, fun x₁ hx₁ => ?_⟩
  have e1 := v2 w₀ hadj u₁ x₁ hx₁
  refine ⟨?_, ?_, fun u₂ x₂ hx₂ => ?_⟩
  · exact (h1 c w hw (k + 1) hk s' hs').2.2.2 x₁ w₀ _ (e1 ▸ hne) (e1 ▸ h2 hG c w hw k hk s s' hs hs' p hp u₁ _ φ hu _ hKF hne)
  · exact (h4 c w hw (k + 1) hk s' hs').1 x₁ w₀ (e1 ▸ hne) (e1 ▸ h3 hG c w hw k hk s s' hs hs' p hp u₁ φ hq _ hKF)
  · have e := ex u₂
    rw [e1, v2 w₀ hadj u₂ x₂ hx₂] at e
    rw [← e]
    exact (hM'.schur x₁ x₂ w₀ w₀).symm

end GlobalTheory.ChainTw

end
end

