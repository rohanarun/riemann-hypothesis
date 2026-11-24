module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3094
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0028
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2708
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsGeoOfSignatureRankBounds
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0074
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0073
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0693
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0013
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0014
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKernelMatchOnOppositeParabolic
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsAlgebraicFunctionDefiniteThetaNeZero
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.DefThetaNZ
section Darboux
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem exists_algebraic_vector_definite_theta_ne (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') (hDec : Decay B G om om')
    {Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ} (hΦ' : Φ' ∈ G.M'.So B.ψ B.τ₁) (hne : G.M'.I om' Φ' ≠ 0) :
    ∃ ΦD ∈ GlobalTheory.SquareAgree.algD G.M' B.ψ B.emb, G.M'.I om' ΦD ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply hne
  clear hne
  funext h
  have hPair := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  have hpres : ∀ x, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), om' x Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')) :=
    hPair.weil.isUSplitting.pres
  have hdense := GlobalTheory.T.polynomialFock_dense_archimedeanSchwartz F E σ B _ _ _ _ G.M' _ _ om' _ _ _ _ hPair
  have hsch : ∀ Ψ ∈ G.M'.So B.ψ B.τ₁, Ψ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')) := by
    intro Ψ hΨ
    refine (Submodule.span_le.2 ?_) hΨ
    rintro _ ⟨f, φ, hSB, hvac, -, rfl⟩
    refine GlobalTheory.TensUniq.pure_mem_schA f φ hSB ?_
    filter_upwards [hvac, hT.geo.hM'.std] with v h1 h2
    rw [h1, h2]
  show G.M'.I om' Φ' h = 0
  induction hΦ' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hSB, hvac, hv₁, rfl⟩ := hx
    have hc := _root_.GlobalTheory.T.pure_theta_integral_continuous_orthogonal hP F E σ B a a' G X om om' hT hDec φ hSB hvac hv₁ h
    have hz : ∀ P ∈ (G.M'.Pol B.ψ B.emb : Set (SInf F (Fin a' × Fin (a + a')))), G.M'.I om' (pure P φ) h = 0 := fun P hP' =>
      congrFun (hall _ (Submodule.subset_span ⟨P, φ, hP', hSB, hvac, rfl⟩)) h
    have hcl : IsClosed {f : SInf F (Fin a' × Fin (a + a')) | G.M'.I om' (pure f φ) h = 0} := isClosed_eq hc continuous_const
    have hsub := hcl.closure_subset_iff.2 hz
    rw [hdense.closure_eq] at hsub
    exact hsub (Set.mem_univ f)
  | zero => exact I_zero _ _ h
  | add x y hx hy ihx ihy =>
    rw [I_add' G.M' om' ((hDec.2 x hx).2.1 h) ((hDec.2 y hy).2.1 h) (fun g => ⟨hpres _ _ (hsch x hx), hpres _ _ (hsch y hy)⟩),
      ihx, ihy, add_zero]
  | smul c x hx ihx => rw [I_smul', ihx, mul_zero]
end Darboux
end GlobalTheory.DefThetaNZ
namespace GlobalTheory.DefThetaNZ
open scoped Matrix
theorem exists_algebraic_function_definite_theta_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
  GlobalTheory.SquareComm.IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) →
  ∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∃ Φ ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ ≠ 0 := by
  intro hP hK hL D ψ θ _hψ hθ W W₁ X A A₁ B α β hT _hdef ν₁ 𝓕₁ hν₁ ωA ωB Pi rf rl p p' hM
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Ker.HypModel.exists_haar_fundDom D W
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ :=
    _root_.GlobalTheory.SquareAgree.exists_isOver D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hM.weilA hM.weilB
  obtain ⟨R, Rf, hR⟩ := hL D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  obtain ⟨hDec, hK'⟩ := hK.1 D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  obtain ⟨⟨⟨Φ', hΦ'So, hne⟩, -⟩, -⟩ := hK' R Rf hR
  obtain ⟨ΦD, hΦD, hneD⟩ := _root_.GlobalTheory.DefThetaNZ.exists_algebraic_vector_definite_theta_ne hP hTD hDec hΦ'So hne
  obtain ⟨Φ, hΦ, hDat⟩ := hO.algB' ΦD hΦD
  refine ⟨Φ, hΦ, fun h0 => ?_⟩
  obtain ⟨h', hh'⟩ := Function.ne_iff.1 hneD
  obtain ⟨h, rfl⟩ := _root_.GlobalTheory.SquareAgree.kapX_surjective D X e hO.JX h'
  have := GlobalTheory.SquareAgree.thetaInt_eq_modelI D W₁ X _ _ _ Γ.M' (-1) hO.JW₁ ν₁ 𝓕₁ ωB om' (GlobalTheory.SquareAgree.kapX X e hO.JX) ΦD Φ
    hO.measW₁ hO.domW₁ (hO.theta_eq_B hDat) h
  rw [h0] at this
  exact hh' this.symm
end GlobalTheory.DefThetaNZ
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_theta_lift_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
  GlobalTheory.SquareComm.IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) →
  ∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∃ Φ ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ ≠ 0 := by
  first | exact @_root_.GlobalTheory.DefThetaNZ.exists_algebraic_function_definite_theta_ne_zero | exact _root_.GlobalTheory.DefThetaNZ.exists_algebraic_function_definite_theta_ne_zero | (intros; apply _root_.GlobalTheory.DefThetaNZ.exists_algebraic_function_definite_theta_ne_zero <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsGoodGeometryOverCarriedFrames
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.exists_good_geometry_over_carried_frames : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW) (lam : T → ℂ) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), GlobalTheory.SqTower.IsStageC W i j p q X →
      Factor X W.ψ W.θ lam → GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank →
      ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank A'.rank),
        GlobalTheory.SqStepBig.Over X Γ ∧ Γ.p = p ∧ Γ.q = q ∧ Γ.IsGood Bs ∧
        ∀ s, (s = t ∨ s = μ₀) → GlobalTheory.SqStepBig.Carried G W i j X Bs FA FA' FW Γ s := by
  intro _
  refine GlobalTheory.SqStepBig.gbig_two GlobalTheory.T.towerStage_seesawDictionary_framesSignatures GlobalTheory.T.towerStage_seesawDictionary_framesSignatures ?_
  intro D T Lc sc G μ₀ C x b q1 _ W _ i j p q A A' WW X lam t Bs hX _ hB
  obtain ⟨FA, FA', FW, a, b, -, -, -, hd⟩ := q1 W i j p q A A' WW X hX
  obtain ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXi⟩ := hX
  obtain ⟨⟨hψ, -⟩, hBs, hemb, -, -, hκ⟩ := hB
  have hsz := GlobalTheory.StageDict.stage_sizes i j hp hq hrA hrA'
  obtain ⟨Γ, hp', hq', hg, hS⟩ := UpperTheory.exists_geo_of_signature_rank_bounds D W.ψ T A A' WW X FA FA' FW hXi.rank Bs p q hBs hψ hemb hXi.rigA hXi.rigA' hXi.rigW
    hXi.meas hXi.meas' hnA hnA' hnW hsz.1 hsz.2.1 hsz.2.2.1 hκ
  refine ⟨FA, FA', FW, Γ, ⟨⟨rfl, hS.JA, hS.latA.1⟩, ⟨rfl, hS.JB, hS.latB.1⟩, ⟨hXi.rank.symm, hS.pairA.JW, hS.latA.2⟩⟩,
    hp', hq', hg, fun s _ => ?_⟩
  obtain ⟨-, -, f1, f2, k1, k2⟩ := hd s
  refine ⟨f1, f2, k1, k2, fun om om' hT => ?_⟩
  obtain ⟨cA, cB, hO, -⟩ := UpperTheory.exists_seesaw_intertwiners_of_triple D W.ψ W.θ hXi.isVac.2.inf T A A' WW X FA FA' FW hXi.rank Bs Γ hS
    (GlobalTheory.SqStep.chs G i j s) om om' hT (X.ω s) (X.ω' s) (hXi.weil s) (hXi.weil' s)
  exact ⟨_, cA, cB, hO⟩
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.StageUniqueOfArchimedeanTriple
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.StageUniq
open GlobalTheory.SquareComm GlobalTheory.BotUniq
private theorem grid_bigness_mono {P Q : GP} (hP : GBig P)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨CF1, h1⟩ := hP
  refine ⟨CF1, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, g1⟩ := h1 ε CF hCF
  exact ⟨C1, x1, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ (g1 C hC D large₂ he hx hr T Lc μ₀ hμ G)⟩
theorem stage_unique_of_archimedean_triple (hH : GlobalTheory.Published.HoweDualityReal) (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) {A A' WW : HSp D} (α β : (AE D)ˣ →* Circle)
    (hT : IsTriple A A' WW α β) (m : MeasureTheory.Measure (GA D A)) (fd : Set (GA D A))
    (m' : MeasureTheory.Measure (GA D A')) (fd' : Set (GA D A'))
    (hme : IsHaarFD A m fd) (hme' : IsHaarFD A' m' fd') (ω : GlobalTheory.Grid.WRep A WW) (ω' : GlobalTheory.Grid.WRep A' WW)
    (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW)
    (Pi₀ : ModuleCat.{0} ℂ) (rf₀ : GA D WW → Module.End ℂ Pi₀)
    (rl₀ : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi₀)
    (p₀ : (WO A WW → ℂ) →ₗ[ℂ] Pi₀) (p₀' : (WO A' WW → ℂ) →ₗ[ℂ] Pi₀)
    (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi)
    (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi)
    (p : (WO A WW → ℂ) →ₗ[ℂ] Pi) (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi)
    (hm₀ : IsMatch ψ θ FA FA' FW α β ω ω' Pi₀ rf₀ rl₀ p₀ p₀')
    (hm : IsMatch ψ θ FA FA' FW α β ω ω' Pi rf rl p p') :
    ∃ (E : Pi₀ ≃ₗ[ℂ] Pi) (c : ℂ), c ≠ 0 ∧ (∀ Φ ∈ algF ψ θ true FA FW, p Φ = c • E (p₀ Φ)) ∧
      ∀ Φ' ∈ algF ψ θ false FA' FW, p' Φ' = E (p₀' Φ') := by
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ := _root_.GlobalTheory.SquareAgree.exists_isOver D ψ θ hθ A A' WW FA FA' FW _ _ hT m fd m' fd'
    hme hme' ω ω' hm.weilA hm.weilB
  obtain ⟨R, Rf, hR⟩ := hL D.host.F D.host.E D.sp.cm.sig Bs A.rank A'.rank Γ Xc om om' hTD
  have kA : ∀ Φ ∈ algF ψ θ true FA FW, p₀ Φ = 0 ↔ p Φ = 0 := fun Φ hΦ => by
    obtain ⟨ΦD, hΦD, hD⟩ := hO.algA Φ hΦ
    rw [_root_.GlobalTheory.SquareAgree.mem_ker_iff_polarization_match_eq_zero hH hP D _ _ A A' WW FA FA' FW _ _ _ _
        _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi₀ rf₀ rl₀ p₀ p₀' hm₀ Φ hΦ ΦD hΦD hD,
      _root_.GlobalTheory.SquareAgree.mem_ker_iff_polarization_match_eq_zero hH hP D _ _ A A' WW FA FA' FW _ _ _ _
        _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hm Φ hΦ ΦD hΦD hD]
  have kB : ∀ Φ ∈ algF ψ θ false FA' FW, p₀' Φ = 0 ↔ p' Φ = 0 := fun Φ hΦ => by
    obtain ⟨ΦD, hΦD, hD⟩ := hO.algB Φ hΦ
    rw [_root_.GlobalTheory.SquareAgree.derivative_eq_zero_iff_polarization_match hH hP D _ _ A A' WW FA FA' FW _ _
        _ _ _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi₀ rf₀ rl₀ p₀ p₀' hm₀ Φ hΦ ΦD hΦD hD,
      _root_.GlobalTheory.SquareAgree.derivative_eq_zero_iff_polarization_match hH hP D _ _ A A' WW FA FA' FW _ _
        _ _ _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hm Φ hΦ ΦD hΦD hD]
  obtain ⟨EA, hEA⟩ := exists_equiv_of_ker _ p₀ p hm₀.mapA.onto hm.mapA.onto kA
  obtain ⟨EB, hEB⟩ := exists_equiv_of_ker _ p₀' p' hm₀.mapB.onto hm.mapB.onto kB
  have fA : ∀ h ∈ GfC WW, ∀ x, EA (rf₀ h x) = rf h (EA x) := fun h hh =>
    intertwine _ p₀ p EA hEA hm₀.mapA.onto _ _ fun Φ hΦ =>
      ⟨_, hm₀.mapA.stabX.1 h hh Φ hΦ, hm₀.mapA.eqf h hh Φ hΦ, hm.mapA.eqf h hh Φ hΦ⟩
  have fB : ∀ h ∈ GfC WW, ∀ x, EB (rf₀ h x) = rf h (EB x) := fun h hh =>
    intertwine _ p₀' p' EB hEB hm₀.mapB.onto _ _ fun Φ hΦ =>
      ⟨_, hm₀.mapB.stabX.1 h hh Φ hΦ, hm₀.mapB.eqf h hh Φ hΦ, hm.mapB.eqf h hh Φ hΦ⟩
  have lA : ∀ τ, ∀ Y ∈ lieAt WW τ, ∀ x, EA (rl₀ τ Y x) = rl τ Y (EA x) := fun τ Y hY =>
    intertwine _ p₀ p EA hEA hm₀.mapA.onto _ _ fun Φ hΦ => by
      obtain ⟨Φ', hΦ', hd⟩ := hm₀.mapA.stabX.2 τ Y hY Φ hΦ
      exact ⟨Φ', hΦ', hm₀.mapA.eql τ Y hY Φ hΦ Φ' hΦ' hd, hm.mapA.eql τ Y hY Φ hΦ Φ' hΦ' hd⟩
  have lB : ∀ τ, ∀ Y ∈ lieAt WW τ, ∀ x, EB (rl₀ τ Y x) = rl τ Y (EB x) := fun τ Y hY =>
    intertwine _ p₀' p' EB hEB hm₀.mapB.onto _ _ fun Φ hΦ => by
      obtain ⟨Φ', hΦ', hd⟩ := hm₀.mapB.stabX.2 τ Y hY Φ hΦ
      exact ⟨Φ', hΦ', hm₀.mapB.eql τ Y hY Φ hΦ Φ' hΦ' hd, hm.mapB.eql τ Y hY Φ hΦ Φ' hΦ' hd⟩
  let ι := {g // g ∈ GfC WW} ⊕ {x : D.what₂.Tau × Matrix (Fin WW.rank) (Fin WW.rank) ℂ // x.2 ∈ lieAt WW x.1}
  let ρ : ι → Module.End ℂ Pi₀ := Sum.elim (fun g => rf₀ g.1) (fun x => rl₀ x.1.1 x.1.2)
  have hrank : Module.rank ℂ Pi₀ ≤ Cardinal.aleph0 :=
    _root_.GlobalTheory.SquareAgree.rank_polarization_pi_le_aleph0 hH hP D _ _ A A' WW FA FA' FW _ _ _ _ _ _ _ _ e Bs Γ Xc om om'
      cA cB hθ hT hO hTD R Rf hR Pi₀ rf₀ rl₀ p₀ p₀' hm₀
  have hirr : ∀ N : Submodule ℂ Pi₀, (∀ k, ∀ x ∈ N, ρ k x ∈ N) → N = ⊥ ∨ N = ⊤ := fun N hN =>
    hm₀.irred.2 N (fun g hg x hx => hN (Sum.inl ⟨g, hg⟩) x hx) fun τ Y hY x hx => hN (Sum.inr ⟨(τ, Y), hY⟩) x hx
  have hcomm : ∀ k, ((EA.trans EB.symm : Pi₀ ≃ₗ[ℂ] Pi₀) : Module.End ℂ Pi₀) * ρ k =
      ρ k * ((EA.trans EB.symm : Pi₀ ≃ₗ[ℂ] Pi₀) : Module.End ℂ Pi₀) := by
    rintro (⟨g, hg⟩ | ⟨⟨τ, Y⟩, hY⟩)
    · exact comm_of_intertwine EA EB _ _ (fA g hg) (fB g hg)
    · exact comm_of_intertwine EA EB _ _ (lA τ Y hY) (lB τ Y hY)
  obtain ⟨c, hc⟩ := GlobalTheory.dixmier_commutant_scalar ι Pi₀ ρ hrank hirr _ hcomm
  have hT' : ∀ x, EB.symm (EA x) = c • x := fun x => by
    have := LinearMap.congr_fun hc x
    simpa using this
  haveI : Nontrivial Pi₀ := hm₀.irred.1
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := exists_ne (0 : Pi₀)
    have h1 := hT' x
    rw [zero_smul, LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff] at h1
    exact hx h1
  refine ⟨EB, c, hc0, fun Φ hΦ => ?_, fun Φ hΦ => hEB Φ hΦ⟩
  rw [hEA Φ hΦ, ← LinearEquiv.map_smul, ← hT', LinearEquiv.apply_symm_apply]
theorem _root_.GlobalTheory.T.theta_stage_unique : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (a b : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j a b X →
    ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), ∀ (Pi₀ : ModuleCat.{0} ℂ) rf₀ rl₀ p₀ p₀' (Pi : ModuleCat.{0} ℂ) rf rl p p',
    GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi₀ rf₀ rl₀ p₀ p₀' →
    GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' →
    ∃ (E : Pi₀ ≃ₗ[ℂ] Pi) (c : ℂ), c ≠ 0 ∧ (∀ Φ ∈ GlobalTheory.SquareComm.algF W.ψ W.θ true FA FW, p Φ = c • E (p₀ Φ)) ∧
      ∀ Φ' ∈ GlobalTheory.SquareComm.algF W.ψ W.θ false FA' FW, p' Φ' = E (p₀' Φ') := by
  intro hP _ hL
  refine grid_bigness_mono GlobalTheory.T.towerStage_seesawDictionary_framesSignatures ?_
  intro D T Lc sc G μ₀ C x b _ H W i j a a' A A' WW X hX FA FA' FW t Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm
  obtain ⟨_, _, _, _, _, -, -, -, hall⟩ := H W i j a a' A A' WW X hX
  have hIs := hX.2.2.2.2.2.2.2
  exact _root_.GlobalTheory.StageUniq.stage_unique_of_archimedean_triple hP.howeDualityReal hP hL W.ψ W.θ hIs.isVac.2.inf _ _ (hall t).1 X.m X.fd X.m' X.fd'
    hIs.meas hIs.meas' (X.ω t) (X.ω' t) FA FA' FW Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm
end GlobalTheory.StageUniq
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaImageEqSpanDarboux
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.DarbImage
section Generic
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
end Generic
end GlobalTheory.DarbImage
namespace GlobalTheory.DarbImage
theorem theta_image_darboux_basis : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (∀ T : ((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) →ₗ[ℂ] (WO W X → ℂ),
          (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
            T Φ = GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Φ) →
          (GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb).map T = algF ψ θ true A B) ∧
        ∀ T : ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) →ₗ[ℂ] (WO W₁ X → ℂ),
          (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)),
            T Φ = GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Φ) →
          (GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb).map T = algF ψ θ false A₁ B := by
  intro hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have hG : Γ.M.IsGood Bs.ψ := hM.triple.geo.hM
  have hG' : Γ.M'.IsGood Bs.ψ := hM.triple.geo.hM'
  have hs := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz D.sp.cm.sig Γ.V Γ.W Γ.M Bs.ψ Bs.emb hG
  have hs' := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz D.sp.cm.sig Γ.V' Γ.W Γ.M' Bs.ψ Bs.emb hG'
  refine ⟨fun T hT => ?_, fun T hT => ?_⟩
  · refine map_eq Γ.M Bs.ψ Bs.emb _ T _ hs hT
      (_root_.GlobalTheory.T.gaussian_theta_lift_algebraic hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM)
      (fun f φ u f₁ hf hu hA h1 h2 hin => ?_) ?_
    · obtain ⟨L, hLc, hLf, hL⟩ := _root_.GlobalTheory.T.theta_pure_tensor_hasDerivAt_first hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB
        R Rf hM f φ u f₁ hf hu hA h1 h2
      rw [hL]
      exact _root_.GlobalTheory.SquareComm.LineDeriv.deriv_line_mem_algF D ψ θ hψ hθ true W X A B _ hin L hLc hLf
    · rw [algF, Submodule.span_le]
      rintro q ⟨g, P, hg, rfl⟩
      obtain ⟨Φ, hΦ, hΦe⟩ := _root_.GlobalTheory.T.theta_lift_onto_fockSpace hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB
        R Rf hM g P hg
      exact ⟨Φ, hΦ, by rw [hT Φ (hs hΦ), hΦe]⟩
  · refine map_eq Γ.M' Bs.ψ Bs.emb _ T _ hs' hT
      (_root_.GlobalTheory.T.pure_gaussian_theta_lift_algebraic hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM)
      (fun f φ u f₁ hf hu hA h1 h2 hin => ?_) ?_
    · obtain ⟨L, hLc, hLf, hL⟩ := _root_.GlobalTheory.T.theta_pure_tensor_hasDerivAt_second hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB
        R Rf hM f φ u f₁ hf hu hA h1 h2
      rw [hL]
      exact _root_.GlobalTheory.SquareComm.LineDeriv.deriv_line_mem_algF D ψ θ hψ hθ false W₁ X A₁ B _ hin L hLc hLf
    · rw [algF, Submodule.span_le]
      rintro q ⟨g, P, hg, rfl⟩
      obtain ⟨Φ, hΦ, hΦe⟩ := _root_.GlobalTheory.T.fockSpace_contained_darbouxAlgebra_theta_image hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB
        R Rf hM g P hg
      exact ⟨Φ, hΦ, by rw [hT Φ (hs' hΦ), hΦe]⟩
end GlobalTheory.DarbImage
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_image_eq_span_darboux : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (∀ T : ((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) →ₗ[ℂ] (WO W X → ℂ),
          (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
            T Φ = GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Φ) →
          (GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb).map T = algF ψ θ true A B) ∧
        ∀ T : ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) →ₗ[ℂ] (WO W₁ X → ℂ),
          (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)),
            T Φ = GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Φ) →
          (GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb).map T = algF ψ θ false A₁ B := by
  first | exact @_root_.GlobalTheory.DarbImage.theta_image_darboux_basis | exact _root_.GlobalTheory.DarbImage.theta_image_darboux_basis | (intros; apply _root_.GlobalTheory.DarbImage.theta_image_darboux_basis <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareThetaIntegralsEq
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
namespace GlobalTheory.SquareAgree
theorem twisted_theta_integrals_agree : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SquareSt.ThetaIntegralsAgree := by
  intro hP hK hL D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hM
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ :=
    _root_.GlobalTheory.SquareAgree.exists_isOver D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hM.weilA hM.weilB
  obtain ⟨R, Rf, hR⟩ := hL D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  obtain ⟨hDec, hK'⟩ := hK.1 D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  obtain ⟨⟨-, ⟨c, hc, -⟩, hc0⟩, hCo⟩ := hK' R Rf hR
  obtain ⟨s, hs0, hs⟩ := _root_.GlobalTheory.T.twisted_theta_kernels_agree_up_to_scalar hP.howeDualityReal hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR
    Pi rf rl p p' hM
  refine ⟨c * s, mul_ne_zero (hc0 c hc) hs0, fun Φ' hΦ' => ?_⟩
  obtain ⟨Φ₀, hΦ₀, hrel, Φ₀D, hD₀, hSo⟩ :=
    GlobalTheory.SquareAgree.CoinvPass.coinv_passage D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hO hTD R Rf hR hCo Φ' hΦ'
  obtain ⟨hbd, hconv, -⟩ := hDec.2 Φ₀D hSo
  refine ⟨Φ₀, hΦ₀, hrel, _root_.GlobalTheory.ModGrowth.modInt_of_bound D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hO hν₁ hTD Φ₀ Φ₀D hD₀
    hconv ?_, fun Φ hΦ hp => ?_⟩
  · obtain ⟨C, k, hC⟩ := hbd 0
    exact ⟨C, k, fun g h => by simpa using hC g h⟩
  · obtain ⟨ΦD, -, hD⟩ := hO.algA Φ hΦ
    have hm := hs Φ hΦ Φ₀ hΦ₀ ΦD Φ₀D hD hD₀ hSo hp
    funext h
    rw [GlobalTheory.SquareAgree.thetaInt_eq_modelI D W X _ _ _ Γ.M 1 hO.JW ν 𝓕 ωA om (kapX X e hO.JX) ΦD Φ hO.measW hO.domW (hO.theta_eq_A hD) h,
      _root_.Pi.smul_apply,
      GlobalTheory.SquareAgree.thetaInt_eq_modelI D W₁ X _ _ _ Γ.M' (-1) hO.JW₁ ν₁ 𝓕₁ ωB om' (kapX X e hO.JX) Φ₀D Φ₀ hO.measW₁ hO.domW₁ (hO.theta_eq_B hD₀) h,
      hc ΦD (s • Φ₀D) hm (kapX X e hO.JX h), I_smul, smul_eq_mul, mul_assoc]
end GlobalTheory.SquareAgree
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_square_theta_integrals_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree := by
  first | exact @_root_.GlobalTheory.SquareAgree.twisted_theta_integrals_agree | exact _root_.GlobalTheory.SquareAgree.twisted_theta_integrals_agree | (intros; apply _root_.GlobalTheory.SquareAgree.twisted_theta_integrals_agree <;> assumption)
end
end

