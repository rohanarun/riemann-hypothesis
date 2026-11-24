module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3117
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0096
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0095
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0694
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0693
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0518
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0099
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0006
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0097

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralsAgreeOfIntegrableKernel
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
namespace GlobalTheory.ThetaAgreeConv
section Reg
open MeasureTheory GlobalTheory.SquareComm GlobalTheory.RegCompare
variable {D : D7}
theorem thetaIntegral_eq_zero_of_finiteRelation (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {W W₁ X : HSp D} {A₁ : GlobalTheory.ChainFr.Fr W₁}
    {B : GlobalTheory.ChainFr.Fr X} {α β : (AE D)ˣ →* Circle} (hT : IsTriple W W₁ X α β) {ν₁ : Measure (GA D W₁)}
    {𝓕₁ : Set (GA D W₁)} (hν₁ : IsHaarFD W₁ ν₁ 𝓕₁) {ωB : GlobalTheory.Grid.WRep W₁ X}
    (hw : GlobalTheory.Grid.IsWeil ψ false W₁ X α (α / β) ωB)
    (hstab : ∀ g ∈ GfC W₁, ∀ Φ ∈ algF ψ θ false A₁ B, ωB (g, 1) Φ ∈ algF ψ θ false A₁ B)
    {Ψ : WO W₁ X → ℂ} (hΨ : Ψ ∈ finRel ωB (algF ψ θ false A₁ B)) (hint : Intg ωB ν₁ 𝓕₁ Ψ) :
    thetaInt ωB ν₁ 𝓕₁ Ψ = 0 := by
  set S := algF ψ θ false A₁ B with hSdef
  have hL : ∀ Φ ∈ S, ∀ γ ∈ GQ W₁, ∀ g h, thetaKO ωB (γ * g) h Φ = thetaKO ωB g h Φ :=
    _root_.GlobalTheory.SquareComm.ThetaLeft.main D ψ θ hθ W₁ X A₁ B α (α / β) ωB hw
  have hle : finRel ωB S ≤ S := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, Φ, hΦ, rfl⟩
    exact S.sub_mem (hstab u hu Φ hΦ) hΦ
  have hΨS : Ψ ∈ S := hle hΨ
  have hrel := hΨ
  rw [finRel, Submodule.mem_span_set'] at hrel
  obtain ⟨n, c, g, hsum⟩ := hrel
  choose u hu Ψi hΨi hg using fun i => (g i).2
  obtain ⟨z, hzG, hz0, hz⟩ := _root_.GlobalTheory.T.twist_regulariser_isGood hP hK D ψ θ hθ W W₁ X A₁ B α β hT ν₁ 𝓕₁ hν₁ ωB hw n Ψi u hΨi hu
  have hX : ∀ i, ModInt θ ωB ν₁ 𝓕₁ (wop ωB z (Ψi i)) ∧
      ∃ u' ∈ GfC W₁, wop ωB z (ωB (u i, 1) (Ψi i)) = ωB (u', 1) (wop ωB z (Ψi i)) := fun i => hz i
  choose u' hu' hcomm using fun i => (hX i).2
  have hXS : ∀ i, wop ωB z (Ψi i) ∈ S := fun i => wop_mem hstab hzG (hΨi i)
  have hXr := fun i => modInt_right hν₁ (hL _ (hXS i)) (hX i).1 (u' i)
  have eΨ : Ψ = ∑ i, c i • (ωB (u i, 1) (Ψi i) - Ψi i) := by
    have e : ∑ i, c i • (g i : WO W₁ X → ℂ) = ∑ i, c i • (ωB (u i, 1) (Ψi i) - Ψi i) := by simp only [hg]
    rw [← e, hsum]
  have eW : wop ωB z Ψ = ∑ i, c i • (ωB (u' i, 1) (wop ωB z (Ψi i)) - wop ωB z (Ψi i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eΨ, map_sum]
    simp only [map_smul, map_sub, hcomm]
  have hJ : thetaInt ωB ν₁ 𝓕₁ (wop ωB z Ψ) = 0 := by
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Intg ωB ν₁ 𝓕₁ (c i • (ωB (u' i, 1) (wop ωB z (Ψi i)) - wop ωB z (Ψi i))) := fun i _ =>
      ((intg_of_modInt (hXr i).1).sub (intg_of_modInt (hX i).1)).smul _
    rw [eW, thetaInt_sum _ hi]
    simp only [thetaInt_smul, thetaInt_sub (intg_of_modInt (hXr _).1) (intg_of_modInt (hX _).1), (hXr _).2, sub_self,
      smul_zero, Finset.sum_const_zero]
  rw [thetaInt_wop_of_intg hν₁ (hL Ψ hΨS) hint z] at hJ
  exact (smul_eq_zero.1 hJ).resolve_left hz0
end Reg
theorem thetaIntegrals_agree_of_integrable_kernel : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
    GlobalTheory.SquareComm.IsTriple W W₁ X α β →
    ∀ (ν : MeasureTheory.Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : MeasureTheory.Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)),
    GlobalTheory.SquareComm.IsHaarFD W ν 𝓕 → GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ GlobalTheory.SquareComm.algF ψ θ true A B, ∀ Φ' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B,
      (∀ h, MeasureTheory.IntegrableOn (fun g => thetaKO ωB g h Φ') 𝓕₁ ν₁) → p Φ = p' Φ' →
      GlobalTheory.SquareComm.thetaInt ωA ν 𝓕 Φ = c • GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ' := by
  intro hP hK hL D ψ θ hψ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hM
  obtain ⟨c, hc0, hc⟩ := _root_.GlobalTheory.T.twisted_square_theta_integrals_eq hP hK hL D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁
    ωA ωB Pi rf rl p p' hM
  refine ⟨c, hc0, fun Φ hΦ Φ' hΦ' hint hp => ?_⟩
  obtain ⟨Φ₀, -, hrel, ⟨N, C, hmod⟩, hI⟩ := hc Φ' hΦ'
  have hp0 : p' Φ' = p' Φ₀ := by
    have := map_finRel_eq_zero hM hrel
    rwa [map_sub, sub_eq_zero] at this
  rw [hI Φ hΦ (hp.trans hp0)]
  congr 1
  have hlin : ∀ g h, thetaKO ωB g h (Φ' - Φ₀) = thetaKO ωB g h Φ' - thetaKO ωB g h Φ₀ := fun g h => by
    simp only [thetaKO, map_sub, _root_.Pi.sub_apply]
  have hint' : ∀ h, MeasureTheory.IntegrableOn (fun g => thetaKO ωB g h (Φ' - Φ₀)) 𝓕₁ ν₁ := fun h => by
    simp only [hlin]; exact (hint h).sub (hmod h).1
  have h0 := _root_.GlobalTheory.ThetaAgreeConv.thetaIntegral_eq_zero_of_finiteRelation hP hK hθ hT hν₁ hM.weilB hM.mapB.stabM.1 hrel hint'
  funext h
  have e := congrFun h0 h
  simp only [GlobalTheory.SquareComm.thetaInt, hlin, _root_.Pi.zero_apply] at e ⊢
  rw [MeasureTheory.integral_sub (hint h) (hmod h).1] at e
  exact (sub_eq_zero.1 e).symm
end GlobalTheory.ThetaAgreeConv
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
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaIntegrals_agree_of_convergence : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
    GlobalTheory.SquareComm.IsTriple W W₁ X α β →
    ∀ (ν : MeasureTheory.Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : MeasureTheory.Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)),
    GlobalTheory.SquareComm.IsHaarFD W ν 𝓕 → GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ GlobalTheory.SquareComm.algF ψ θ true A B, ∀ Φ' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B,
      (∀ h, MeasureTheory.IntegrableOn (fun g => thetaKO ωB g h Φ') 𝓕₁ ν₁) → p Φ = p' Φ' →
      GlobalTheory.SquareComm.thetaInt ωA ν 𝓕 Φ = c • GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ' := by
  first | exact @_root_.GlobalTheory.ThetaAgreeConv.thetaIntegrals_agree_of_integrable_kernel | exact _root_.GlobalTheory.ThetaAgreeConv.thetaIntegrals_agree_of_integrable_kernel | (intros; apply _root_.GlobalTheory.ThetaAgreeConv.thetaIntegrals_agree_of_integrable_kernel <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaTripleMapsLieEquivariant
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
theorem GlobalTheory.TripleAssembly.theta_triple_maps_lie_equivariant : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
        (∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, IsDer θ X (fun g => ωA (1, g)) τ Y Φ Φ' →
            GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ' = GlobalTheory.TripleAssembly.opLie θ ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) τ Y (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) ∧
          ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ false A₁ B, ∀ Φ' ∈ algF ψ θ false A₁ B, IsDer θ X (fun g => ωB (1, g)) τ Y Φ Φ' →
            GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ' = GlobalTheory.TripleAssembly.opLie θ ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) τ Y (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ) := by
  intro hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have key : ∀ τ, ∀ Y ∈ lieAt X τ, ∃ T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf),
      (∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, IsDer θ X (fun g => ωA (1, g)) τ Y Φ Φ' →
        GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ' = T (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) ∧
      (∀ Φ ∈ algF ψ θ false A₁ B, ∀ Φ' ∈ algF ψ θ false A₁ B, IsDer θ X (fun g => ωB (1, g)) τ Y Φ Φ' →
        GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ' = T (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ)) := by
    intro τ Y hY
    obtain ⟨γ, hγ, hγt⟩ := _root_.GlobalTheory.TransportedLine.exists_line_toUX_oneP D θ hθ X e Γ.W h.JX τ Y hY
    obtain ⟨Ti, hTi, hTi'⟩ := _root_.GlobalTheory.RealLieOp.exists_realOp Bs Γ Xc om om' R Rf hM γ hγ
    refine ⟨LinearMap.rTensor _ Ti, ?_, ?_⟩
    · intro Φ hΦ Φ' hΦ' hD
      obtain ⟨m, f, f₁, φ, hf, hsum, rfl, rfl⟩ := _root_.GlobalTheory.T.tripleProduct_lieDeriv_left_pure_tensor hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM τ Y hY γ hγ hγt Φ hΦ Φ' hΦ' hD
      have hmem : (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb :=
        Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, φ i, (hf i).1, (hf i).2.1, (hf i).2.2.1, rfl⟩
      have hφ : ∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = Γ.M.vac v :=
        fun i => ⟨(hf i).2.1, (hf i).2.2.1⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [_root_.GlobalTheory.T.tripleProduct_image_thetaSum_pure hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM m f₁ φ hφ hsum, _root_.GlobalTheory.T.tripleProduct_image_thetaSum_pure hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM m f φ hφ hmem, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.rTensor_tmul, ← hTi _ (hf i).1 _ (hf i).2.2.2]
    · intro Φ hΦ Φ' hΦ' hD
      obtain ⟨m, f, f₁, φ, hf, hsum, rfl, rfl⟩ := _root_.GlobalTheory.T.tripleProduct_lieDeriv_readoff hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM τ Y hY γ hγ hγt Φ hΦ Φ' hΦ' hD
      have hmem : (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb :=
        Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, φ i, (hf i).1, (hf i).2.1, (hf i).2.2.1, rfl⟩
      have hφ : ∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = Γ.M'.vac v :=
        fun i => ⟨(hf i).2.1, (hf i).2.2.1⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [_root_.GlobalTheory.T.tripleProduct_secondMap_theta_pure hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM m f₁ φ hφ hsum, _root_.GlobalTheory.T.tripleProduct_secondMap_theta_pure hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM m f φ hφ hmem, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.rTensor_tmul, ← hTi' _ (hf i).1 _ (hf i).2.2.2]
  have H : ∀ τ, ∀ Y ∈ lieAt X τ, ∃ T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf),
      ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, IsDer θ X (fun g => ωA (1, g)) τ Y Φ Φ' →
        GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ' = T (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ) :=
    fun τ Y hY => let ⟨T, hA, _⟩ := key τ Y hY; ⟨T, hA⟩
  have hOp : ∀ τ, ∀ (Y) (hY : Y ∈ lieAt X τ),
      GlobalTheory.TripleAssembly.opLie θ ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) τ Y = (H τ Y hY).choose := by
    intro τ Y hY
    unfold GlobalTheory.TripleAssembly.opLie
    rw [dite_eq_left (H τ Y hY)]
  refine ⟨fun τ Y hY Φ hΦ Φ' hΦ' hD => ?_, fun τ Y hY Φ hΦ Φ' hΦ' hD => ?_⟩
  · rw [hOp τ Y hY]
    exact (H τ Y hY).choose_spec Φ hΦ Φ' hΦ' hD
  · have k := key τ Y hY
    have hA := k.choose_spec.1
    have hB := k.choose_spec.2
    have hst : ∀ Φ ∈ algF ψ θ true A B, ∃ Φ' ∈ algF ψ θ true A B, IsDer θ X (fun g => ωA (1, g)) τ Y Φ Φ' :=
      (_root_.GlobalTheory.AlgStable.algF_isStable D ψ θ hψ hθ true W X A B β (β / α) ωA hWA).2.2 τ Y hY
    have hon : (algF ψ θ true A B).map (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) = ⊤ := (_root_.GlobalTheory.T.triple_algebra_map_surjective hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM).1
    have hEq : (H τ Y hY).choose = k.choose := by
      apply LinearMap.ext
      intro x
      have hx : ∃ Ψ, Ψ ∈ algF ψ θ true A B ∧ GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Ψ = x :=
        (Submodule.mem_map (f := GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) (p := algF ψ θ true A B)).1
          ((Submodule.eq_top_iff'.1 hon) x)
      have hΨ := hx.choose_spec.1
      have h1 := (hst _ hΨ).choose_spec
      rw [← hx.choose_spec.2]
      exact ((H τ Y hY).choose_spec _ hΨ _ h1.1 h1.2).symm.trans (hA _ hΨ _ h1.1 h1.2)
    exact (hB Φ hΦ Φ' hΦ' hD).trans (congrArg (fun T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf) =>
      T (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ)) ((hOp τ Y hY).trans hEq).symm)
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
theorem _root_.GlobalTheory.T.theta_triple_lift_lie_equivariant : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
        (∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, IsDer θ X (fun g => ωA (1, g)) τ Y Φ Φ' →
            GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ' = GlobalTheory.TripleAssembly.opLie θ ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) τ Y (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) ∧
          ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ false A₁ B, ∀ Φ' ∈ algF ψ θ false A₁ B, IsDer θ X (fun g => ωB (1, g)) τ Y Φ Φ' →
            GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ' = GlobalTheory.TripleAssembly.opLie θ ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) τ Y (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ) := by
  first | exact @_root_.GlobalTheory.TripleAssembly.theta_triple_maps_lie_equivariant | exact _root_.GlobalTheory.TripleAssembly.theta_triple_maps_lie_equivariant | (intros; apply _root_.GlobalTheory.TripleAssembly.theta_triple_maps_lie_equivariant <;> assumption)
end
end

