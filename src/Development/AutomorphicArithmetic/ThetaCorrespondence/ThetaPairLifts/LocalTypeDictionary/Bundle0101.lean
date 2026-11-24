module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3117
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3121
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0049

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DvStageGeoPass
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.StageGeo.geometric_stage_constant_on_pure_tensors :
    _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : MeasureTheory.Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : MeasureTheory.Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : Base D.host.F D.host.E) (Γ : Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → GlobalTheory.SquareAgree.IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    IsHaarFD W₁ ν₁ 𝓕₁ → IsWeil ψ false W₁ X α (α / β) ωB →
    (∀ g ∈ GfC W₁, ∀ Φ ∈ algF ψ θ false A₁ B, ωB (g, 1) Φ ∈ algF ψ θ false A₁ B) →
    ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F W.rank W₁.rank) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F W.rank W₁.rank) (c : ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ Xc om om' R Rf c →
    ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f' ∈ Γ.M'.Pol Bs.ψ Bs.emb,
    ∀ (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ)
      (φ' : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ v, φ' v ∈ GlobalTheory.WeilM.SB _) → (∀ v ∉ Xc.T, φ v = Γ.M.vac v) → (∀ v ∉ Xc.T, φ' v = Γ.M'.vac v) →
    R.p f = R.p' f' → (∀ v ∈ Xc.T, Rf.p v (φ v) = Rf.p' v (φ' v)) →
    ∀ (Φ : WO W X → ℂ) (Φ' : WO W₁ X → ℂ), GlobalTheory.SquareAgree.IsDatum Γ.M ψ cA (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) Φ →
      GlobalTheory.SquareAgree.IsDatum Γ.M' ψ cB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ') Φ' →
      (∀ h, MeasureTheory.IntegrableOn (fun g => thetaKO ωB g h Φ') 𝓕₁ ν₁) →
      thetaInt ωA ν 𝓕 Φ = c • thetaInt ωB ν₁ 𝓕₁ Φ' := by
  intro hP hK D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hν₁ hw hstab R Rf c hM hc f hf f' hf' φ φ'
    s s' v v' hR hfin Φ Φ' hD hD' hint
  have hT := hM.triple
  obtain ⟨hDec, hK'⟩ := hK.1 D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hT
  obtain ⟨-, hC⟩ := hK' R Rf hM
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := by rw [← hO.psi]; exact hT.base.std
  have hstd := hT.geo.hM'.std
  obtain ⟨-, hco, hex, -⟩ := hC.1 Bs.v₁ hT.chars.good
  have hv₁ : Bs.v₁ ∉ Xc.T := hT.chars.good.1
  have hcof : ∀ᶠ w in Filter.cofinite, φ' w = Γ.M'.vac w :=
    Filter.Eventually.mono Xc.T.finite_toSet.compl_mem_cofinite fun w hw => v' w hw
  have hφstd : ∀ᶠ w in Filter.cofinite, φ' w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers D.host.F} 1 :=
    (hcof.and hstd).mono fun w h => h.1.trans h.2
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor Bs.v₁ f' φ' hφstd
  obtain ⟨φo, hφo, hp⟩ := hex Bs.τ₁ (Rf.p' Bs.v₁ (φ' Bs.v₁))
  have hφoSB : φo ∈ GlobalTheory.WeilM.SB _ := hφo.1
  have hδ : φ' Bs.v₁ - φo ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om' Bs.v₁ :=
    (hco _ (sub_mem (s' Bs.v₁) hφoSB)).1 (by rw [map_sub, hp, sub_self])
  have hupd : ∀ w, Function.update φ' Bs.v₁ φo w ∈ GlobalTheory.WeilM.SB _ := by
    intro w
    by_cases hw : w = Bs.v₁
    · subst hw; rw [Function.update_self]; exact hφoSB
    · rw [Function.update_of_ne hw]; exact s' w
  have hcof' : ∀ᶠ w in Filter.cofinite, Function.update φ' Bs.v₁ φo w = Γ.M'.vac w := by
    filter_upwards [hcof, Filter.eventually_cofinite_ne Bs.v₁] with w h1 hne
    rw [Function.update_of_ne hne]; exact h1
  obtain ⟨Φ₀D, eD⟩ : ∃ Φ₀D, Φ₀D = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' (Function.update φ' Bs.v₁ φo) := ⟨_, rfl⟩
  have h0a : Φ₀D ∈ GlobalTheory.SquareAgree.algD Γ.M' Bs.ψ Bs.emb := Submodule.subset_span ⟨f', _, hf', hupd, hcof', eD⟩
  have h0s : Φ₀D ∈ Γ.M'.So Bs.ψ Bs.τ₁ :=
    Submodule.subset_span ⟨f', _, hupd, hcof', by rw [Function.update_self]; exact hφo, eD⟩
  have hdiff : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ' - Φ₀D ∈ GlobalTheory.SquareAgree.CoinvPass.relD Γ.M' om' Bs.ψ Bs.emb Bs.v₁ := by
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ' = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin D.host.F Bs.v₁) (φ' Bs.v₁) r := by
      rw [hrt, Function.update_eq_self]
    rw [e1, eD, ← hrt, ← GlobalTheory.SquareAgree.CoinvPass.tens_sub']
    exact GlobalTheory.SquareAgree.CoinvPass.tens_mem_relD Γ.M' om' Bs.ψ Bs.emb Bs.v₁ hstd hf' s' hcof hr hrt _ hδ
  have hpm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) Φ₀D := by
    refine ⟨insert Bs.v₁ Xc.T, Finset.subset_insert _ _, 1, 1, fun _ => f, fun _ => φ, fun _ => f',
      fun _ => Function.update φ' Bs.v₁ φo, fun _ => ⟨hf, s, fun w hw => v w fun h => hw (Finset.mem_insert_of_mem h)⟩,
      fun _ => ⟨hf', hupd, fun w hw => ?_⟩, by simp, by simp [eD], ?_⟩
    · beta_reduce
      rw [Function.update_of_ne fun h : w = Bs.v₁ => hw (h ▸ Finset.mem_insert_self _ _)]
      exact v' w fun h => hw (Finset.mem_insert_of_mem h)
    · rw [Fin.sum_univ_one, Fin.sum_univ_one, hR]
      congr 2
      funext w
      obtain ⟨w, hw⟩ := w
      by_cases h : w = Bs.v₁
      · subst h
        show Rf.p Bs.v₁ (φ Bs.v₁) = Rf.p' Bs.v₁ (Function.update φ' Bs.v₁ φo Bs.v₁)
        rw [Function.update_self, hp, v _ hv₁, v' _ hv₁]
        exact (hM.fin.sph _ hv₁).1
      · show Rf.p w (φ w) = Rf.p' w (Function.update φ' Bs.v₁ φo w)
        rw [Function.update_of_ne h]
        exact hfin w ((Finset.mem_insert.1 hw).resolve_left h)
  have hm := GlobalTheory.SquareAgree.PolMatchConst.match_of_polMatch Bs Γ Xc om om' R Rf hT _ _ hpm h0s
  obtain ⟨Φ₀, hΦ₀, hD0⟩ := hO.algB' Φ₀D h0a
  have hc1 : (-1 : D.host.E) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hk : GlobalTheory.SquareAgree.kapX X e hO.JX 1 = 1 := by
    apply Subtype.ext
    simp [GlobalTheory.SquareAgree.kapX]
  have key : ∀ Ψ ∈ GlobalTheory.SquareAgree.CoinvPass.relD Γ.M' om' Bs.ψ Bs.emb Bs.v₁,
      ∃ Φ ∈ finRel ωB (algF ψ θ false A₁ B), GlobalTheory.SquareAgree.IsDatum Γ.M' ψ cB Ψ Φ := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, hg, Ψ₀, hΨ₀, rfl⟩ := hz
      obtain ⟨Φ₁, hΦ₁, hD1⟩ := hO.algB' Ψ₀ hΨ₀
      have hgu : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc1 hO.JW₁ g) = g :=
        (GlobalTheory.ConjUTransport.conjEquiv W₁ (-1) hc1 hO.JW₁).right_inv g
      have hW := hO.weilB Ψ₀ Φ₁ hD1 (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc1 hO.JW₁ g) 1
      rw [hgu, hk] at hW
      exact ⟨_, Submodule.subset_span ⟨_, GlobalTheory.SquareAgree.CoinvPass.conjUInv_mem_GfC W₁ Γ.V' (-1) hc1 hO.JW₁ Bs.v₁ g hg, Φ₁, hΦ₁,
        rfl⟩, GlobalTheory.SquareAgree.CoinvPass.isDatum_sub hψ hW hD1⟩
    | zero => exact ⟨0, zero_mem _, GlobalTheory.SquareAgree.CoinvPass.isDatum_zero⟩
    | add a b _ _ ha hb =>
      obtain ⟨Φa, ha, hDa⟩ := ha
      obtain ⟨Φb, hb, hDb⟩ := hb
      exact ⟨Φa + Φb, add_mem ha hb, GlobalTheory.SquareAgree.CoinvPass.isDatum_add hψ hDa hDb⟩
    | smul c a _ ha =>
      obtain ⟨Φa, ha, hDa⟩ := ha
      exact ⟨c • Φa, Submodule.smul_mem _ c ha, GlobalTheory.SquareAgree.CoinvPass.isDatum_smul c hDa⟩
  obtain ⟨Ψ, hΨ, hDΨ⟩ := key _ hdiff
  have hrel : Φ' - Φ₀ ∈ finRel ωB (algF ψ θ false A₁ B) :=
    GlobalTheory.SquareAgree.CoinvPass.isDatum_unique cB.surjective (GlobalTheory.SquareAgree.CoinvPass.isDatum_sub hψ hD' hD0) hDΨ ▸ hΨ
  obtain ⟨hbd, hconv, -⟩ := hDec.2 Φ₀D h0s
  obtain ⟨N, C, hmod⟩ := _root_.GlobalTheory.ModGrowth.modInt_of_bound D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hO hν₁ hT Φ₀ Φ₀D hD0
    hconv (by
      obtain ⟨C, k, hC⟩ := hbd 0
      exact ⟨C, k, fun g h => by simpa using hC g h⟩)
  have hlin : ∀ g h, thetaKO ωB g h (Φ' - Φ₀) = thetaKO ωB g h Φ' - thetaKO ωB g h Φ₀ := fun g h => by
    simp only [thetaKO, map_sub, _root_.Pi.sub_apply]
  have hint' : ∀ h, MeasureTheory.IntegrableOn (fun g => thetaKO ωB g h (Φ' - Φ₀)) 𝓕₁ ν₁ := fun h => by
    simp only [hlin]; exact (hint h).sub (hmod h).1
  have h0 := _root_.GlobalTheory.ThetaAgreeConv.thetaIntegral_eq_zero_of_finiteRelation hP hK hθ hTr hν₁ hw hstab hrel hint'
  funext h
  have e0 := congrFun h0 h
  have e1 : thetaInt ωB ν₁ 𝓕₁ Φ' h = thetaInt ωB ν₁ 𝓕₁ Φ₀ h := by
    simp only [thetaInt, hlin, _root_.Pi.zero_apply] at e0 ⊢
    rw [MeasureTheory.integral_sub (hint h) (hmod h).1] at e0
    exact sub_eq_zero.1 e0
  rw [_root_.Pi.smul_apply, e1,
    GlobalTheory.SquareAgree.thetaInt_eq_modelI D W X _ _ _ Γ.M 1 hO.JW ν 𝓕 ωA om (GlobalTheory.SquareAgree.kapX X e hO.JX) _ Φ hO.measW hO.domW
      (hO.theta_eq_A hD) h,
    GlobalTheory.SquareAgree.thetaInt_eq_modelI D W₁ X _ _ _ Γ.M' (-1) hO.JW₁ ν₁ 𝓕₁ ωB om' (GlobalTheory.SquareAgree.kapX X e hO.JX) Φ₀D Φ₀
      hO.measW₁ hO.domW₁ (hO.theta_eq_B hD0) h,
    hc _ _ hm (GlobalTheory.SquareAgree.kapX X e hO.JX h), smul_eq_mul]
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HasDerivAtLargeParameterThetaIntegral
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
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.ChainFr MeasureTheory
noncomputable section
namespace GlobalTheory.ConvThetaNe
open GlobalTheory.SquareAgree GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
section Over
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {W W₁ X : HSp D} {A : Fr W} {A₁ : Fr W₁} {B : Fr X}
  {α β : (AE D)ˣ →* Circle} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {ν₁ : Measure (GA D W₁)} {𝓕₁ : Set (GA D W₁)}
  {ωA : WRep W X} {ωB : WRep W₁ X} {e : Fin X.rank ≃ Fin (W.rank + W₁.rank)}
  {Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank}
  {Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W}
  {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W}
  {cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X}
  {cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X}
theorem hasDerivAt_large_parameter_theta_integral (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hθ : IsInfFam θ)
    (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB) (hT : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om')
    (hC : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F _, Γ.M.Conv om Φ) {τ : D.what₂.Tau} {Y : Matrix (Fin X.rank) (Fin X.rank) ℂ}
    (hY : Y ∈ lieAt X τ) {Φ Φ' : WO W X → ℂ} (hΦ : Φ ∈ algF ψ θ true A B) (hΦ' : Φ' ∈ algF ψ θ true A B)
    (hd : IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ') (h : GA D X) :
    HasDerivAt (fun t : ℝ => thetaInt ωA ν 𝓕 Φ (h * oneP θ X τ Y t)) (thetaInt ωA ν 𝓕 Φ' h) 0 := by
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hO.JX
  obtain ⟨δ, hδ⟩ := GlobalTheory.OscLie.exists_lie_deriv_pol Bs Γ Xc om om' hT γ hγ
  obtain ⟨ΦD, hΦD, hD⟩ := hO.algA Φ hΦ
  obtain ⟨Φ'D, -, hD'⟩ := hO.algA Φ' hΦ'
  have hPD : ΦD ∈ GlobalTheory.ThK.PolData Bs Γ.M := by
    refine Submodule.span_mono ?_ hΦD
    rintro _ ⟨f, φ, h1, h2, h3, rfl⟩
    exact ⟨f, h1, φ, h2, h3, rfl⟩
  obtain ⟨T, m, f, φ, hf, rfl⟩ := GlobalTheory.ThK.CycGen.exists_decOn_some Γ.M ΦD hPD
  have e1 := _root_.GlobalTheory.SquareAgree.DatA.polarization_datum_lie_derivative hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hT τ Y γ
    hγt hγ Φ Φ' hd T m f (fun i => δ (f i)) φ hf (fun i => (hδ _ (hf i).1).2) hD Φ'D hD'
  obtain ⟨l, hla, hl⟩ := GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral Γ.M Bs.ψ _ _ om hT.weil hC
  obtain ⟨Φ₁, -, hp, hI⟩ := _root_.GlobalTheory.ThetaIntegralLine.thetaIntegral_line_hasDerivAt hP Γ.M Bs.ψ _ _ om hT.base.cm hT.base.std hT.weil hC
    (fun g hg x => by
      obtain ⟨L, hL⟩ := hT.weil.isUSplitting.adm (1, x) l hla g hg
      refine L.continuous.congr fun u => ?_
      rw [GlobalTheory.BigNZ.I_eq_l hT hl (Submodule.subset_span ⟨u, g, hg, rfl⟩), ← hL u]
      rfl) hγ hD.1
  have hM := hT.geo.hM
  have hrest : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑(f i)) (GlobalTheory.EvZeroInf.finPart (φ i)) := fun i =>
    ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz, by
      rw [← GlobalTheory.EvZeroInf.pure_eq_tens]
      exact (GlobalTheory.BigNZ.IsFinPart.fam (M := Γ.M) (T := T) (hf i).2).mem hM _⟩
  have e2 : Φ₁ = Φ'D := by
    funext x
    refine (hp x).unique ?_
    rw [e1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.sum_apply, GlobalTheory.EvZeroInf.pure_eq_tens]
    exact HasDerivAt.fun_sum fun i _ => (hδ _ (hf i).1).2 _ (hrest i) x
  have := hI (kapX X e hO.JX h)
  rw [e2] at this
  simp only [int_eq hO hD, int_eq hO hD', GlobalTheory.KapXLine.kapX_mul, ← hγt]
  exact this
end Over
theorem convergent_theta_integral_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
  ∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∀ Φ' ∈ algF ψ θ false A₁ B, (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ') 𝓕₁ ν₁) → p' Φ' ≠ 0 → thetaInt ωB ν₁ 𝓕₁ Φ' ≠ 0 := by
  intro hP hK hL D ψ θ hψ hθ W W₁ X A A₁ B α β hT ν₁ 𝓕₁ hν₁ ωA ωB Pm rf rl p p' hm Φ' hΦ' hint' hp' h0'
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Ker.HypModel.exists_haar_fundDom D W
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ :=
    _root_.GlobalTheory.SquareAgree.exists_isOver D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hm.weilA hm.weilB
  have hC := (hK.1 _ _ _ Bs _ _ Γ Xc om om' hTD).1.1
  obtain ⟨c, -, hc⟩ := _root_.GlobalTheory.T.thetaIntegrals_agree_of_convergence hP hK hL D ψ θ hψ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm
  set S := algF ψ θ true A B with hS
  have hint : ∀ Φ ∈ S, ∀ h, IntegrableOn (fun g => thetaKO ωA g h Φ) 𝓕 ν := fun Φ hΦ h => integrable_big hO hC hΦ h
  have tr : ∀ (Φ : WO W X → ℂ) (h k : GA D X), thetaInt ωA ν 𝓕 (ωA (1, k) Φ) h = thetaInt ωA ν 𝓕 Φ (h * k) := by
    intro Φ h k
    simp only [thetaInt, thetaKO, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have tadd : ∀ Φ ∈ S, ∀ Ψ ∈ S, thetaInt ωA ν 𝓕 (Φ + Ψ) = thetaInt ωA ν 𝓕 Φ + thetaInt ωA ν 𝓕 Ψ := by
    intro Φ hΦ Ψ hΨ; funext h
    have e : (fun g => thetaKO ωA g h (Φ + Ψ)) = fun g => thetaKO ωA g h Φ + thetaKO ωA g h Ψ := by
      funext g; simp [thetaKO, map_add (f := _)]
    simp only [thetaInt, Pi.add_apply]
    rw [e]
    exact integral_add (hint Φ hΦ h) (hint Ψ hΨ h)
  have tsmul : ∀ (s : ℂ) Φ, thetaInt ωA ν 𝓕 (s • Φ) = s • thetaInt ωA ν 𝓕 Φ := by
    intro s Φ; funext h
    have e : (fun g => thetaKO ωA g h (s • Φ)) = fun g => s * thetaKO ωA g h Φ := by
      funext g; simp [thetaKO, map_smul]
    simp only [thetaInt, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact integral_const_mul s _
  let K : Submodule ℂ (WO W X → ℂ) :=
    { carrier := {Φ | Φ ∈ S ∧ thetaInt ωA ν 𝓕 Φ = 0}
      add_mem' := fun {a b} ha hb => ⟨S.add_mem ha.1 hb.1, by rw [tadd a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨S.zero_mem, by funext h; simp [thetaInt, thetaKO]⟩
      smul_mem' := fun s a ha => ⟨S.smul_mem s ha.1, by rw [tsmul, ha.2, smul_zero]⟩ }
  have kill : ∀ Ψ ∈ S, p Ψ = 0 → thetaInt ωA ν 𝓕 Ψ = 0 := fun Ψ hΨ h0 => by
    rw [hc Ψ hΨ 0 (zero_mem _) (fun h => by simp [thetaKO]) (by rw [h0, map_zero])]
    funext h; simp [thetaInt, thetaKO]
  have stf : ∀ g ∈ GfC X, ∀ x ∈ K.map p, rf g x ∈ K.map p := by
    rintro g hg _ ⟨Ψ, ⟨hΨS, hΨ0⟩, rfl⟩
    refine ⟨ωA (1, g) Ψ, ⟨hm.mapA.stabX.1 g hg Ψ hΨS, ?_⟩, hm.mapA.eqf g hg Ψ hΨS⟩
    funext h
    rw [tr, hΨ0]
    rfl
  have stl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ K.map p, rl τ Y x ∈ K.map p := by
    rintro τ Y hY _ ⟨Ψ, ⟨hΨS, hΨ0⟩, rfl⟩
    obtain ⟨Ψ', hΨ'S, hder⟩ := hm.mapA.stabX.2 τ Y hY Ψ hΨS
    refine ⟨Ψ', ⟨hΨ'S, funext fun h => ?_⟩, hm.mapA.eql τ Y hY Ψ hΨS Ψ' hΨ'S hder⟩
    have h1 := _root_.GlobalTheory.ConvThetaNe.hasDerivAt_large_parameter_theta_integral hP hθ hO hTD hC hY hΨS hΨ'S hder h
    rw [hΨ0] at h1
    exact h1.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  rcases hm.irred.2 (K.map p) stf stl with hbot | htop
  · obtain ⟨Φ, hΦ, hpΦ⟩ : p' Φ' ∈ S.map p := hm.mapA.onto ▸ Submodule.mem_top
    have h1 : p Φ ∈ K.map p := ⟨Φ, ⟨hΦ, by rw [hc Φ hΦ Φ' hΦ' hint' hpΦ, h0', smul_zero]⟩, rfl⟩
    rw [hbot, Submodule.mem_bot, hpΦ] at h1
    exact hp' h1
  · obtain ⟨Φ, hΦ, hne⟩ := exists_big_ne hK hL hO hTD
    obtain ⟨Ψ, ⟨hΨS, hΨ0⟩, hΨp⟩ : p Φ ∈ K.map p := by rw [htop]; exact Submodule.mem_top
    have h1 := tadd _ (S.sub_mem hΦ hΨS) Ψ hΨS
    rw [sub_add_cancel, kill _ (S.sub_mem hΦ hΨS) (by rw [map_sub, hΨp, sub_self]), hΨ0, add_zero] at h1
    exact hne h1
end GlobalTheory.ConvThetaNe
end
end
end

