module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0534
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0031
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0033

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspAverageKFiniteDecomposition
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
noncomputable section
namespace GlobalTheory.CuspKFinDecomp
theorem cusp_average_k_finite_decomposition : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (U : Subgroup (GA D N.V)), IsOpen (U : Set (GA D N.V)) → (∀ k ∈ U, k ∈ GfC N.V → ∀ g, φ (g * k) = φ g) → ∀ (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ), (∀ τ, GlobalTheory.TypeSum.KFinFun (N.M.ε τ) (e τ)) → ∀ (l : List D.what₂.Tau), (∀ τ, τ ∈ l) → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → SmT N.M), (∀ j, F j ∈ N.Cusp θ) ∧ (∀ j, ∀ k ∈ U, k ∈ GfC N.V → ∀ g, F j (v j) (g * k) = F j (v j) g) ∧ GlobalTheory.CuspApproxAll.avgList θ N e l φ = ∑ j, F j (v j) := by
  intro D θ hθ hP N φ hφ U hU hlev e he l hl
  have key : ∀ l' : List D.what₂.Tau, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N (GlobalTheory.CuspApproxAll.avgList θ N e l' φ) ∧
      (∀ k ∈ U, k ∈ GfC N.V → ∀ g, GlobalTheory.CuspApproxAll.avgList θ N e l' φ (g * k) = GlobalTheory.CuspApproxAll.avgList θ N e l' φ g) ∧
      ∀ τ ∈ l', GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.CuspApproxAll.avgList θ N e l' φ) := by
    intro l'
    induction l' with
    | nil => exact ⟨hφ, hlev, fun τ h => absurd h List.not_mem_nil⟩
    | cons τ l' ih =>
      rw [GlobalTheory.CuspApproxAll.avgList_cons]
      refine ⟨_root_.GlobalTheory.T.averaging_preserves_cusp_type D θ hθ hP N _ ih.1 τ (e τ) (he τ), avg_lev D θ hθ N _ U ih.2.1 τ (e τ), fun τ' hτ' => ?_⟩
      rcases List.mem_cons.1 hτ' with rfl | h
      · exact _root_.GlobalTheory.CuspKFin.kFinAt_avg D θ hθ N _ ih.1.1 τ' (e τ') (he τ')
      · exact _root_.GlobalTheory.CuspKFin.kFinAt_avg_of_kFinAt D θ hθ N _ ih.1.1 τ' τ (e τ) (he τ) (ih.2.2 τ' h)
  obtain ⟨hc, hlv, hk⟩ := key l
  obtain ⟨-, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D N.V
    (Measure.haar : Measure (GA D N.V)) inferInstance
  obtain ⟨n, T₀, u, hT₀, hsum⟩ := _root_.GlobalTheory.T.cuspForm_decomposes_into_kFinite_components D θ hθ hP N _ hc U hU hlv (fun τ => hk τ (hl τ))
    (Measure.haar : Measure (GA D N.V)) 𝓕 inferInstance h𝓕
  have hext := fun j => (GlobalTheory.GKExt.extExists hP.harishChandraModules hP.casselmanWallach D θ hθ N.V N.S N.M
    {k | k ∈ U ∧ k ∈ GfC N.V} 1 (Measure.haar : Measure (GA D N.V)) 𝓕 inferInstance h𝓕 (T₀ j) (hT₀ j)).exists
  choose T hT using hext
  have hsm : ∀ τ (w : N.M.H τ), w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → w ∈ N.M.sm τ := fun τ w hw =>
    (_root_.GlobalTheory.SmVecModel.mem_sm_iff N.M τ w).2 ((GlobalTheory.TypeSum.std_of_isDS hP.harishChandraModules (N.M.ds τ)).2.2.1 w hw)
  refine ⟨n, fun j => PiTensorProduct.lift (T j),
    fun j => PiTensorProduct.tprod ℂ (fun τ => (⟨(u j τ : N.M.H τ), hsm τ _ (u j τ).2⟩ : N.M.sm τ)),
    fun j => ?_, fun j k hk hkf g => ?_, ?_⟩
  · exact N.multT_le_cusp θ {k | k ∈ U ∧ k ∈ GfC N.V} 1
      (Submodule.mem_map_of_mem (Submodule.subset_span (hT j).1))
  · rw [PiTensorProduct.lift.tprod]
    have := (hT j).1.lev (fun τ => (⟨(u j τ : N.M.H τ), hsm τ _ (u j τ).2⟩ : N.M.sm τ)) k ⟨hk, hkf⟩ g
    simpa using this
  · rw [hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PiTensorProduct.lift.tprod]
    exact ((hT j).2 _ (u j) fun τ => rfl).symm
end GlobalTheory.CuspKFinDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_cusp_average_k_finite_decomposition : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (U : Subgroup (GA D N.V)), IsOpen (U : Set (GA D N.V)) → (∀ k ∈ U, k ∈ GfC N.V → ∀ g, φ (g * k) = φ g) → ∀ (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ), (∀ τ, GlobalTheory.TypeSum.KFinFun (N.M.ε τ) (e τ)) → ∀ (l : List D.what₂.Tau), (∀ τ, τ ∈ l) → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → SmT N.M), (∀ j, F j ∈ N.Cusp θ) ∧ (∀ j, ∀ k ∈ U, k ∈ GfC N.V → ∀ g, F j (v j) (g * k) = F j (v j) g) ∧ GlobalTheory.CuspApproxAll.avgList θ N e l φ = ∑ j, F j (v j) := by
  first | exact @_root_.GlobalTheory.CuspKFinDecomp.cusp_average_k_finite_decomposition | exact _root_.GlobalTheory.CuspKFinDecomp.cusp_average_k_finite_decomposition | (intros; apply _root_.GlobalTheory.CuspKFinDecomp.cusp_average_k_finite_decomposition <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilAlgebraicSubspaceKInftyStable
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.CompactStableD
theorem algebraic_vectors_kInfty_stable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.V Bs.emb, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, om (k, 1) ΦD ∈ algD Γ.M Bs.ψ Bs.emb := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _ _ _ hT _ _ _ _ _ _ k hk ΦD hΦ
  obtain ⟨Dop, hDP, hD⟩ := (_root_.GlobalTheory.T.dualPair_preserves_polarization hP _ _ D.sp.cm.sig Bs _ _ Γ.V Γ.W Γ.M Xc.β (Xc.β / Xc.α) om _ _ _ _
    (GlobalTheory.ThK.RealUniq.isPair_V hT)).2.1 k hk
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hSB, hcof, rfl⟩ := hx
    have hstd : ∀ᶠ v in Filter.cofinite,
        φ v = Set.indicator {x : Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v |
          ∀ j, x j ∈ v.adicCompletionIntegers D.host.F} 1 := by
      filter_upwards [hcof, hT.geo.hM.std] with v h1 h2
      rw [h1, h2]
    have key : om (k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dop f) φ :=
      (hD _ hf _).2 rfl _ (GlobalTheory.ThK.EvUniqInf.rest_pure _ _ hSB hstd)
    rw [key]
    exact Submodule.subset_span ⟨Dop f, φ, hDP _ hf, hSB, hcof, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
end GlobalTheory.SquareAgree.CompactStableD
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_algebraic_subspace_kInfty_stable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.V Bs.emb, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, om (k, 1) ΦD ∈ algD Γ.M Bs.ψ Bs.emb := by
  first | exact @_root_.GlobalTheory.SquareAgree.CompactStableD.algebraic_vectors_kInfty_stable | exact _root_.GlobalTheory.SquareAgree.CompactStableD.algebraic_vectors_kInfty_stable | (intros; apply _root_.GlobalTheory.SquareAgree.CompactStableD.algebraic_vectors_kInfty_stable <;> assumption)
end
end

