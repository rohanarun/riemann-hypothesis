module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0539
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0030
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0038
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0555
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvergenceDownChain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0439
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0543
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0004
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0033
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0532

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.AdelicStabilizerLieKerPolarization
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.SquareAgree.StabLieAdelic
end GlobalTheory.SquareAgree.StabLieAdelic
open GlobalTheory.SquareAgree.StabLieAdelic in
theorem GlobalTheory.SquareAgree.StabLieAdelic.stabilizer_lie_adelic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N' : Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ), IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N' →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ N', ∀ Φ₀, IsDatum Γ.M' ψ cB ΦD Φ₀ →
    ∃ ΨD ∈ N', ∃ Φ₁ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB ΨD Φ₁ ∧ IsDer θ X (fun h => ωB (1, h)) τ Y Φ₀ Φ₁ := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ _ hO hT Pi rf rl p p' _ N' hN τ Y hY
    ΦD hΦD Φ₀ hD
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hO.JX
  obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.T.twist_lie_derivative_model hP Bs Γ Xc om om' hT γ hγ
  obtain ⟨m, f, φ, hf, rfl⟩ := exists_sum_pure Γ.M' Bs.ψ Bs.emb (hN.le hΦD)
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite,
      φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers D.host.F} 1 :=
    fun i => ((hf i).2.2.and hT.geo.hM'.std).mono fun v h => h.1.trans h.2
  have hΨalg : (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ (f i)) (φ i)) ∈ algD Γ.M' Bs.ψ Bs.emb :=
    Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span ⟨δ (f i), φ i, (hδ _ (hf i).1).1, (hf i).2.1, (hf i).2.2, rfl⟩
  have hder : ∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x)
      ((∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ (f i)) (φ i)) x) 0 := by
    intro x
    have e1 : (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x) =
        fun t => ∑ i, om' (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x := by
      funext t
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_apply]
    rw [e1, Finset.sum_apply]
    exact HasDerivAt.fun_sum fun i _ =>
      (hδ _ (hf i).1).2 _ (GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hf i).2.1 (hstd i)) x
  have hΨN := hN.stabLie γ hγ _ hΦD _ hΨalg hder
  obtain ⟨Φ₁, hΦ₁, hD₁⟩ := hO.algB' _ hΨalg
  refine ⟨_, hΨN, Φ₁, hΦ₁, hD₁, ?_⟩
  intro z
  obtain ⟨u, rfl⟩ := cB.surjective z
  have hs : IsStd ψ := hO.psi ▸ hT.base.std
  have hg : Γ.M'.IsGood ψ := hO.psi ▸ hT.geo.hM'
  have hw : Γ.M'.IsWeil ψ Xc.α (Xc.α / Xc.β) om' := hO.psi ▸ hT.weil'
  have key := _root_.GlobalTheory.T.theta_sum_differentiable_along_line hP Γ.M' ψ Xc.α (Xc.α / Xc.β) om' hT.base.cm hs hg hw γ hγ m f (fun i => δ (f i)) φ
    (fun i => (hf i).2) (fun i => (hδ _ (hf i).1).2) u
  have e2 : (fun t : ℝ => ωB (1, oneP θ X τ Y t) Φ₀ (cB u)) = fun t : ℝ =>
      GlobalTheory.WeilM.thetaSum D.host.F (Γ.M'.co.rho ψ u (om' (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))) := by
    funext t
    have h1 := (hO.weilB _ Φ₀ hD 1 (oneP θ X τ Y t)).2 u
    rw [conjU_one, ← hγt t] at h1
    exact h1.symm
  rw [e2, ← hD₁.2 u]
  exact key
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
theorem _root_.GlobalTheory.T.adelic_stabilizer_lie_ker_polarization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N' : Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ), IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N' →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ N', ∀ Φ₀, IsDatum Γ.M' ψ cB ΦD Φ₀ →
    ∃ ΨD ∈ N', ∃ Φ₁ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB ΨD Φ₁ ∧ IsDer θ X (fun h => ωB (1, h)) τ Y Φ₀ Φ₁ := by
  first | exact @_root_.GlobalTheory.SquareAgree.StabLieAdelic.stabilizer_lie_adelic | exact _root_.GlobalTheory.SquareAgree.StabLieAdelic.stabilizer_lie_adelic | (intros; apply _root_.GlobalTheory.SquareAgree.StabLieAdelic.stabilizer_lie_adelic <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspFormsApproximatedByThetaLifts
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.CuspApproxX
open GlobalTheory.Grow GlobalTheory.Size
end GlobalTheory.CuspApproxX
namespace GlobalTheory.CuspApproxX
open GlobalTheory.Grow GlobalTheory.Size
theorem cusp_form_approx_by_lift (happrox : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → ∀ (a : ℕ) (δ : ℝ), 0 < δ → ∃ (n : ℕ) (T : Fin n → Formalism.IndefR.Mult.MMap (G.V i j).M) (v : Fin n → (G.V i j).M.Vec), (∀ l, Formalism.IndefR.Mult.IsMultMap R.θ (G.V i j).M ∅ 1 (T l)) ∧ ∀ g, ‖φ g - ∑ l, T l (v l) g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a ≤ δ) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → (G.V i j).Maps) (v : Fin n → SmT (G.V i j).M), (∀ l, F l ∈ (G.V i j).Cusp R.θ) ∧ (∀ l h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * F l (v l) g) (G.meas t i j).fd (G.meas t i j).ν) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * F l (v l) g ∂(G.meas t i j).ν‖ < ε := by
  intro _hL hP D _hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ hint C hC ε hε
  have hM := GlobalTheory.PairLift.haar_vert hRB hG t hi.le hj
  have : BorelSpace (GA D (G.V i j).V) := ⟨rfl⟩
  have hw := (hG.arrows.X i j hi hj).weil
  obtain ⟨K, a, hK⟩ := thetaKO_le_quotHeight hRB.inf hw hΦ
    (hC.image (GlobalTheory.Grid.continuous_ofSgn_symm true (G.V (i + 1) j).V))
  have hK' : ∀ h ∈ C, ∀ g, ‖thetaKO (G.X i j).ω h g Φ‖ ≤ |K| * quotHeight (G.V i j).V g ^ a := by
    intro h hh g
    have key := hK _ ⟨h, hh, rfl⟩ g
    refine le_trans (le_of_eq ?_) (key.trans (mul_le_mul_of_nonneg_right (le_abs_self K)
      (pow_pos (quotHeight_pos _ g) a).le))
    congr 1
  have hI : ∀ ψ' : GA D (G.V i j).V → ℂ, RapidDec (G.V i j).V ψ' → ∀ h,
      IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * ψ' g) (G.meas t i j).fd (G.meas t i j).ν := by
    intro ψ' hr h
    have key := GlobalTheory.Chain.LiftConv.integrableOn_of_rapidDec (GlobalTheory.KernelSeminorm.thetaGrowth D) hRB.inf hw hΦ hM.1
      hM.2 hr ((GlobalTheory.Grid.ofSgn true _).symm h)
    convert key using 3 with g
    simp only [thetaKO, GlobalTheory.Grid.WRep.toSgn, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply,
      MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, MonoidHom.id_apply]
  have hfin := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hM.1 hM.2
  set vol := (G.meas t i j).ν.real (G.meas t i j).fd with hvol
  have hv0 : 0 ≤ vol := measureReal_nonneg
  set δ := ε / (2 * ((|K| + 1) * (vol + 1))) with hδ
  have hpos : 0 < 2 * ((|K| + 1) * (vol + 1)) := by positivity
  have hδ0 : 0 < δ := div_pos hε hpos
  obtain ⟨n, Tm, v, hT, hap⟩ := happrox hP D G₀ Pl0 T A Ks R G hRB hG i j hi.le hj φ hφ a δ hδ0
  have hval : ∀ l, (PiTensorProduct.lift (Tm l)) (PiTensorProduct.tprod ℂ (v l)) = Tm l (v l) := fun l =>
    PiTensorProduct.lift.tprod _
  have hR : ∀ l, RapidDec (G.V i j).V (Tm l (v l)) := fun l =>
    rapidDec_of_cuspForm hP.cuspRapidDecay hRB.inf ((hT l).aut (v l)) ((hT l).cusp (v l))
  refine ⟨n, fun l => PiTensorProduct.lift (Tm l), fun l => PiTensorProduct.tprod ℂ (v l), fun l => ?_, fun l h => ?_,
    fun h hh => ?_⟩
  · rw [Formalism.IndefR.Mult.mem_multT, LinearEquiv.symm_apply_apply]
    exact Submodule.subset_span (hT l)
  · rw [hval]; exact hI _ (hR l) h
  · simp only [hval]
    have hIl : ∀ l, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * Tm l (v l) g) (G.meas t i j).fd
        (G.meas t i j).ν := fun l => hI _ (hR l) h
    rw [← integral_finsetSum _ fun l _ => hIl l, ← integral_sub (hint h) (integrable_finsetSum _ fun l _ => hIl l)]
    have hb : ∀ g ∈ (G.meas t i j).fd, ‖thetaKO (G.X i j).ω h g Φ * φ g -
        ∑ l, thetaKO (G.X i j).ω h g Φ * Tm l (v l) g‖ ≤ |K| * δ := by
      intro g _
      rw [← Finset.mul_sum, ← mul_sub, norm_mul]
      have h1 := hK' h hh g
      have h2 := hap g
      have hq := (pow_pos (quotHeight_pos (G.V i j).V g) a).le
      calc ‖thetaKO (G.X i j).ω h g Φ‖ * ‖φ g - ∑ l, Tm l (v l) g‖
          ≤ |K| * quotHeight (G.V i j).V g ^ a * ‖φ g - ∑ l, Tm l (v l) g‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = |K| * (‖φ g - ∑ l, Tm l (v l) g‖ * quotHeight (G.V i j).V g ^ a) := by ring
        _ ≤ |K| * δ := mul_le_mul_of_nonneg_left h2 (abs_nonneg K)
    refine (norm_setIntegral_le_of_norm_le_const hfin hb).trans_lt ?_
    rw [← hvol]
    have e : |K| * δ * vol ≤ (|K| + 1) * (vol + 1) * δ := by
      have : |K| * vol ≤ (|K| + 1) * (vol + 1) := by nlinarith [abs_nonneg K]
      nlinarith
    have e2 : (|K| + 1) * (vol + 1) * δ = ε / 2 := by
      rw [hδ]; field_simp
    linarith
end GlobalTheory.CuspApproxX
namespace GlobalTheory.CuspApproxX
theorem cusp_form_approx_by_lift_of_type : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → (G.V i j).Maps) (v : Fin n → SmT (G.V i j).M), (∀ l, F l ∈ (G.V i j).Cusp R.θ) ∧ (∀ l h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * F l (v l) g) (G.meas t i j).fd (G.meas t i j).ν) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * F l (v l) g ∂(G.meas t i j).ν‖ < ε :=
  _root_.GlobalTheory.CuspApproxX.cusp_form_approx_by_lift _root_.GlobalTheory.T.pure_cusp_form_approx_of_twist
end GlobalTheory.CuspApproxX
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_forms_approximated_by_theta_lifts : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → (G.V i j).Maps) (v : Fin n → SmT (G.V i j).M), (∀ l, F l ∈ (G.V i j).Cusp R.θ) ∧ (∀ l h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * F l (v l) g) (G.meas t i j).fd (G.meas t i j).ν) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * F l (v l) g ∂(G.meas t i j).ν‖ < ε := by
  first | exact @_root_.GlobalTheory.CuspApproxX.cusp_form_approx_by_lift_of_type | exact _root_.GlobalTheory.CuspApproxX.cusp_form_approx_by_lift_of_type | (intros; apply _root_.GlobalTheory.CuspApproxX.cusp_form_approx_by_lift_of_type <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FlipSequenceStartColumn
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.FlipStart.Col
variable {D : D7}
variable {T : Type} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
end GlobalTheory.FlipStart.Col
open GlobalTheory.FlipStart GlobalTheory.FlipStart.Col in
theorem GlobalTheory.FlipStart.flipSequence_start_column : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)) (q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank), GlobalTheory.FlipStart.ChainVecs ch t f → GlobalTheory.FlipStart.ChainPols ch q → ∀ M : Vol ch.G, M.Is t → ∀ y : (R.HX t).H, PathConv ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) ∧ liftP ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) = ch.cv.lift t y := by
  intro _ _
  refine ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t f q hf hq M hM y
  have h := col_top hch.weil s.core.chain s.core.models hq hM y D.R.m rfl (fun j => ch.W.fock (.mu t 0 j) (f j) (q j))
    (fun j => ⟨fun h => ⟨f j, (hf j).1 h, rfl⟩, fun h => ⟨f j, (hf j).2 h, rfl⟩⟩) (formTop ch t y)
    (by unfold formTop; exact cast_fun_heq _ _)
  exact ⟨h.1, eq_of_heq h.2⟩
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flipSequence_column_succ : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)) (q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank), GlobalTheory.FlipStart.ChainVecs ch t f → GlobalTheory.FlipStart.ChainPols ch q → ∀ M : Vol ch.G, M.Is t → ∀ y : (R.HX t).H, PathConv ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) ∧ liftP ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) = ch.cv.lift t y := by
  first | exact @_root_.GlobalTheory.FlipStart.flipSequence_start_column | exact _root_.GlobalTheory.FlipStart.flipSequence_start_column | (intros; apply _root_.GlobalTheory.FlipStart.flipSequence_start_column <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FockVectorsKFinite
section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.FockKFin
theorem fock_space_kFinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ f ∈ M.Pol B.ψ B.emb, ∃ S : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), FiniteDimensional ℂ S ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ → f₁ ∈ S := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP f hf
  have hPA := _root_.GlobalTheory.T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨m, L, hD⟩ := GlobalTheory.T.heisenbergLine_derivative_finite_span F E σ n d X W M B.ψ hP.base.std
  choose! Dfun hDiff hDspan using hD
  have hK := hPA.2.1
  simp only [GlobalTheory.RealActs.OpOn] at hK
  choose! Tk hTpres hTacts using hK
  have hGP : ∀ f₀, M.IsGauss B.ψ B.emb f₀ → f₀ ∈ M.Pol B.ψ B.emb := fun f₀ h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have hclos : ∀ u, At (evI F) u → ∀ g ∈ M.Pol B.ψ B.emb, Dfun u g ∈ M.Pol B.ψ B.emb := fun u hu g hg =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu g (Submodule.mem_sInf.1 hg N hN) _ ((hDiff u hu g _).2 rfl)
  have hmin : ∀ N : Submodule ℂ (SInf F (Fin n × Fin d)), {f₀ | M.IsGauss B.ψ B.emb f₀} ⊆ N →
      (∀ u ∈ {u : Matrix (Fin n) (Fin d) (AE F E) | At (evI F) u}, ∀ g ∈ N, Dfun u g ∈ N) → M.Pol B.ψ B.emb ≤ N := by
    intro N hG hN
    refine sInf_le ⟨fun f₀ h => hG h, fun u hu g hg g₁ hg₁ => ?_⟩
    rw [(hDiff u hu g g₁).1 hg₁]
    exact hN u hu g hg
  have hAt : ∀ k : UA σ X.J, ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) (mat k * u) :=
    fun k u hu c hc => by rw [← Matrix.mul_smul, hu c hc, Matrix.mul_zero]
  obtain ⟨S, hS, hSk⟩ := _root_.GlobalTheory.exists_finiteDimensional_orbit_of_generated (SInf F (Fin n × Fin d)) (Matrix (Fin n) (Fin d) (AE F E))
    {k // k ∈ KInf σ X B.emb} {u | At (evI F) u} {f₀ | M.IsGauss B.ψ B.emb f₀} (M.Pol B.ψ B.emb) Dfun m L
    (fun k => Tk k.1) (fun k u => mat k.1 * u) (_root_.GlobalTheory.FockVac.span_finiteDimensional F E σ B n d X W M χX χW om r s r' s' hP)
    (fun u hu g => hDspan u hu g) (fun f₀ h => hGP f₀ h) (fun u hu g hg => hclos u hu g hg) hmin
    (fun k g hg => Submodule.subset_span
      (_root_.GlobalTheory.T.fock_vacuum_stabilized_is_gaussian hPr F E σ B n d X W M χX χW om r s r' s' hP k.1 k.2 g hg _
        ((hTacts k.1 k.2 g (hGP g hg) _).2 rfl)))
    (fun k u hu => hAt k.1 u hu)
    (fun k u hu g hg => (hDiff _ (hAt k.1 u hu) _ _).1
      (GlobalTheory.T.compactUnitary_moves_heisenbergDerivative F E σ B n d X W M χX χW om r s r' s' hP k.1 k.2 u hu g (Dfun u g) (Tk k.1 g)
        (Tk k.1 (Dfun u g)) ((hDiff u hu g _).2 rfl) ((hTacts k.1 k.2 g hg _).2 rfl)
        ((hTacts k.1 k.2 _ (hclos u hu g hg) _).2 rfl)))
    f hf
  exact ⟨S, hS, fun k hk f₁ hact => by rw [(hTacts k hk f hf f₁).1 hact]; exact hSk ⟨k, hk⟩⟩
end GlobalTheory.FockKFin
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_vectors_kFinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ f ∈ M.Pol B.ψ B.emb, ∃ S : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), FiniteDimensional ℂ S ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ → f₁ ∈ S := by
  first | exact @_root_.GlobalTheory.FockKFin.fock_space_kFinite | exact _root_.GlobalTheory.FockKFin.fock_space_kFinite | (intros; apply _root_.GlobalTheory.FockKFin.fock_space_kFinite <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.IsDatumDerivativeSecondFactorEqSumPure
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.SquareAgree.LieDat
theorem isDatum_derivative_second_factor_eq_sum_pure : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) (γ : Multiplicative ℝ →* UA D.sp.cm.sig Γ.W.J),
    (∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hO.JX (oneP θ X τ Y t)) → γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.W →
    ∀ (Φ Φ' : WO W₁ X → ℂ), IsDer θ X (fun h => ωB (1, h)) τ Y Φ Φ' →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F))) (m : ℕ) (f f₁ : Fin m → SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
    (∀ i, f i ∈ Γ.M'.Pol Bs.ψ Bs.emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ v ∉ T, φ i v = Γ.M'.vac v) →
    (∀ i, ActsD (evI D.host.F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
    IsDatum Γ.M' ψ cB (∑ i, pure (f i) (φ i)) Φ →
    ∀ Φ'D, IsDatum Γ.M' ψ cB Φ'D Φ' → Φ'D = ∑ i, pure (f₁ i) (φ i) := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hT τ Y γ hγ hL Φ Φ' hDer T m f f₁ φ hf hact hD Φ'D hΦ'D
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT.base.std
  have hM : Γ.M'.IsGood ψ := hO.psi ▸ hT.geo.hM'
  have hW : Γ.M'.IsWeil ψ Xc.α (Xc.α / Xc.β) om' := hO.psi ▸ hT.weil'
  have hev : ∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = Γ.M'.vac v := fun i =>
    ⟨(hf i).2.1, Filter.eventually_cofinite.2 ((T.finite_toSet).subset fun v hv => by
      by_contra h; exact hv ((hf i).2.2 v h))⟩
  have hval : ∀ (t : ℝ) u, GlobalTheory.WeilM.thetaSum D.host.F (Γ.M'.co.rho ψ u (om' (1, γ (Multiplicative.ofAdd t)) (∑ i, pure (f i) (φ i)))) =
      ωB (1, oneP θ X τ Y t) Φ (cB u) := by
    intro t u
    have h := (hO.weilB _ Φ hD 1 (oneP θ X τ Y t)).2 u
    rwa [GlobalTheory.LocWeilAct.conjU_one', ← hγ t] at h
  have hnew : IsDatum Γ.M' ψ cB (∑ i, pure (f₁ i) (φ i)) Φ' := by
    refine ⟨Submodule.sum_mem _ fun i _ => GlobalTheory.TensUniq.pure_mem_schA (f₁ i) (φ i) (hev i).1
      (((hev i).2.and hM.std).mono fun v hv => hv.1.trans hv.2), fun u => ?_⟩
    have h1 := _root_.GlobalTheory.T.theta_sum_differentiable_along_line hP Γ.M' ψ Xc.α (Xc.α / Xc.β) om' hT.base.cm hstd hM hW γ hL m f f₁ φ hev hact u
    have h2 : HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M'.co.rho ψ u (om' (1, γ (Multiplicative.ofAdd t)) (∑ i, pure (f i) (φ i))))) (Φ' (cB u)) 0 := by
      simp only [hval]
      exact hDer (cB u)
    exact h1.unique h2
  exact GlobalTheory.T.schwartzDatum_eq_of_thetaFunction_eq Γ.M' ψ hstd cB Φ'D _ Φ' hΦ'D hnew
end GlobalTheory.SquareAgree.LieDat
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_polarization_datum_derivative_second : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) (γ : Multiplicative ℝ →* UA D.sp.cm.sig Γ.W.J),
    (∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hO.JX (oneP θ X τ Y t)) → γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.W →
    ∀ (Φ Φ' : WO W₁ X → ℂ), IsDer θ X (fun h => ωB (1, h)) τ Y Φ Φ' →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F))) (m : ℕ) (f f₁ : Fin m → SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
    (∀ i, f i ∈ Γ.M'.Pol Bs.ψ Bs.emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ v ∉ T, φ i v = Γ.M'.vac v) →
    (∀ i, ActsD (evI D.host.F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
    IsDatum Γ.M' ψ cB (∑ i, pure (f i) (φ i)) Φ →
    ∀ Φ'D, IsDatum Γ.M' ψ cB Φ'D Φ' → Φ'D = ∑ i, pure (f₁ i) (φ i) := by
  first | exact @_root_.GlobalTheory.SquareAgree.LieDat.isDatum_derivative_second_factor_eq_sum_pure | exact _root_.GlobalTheory.SquareAgree.LieDat.isDatum_derivative_second_factor_eq_sum_pure | (intros; apply _root_.GlobalTheory.SquareAgree.LieDat.isDatum_derivative_second_factor_eq_sum_pure <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumPureLineDifferentiable
section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.ThetaLinePureW
theorem hasDerivAt_thetaSum_pure_weight : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
    ∀ φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) → ∀ u : Matrix (Fin a) (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ))))
      (GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ))) 0 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' h γ hγ f _ f₁ hD φ hφ hv u
  have H := _root_.GlobalTheory.T.theta_sum_differentiable_along_line hP G.M B.ψ X.β (X.β / X.α) om h.base.cm h.base.std h.geo.hM h.weil γ hγ 1 (fun _ => f) (fun _ => f₁)
    (fun _ => φ) (fun _ => ⟨hφ, hv⟩) (fun _ => hD) u
  simpa using H
end GlobalTheory.ThetaLinePureW
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSum_pure_line_differentiable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
    ∀ φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) → ∀ u : Matrix (Fin a) (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ))))
      (GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ))) 0 := by
  first | exact @_root_.GlobalTheory.ThetaLinePureW.hasDerivAt_thetaSum_pure_weight | exact _root_.GlobalTheory.ThetaLinePureW.hasDerivAt_thetaSum_pure_weight | (intros; apply _root_.GlobalTheory.ThetaLinePureW.hasDerivAt_thetaSum_pure_weight <;> assumption)
end
end

