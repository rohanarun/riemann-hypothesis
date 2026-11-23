module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatContrIntIndicator
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0366
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiAtTransport
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0351
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AconvSingleList
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TriStep.IdempotentCombination

variable {D : D7}

section Idem
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cA_idem (q : GlobalTheory.FinPl.SplitPt D k) : cA D (q.e + cA D q.e) = q.e + cA D q.e := by
  obtain ⟨ε, -, h4⟩ := q.above
  rw [h4]
  show cA D (ε ⊗ₜ[D.host.F] (1 : D.host.E)) = ε ⊗ₜ[D.host.F] (1 : D.host.E)
  simp [cA, sigR]

theorem idem_sq (q : GlobalTheory.FinPl.SplitPt D k) : (q.e + cA D q.e) * (q.e + cA D q.e) = q.e + cA D q.e := by
  have h1 := q.split.1
  have h2 := q.split.2.1
  have h3 : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, h1]
  linear_combination h1 + 2 * h2 + h3

end Idem

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem aconv_cons {G : Type} [AddMonoid G] (e : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    aconv (e :: l) = ∑ g ∈ e.support, ∑ h ∈ (aconv l).support, Finsupp.single (g + h) (e g * aconv l h) := rfl

theorem comb_aconv_cons (e : WO S T →₀ ℂ) (l : List (WO S T →₀ ℂ))
    (h : ∀ x ∈ e.support, ∀ y ∈ (aconv l).support, symplO S T x y = 0) (f : WO S T → ℂ) :
    comb ψ S T (aconv (e :: l)) f = comb ψ S T e (comb ψ S T (aconv l) f) := by
  rw [GlobalTheory.HeisComb.comb_comb, GlobalTheory.HeisComb.comb_eq_sum, aconv_cons]
  rw [← Finsupp.sum_finsetSum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Finsupp.sum_finsetSum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h0 : symplOH S T x y = 0 := by
    unfold symplOH
    rw [h x hx y hy, mul_zero]
  rw [Finsupp.sum_single_index (zero_smul ℂ (heisO ψ S T (x + y) f)), GlobalTheory.WeilVacMove.heisO_heisO, h0, AddChar.map_zero_eq_one,
    one_smul]

end GlobalTheory.TriStep.IdempotentCombination

namespace GlobalTheory.TriStep

theorem aconv_single_list {G : Type} [AddMonoid G] (d : G →₀ ℂ) : aconv [d] = d := by
  show d.sum (fun g a => (Finsupp.single 0 1 : G →₀ ℂ).sum fun h b => Finsupp.single (g + h) (a * b)) = d
  calc d.sum (fun g a => (Finsupp.single 0 1 : G →₀ ℂ).sum fun h b => Finsupp.single (g + h) (a * b))
        = d.sum (fun g a => Finsupp.single g a) := by
          congr 1; funext g a; rw [Finsupp.sum_single_index (by simp), add_zero, mul_one]
    _ = d := Finsupp.sum_single d

theorem comb_aconv_away {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) {A T : HSp D}
    (c d : WO A T →₀ ℂ) (hc : Q.Away c)
    (hd : ∀ u ∈ d.support, IsHalf ((ofSplit Q.q).e + cA D (ofSplit Q.q).e) u) (g : WO A T → ℂ) :
    comb ψ A T (aconv [c, d]) g = comb ψ A T c (comb ψ A T d g) := by
  rw [GlobalTheory.TriStep.IdempotentCombination.comb_aconv_cons c [d] ?_ g, aconv_single_list]
  intro x hx y hy
  rw [aconv_single_list] at hy
  have hy' : IsHalf (Q.q.e + cA D Q.q.e) y := hd y hy
  refine GlobalTheory.HeisComb.symplO_half A T (1 - (Q.q.e + cA D Q.q.e)) (Q.q.e + cA D Q.q.e) x y ?_ ?_ (hc x hx) hy'
  · rw [map_sub, map_one, GlobalTheory.TriStep.IdempotentCombination.cA_idem]
  · rw [sub_mul, one_mul, GlobalTheory.TriStep.IdempotentCombination.idem_sq, sub_self]

theorem valK_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (T₁ : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.B.V S.J.W → ℂ)) (T₂ : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.J.W S.B'.V → ℂ)), (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ → ∀ (U₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) →ₗ[ℂ] (WO S.B.V₀ S.J.W₀ → ℂ)) (U₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) →ₗ[ℂ] (WO S.J.W₀ S.B'.V₀ → ℂ)), (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) Φ.1 → flatBF S.s₁ (T₁ Φ) = U₁ Ψ) → (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) Φ.1 → flatFB S.s₂ (T₂ Φ) = U₂ Ψ) → (∀ Ψ₁ Ψ₂, ∃ Ξ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k), Ξ.1 = GlobalTheory.LocFlat.contr Q.ψk Q.ν Ψ₁.1 Ψ₂.1 ∧ GlobalTheory.Unf.contr S.l S.J.W₀ S.vL (U₁ Ψ₁) (U₂ Ψ₂) = Λ Ξ) → ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ : SB (Matrix Q.n₂ Q.n₁ Q.k)) d₁ d₂, (ofSplit Q.q).IsCombAt ψ Q.F.F₀ Q.F.F₁ d₁ Ξ₁.1 → (ofSplit Q.q).IsCombAt ψ Q.F.F₁ Q.F.F₂ d₂ Ξ₂.1 → ∀ O₁ O₂, IsOne O₁ → IsOne O₂ → ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f = S.val (aconv [c₁, d₁]) (aconv [c₂, d₂]) (T₁ O₁) (T₂ O₂) φ f 1 1 1 := by
  intro D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ T₁ T₂ hT₁ hT₂ U₁ U₂ hU₁ hU₂ hcon Ξ₁ Ξ₂ d₁ d₂ hd₁ hd₂ O₁ O₂ hO₁ hO₂ f hf
  have hσc : Q.c = 2 * σ := by have := Q.F.bes.1; omega
  have hun := GlobalTheory.LocFlat.flat_contr_intIndicator Q.k Q.ψk Q.ν Q.cond Q.unitVol
  let P₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  let P₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  let R₁ : SB (Matrix Q.n₁ Q.n₀ Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  let R₂ : SB (Matrix Q.n₂ Q.n₁ Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  have e₁ : flatBF S.s₁ (T₁ O₁) = U₁ P₁ := hU₁ O₁ P₁ (by
    rw [hO₁, (hun Q.n₁ Q.n₀ Q.n₀ (Q.c + 1 + 1) (σ + 1 + 1)).1, if_neg (by omega)])
  have e₂ : flatFB S.s₂ (T₂ O₂) = U₂ P₂ := hU₂ O₂ P₂ (by
    rw [hO₂, (hun Q.n₂ Q.n₁ Q.n₀ (Q.c + 1) (σ + 1)).2.1 (by omega) (by omega)])
  obtain ⟨ΞO, hΞO, eΛ⟩ := hcon P₁ P₂
  have hΞO' : ∀ q, ΞO.1 q = R₁.1 q.1 * R₂.1 q.2 := fun q => by
    rw [hΞO]; exact (hun Q.n₁ Q.n₀ Q.n₂ 0 0).2.2 q
  have hbi := (GlobalTheory.BiComb.comb_bimodel_and_line D Q.k (ofSplit Q.q) ψ Q.n₁ Q.n₀ Q.n₂).1 S.B.A S.J.W₀ S.B'.A
    Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ d₁ d₂ Ξ₁ R₁ Ξ₂ R₂ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) ΞO hΛ hd₁ hd₂ rfl rfl (fun q => rfl) hΞO'
  have hbc := GlobalTheory.ProdLocInv.biComb_comp ψ S.B.A S.J.W₀ S.B'.A c₁ d₁ (aconv [c₁, d₁]) c₂ d₂ (aconv [c₂, d₂])
    (comb_aconv_away Q c₁ d₁ hc₁ hd₁.1) (comb_aconv_away Q c₂ d₂ hc₂ hd₂.1) (Λ ΞO)
  have hom₁ : S.s₁.om (1, 1) = 1 := map_one _
  have hom₂ : S.s₂.om (1, 1) = 1 := map_one _
  simp only [GlobalTheory.TriStep.valK, Dbl2.val, Dbl2.con, GlobalTheory.TriStep.rTrans_one]
  rw [hom₁, hom₂, Module.End.one_apply, Module.End.one_apply, e₁, e₂, eΛ, ← hbc, hbi]

end GlobalTheory.TriStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicUnitaryRealMulFiniteDecomposition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicSplitParts

variable {D : D7}

theorem infMat_eq_map (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (h : GA D V) :
    infMat D.sp.cm.sig V.gram θ h = (infHom V h).1.map θ := rfl

theorem split_parts : ∀ (D : D7) (V : HSp D), (∀ h : GA D V, ∃ a ∈ GinfC V, ∃ k ∈ GfC V, h = a * k) ∧ ∀ a ∈ GinfC V, ∀ k ∈ GfC V, Lev.finE V (a * k) = Lev.finE V k ∧ ∀ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ, infMat D.sp.cm.sig V.gram θ (a * k) = infMat D.sp.cm.sig V.gram θ a := by
  intro D V
  refine ⟨fun h => ?_, fun a ha k hk => ⟨?_, fun θ => ?_⟩⟩
  · obtain ⟨p, hp⟩ := (GlobalTheory.AdelicSplit.splitEquiv V).surjective h
    exact ⟨p.1.1, p.1.2, p.2.1, p.2.2, hp.symm⟩
  · have h1 : finE V a = 1 := by
      have : finHom V a = 1 := ha
      simp only [finE, MonoidHom.comp_apply, this, map_one]
    rw [map_mul, h1, one_mul]
  · have h1 : infHom V k = 1 := hk
    rw [infMat_eq_map, infMat_eq_map, map_mul, h1, mul_one]

end GlobalTheory.AdelicSplitParts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BeforeLastStepDatumTransportBadPrime
section
noncomputable section

namespace GlobalTheory.Transport.TwistCpl

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep

variable {E : Type} [Field E] [NumberField E]

theorem intAt_iff_val (P : HeightOneSpectrum (𝓞 E)) (a : E) : IntAt P a ↔ P.valuation E a ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, h⟩
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hs
    have h2 := congrArg (P.valuation E) h
    rw [map_mul, h1, one_mul] at h2
    rw [h2]
    exact P.valuation_le_one r
  · intro h
    obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer a h
    exact ⟨n, d, d.2, by rw [mul_comm]; exact hnd⟩

theorem intAt_inv_pow_mul {P : HeightOneSpectrum (𝓞 E)} {q B c : ℕ} (hq : (q : E) ≠ 0) {z : E}
    (hz : P.valuation E z ≤ P.valuation E (((q ^ B * c : ℕ) : ℕ) : E)) : IntAt P (((q : E) ^ B)⁻¹ * z) := by
  rw [intAt_iff_val, map_mul, map_inv₀]
  have hc : P.valuation E ((c : ℕ) : E) ≤ 1 :=
    (intAt_iff_val P _).1 ⟨(c : 𝓞 E), 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have h1 : P.valuation E z ≤ P.valuation E ((q : E) ^ B) := by
    refine hz.trans ?_
    rw [Nat.cast_mul, Nat.cast_pow, map_mul]
    exact mul_le_of_le_one_right' hc
  have h0 : P.valuation E ((q : E) ^ B) ≠ 0 := (Valuation.ne_zero_iff _).2 (pow_ne_zero _ hq)
  exact (inv_mul_le_one₀ (zero_lt_iff.2 h0)).2 h1

end GlobalTheory.Transport.TwistCpl

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker

theorem GlobalTheory.Transport.TwistCpl.psiAt_transport_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (hm : i + 2 = B.R.m) (al : (I.idx a).β i) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a))
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u (i)) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N (i))) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i)) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 → cosetIn q' = cosetIn p' →
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P)
                (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀)
                ((Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P).symm (Formalism.L2.Col.repY p'.1.2)) =
        Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P)
          (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x)
          ((Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P).symm (Formalism.L2.Col.repY q'.1.2)) := by
  intro B X I hI l u a i hm al P p q p' q' k y k' y' hp hN hp' hN' hq hq' hc
  have hL := hI.idx_ok a
  rw [show B.R.m - 2 = i by omega] at hL
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · refine ⟨Formalism.L2.Col.qOf P.1, Nat.pos_of_ne_zero fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), ?_⟩
    rintro _ ⟨c, rfl⟩ x x₀ hx
    exact GlobalTheory.Transport.Pen.psiAt_frames (base_fields_primes_ok B X).1 l.pr hL al P hP p q p' q' hp hN hp' hN' hq hq' hc
      (GlobalTheory.Transport.Pen.lt_of_congAt hx)
  · have hPQ : P.1 ∈ I.Q a := (Finset.mem_union.1 P.2).resolve_left hP
    have hq0n : Formalism.L2.Col.qOf P.1 ≠ 0 := fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    have hq0 : ((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ≠ 0 := Nat.cast_ne_zero.2 hq0n
    refine ⟨Formalism.L2.Col.qOf P.1 ^ (I.cst a).B, pow_pos (Nat.pos_of_ne_zero hq0n) _, ?_⟩
    rintro _ ⟨c, rfl⟩ x x₀ hx
    have hr := _root_.GlobalTheory.Transport.TwistRead.qread I u a i P hPQ (GlobalTheory.Mem.Df.disjoint_vGs_Q I hI l a) p q p' q' k y k' y' hp hN hp' hN' hq hq' _ x x₀ hx
    have hm' : i + 1 + 1 = B.R.m := by omega
    set x₁ := Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀ with hx₁
    set x₂ := Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x with hx₂
    set y₁ := (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P).symm (Formalism.L2.Col.repY p'.1.2) with hy₁
    set y₂ := (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P).symm (Formalism.L2.Col.repY q'.1.2) with hy₂
    have s1 := hL.psiInvX al P x₁ (x₂ - x₁) y₁ fun s l => by
      have := hr l s
      rw [Matrix.sub_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply] at this
      exact GlobalTheory.Transport.TwistCpl.intAt_inv_pow_mul hq0 (by rw [LinearMap.sub_apply, Pi.sub_apply]; exact this)
    rw [add_sub_cancel] at s1
    rw [← s1]
    have h1 : y₁ ∈ cosetIn p' P := ⟨_, p'.repY_mem hm', by simp [hy₁]⟩
    rw [← hc] at h1
    obtain ⟨z, hz, h2⟩ := h1
    rw [if_neg hP] at h2
    have h3 := add_mem h2 ((GlobalTheory.TopLaw.coset_sub q'.1.1 (q'.mem_ybSet hm') hz (q'.repY_mem hm') P).2 hP)
    rw [← smul_add, sub_add_sub_cancel] at h3
    have h4 := hL.psiInv al P x₂ y₂ (y₁ - y₂) fun j => by
      rw [if_neg hP]
      open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.TopStep in exact mem_stdAt.1 h3 j
    rwa [add_sub_cancel] at h4
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatWeilRepresentationCores
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.FlatCommBF

variable {D : D7}

theorem sFinite_of_haar {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (ν : Measure G) (h : ν.IsHaarMeasure) : SFinite ν := by
  haveI := h
  infer_instance

theorem continuous_psiUni (ψ : AddChar (AF D.host.F) ℂ) (hψ : Continuous ψ) (ρ : ℕ) :
    Continuous fun u : UX D ρ => psiUni ψ u.1 := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hv : Continuous fun u : UX D ρ => u.1.1 := Units.continuous_val.comp continuous_subtype_val
  unfold psiUni psiE upSum
  refine hψ.comp (ht.comp ?_)
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  split_ifs
  · exact (continuous_apply j).comp ((continuous_apply i).comp hv)
  · exact continuous_const

theorem jacT_integral (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (y : Mx D S.rank ρ) (n : GA D T) {U : Type} [MeasurableSpace U] (m : Measure U) (G : U → WO S T₀ → ℂ)
    (w : WO S T₀) : jacT ψ d S y n (fun w' => ∫ u, G u w' ∂m) w = ∫ u, jacT ψ d S y n (G u) w ∂m := by
  simp only [jacT, heisO, Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, integral_const_mul]

theorem jacT_smul (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (y : Mx D S.rank ρ) (n : GA D T) (c : ℂ) (f : WO S T₀ → ℂ) :
    jacT ψ d S y n (c • f) = c • jacT ψ d S y n f := by
  funext w
  simp only [jacT, heisO, Pi.smul_apply, smul_eq_mul]
  ring


set_option maxHeartbeats 400000 in
theorem flatBF_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ radX J.d, ∀ h', flatBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flatBF s Ψ)) := by
  intro D ψ ρ B J s om' hom' Ψ hΨ h₀ n hn h'
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  obtain ⟨hloc, hsc, -⟩ := GlobalTheory.UnitU.topology D ρ
  haveI := hloc
  haveI := hsc
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : SFinite s.vU.ν := @sFinite_of_haar (UX D ρ) _ _ _ hloc hsc s.vU.ν s.vU.unit.1
  obtain ⟨hbase, -, hx0, -⟩ := GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d
  have hlin : LinearIndependent D.host.E J.d.e.transpose := hbase.1
  have hev := GlobalTheory.Unf.evalAt_xZero_yZero D ψ ρ B J s om' hom' Ψ hΨ
  have hom1 : s.om 1 Ψ = Ψ := by rw [map_one]; rfl

  have e3 : ∀ u : UX D ρ, evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ)) = s.om₀ (1, h') (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ u.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ))) := by
    intro u
    have h := hev.1 u 1 1 (one_mem _) h'
    rw [map_one, one_mul, ← Prod.one_eq_mk, map_one, ← Prod.one_eq_mk, map_one] at h
    rw [h]
    simp only [opA, jacT_one]
    rfl
  have e2 : ∀ u : UX D ρ, evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ)) = opA ψ J.d B.o B.ζ s.om₀ n h' (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ
      (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))) := by
    intro u
    have h := hev.1 u 1 n hn h'
    rw [map_one, ← Prod.one_eq_mk, map_one, ← Prod.one_eq_mk, map_one] at h
    exact h

  have hmix := GlobalTheory.MixValues.mixed_values D ψ hstd
  have thev : ∀ Φ, IsThetaFunO ψ B.V J.W Φ → ∀ u : UX D ρ, IsThetaFunO ψ B.V₀ J.W₀
      (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Φ (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))) :=
    fun Φ hΦ u => hmix.2 B.V₀ J.W J.W₀ ρ J.d s.vT.μ s.vT.𝓕 s.vT.covol _
      (hmix.1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Φ hΦ _) _
  have thom : ∀ p, IsThetaFunO ψ B.V J.W (s.om p Ψ) := fun p => s.weil.om_pres p Ψ hΨ
  have hFL := GlobalTheory.Unf.Flat.flatLaw D ψ hstd B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU J.d.e hlin
    (yZero B.V₀ ρ (vecB B.o B.ζ))
  have thflat : ∀ p, IsThetaFunO ψ B.V₀ J.W₀ (flatBF s (s.om p Ψ)) := fun p => by
    have h := (hFL _ (thom p)).2
    rw [← hx0] at h
    exact h
  obtain ⟨M, hMi, hM⟩ := GlobalTheory.Unf.flatFun_majorant D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil s.vU J.d.e hlin
    Ψ hΨ {1, (1, J.d.emb0 h'), (1, n * J.d.emb0 h'), (embA B.d B.o h₀, n * J.d.emb0 h')} (Set.toFinite _).isCompact
  simp only [← hx0] at hM
  have bound : ∀ p ∈ ({1, (1, J.d.emb0 h'), (1, n * J.d.emb0 h'), (embA B.d B.o h₀, n * J.d.emb0 h')} :
      Set (GA D B.V × GA D J.W)), ∀ (u : UX D ρ) w, ‖star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕
      (s.om p Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w‖ ≤ M u :=
    fun p hp u w => hM p hp _ w u
  have hmc := GlobalTheory.MixCont.mixed_coords_continuous D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil Ψ hΨ
  have hxu : Continuous fun u : UX D ρ => xZero J.d ⬝ u.1.1 :=
    continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)
  have cont : ∀ p, Continuous fun q : UX D ρ × WO B.V₀ J.W₀ => star (psiUni ψ q.1.1) *
      evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om p Ψ) (xZero J.d ⬝ q.1.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) q.2 := by
    intro p
    have h1 : Continuous fun q : UX D ρ × WO B.V₀ J.W₀ => ((p, xZero J.d ⬝ q.1.1.1, yZero B.V₀ ρ (vecB B.o B.ζ), q.2) :
        (GA D B.V × GA D J.W) × Mx D J.W.rank ρ × Mx D B.V₀.rank ρ × WO B.V₀ J.W₀) :=
      continuous_const.prodMk ((hxu.comp continuous_fst).prodMk (continuous_const.prodMk continuous_snd))
    have h2 := hmc.2.comp h1
    have h3 : Continuous fun q : UX D ρ × WO B.V₀ J.W₀ => star (psiUni ψ q.1.1) :=
      ((continuous_psiUni ψ hstd.1.1 ρ).comp continuous_fst).star
    exact h3.mul h2
  have hci := GlobalTheory.CommInt.om_integral_comm D ψ B.V₀ J.W₀ s.χV s.χW s.om₀ s.weil₀ (UX D ρ) s.vU.ν

  have hF : ∀ u : UX D ρ, (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) = star (psiUni ψ u.1) • evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) :=
    fun u => rfl
  have hG : ∀ (u : UX D ρ) w, s.om₀ (1, h') (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) w =
      star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w := by
    intro u w
    rw [hF, map_smul, e3]
    rfl
  have step1 : ∀ w, s.om₀ (1, h') (flatBF s Ψ) w = ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν := by
    intro w
    have h := hci (fun u w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) (1, h') M
      (fun u => by rw [hF]; exact GlobalTheory.OrientedHeis.theta_smul _ (thev Ψ hΨ u))
      (by have h := cont 1; rw [hom1] at h; exact h)
      (by simp only [hG]; exact cont _)
      hMi
      (fun u w => ⟨by have h := bound 1 (by simp) u w; rw [hom1] at h; exact h, by rw [hG]; exact bound _ (by simp) u w⟩)
      (by have h := thflat 1; rw [hom1] at h; exact h) w
    exact h.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => hG u w))

  have hF2 : ∀ u : UX D ρ, (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) =
      star (psiUni ψ u.1) • evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) := fun u => rfl
  have hG2 : ∀ (u : UX D ρ) w, s.om₀ (B.o.emb (h₀, 1), 1) (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) w =
      star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w := by
    intro u w
    rw [hF2, map_smul, e2, hev.1 u h₀ n hn h']
    rfl
  have step2 : ∀ w, s.om₀ (B.o.emb (h₀, 1), 1) (fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν) w =
      ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν := by
    intro w
    have h := hci (fun u w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) (B.o.emb (h₀, 1), 1) M
      (fun u => by rw [hF2]; exact GlobalTheory.OrientedHeis.theta_smul _ (thev _ (thom _) u))
      (cont _)
      (by simp only [hG2]; exact cont _)
      hMi
      (fun u w => ⟨bound _ (by simp) u w, by rw [hG2]; exact bound _ (by simp) u w⟩)
      (thflat _) w
    exact h.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => hG2 u w))

  have hopa : opA ψ J.d B.o B.ζ s.om₀ n h' (flatBF s Ψ) =
      fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν := by
    funext w
    have h1 : s.om₀ (1, h') (flatBF s Ψ) = fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν :=
      funext step1
    show jacT ψ J.d B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ)) n (s.om₀ (1, h') (flatBF s Ψ)) w = _
    rw [h1, jacT_integral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have h2 : (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) =
        star (psiUni ψ u.1) • s.om₀ (1, h') (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))) := by
      rw [e3]; rfl
    dsimp only
    rw [h2, jacT_smul, e2]
    rfl
  rw [hopa]
  funext w
  exact (step2 w).symm

end GlobalTheory.Unf.FlatCommBF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainFractionalIdealRelations
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.ChainIdeals

theorem host_ne_zero (D : D7) :
    FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 ≠ 0 ∧ D.host.AA ≠ 0 ∧ D.host.AAbar ≠ 0 ∧ dI D ≠ 0 := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h
  · rw [h, zero_mul, zero_mul, zero_mul] at hP; exact zero_ne_one hP
  · rw [h, mul_zero, zero_mul, zero_mul] at hP; exact zero_ne_one hP
  · rw [h, mul_zero, zero_mul] at hP; exact zero_ne_one hP
  · rw [dI] at h; rw [h, zero_mul] at hP; exact zero_ne_one hP

end GlobalTheory.SeeSaw.ChainIdeals
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelColumnSubOneMemBaseLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevel_column_sub_one_mem_baseLattice : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ j (hj : j ≤ B.R.m) b, ∀ κ ∈ A.U j b, ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → ∀ s : Fin ((I.rec7 l Z).R.N j), (fun r => Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (GlobalTheory.AdForm.finM _ (rankN (I.rec7 l Z) j hj) κ r s) - (1 : Matrix (Fin ((I.rec7 l Z).R.N j)) (Fin ((I.rec7 l Z).R.N j)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) r s) ∈ Formalism.UG.latS (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (intV (I.rec7 l Z).host.E v) (A.K j hj b).lev.Lb := by
  first | exact @GlobalTheory.AdForm.level_col_sub_one_mem | exact GlobalTheory.AdForm.level_col_sub_one_mem | (intros; apply GlobalTheory.AdForm.level_col_sub_one_mem <;> assumption)
end

