module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0218
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharInCuspidalSupportOfJacquetSubquotientFactor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0369
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0853
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0873
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0856
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0854
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0852
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0860
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleHarishChandraOfStdTraceNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0861
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfFive
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0480
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0876
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0812
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0795
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0838

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitLocalOfGreen
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockTypeSplit

open ValuativeRel Polynomial

section Finite

theorem isRoot_of_parVec {p : ℕ} [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) {r : ℕ} {α : Type} [Fintype α] [LinearOrder α]
    {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ Fin r) (a : α)
    {θ : (ZMod p)ˣ →* ℂˣ} {u : ZMod p} {f : (ZMod p)[X]} (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (hρ : CategoryTheory.Simple ρ)
    (hf : GlobalTheory.GLq.HasLabel L (fun x => ρ.character x) f) (hθ : GlobalTheory.GLp.IsCharLab L θ u) (ha : Fintype.card (m a) = 1)
    {v : ρ} (hv : v ≠ 0) (h : ParVec ρ.ρ e a θ v) : f.IsRoot u := by
  obtain ⟨c, v', hc, hv', hs⟩ := _root_.GlobalTheory.LevelType.exists_stdVec_of_parVec p r α m e a θ _ ρ.ρ v ha hv h
  have ht := _root_.GlobalTheory.LevelType.stdTrace_ne_zero p r c θ ρ v' hv' hs
  have hr : r = c + 1 + (r - c - 1) := by omega
  obtain ⟨A, B, hA, hB, h1, h2⟩ := _root_.GlobalTheory.LevelType.exists_irr_hc_of_stdTrace_ne_zero p r c (r - c - 1) θ ρ.character hr ⟨ρ, fun _ => rfl⟩ ht
  obtain ⟨σ, hσ, h3⟩ := _root_.GlobalTheory.LevelType.RestrictionTwo.exists_irr_hc_of_stdTrace_ne_zero p c θ A hA h2
  exact _root_.GlobalTheory.GLq.DetSplit.root_of_constituent p L r c _ θ u f _ A B σ hr ⟨ρ, hρ, fun _ => rfl⟩ hA hB hσ hf hθ h1 h3

end Finite

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem isSubquotient_jac_two {a b n V W : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n]
    [DecidableEq n] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : a ⊕ b ≃ n)
    {π : Representation ℂ (GL n F) V} {τ : Representation ℂ (GL n F) W} (hτ : IsSmooth τ) (h : IsSubquotient π τ) :
    IsSubquotient (GlobalTheory.SmGL.jac (two e) π) (GlobalTheory.SmGL.jac (two e) τ) := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap τ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  refine (IsSubquotient.of_surjective (jacMap (two e) f) fun y => ?_).trans (.of_injective (jacMap (two e) ι) ?_)
  · obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨v, rfl⟩ := hf w
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : ι v ∈ twKer τ (unipRad F (two e)) 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
    have hN := GlobalTheory.InertSupp.unipRad_eq_unipOf F (e := two e) (c := fun i => ((blk (two e) i).toNat : ℤ))
      fun i j => by cases blk (two e) i <;> cases blk (two e) j <;> simp
    obtain ⟨T, hT, h2⟩ := GlobalTheory.JacquetExact.exists_finset_of_mem_twKer h1
    obtain ⟨H, hle, hH, hSH⟩ := GlobalTheory.UnipCompact.exists_compact_subgroup F n _ T (hN ▸ hT)
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    exact GlobalTheory.IwahoriInj.twKer_mono (hle.trans hN.ge)
      (GlobalTheory.JacquetExact.mem_twKer_of_compact hτ ι Subtype.val_injective hH (h2 H hSH))

variable {p : ℕ} [Fact p.Prime] {r t : ℕ}

theorem typeVec_first {X : Bool → Type} [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)]
    (ρ : ∀ j, Representation ℂ (GL (Two (Fin r) (Fin t) j) F) (X j)) (hρ : ∀ j, IsSmooth (ρ j))
    {Y : Type} [AddCommGroup Y] [Module ℂ Y] {τ : Representation ℂ (Levi F (Two (Fin r) (Fin t))) Y}
    (h : IsSubquotient τ (piTensor ρ)) {z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))} {w : Y}
    (hw : TypeVec (n := Fin r) (τ.comp (MonoidHom.mulSingle (fun j => GL (Two (Fin r) (Fin t) j) F) false)) z w) :
    ∃ x, TypeVec (n := Fin r) (ρ false) z x := by
  obtain ⟨y, hy⟩ := TypeVec.up (n := Fin r)
    (π := (piTensor ρ).comp (MonoidHom.mulSingle (fun j => GL (Two (Fin r) (Fin t) j) F) false))
    (isSmooth_comp (isSmooth_piTensor hρ) _ (continuous_mulSingle (A := fun j => GL (Two (Fin r) (Fin t) j) F) false))
    (GlobalTheory.CuspRep.ParLaws.isSubquotient_comp h _) hw
  exact TypeVec.factor (m := Two (Fin r) (Fin t)) ρ false hy

theorem typeVec_iff {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin r) F) W)
    (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (y : W) (h : TypeVec π z y) : IsLevelOne π y ∧ NotKilled π z y := by
  obtain ⟨h1, ℓ, hℓ, h0⟩ := h
  refine ⟨fun h hh => h1 h (GlobalTheory.StepData.mem_KOne.2 fun a b => ?_), ℓ, fun g a b => ?_, h0⟩
  · simpa [Matrix.one_apply] using hh a b
  · rw [dite_eq_left ⟨a.2, b.2⟩]
    exact hℓ g a b

end Local

theorem hasLabelO_of_mul {p : ℕ} [Fact p.Prime] {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod p)}
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod p) C) {r : ℕ} (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (hρ : CategoryTheory.Simple ρ)
    {f : (ZMod p)[X]} (h0 : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ ≠ 0)
    (h : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * Formalism.L2.NT.eSerO O r f = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) : Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O ρ f := by
  classical
  rw [GlobalTheory.SerOSys.eSerO_eq_sum, Finset.mul_sum] at h
  obtain ⟨z, hz, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h.trans_ne h0)
  obtain ⟨τ, hτ, rfl, hl⟩ := (GlobalTheory.SerOSys.Zl_finite O r f).mem_toFinset.1 hz
  refine GlobalTheory.SerOSys.hasLabelO_of_repIso O hl (GlobalTheory.SerOSys.repIso_of_zIdem_eq ρ τ hρ hτ ?_)
  by_contra e
  exact hne (GlobalTheory.SerOSys.zIdem_mul_eq_zero ρ τ hρ hτ e)

theorem exists_hasLabel {p : ℕ} [Fact p.Prime] (t : Formalism.CyclotomicNorms.Fbar p →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar p, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar p) (hζ : Formalism.L2.NT.IsGenSys ζ)
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod p) (Formalism.L2.NT.convC t ht ζ hζ))
    (hO : ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod p))), 1 ≤ d → CategoryTheory.Simple τ →
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod p) τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (Formalism.L2.NT.convC t ht ζ hζ) τ (O.lab d τ))
    {r : ℕ} (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (hρ : CategoryTheory.Simple ρ) {f : (ZMod p)[X]}
    (h0 : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ ≠ 0)
    (h : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * Formalism.L2.NT.eSerO O r f = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) :
    ∃ L : GlobalTheory.GLq.LabelDatum p, L.teich = t ∧ L.gen = ζ ∧ GlobalTheory.GLq.HasLabel L (fun x => ρ.character x) f := by
  let L : GlobalTheory.GLq.LabelDatum p := ⟨t, ht, ζ, fun d hd => (hζ d hd).1,
    fun d e hd he => (hζ d hd).2 (d * e) (dvd_mul_right d e) (Nat.mul_pos hd he)⟩
  exact ⟨L, rfl, rfl, _root_.GlobalTheory.SerCmp.hasLabel_of_hasLabelO p L O (fun d V hd hs hc => _root_.GlobalTheory.SerCmp.LabConv.isCuspOf_of_hasCuspLabel p L t ht hζ rfl d V _ hd
    ((_root_.GlobalTheory.CuspCharRep.isCusp_character_iff_isCuspidal p d V hd hs).2 hc) (hO d V hd hs hc)) (_root_.GlobalTheory.HCChar.trace_hcRep_eq_hcL p) (_root_.GlobalTheory.GLq.ConstIff.constituent_hcRep_iff p) r ρ f hρ
    (hasLabelO_of_mul O ρ hρ h0 h)⟩


end GlobalTheory.BlockTypeSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformisedCoverIsDictionaryFrameCompatible
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem relab_and_goodEmb_of_inc {D : D7} (T : CoreJ D) (j : ℕ) (C : Cover T j T.σ₀) (hinc : C.σ₂.comp C.inc = T.σ₀) :
    (∀ τ, relab C.d.c₂ C.σ₂ τ = τ) ∧ GoodEmb C.d.c₂ C.σ₂ := by
  have key : ∀ (z : ℂ) (hz : z ∈ T.Q.c.F) (hz2 : z ∈ C.d.c₂.F), C.σ₂ ⟨z, hz2⟩ = z := by
    intro z hz hz2
    have h1 : (⟨z, hz2⟩ : C.d.c₂.F) = C.inc ⟨z, hz⟩ := Subtype.ext rfl
    have h2 : C.σ₂ (C.inc ⟨z, hz⟩) = T.σ₀ ⟨z, hz⟩ := by rw [← RingHom.comp_apply, hinc]
    rw [h1, h2]
    rfl
  refine ⟨fun τ => RingHom.ext fun x => key _ (T.Q.c.conj τ x) _, ?_⟩
  have hz : T.Q.H.rt0 ∈ T.Q.c.F := GlobalTheory.coe_baseKA_rho T.Q.l ▸ T.Q.c.le (baseKA T.Q.l).ρ.2
  have hz2 : T.Q.H.rt0 ∈ C.d.c₂.F := GlobalTheory.coe_baseKA_rho C.d.l₂ ▸ C.d.c₂.le (baseKA C.d.l₂).ρ.2
  have e : (IntermediateField.inclusion C.d.c₂.le) (baseKA C.d.l₂).ρ = ⟨T.Q.H.rt0, hz2⟩ :=
    Subtype.ext (GlobalTheory.coe_baseKA_rho C.d.l₂)
  unfold GoodEmb
  rw [RingHom.comp_apply]
  erw [e]
  exact key _ hz hz2

theorem isDict_cover_of_isUnif {D : D7} (T : CoreJ D) (hL : LawsJ T) (j : ℕ) (hj : InR D j) (W : HSp D)
    (hV : T.V j T.σ₀ = W) (hr : W.rank = D.R.r) (C : Cover T j T.σ₀) (hC : C.IsUnif) (hGE : GoodEmb C.d.c₂ C.σ₂) :
    IsDict C.U₂ W hr (castDict hV C.dict₂) (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j)
        (T.x₀ j T.σ₀) := by
  subst hV
  obtain ⟨-, -, -, hU, -, hr', g, e, F, ik, φ, th, hMW, hth, hDL⟩ := hC
  have hP := hL.pins
  have hg := T.toCore.good_σ₀
  have hr1 : 1 ≤ D.R.r := by
    have h2 := D.R.two_le_m
    have h3 := D.R.m_add_three_le_k
    simp only [Ranks.r]; omega
  have hio := GlobalTheory.TupleCover.iotaOK_and_frame T hL j hj _ hg _ rfl hr
  refine ⟨hU, hio.1, fun k => ⟨hMW k, fun τ => ?_, ?_⟩, fun k τ hτ => ?_, g, e, F, ik, φ, th, hth, hDL⟩
  · rw [(hU.2.1 k).2 τ]
    exact ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hP.1 τ, fun ⟨ρ, h⟩ => h ▸ hP.1.2.2.2 ρ⟩
  · have hU' := (Formalism.L2.PjFree.isUnf_ofPj _).2 hU
    obtain ⟨w⟩ := nonempty_uw hU'
    have h1 : (C.U₂.X k).κ0 = 2 * (C.U₂.X k).ξ0 :=
      (GlobalTheory.Dict.uw_lattice _ _ _ _ _ _ _ _ _ ((Formalism.L2.PjFree.goodEmb_iff _).2 hGE) hU' hr1 w k).1
    rw [h1, (hMW k).2, mul_neg]
  · rw [(hMW k).1, (hU.2.1 k).1]
    exact hio.2 τ (((hU.2.1 k).2 τ).1 hτ)


set_option maxHeartbeats 1000000 in
theorem cover_dict_frameTie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → IsDict C.U₂ (Wc D i) (rank_Wc i) (castDict hV C.dict₂) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) ∧ FrameTie C.U₂ (Wc D i) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.σ₀) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) ∧ (∀ τ, relab C.d.c₂ C.σ₂ τ = τ) ∧ GoodEmb C.d.c₂ C.σ₂ := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL _ _ _ hmod _ hT i _ hV C hC
  have hj := inR i
  have hinc : C.σ₂.comp C.inc = T.σ₀ := hC.2.2.1
  obtain ⟨hrel, hGE⟩ := relab_and_goodEmb_of_inc T _ C hinc
  have hD := isDict_cover_of_isUnif T hL _ hj _ hV (rank_Wc i) C hC hGE
  have hU := hD.1
  have hP := hL.pins
  have hdp : (T.Q.Dw ((i : ℕ) + 1)).p = (D.R.sigW ((i : ℕ) + 1)).1 := (hP.2.2.2 _ hj).1
  have hres : res T (sg0 D A) = T.toCore.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T hT.alg hP.2.2.1]
  have hx : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.toCore.σ₀) :=
    hres ▸ hT.x0 i (sg0 D A) (base_embedding_good T R hT.alg hP.2.2.1)
  have hε : ∀ ρ a, (R.MW i (sg0 D A)).ε ρ a = decide ((a : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p) := fun ρ a => by
    rw [hmod.order i ρ a, hdp,
      show (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ hj.1 hj.2 _]
  refine ⟨hD, fun k => ⟨isInvOf_cart _ _ _ hx (by have := hU.1; have := (hU.2.1 k).1; omega) hε,
    fun hq => isBasOf_onb _ _ _ hx hq hε⟩, hrel, hGE⟩

end GlobalTheory.LevelSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedCocycleDescentEnlargement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

namespace GlobalTheory.UseLoc

theorem descUr_entry (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (a b : Fin k) :
    (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M)) g a b =
      IntermediateField.inclusion C.le ((Br.loc D.nbr i w hw M) g a b) := by
  simp only [mapM, locOC, Br.loc, Br.locM, MonoidHom.coe_comp, Function.comp_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  rfl


set_option maxHeartbeats 2000000 in
theorem descUr_mem : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (I : Subgroup (Br.G D.nbr i w hw))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ Z1urD (latC C (locOC C M)) I → z ∈ Z1urD (Br.locLat D.nbr i w hw M) I := by
  intro D i w hw C k M I z hz
  obtain ⟨r, hrl, hr1, hrO⟩ :=
    GlobalTheory.CoefRetraction.exists_integral_retraction (D.nd.l i) (D.nbr i w hw).LL C.LL C.le
  have hri : ∀ a, r (IntermediateField.inclusion C.le a) = a := fun a => by
    have := hrl a 1
    simpa [hr1] using this
  obtain ⟨x', hx'⟩ := hz
  obtain ⟨v', rfl⟩ := Submodule.Quotient.mk_surjective _ x'
  refine ⟨Submodule.Quotient.mk (fun j => r (v' j)), fun g hg => ?_⟩
  have h : liftQ C.le k (z g) = actD (latC C (locOC C M)) g (Submodule.Quotient.mk v') - Submodule.Quotient.mk v' := hx' g hg
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective (Br.locLat D.nbr i w hw M).T (z g)
  rw [← hu] at h ⊢
  have h1 : (Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k) (incV C.le k u)) =
      Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k) ((repV C (locOC C M)) g v') -
        Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k) v' := h
  rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.eq] at h1
  show (Submodule.Quotient.mk (p := stdG ↥(OL (D.nbr i w hw).LL) ↥(D.nbr i w hw).LL.1 k) u) =
      Submodule.Quotient.mk (p := stdG ↥(OL (D.nbr i w hw).LL) ↥(D.nbr i w hw).LL.1 k) ((matRep (Br.loc D.nbr i w hw M)) g (fun j => r (v' j))) -
        Submodule.Quotient.mk (p := stdG ↥(OL (D.nbr i w hw).LL) ↥(D.nbr i w hw).LL.1 k) (fun j => r (v' j))
  rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.eq]
  obtain ⟨t, ht⟩ := h1
  refine ⟨fun j => ⟨r (t j), hrO _ (t j).2⟩, ?_⟩
  funext j
  have hj := congrFun ht j
  have hrl' : ∀ a x, r (IntermediateField.inclusion C.le a * x) = a * r x := hrl
  have hj' : ((t j : ↥(OL C.LL)) : ↥C.LL.1) = IntermediateField.inclusion C.le (u j) -
      ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec v' j - v' j) := hj
  change r ((t j : ↥(OL C.LL)) : ↥C.LL.1) =
    u j - ((Br.loc D.nbr i w hw M g).mulVec (fun j => r (v' j)) j - r (v' j))
  rw [hj', map_sub, map_sub, hri]
  congr 2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, descUr_entry, hrl']

end GlobalTheory.UseLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.XiTypeProof

theorem xiType : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), (∀ i j b, Faithful (rd i j b)) →
    (∀ i j b, ActRead (rd i j b)) → ρ.LevelOf D.nexp → XiType rd := by
  intro D ρ hρ rd hF hA hL i _ j b Q M hQ s h P _ _ a x hx
  unfold Formalism.MainNotions.IntegralHeckeForms.Fm0
  rw [Submodule.mem_iInf]
  intro u
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M)) :=
    GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint D _ D.ntw ρ hρ i j b _ (fun _ h => isSplit_of_mem_admissibleConjugatePairPlaces h) (hQ.2.2.mono_left (admissibleConjugatePairPlaces_subset i Q M))
  have hu : ρ.eG i j b u ∈ (ρ.B i j b).G.P.H := (hL.U_eq i j b u).2 u.2
  obtain ⟨κ, hlift, hsupp, hser⟩ := GlobalTheory.T.thetaSeries_type_under_supported_lifts D _ _ (ρ.B i j b) (hρ.base i j b) (D.sp.V_sig _) _ (hρ.weil_base i j b) _ hu
  have hg := GlobalTheory.UnivGood.univOf_good D _ D.ntw ρ hρ D.nexp i Q M
  have hdet : detChar (Wc D j) ((univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))) κ = 1 := by
    apply Multiplicative.toAdd.injective
    funext PP
    have := _root_.GlobalTheory.TwistTypeDet.detChar_eq_one_of_suppAt D _ _ (ρ.B i j b) (hρ.base i j b) (D.sp.V_sig _) _ ⟨{PP.1}, _, _⟩ (hg.2 PP.1 PP.2)
      (hadm.mono (by simpa using PP.2)) _ κ hlift hsupp
    exact congrArg Multiplicative.toAdd this
  apply (hF i j b).injective
  funext g
  change rd i j b (D.nexp.actG i _ b u x) g = rd i j b (((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) • x) g
  rw [hA i j b u κ hlift, map_smulₛₗ, Pi.smul_apply, hx]
  unfold Setup.xi
  rw [Base.xiCoef_apply, Base.xiCoef_apply, detChar_mul hg.delQ_real, hdet, mul_one]
  refine (hser _ hadm _ h P g).trans ?_
  rw [hL.psiU_eq i j b u hu, smul_eq_mul]
  rfl

end GlobalTheory.XiTypeProof
end

