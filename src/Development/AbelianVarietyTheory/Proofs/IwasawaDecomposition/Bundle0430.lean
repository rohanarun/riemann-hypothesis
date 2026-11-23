module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0312
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0426
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLastStepTwistBasePoint
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.UnipotentAdelicQuotients.Bundle0002
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeOperatorKeepsRationalIntegralLevelForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBasePointChartMulTwistStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleBasePoint_chart_mul_twist_alt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (Lb0 : Ch0 → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U0 : Ch0 → Subgroup (GA B (B.R.N i))) (chi0 : ∀ β, U0 β →* ℂˣ) (y0 : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)) (st0 : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k0 : Ch0 → GA B (B.R.N i)), I.Reads u I.mu0 i chOf0 Lb0 U0 chi0 y0 st0 k0 → ∀ (g : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → Ch0) (t : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i)), (∀ β, ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf (t β) p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)) → (∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) (t β) = 1) → (a = I.mu0 → ∀ β, t β = 1) → GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i (fun β => k0 (g β) * t β) := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.admissibleBasePoint_chart_mul_twist | exact GlobalTheory.Mem.Col2.TC.ChTw.admissibleBasePoint_chart_mul_twist | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.admissibleBasePoint_chart_mul_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseRowCountEqFinrankTypePartBaseLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.BaseRowCount

theorem sum_finrank_le_of_indep {K V I : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    [Fintype I] (S : I → Submodule K V) (hi : iSupIndep S) :
    ∑ i, Module.finrank K (S i) ≤ Module.finrank K V := by
  classical
  have h : Module.finrank K ↥(⨆ i, S i) = ∑ i, Module.finrank K (S i) := by
    rw [Submodule.iSup_eq_range_dfinsupp_lsum, LinearMap.finrank_range_of_inj hi.dfinsupp_lsum_injective]
    exact Module.finrank_directSum (R := K) (fun i => S i)
  rw [← h]
  exact Submodule.finrank_le _


set_option maxHeartbeats 2000000 in
theorem nRows0_eq_finrank_isotE : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ π : D.what₂.FT, D.what₂.nRows0 π = Module.finrank ℂ (principalLevelFrame.isotE R.toRealDat.θ Y.PY (R.toRealDat.MY 0) (levS _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) R.toRealDat.e0 (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) := by
  intro hW hDS hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hHost
  classical
  have hI : Inputs D := GlobalTheory.LinksInputs.inputs_of_hypotheses hW hDS hHC hCR D
  have hB := hP.char.base
  have h0 := hB.models.ν0
  have hs := GlobalTheory.HilbertLevels.scaled (inv_pos.2 (GlobalTheory.HilbertLevels.nP_pos F.lv2 false)) h0.1.1 h0.2
  have hO := (GlobalTheory.FinTypesRows.isotL_span_orth D (Yc D 0) _ R.θ (R.MY 0) Y.PY Y.hF (R.βY 0)
    (R.dat0 (R.toRealDat.levR F.lv2 false)) R.e0 _ R.fd0 hI (D.sp.Y_sig _) hB.models.inf Y.stdPsi.1 hs.1 hs.2
    (GlobalTheory.Mem.R3.IsotIndep.gaL_finSum _ _ _ _ _)).2
  have hT := Y.tied.base
  let f : D.what₂.EE0 →ₗ[ℂ] _ := (Submodule.subtype _) ∘ₗ Y.Iz.jE.toLinearMap
  have hf : Function.Injective f := Subtype.val_injective.comp Y.Iz.jE.injective
  let Wp : D.what₂.FT → Submodule ℂ D.what₂.EE0 := fun π => (Y.Iz.prt π).comap f

  have hOrth : ∀ π π', π ≠ π' → ∀ x ∈ Wp π, ∀ y ∈ Wp π', ⟪x, y⟫_ℂ = 0 := by
    intro π π' hne x hx y hy
    have hx' : f x ∈ Y.Iz.prt π := hx
    have hy' : f y ∈ Y.Iz.prt π' := hy
    rw [Y.prtE0] at hx' hy'
    obtain ⟨a, ha, hax⟩ := hx'
    obtain ⟨b, hb, hby⟩ := hy'
    have hni : ¬ (principalLevelFrame.FinTyp.conjT (principalLevelFrame.rowRepR R.θ (Y.eFT π))).Iso
        (principalLevelFrame.FinTyp.conjT (principalLevelFrame.rowRepR R.θ (Y.eFT π'))) :=
      principalLevelFrame.not_iso_conjT fun h => hne (Y.eFT.injective (principalLevelFrame.rowRepR_inj R.θ _ _ h))
    have key := hO _ _ hni a ha b hb
    rw [hT.ee x y]
    unfold ChainReal.ipE ipMT
    refine Eq.trans ?_ key
    have e1 : (Y.Iz.jE x).val = f x := rfl
    have e2 : (Y.Iz.jE y).val = f y := rfl
    rw [e1, e2, ← hax, ← hby]
    congr 1
    · exact LinearEquiv.symm_apply_apply _ a
    · exact LinearEquiv.symm_apply_apply _ b
  have hInd : iSupIndep Wp := by
    apply OrthogonalFamily.independent
    rw [orthogonalFamily_iff_pairwise]
    intro σ σ' hne
    rw [Function.onFun, Submodule.isOrtho_iff_inner_eq]
    exact hOrth σ σ' hne
  have hle : ∀ π, D.what₂.nRows0 π ≤ Module.finrank ℂ (Wp π) := by
    intro π
    unfold Formalism.BasicNotions.Rows.Data.nRows0
    let v : {σ // D.what₂.ft0 σ = π} → Wp π := fun σ => ⟨D.what₂.onb0 σ.1, by
      show f _ ∈ Y.Iz.prt π
      have := hT.ft σ.1
      rw [σ.2] at this
      exact this⟩
    have hli : LinearIndependent ℂ v := by
      apply LinearIndependent.of_comp (Wp π).subtype
      exact D.what₂.onb0.toBasis.linearIndependent.comp _ Subtype.val_injective
    exact hli.fintype_card_le_finrank
  have hdim : Module.finrank ℂ D.what₂.EE0 = D.what₂.D0 := by
    rw [Module.finrank_eq_card_basis D.what₂.onb0.toBasis, Fintype.card_fin]
  have hsum : ∑ π, D.what₂.nRows0 π = D.what₂.D0 := by
    unfold Formalism.BasicNotions.Rows.Data.nRows0
    rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv D.what₂.ft0), Fintype.card_fin]
  have hsle : ∑ π, Module.finrank ℂ (Wp π) ≤ D.what₂.D0 := hdim ▸ sum_finrank_le_of_indep Wp hInd
  have heq : ∀ π, D.what₂.nRows0 π = Module.finrank ℂ (Wp π) := by
    have h2 : ∑ π, D.what₂.nRows0 π = ∑ π, Module.finrank ℂ (Wp π) :=
      le_antisymm (Finset.sum_le_sum fun π _ => hle π) (hsle.trans hsum.ge)
    intro π
    exact (Finset.sum_eq_sum_iff_of_le (fun π _ => hle π)).1 h2 π (Finset.mem_univ π)
  intro π
  rw [heq π]
  have hrng : Y.Iz.prt π ≤ LinearMap.range f := by
    intro z hz
    rw [Y.prtE0] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    have hz : (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap a ∈
        (toChainReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop).EEc false :=
      ⟨a, (Submodule.mem_inf.1 ha).1, rfl⟩
    refine ⟨Y.Iz.jE.symm ⟨_, hz⟩, ?_⟩
    change (Submodule.subtype _ (Y.Iz.jE (Y.Iz.jE.symm ⟨_, hz⟩))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hmap : (Wp π).map f = Y.Iz.prt π := by
    show ((Y.Iz.prt π).comap f).map f = _
    rw [Submodule.map_comap_eq, inf_eq_right.2 hrng]
  rw [(Submodule.equivMapOfInjective f hf (Wp π)).finrank_eq, hmap, Y.prtE0]
  first
    | exact LinearEquiv.finrank_map_eq _ _
    | exact LinearEquiv.finrank_map_eq (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _) _
    | exact ((Submodule.equivMapOfInjective (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap (LinearEquiv.injective _) _).finrank_eq).symm

end GlobalTheory.BaseRowCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLastStepTwistBasePointStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lastStep_twistBasePoint : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClsTied (D := (I.rec7 l Z)) u B.R.m le_rfl), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∃ k, I.Reads u I.mu0 B.R.m (fun _ => ()) (fun _ => K.lev.Lb) (fun _ => K.lev.U) (fun _ => K.lev.chi) (fun c => (K.y c).1) (fun c s => (K.stabI c s).1) k) → ∃ (K1 : ∀ β : Unit, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) B.R.m le_rfl (fun c : {c // (fun _ : (I.stp u a B.R.m).Cl => ()) c = β} => (I.chain l u a).stab B.R.m c.1) (fun c => latCrd (I.rec7 l Z) B.R.m le_rfl (I.latAt u a B.R.m c.1))), (∃ k, I.Reads u a B.R.m (fun _ => ()) (fun β => (K1 β).lev.Lb) (fun β => (K1 β).lev.U) (fun β => (K1 β).lev.chi) (fun c => ((K1 ()).y ⟨c, rfl⟩).1) (fun c s => ((K1 ()).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d → IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 → PtOf (g * k β) (tilF I.sel (I.tup a) u d)) ∧ I.TopBase l Z u a (K1 ()).lev.U (fun c => ((K1 ()).y ⟨c, rfl⟩).1) ∧ (∀ v, v ∉ Q → (K1 ()).lev.Uloc v = K.lev.Uloc v) ∧ (∃ n : ℕ, 0 < n ∧ ∀ κ, (K1 ()).lev.chi κ ^ n = 1) ∧ ∀ (κ : (K1 ()).lev.U) (κ' : K.lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K1 ()).lev.chi κ = K.lev.chi κ' := by
  first | exact @GlobalTheory.Mem.Col2.TC.chart_twm | exact GlobalTheory.Mem.Col2.TC.chart_twm | (intros; apply GlobalTheory.Mem.Col2.TC.chart_twm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevelTwistTrivialLocalMoveStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevel_twistTrivial_localMove : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ), i ≤ B.R.m → ∀ {Ch : Type} (chOf : (I.stp u a i).Cl → Ch) (Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U : Ch → Subgroup (GA B (B.R.N i))) (chi : ∀ β, U β →* ℂˣ) (y : (I.stp u a i).Cl → GA B (B.R.N i)) (st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k : Ch → GA B (B.R.N i)), I.Reads u a i chOf Lb U chi y st k → ∀ (c : (I.stp u a i).Cl) (x : GA B (B.R.N i)), x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i) → (∀ v, I.UnderQ a v → bc (prV (E := B.host.E) v) x = 1) → x ∈ U (chOf c) → ∃ κ, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u a i c ((k (chOf c))⁻¹ * x * k (chOf c)) κ := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.locMv_of_mem | exact GlobalTheory.Mem.Col2.TC.ChTw.locMv_of_mem | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.locMv_of_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjIdealEqConjP
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.Brg


open _root_.Formalism.L2.Col in
theorem conjIdeal_eq_conjP {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal = (conjPrime₂ P).asIdeal := by
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    rintro r ⟨s, hs, e⟩
    show r ∈ (conjPrime₂ P).asIdeal
    rw [mem_conjP]
    have : cO E r = s := RingOfIntegers.ext (by
      show star (r : E) = (s : E)
      have e' : (r : E) = star (s : E) := e
      rw [e', star_star])
    rw [this]; exact hs
  · intro r hr
    rw [mem_conjP] at hr
    refine Ideal.subset_span ⟨cO E r, hr, ?_⟩
    show (r : E) = star (star (r : E))
    rw [star_star]


open _root_.Formalism.L2.Col in
theorem g_notMem_of_levOff {X : Fields} {Pr : Primes X} (hPr : Pr.Ok)
    (P : letI := X.starE; LevOff (E := X.E) ∅ Pr.vGs ∅) (k : Fin 2) :
    ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal := by
  classical
  letI := X.starE
  intro hk
  have h0 : X.conjO (Pr.piG k) ≠ 0 := by
    refine right_ne_zero_of_mul (a := Pr.piG k) ?_
    rw [hPr.piG_norm k]
    exact_mod_cast (hPr.g_prime k).ne_zero
  have hsub : ∀ Q, Q ∈ Pr.vG k → Q ∈ Pr.vGs := fun Q hQ => by
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases k
    exacts [Or.inl hQ, Or.inr hQ]
  rw [← hPr.piG_norm k] at hk
  rcases P.1.isPrime.mem_or_mem hk with h | h
  · have hc : conjPrime₂ P.1 ∈ Pr.vG k := by
      refine (mem_divs h0 _).2 ?_
      rw [mem_conjP]
      show cO X.E (X.conjO (Pr.piG k)) ∈ P.1.asIdeal
      exact (cO_cO (Pr.piG k)).symm ▸ h
    exact P.2.2.2 (conjPrime₂ P.1) (Or.inr (hsub _ hc)) (conjIdeal_eq_conjP P.1).symm
  · exact P.2.2.1 (Or.inr (hsub _ ((mem_divs h0 _).2 h)))

end GlobalTheory.Mem.R3.Brg

namespace GlobalTheory.Mem.R3.Brg

theorem muVal_eq {B : Base} {px : PreX B.toPre} (I : ColIn B px) (hI : I.Ok) (hV : ValsIn I) (i : Fin B.R.m) {a : I.ι}
    {τ : Tup B.fields.F B.fields.E B.fields.K I.S} (hτ : I.tup a = τ) (P : HeightOneSpectrum (𝓞 B.fields.E))
    (hg : ∀ k, ((B.host.g k : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal) (hu : (I.xi a).UnrAt P) :
    B.embLL ((I.Ch.muVal i P * xiValOf I τ P : B.LLˣ) : B.LL) = (((I.C.mu0 i * I.xi a).val P : ℂˣ) : ℂ) := by
  subst hτ
  rw [Formalism.L2.Host.HChar.val_mul, Units.val_mul, Units.val_mul, map_mul, hV.embLL_xiValOf a P hu]
  congr 1
  exact hI.ch_tied.muVal i P hg

theorem values : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    (∀ (i : Fin X.toD7.R.m) t, ∀ P ∈ (famR X I hX U Xg tr).A.ok t,
      X.toD7.what₂.embLL ((famR X I hX U Xg tr).A.muVal i t P : X.toD7.what₂.LL) =
        (((L.C.mu0 i * L.xiH t).val (P.1 : Pl X.toD7.host.E) : ℂˣ) : ℂ)) ∧
    (∀ P ∈ (famR X I hX U Xg tr).A.ok (famR X I hX U Xg tr).A.μ0,
      X.toD7.what₂.embLL ((famR X I hX U Xg tr).A.etaVal P : X.toD7.what₂.LL) =
        Formalism.L2.Host.etaAlg X.toD7.host L.C.eta (P.1 : Pl X.toD7.host.E)) ∧
    ∀ t PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → ∃ z : X.toD7.what₂.LL, IsPrimitiveRoot z (Nat.card (kP PP)) := by
  intro X px I hX U Xg tr L eG hI hV hL _
  classical
  letI := X.B.fields.starE
  have hPr : (X.B.primes px).Ok := (GlobalTheory.Mem.Col2.base_fields_primes_ok X.B px).2.1
  refine ⟨fun i t P hP => ?_, fun P _ => ?_, fun t PP hPP => ?_⟩
  · have hP' : P.1 ∈ Formalism.L2.DIV.offSet (E := X.B.fields.E) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ∅ := hP
    have hQ : ∀ PP, PP ∈ I.Q (ixOf I U t) → PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := fun PP h =>
      Finset.mem_union_right _ (by rw [← tup_ixOf I t]; exact h)
    have hg : ∀ k, ((X.B.host.g k : ℕ) : 𝓞 X.B.fields.E) ∉ P.1.asIdeal := g_notMem_of_levOff hPr P
    have hunr : (I.xi (ixOf I U t)).UnrAt P.1 := by
      by_contra hn
      rw [← hL.xiH t] at hn
      rcases (hL.is.Q_ram t P.1).1 hn with h | ⟨PP', h, hc⟩
      · rw [hL.Q t] at h
        exact hP'.2.1 (Or.inr (Finset.mem_coe.2 (hQ _ h)))
      · rw [hL.Q t] at h
        have hle : PP'.asIdeal ≤ (Formalism.L2.Col.conjPrime₂ P.1).asIdeal := fun c hcm => by
          obtain ⟨c', hc', e⟩ := hc c hcm
          refine (Formalism.L2.Col.mem_conjP (E := X.B.fields.E) P.1 c).2 ?_
          have : Formalism.L2.Col.cO X.B.fields.E c = c' := RingOfIntegers.ext e.symm
          rw [this]; exact hc'
        have heq : PP'.asIdeal = (Formalism.L2.Col.conjPrime₂ P.1).asIdeal :=
          PP'.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P.1).isPrime.ne_top hle
        exact hP'.2.2 PP' (Or.inr (Finset.mem_coe.2 (hQ _ h))) (heq.trans (conjIdeal_eq_conjP P.1).symm)
    rw [hL.C, hL.xiH t]
    exact muVal_eq I hI hV i (tup_ixOf I t) P.1 hg hunr
  · show X.B.embLL (I.Ch.etaVal P.1 : X.B.LL) = _
    rw [hL.C]
    exact hI.ch_tied.etaVal P.1
  · rcases hPP with h | h
    · rw [hL.Pg] at h
      obtain ⟨k, hk⟩ : ∃ k, PP ∈ (X.B.primes px).vG k := by
        rcases Finset.mem_union.1 h with h | h
        exacts [⟨0, h⟩, ⟨1, h⟩]
      have hn : Ideal.absNorm PP.asIdeal = X.B.host.g k := hPr.vG_norm k PP hk
      have hcard : Nat.card (kP PP) = X.B.host.g k := by
        rw [← hn, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [hcard]
      exact (GlobalTheory.Core.Cls.coeffField_rootsOfUnity_typePrimes_hermitianStages X k).1
    · rw [hL.Q t] at h
      exact hV.2 _ PP h

end GlobalTheory.Mem.R3.Brg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLatticeClassLocalizationEqUnimodularCompanio
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LshOffLevel

theorem mem_divs_of' {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A}
    (h : P ∈ divs a) : a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · exact (hf.mem_toFinset.1 h)
  · simp at h

theorem lsh_lattice_and_loc_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Y : DivX (I.rec7 l Z)) (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (j : ℕ), j ≤ B.R.m → ∀ (c : (I.stp u μ j).Cl), Submodule.IsLattice B.fields.E ((I.stp u μ j).Lsh c.1 ((I.stp u μ j).rep c)) ∧ ∀ x : Fin (B.R.N j) → B.fields.E, (∃ s : ℕ, ¬ (I.rec7 l Z).what₂.places.resChar w ∣ s ∧ (s : B.fields.E) • x ∈ (I.stp u μ j).Lsh c.1 ((I.stp u μ j).rep c)) ↔ (∃ s : ℕ, ¬ (I.rec7 l Z).what₂.places.resChar w ∣ s ∧ (s : B.fields.E) • x ∈ ((I.stp u μ j).rep c).1.1.deco.1.N) := by
  intro B X I hOk hPins l Z Y u μ w hw j hj c
  classical
  have hpP : ((I.rec7 l Z).what₂.places.resChar w).Prime := (I.rec7 l Z).what₂.places.resChar_prime w
  have hTP : (B.T u).Prime := l.pr.T_prime u
  have hpT : ¬ (I.rec7 l Z).what₂.places.resChar w ∣ B.T u := fun h => hw.1 ((Nat.prime_dvd_prime_iff_eq hpP hTP).1 h)
  set d := ((I.stp u μ j).rep c).1.1.deco with hd
  have hE : (I.stp u μ j).Lsh c.1 ((I.stp u μ j).rep c) = d.1.Lsh := rfl
  rw [hE]
  have hTP' : ∀ P : (B.primes X).vT u, (((B.T u : ℕ) : 𝓞 B.fields.E)) ∈ (P : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal := by
    intro P
    have hpi := mem_divs_of' P.2
    rw [← l.pr.piT_norm u]
    exact Ideal.mul_mem_right _ _ hpi
  have hLN : ∀ x ∈ d.1.Lsh, ((B.T u : ℕ) : B.fields.E) • x ∈ d.1.N := by
    intro x hx
    have := d.2.smul_Lsh_mem_N (a := ((B.T u : ℕ) : 𝓞 B.fields.E)) (fun P => by rw [map_natCast]; exact hTP' P) hx
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul B.fields.E] at this
  refine ⟨d.2.Lsh_lattice, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨s, hs, hx⟩
    refine ⟨B.T u * s, fun h => (hpP.dvd_mul.1 h).elim hpT hs, ?_⟩
    have h3 := hLN _ hx
    have e : ((B.T u * s : ℕ) : B.fields.E) • x = ((B.T u : ℕ) : B.fields.E) • ((s : B.fields.E) • x) := by
      rw [smul_smul, ← Nat.cast_mul]
    exact e ▸ h3
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, d.2.N_le_Lsh hx⟩

end GlobalTheory.LshOffLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqualRankSplittingCharsAdmissibleMulRight
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeilEqRank

variable {D : D7}

theorem equalRankSplittingCharsAdmissible_mul_right {V W : HSp D} {χ χ' ν : IdC D} (h : AdmE V W χ χ') (hν : IsHC D ν) (h0 : ResEta D ν 0) :
    AdmE V W χ (χ' * ν) :=
  ⟨h.1, h.2.1, (GlobalTheory.Mem.HeckeExp.hcSubgroup D).mul_mem (show χ' ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from h.2.2.1)
    (show ν ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from hν), h.2.2.2.1, resEta_mul h.2.2.2.2 h0⟩

theorem equalRankSplittingCharsAdmissible_mul_left {V W : HSp D} {χ χ' ν : IdC D} (h : AdmE V W χ χ') (hν : IsHC D ν) (h0 : ResEta D ν 0) :
    AdmE V W (χ * ν) χ' :=
  ⟨h.1, (GlobalTheory.Mem.HeckeExp.hcSubgroup D).mul_mem (show χ ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from h.2.1)
    (show ν ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from hν), h.2.2.1, resEta_mul h.2.2.2.1 h0, h.2.2.2.2⟩

theorem exists_weilFun_eqRank : ∀ D : D7, WeilEx D → WeilOnEqEx D → WeilTwEq D → ∀ ψ, IsStdChar D ψ (-1) →
    ∃ Wf : WeilFun D ψ, Wf.EqRank := by
  classical
  intro D h1 h2 h3 ψ hψ
  obtain ⟨W₀⟩ := h1 ψ hψ
  have key : ∀ (V W : HSp D) (χ χ' : IdC D), ∃ om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W),
      (V.rank ≠ W.rank → om = W₀.om V W χ χ') ∧ (AdmE V W χ χ' → IsWeilOn ψ V W χ χ' om) := fun V W χ χ' => by
    by_cases h : AdmE V W χ χ'
    · obtain ⟨om, hom⟩ := h2 ψ hψ V W χ χ' h
      exact ⟨om, fun hne => absurd h.1 hne, fun _ => hom⟩
    · exact ⟨W₀.om V W χ χ', fun _ => rfl, fun k => absurd k h⟩
  choose om hne heq using key
  refine ⟨⟨om, fun V W χ χ' ha => ?_, fun V W χ χ' ha => ?_, fun V W χ χ' ha => ?_, fun V W χ χ' ha => ?_,
    fun V W χ χ' ha => ?_, fun V W χ χ' ν ha => ?_, fun V W χ χ' ν ha => ?_, fun V W χ χ' ha => ?_,
    fun V W χ χ' ha => ?_⟩, heq, fun V W χ χ' ν ha hν h0 => ?_, fun V W χ χ' ν ha hν h0 => ?_⟩
  · rw [hne V W χ χ' ha.1]; exact W₀.om_heis V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_aut V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_cont V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_unit V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_split V W χ χ' ha
  · rw [hne V W χ χ' ha.1, hne V W χ (χ' * ν) ha.1]; exact W₀.twW V W χ χ' ν ha
  · rw [hne V W χ χ' ha.1, hne V W (χ * ν) χ' ha.1]; exact W₀.twV V W χ χ' ν ha
  · rw [hne V W χ χ' ha.1, hne W V χ' χ ha.1.symm]; exact W₀.om_swap V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_unr V W χ χ' ha
  · exact (h3 ψ hψ V W χ χ' ν ha hν h0 _ (heq V W χ χ' ha)).1 _ (heq V W χ (χ' * ν) (equalRankSplittingCharsAdmissible_mul_right ha hν h0))
  · exact (h3 ψ hψ V W χ χ' ν ha hν h0 _ (heq V W χ χ' ha)).2 _ (heq V W (χ * ν) χ' (equalRankSplittingCharsAdmissible_mul_left ha hν h0))

end GlobalTheory.Mem.WeilEqRank

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteRepresentativesRowFiniteTypes
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.RowTypeReps


set_option maxHeartbeats 2000000 in
theorem reps_exist : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∃ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hI hP _ y
  have hB := hP.char.base
  have h0 := hB.models.ν0
  have hD : ∀ b, principalLevelFrame.IsotDecomp R.θ y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
      (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.e0 R.ν0 R.fd0 := by
    intro b
    obtain ⟨h1, h2⟩ := GlobalTheory.FinTypesRows.isotL_span_orth D (Yc D 0) _ R.θ (R.MY 0) y.PY y.hF (R.βY 0)
      (R.dat0 (R.toRealDat.levR F.lv2 b)) R.e0 _ _ hI (D.sp.Y_sig _) hB.models.inf y.stdPsi.1 h0.1.1 h0.2
      (GlobalTheory.Mem.R3.IsotIndep.gaL_finSum _ _ _ _ _)
    exact ⟨h1.symm, h2⟩

  have hp : ∀ b, PeterssonHilbertSpace.IsHermPos (Mult.goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
      (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.e0) (Mult.ipM (R.MY 0) R.ν0 R.fd0) := by
    intro b
    have h1 := hermPos_mono (GlobalTheory.HilbertLevels.herm_lev hI hB.models.inf (D.sp.Y_sig _) (R.MY 0) (R.βY 0)
      (R.dat0 (R.toRealDat.levR F.lv2 b)) h0.1.1 h0.2) (Submodule.map_mono (Mult.goodPart_le R.θ (R.MY 0) _ _ R.e0))
    have h2 := h1.map_equiv (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).symm
    convert h2 using 1
    · ext x
      rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
    · funext x x'
      simp only [ipMT, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]
  haveI := principalLevelFrame.finite_FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
    (fun b => levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (fun _ => R.e0) (fun _ => R.ν0) (fun _ => R.fd0) hD hp
  refine ⟨principalLevelFrame.FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
    (fun b => levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (fun _ => R.e0), principalLevelFrame.rowRepR R.θ,
    ⟨inferInstance, fun π => principalLevelFrame.rowRepR_occ R.θ π, fun π π' h => principalLevelFrame.rowRepR_inj R.θ π π' h, ?_⟩⟩
  intro ρ hρ
  exact ⟨Quotient.mk _ ⟨ρ, hρ⟩, Formalism.L2.Col.finTypRep_mk_iso ⟨ρ, hρ⟩⟩

end GlobalTheory.RowTypeReps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeOperatorKeepsRationalIntegralLevelFormsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperator_keeps_rational_integral_levelForms : ∀ (D : D7) (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E)) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (c : CoefA V) (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V), V.gram = 1 → Seed.FrmC.StdLat V → UnitFr P → RatIso P e → Formalism.AUTREP.IsAlgWeight D.host.E V.rank (wtRep c e) → (wtRep c e).IsIrreducible → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (S : CSD D.what₂.LL) (act : Representation D.what₂.LL G₀ S.Forms) (pres : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL c.coef.ρ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ) (tie : Bridge.ActTie (Bridge.ratF V) pres (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).ch act) (eG : G₀ ≃* G0 Pg D.R.r) (P₀ : Subgroup G₀) (ψ₀ : P₀ →* D.what₂.LLˣ), (∀ q : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (tie.red q) = rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _))) → ∀ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) pair del, Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → Bridge.CoefTie V c.coef pres lam c0 pair (nabAtr (labLL D) lam) del → (∀ k : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J, ∃ z : 𝓞 D.what₂.LL, D.what₂.embLL (z : D.what₂.LL) = ((levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ k : ℂ)) → ∀ B, NG.HypOutside (stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) (stdX (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) B → ∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ), s.v ∉ B → Formalism.AUTREP.IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ V.rank → ∀ x, ∃ x', (fun g => pres.ext (lvlForm S act P₀ ψ₀⁻¹ x').1 (toGf P g)) = NG.tN (stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) s ϖ k (fun g => pres.ext (lvlForm S act P₀ ψ₀⁻¹ x).1 (toGf P g)) ∧ ∀ 𝔴 : HeightOneSpectrum (𝓞 D.what₂.LL), (∀ p : ℕ, p.Prime → s.Above p → (p : 𝓞 D.what₂.LL) ∉ 𝔴.asIdeal) → x ∈ S.lvlNab act P₀ ψ₀⁻¹ → ∃ d : 𝓞 D.what₂.LL, d ∉ 𝔴.asIdeal ∧ d • x' ∈ S.lvlNab act P₀ ψ₀⁻¹ := by
  first | exact @GlobalTheory.MtInHecke.tN_lvlForm | exact GlobalTheory.MtInHecke.tN_lvlForm | (intros; apply GlobalTheory.MtInHecke.tN_lvlForm <;> assumption)
end

