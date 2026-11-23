module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0048
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexIteratedLevelChainInFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0056

@[expose] public section
set_option synthInstance.maxHeartbeats 200000

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContraAdmissibleTrace
section
noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace

namespace GlobalTheory.SmGL.ContraTrace

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]

def res (π : Representation ℂ G V) (K : Subgroup G) :
    fixed (contra π) K →ₗ[ℂ] Module.Dual ℂ (fixed π K) :=
  (fixed π K).subtype.dualMap ∘ₗ (smoothPart π.dual).subtype ∘ₗ (fixed (contra π) K).subtype

theorem invariant_of_fixed {π : Representation ℂ G V} {K : Subgroup G} (l : fixed (contra π) K)
    (h : G) (hh : h ∈ K) (w : V) : (l.1 : Module.Dual ℂ V) (π h w) = (l.1 : Module.Dual ℂ V) w := by
  have h1 := mem_fixed.1 l.2 h⁻¹ (inv_mem hh)
  conv_rhs => rw [← h1]
  rw [contra_apply, inv_inv]

theorem res_bijective [T2Space G] {π : Representation ℂ G V} (hπ : IsSmooth π) {K : Subgroup G}
    (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) : Function.Bijective (res π K) := by
  constructor
  · intro l l' h
    refine Subtype.ext (Subtype.ext ?_)
    exact IndDual.dual_ext hπ hK (invariant_of_fixed l) (invariant_of_fixed l')
      fun w hw => LinearMap.congr_fun h ⟨w, hw⟩
  · intro m
    obtain ⟨l₀, hl₀⟩ := LinearMap.exists_extend m
    obtain ⟨l, h1, h2⟩ := DualAverage.exists_invariant_form G V π hπ K hK l₀
    have h3 : ∀ g ∈ K, π.dual g l = l := fun g hg => LinearMap.ext fun w => h1 g⁻¹ (inv_mem hg) w
    refine ⟨⟨⟨l, mem_smoothPart_of_nhds (Filter.mem_of_superset (ho.mem_nhds (one_mem K)) h3)⟩,
      mem_fixed.2 fun g hg => Subtype.ext (h3 g hg)⟩, LinearMap.ext fun w => ?_⟩
    exact (h2 _ (mem_fixed.1 w.2)).trans (LinearMap.congr_fun hl₀ w)

theorem isAdmissible_contra [T2Space G] {π : Representation ℂ G V} (hπ : IsAdmissible π) :
    IsAdmissible (contra π) :=
  ⟨isSmooth_contra π, fun K ho hK =>
    haveI := hπ.2 K ho hK
    FiniteDimensional.of_injective (res π K) (res_bijective hπ.1 ho hK).1⟩

theorem smoothOp_contra [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] [μ.IsInvInvariant] {π : Representation ℂ G V} (hπ : IsSmooth π)
    {f : G → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) (l : smoothPart π.dual) (v : V) :
    (smoothOp (contra π) μ f l : Module.Dual ℂ V) v =
      (l : Module.Dual ℂ V) (smoothOp π μ (fun g => f g⁻¹) v) := by
  have h1 := (isSmooth_contra π).map_smoothOp (μ := μ) hf hc
    (Module.Dual.eval ℂ V v ∘ₗ (smoothPart π.dual).subtype) l
  have h2 := hπ.map_smoothOp (μ := μ) (f := fun g => f g⁻¹) (hf.comp_continuous continuous_inv)
    (hc.comp_homeomorph (Homeomorph.inv G)) (l : Module.Dual ℂ V) v
  refine h1.trans (Eq.trans ?_ h2.symm)
  rw [← integral_inv_eq_self]
  refine integral_congr_ae (.of_forall fun g => ?_)
  show f g⁻¹ • (l : Module.Dual ℂ V) (π g⁻¹⁻¹ v) = f g⁻¹ • (l : Module.Dual ℂ V) (π g v)
  rw [inv_inv]

theorem contra_admissible_trace : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π → IsAdmissible (contra π) ∧ ∀ f : G → ℂ, IsLocallyConstant f → HasCompactSupport f → smoothTrace (contra π) μ f = smoothTrace π μ (fun g => f g⁻¹) := by
  intro G _ _ _ _ _ _ μ _ _ hG V _ _ π hπ
  refine ⟨isAdmissible_contra hπ, fun f hf hc => ?_⟩
  have hf' : IsLocallyConstant fun g => f g⁻¹ := hf.comp_continuous continuous_inv
  have hc' : HasCompactSupport fun g => f g⁻¹ := hc.comp_homeomorph (Homeomorph.inv G)
  obtain ⟨K, ho, hK, hle⟩ := hG _ (Filter.inter_mem
    ((isOpen_leftStabilizer hf hc).mem_nhds (one_mem _))
    ((isOpen_leftStabilizer hf' hc').mem_nhds (one_mem _)))
  have := hπ.2 K ho hK
  have := (isAdmissible_contra hπ).2 K ho hK
  have m1 := (isSmooth_contra π).smoothOp_mem_fixed (μ := μ) hf hc (K := K) fun k hk => (hle hk).1
  have m2 := hπ.1.smoothOp_mem_fixed (μ := μ) hf' hc' (K := K) fun k hk => (hle hk).2
  let e := LinearEquiv.ofBijective _ (res_bijective hπ.1 ho hK)
  rw [smoothTrace, smoothTrace, finRankTrace_eq _ _ m1, finRankTrace_eq _ _ m2,
    ← LinearMap.trace_transpose' (M := fixed π K), ← LinearMap.trace_conj' _ e.symm]
  congr 1
  refine LinearMap.ext fun l => e.injective ?_
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm]
  exact LinearMap.ext fun v => smoothOp_contra μ hπ.1 hf hc l.1 v.1

end GlobalTheory.SmGL.ContraTrace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfFlagOfHermFormPreserving
section
namespace GlobalTheory.FlagEq
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem eq_of_flag_of_hermForm : ∀ {α : Type} {m : α → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : α, Fin (m τ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) → ∀ (h h' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ x y, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h x) (h y) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' x) (h' y)) → ∀ (bv : ∀ τ, Fin (m τ) → (Fin g → ℂ)) (s : ℂ), s ≠ 0 → (∀ τ i, h (Pi.single (e.symm ⟨τ, i⟩) 1) - s • bv τ i ∈ Submodule.span ℂ (bv τ '' {j | j < i})) → (∀ τ i, h' (Pi.single (e.symm ⟨τ, i⟩) 1) - s • bv τ i ∈ Submodule.span ℂ (bv τ '' {j | j < i})) → h = h' := by
  intro α m g e Hm hpos h h' hH bv s hs hh hh'
  have key : ∀ τ, ∀ i : Fin (m τ), h (Pi.single (e.symm ⟨τ, i⟩) 1) = h' (Pi.single (e.symm ⟨τ, i⟩) 1) := by
    intro τ
    let ev : Fin (m τ) → (Fin g → ℂ) := fun j => Pi.single (e.symm ⟨τ, j⟩) 1
    let E : Fin (m τ) → Submodule ℂ (Fin g → ℂ) := fun i => Submodule.span ℂ (ev '' {j | j < i})
    have ha : ∀ i, Submodule.span ℂ (bv τ '' {j | j < i}) ≤ (E i).map h'.toLinearMap := by
      intro i
      induction i using WellFoundedLT.induction with
      | _ i ih =>
        rw [Submodule.span_le]
        rintro _ ⟨j, hj, rfl⟩
        have hj : j < i := hj
        have h1 : h' (ev j) ∈ (E i).map h'.toLinearMap :=
          Submodule.mem_map_of_mem (Submodule.subset_span ⟨j, hj, rfl⟩)
        have h2 : h' (ev j) - s • bv τ j ∈ (E i).map h'.toLinearMap := by
          have := ih j hj (hh' τ j)
          have hsub : {k : Fin (m τ) | k < j} ⊆ {k | k < i} := by
            intro k hk
            exact lt_trans hk hj
          exact Submodule.map_mono (Submodule.span_mono (Set.image_mono hsub)) this
        have h3 : s • bv τ j ∈ (E i).map h'.toLinearMap := by
          have := Submodule.sub_mem _ h1 h2
          simpa using this
        have := Submodule.smul_mem _ s⁻¹ h3
        rw [smul_smul, inv_mul_cancel₀ hs, one_smul] at this
        exact this
    intro i
    induction i using WellFoundedLT.induction with
    | _ i ih =>
      have hon : Set.EqOn h.toLinearMap h'.toLinearMap (E i) := by
        apply LinearMap.eqOn_span'
        rintro _ ⟨j, hj, rfl⟩
        exact ih j hj
      set u := h (ev i) - h' (ev i) with hu
      have hu' : u = (h (ev i) - s • bv τ i) - (h' (ev i) - s • bv τ i) := by
        rw [hu]; abel
      have huB : u ∈ Submodule.span ℂ (bv τ '' {j | j < i}) := by
        rw [hu']; exact Submodule.sub_mem _ (hh τ i) (hh' τ i)
      obtain ⟨v, hvE, hv⟩ := ha i huB
      have hv' : h' v = u := hv
      have hhv : h v = u := by
        rw [← hv']; exact hon hvE
      have hx : h (ev i) = h' (ev i) + u := by rw [hu]; abel
      have hE := hH (ev i) v
      rw [hhv, hv', hx] at hE
      have h0 : hermForm Hm u u = 0 := by
        unfold hermForm at hE ⊢
        rw [add_dotProduct] at hE
        simpa using hE
      by_contra hne
      have hne' : u ≠ 0 := by
        intro h0'; apply hne; rw [hu] at h0'; exact sub_eq_zero.mp h0'
      have := hpos u hne'
      rw [h0] at this
      simp at this
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun ℂ (Fin g)).ext
  intro n
  rw [Pi.basisFun_apply]
  have := key (e n).1 (e n).2
  simpa using this

end GlobalTheory.FlagEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsParabolicDoubleCosetFunctionEqOneStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parabolicDoubleCosetFunction_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k), (∀ g ∈ prX (Cgrp J h), deltaR c g = 1) → ∃ f, IsCosetFn J h f ∧ f h = 1 := by
  first | exact @GlobalTheory.CosetFn.exists_isCosetFn | exact GlobalTheory.CosetFn.exists_isCosetFn | (intros; apply GlobalTheory.CosetFn.exists_isCosetFn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexIteratedLevelChainInFrameStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstVertex_iteratedLevelChain_in_frame :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (ϖ : kˣ) (s : ℕ) (t : Type) [Fintype t] [DecidableEq t]
      (κ : ℕ) (P : _root_.GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin (s + 1))),
    ((∀ u ∈ N k (Fin κ) (s + 1) 1, ∀ γ : GL (Fin κ) k,
        u * embX (s + 1) γ ∈ P.J → ∃ gb, Reduces γ gb ∧ IsUpperUnip Fin.val gb.val) ∧
      (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), Reduces γ gb → IsUpperUnip Fin.val gb.val →
        ∃ hm : embX (s + 1) γ ∈ P.J,
          (P.lam ⟨_, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * superSum Fin.val γ.val)) ∧
      ∀ u ∈ N k (Fin κ) (s + 1) 1, ∀ hm : u ∈ P.J,
        (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * simpleSum u)) →
    ∀ (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (c : ℕ) (H : 0 + c = s + 1),
      (prX (Cgrp ((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).J 1) :
        Set (GL (XIx (Fin κ) t 0) k)) = colGroup (k := k) κ t ∧
      (∀ γ ∈ colGroup (k := k) κ t,
        ∃ hm : embX c γ ∈ ((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).J,
          (((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).lam ⟨_, hm⟩ : ℂ) =
            colChar ψ ϖ γ) ∧
      ∀ u ∈ N k (XIx (Fin κ) t 0) c 1,
        ∀ hm : u ∈ ((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).J,
          (((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).lam ⟨u, hm⟩ : ℂ) =
            ψ (simpleSum u) := by
  first | exact @GlobalTheory.FirstVertexFrame.firstVertex_typeChain | exact GlobalTheory.FirstVertexFrame.firstVertex_typeChain | (intros; apply GlobalTheory.FirstVertexFrame.firstVertex_typeChain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorMovedTensorFinsetSumLinearStatement
section
open MeasureTheory GlobalTheory.FunObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatTensor_movedTensor_finset_sum_linear : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : GlobalTheory.SplitFlip.Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], Continuous ψ → ∀ (ϖ : kˣ) (e : ℕ) (keep : Bool) (g : G.VertexGroup) {ι : Type} (S : Finset ι) (x : ι → ℂ) (T : ι → G.Args → ℂ), (∀ i ∈ S, G.IsTensor ϖ e (GlobalTheory.SplitFlip.oppositePath G.m) (T i)) → ∀ X Y, flatTensor hs ψ ν (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y = ∑ i ∈ S, x i * flatTensor hs ψ ν (moved G keep g (T i)) X Y := by
  first | exact @GlobalTheory.FunObj.flatTensor_moved_sum | exact GlobalTheory.FunObj.flatTensor_moved_sum | (intros; apply GlobalTheory.FunObj.flatTensor_moved_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericLevelOfFrameBlockAndCharacterStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericLevelOfFrame_block_and_character :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (ϖ : kˣ) (κ l : ℕ)
      (P : _root_.GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l)),
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsGenericLevel ψ ϖ P →
        ((∀ u ∈ N k (Fin κ) l 1, ∀ γ : GL (Fin κ) k, u * embX l γ ∈ P.J →
            ∃ gb, Reduces γ gb ∧ IsUpperUnip Fin.val gb.val) ∧
          (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), Reduces γ gb →
            IsUpperUnip Fin.val gb.val → ∃ hm : embX l γ ∈ P.J,
              (P.lam ⟨_, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * superSum Fin.val γ.val)) ∧
          ∀ u ∈ N k (Fin κ) l 1, ∀ hm : u ∈ P.J,
            (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * simpleSum u)) := by
  intro k _ _ _ _ ψ ϖ κ l P h
  have map_residue_apply {a : Type} [Fintype a] [DecidableEq a] (M : GL a 𝒪[k]) (i j : a) :
      ((GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) M : GL a 𝓀[k]) : Matrix a a 𝓀[k]) i j =
        IsLocalRing.residue 𝒪[k] ((M : Matrix a a 𝒪[k]) i j) := by
    simp

  have reduces_of_corner {g : GL (Fin κ ⊕ Fin l) k} {γ : GL (Fin κ) k}
      {g₀ : GL (Fin κ ⊕ Fin l) 𝒪[k]} (hg : GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀ = g)
      (hγ : (g : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k).toBlocks₁₁ = γ)
      (hres : ∀ r s : Fin κ, s ≤ r → IsLocalRing.residue 𝒪[k]
        ((g₀ : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) 𝒪[k]) (Sum.inl r) (Sum.inl s)) =
          (1 : Matrix (Fin κ) (Fin κ) 𝓀[k]) r s) :
      ∃ gb, Reduces γ gb ∧
        IsUpperUnip Fin.val (gb : Matrix (Fin κ) (Fin κ) 𝓀[k]) := by
    subst hg
    set A : Matrix (Fin κ) (Fin κ) 𝒪[k] :=
      (g₀ : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) 𝒪[k]).toBlocks₁₁
    have hB : ∀ r s, s ≤ r → IsLocalRing.residue 𝒪[k] (A r s) = (1 : Matrix (Fin κ) (Fin κ) 𝓀[k]) r s :=
      hres
    have hdet : IsUnit A.det := by
      have : IsLocalRing ↥𝒪[k] := ValuationRing.isLocalRing _
      apply IsLocalRing.notMem_maximalIdeal.1
      intro hm
      rw [← IsLocalRing.residue_eq_zero_iff, RingHom.map_det, Matrix.det_of_isUpperTriangular] at hm
      · have hp : ∏ i, (IsLocalRing.residue 𝒪[k]).mapMatrix A i i = 1 :=
          Finset.prod_eq_one fun i _ => by simp [RingHom.mapMatrix_apply, hB i i le_rfl]
        rw [hp] at hm
        exact one_ne_zero hm
      · intro i j hij
        have hij' : j < i := hij
        simp [RingHom.mapMatrix_apply, hB i j hij'.le, Matrix.one_apply_ne (ne_of_lt hij').symm]
    let γ₀ : GL (Fin κ) 𝒪[k] := A.nonsingInvUnit hdet
    refine ⟨GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) γ₀, ⟨γ₀, ?_, rfl⟩, ?_⟩
    · ext i j
      rw [← hγ]
      rfl
    · intro r s hsr
      rw [map_residue_apply]
      exact hres r s hsr

  have toBlocks₁₁_mul_embX_of_mem_N {u : GL (Fin κ ⊕ Fin l) k} (hu : u ∈ N k (Fin κ) l 1)
      (γ : GL (Fin κ) k) :
      ((u * embX l γ : GL (Fin κ ⊕ Fin l) k) :
        Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k).toBlocks₁₁ = γ := by
    rw [Units.val_mul, _root_.GlobalTheory.StepData.mul_toBlocks₁₁, _root_.GlobalTheory.RootEx.Radical.toBlocks₁₁_of_mem hu,
      _root_.GlobalTheory.RootEx.Radical.embX_val]
    simp

  have one_apply_inl_inl (r s : Fin κ) :
      (1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) 𝓀[k]) (Sum.inl r) (Sum.inl s) =
        (1 : Matrix (Fin κ) (Fin κ) 𝓀[k]) r s := by
    by_cases h : r = s <;> simp [Matrix.one_apply, h]

  have reduces_embX_of_reduces {γ : GL (Fin κ) k}
      {gb : GL (Fin κ) 𝓀[k]} (h : Reduces γ gb) :
      Reduces (embX l γ)
        (embX l gb) := by
    obtain ⟨γ₀, h₁, h₂⟩ := h
    subst h₁ h₂
    let g₀ : GL (Fin κ ⊕ Fin l) 𝒪[k] :=
      ⟨fromBlocks (γ₀ : Matrix (Fin κ) (Fin κ) 𝒪[k]) 0 0 1,
        fromBlocks ((γ₀⁻¹ : GL (Fin κ) 𝒪[k]) : Matrix (Fin κ) (Fin κ) 𝒪[k]) 0 0 1,
        by rw [fromBlocks_multiply]; simp, by rw [fromBlocks_multiply]; simp⟩
    refine ⟨g₀, ?_, ?_⟩ <;> ext i j <;> rcases i with i | i <;> rcases j with j | j <;>
      simp [g₀, _root_.GlobalTheory.RootEx.Radical.embX_val, Matrix.one_apply, apply_ite]

  have one_apply_inr_inr (r s : Fin l) :
      (1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) 𝓀[k]) (Sum.inr r) (Sum.inr s) =
        (1 : Matrix (Fin l) (Fin l) 𝓀[k]) r s := by
    by_cases h : r = s <;> simp [Matrix.one_apply, h]

  have hl (i : Fin κ) : framePos κ l (Sum.inl i) = i := rfl
  have hr (i : Fin l) : framePos κ l (Sum.inr i) = κ + i := rfl

  have superSum_framePos_embX (γ : GL (Fin κ) k) :
      superSum (framePos κ l)
          ((embX l γ : GL (Fin κ ⊕ Fin l) k) :
            Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) =
        superSum Fin.val (γ : Matrix (Fin κ) (Fin κ) k) := by
    unfold superSum
    simp only [Fintype.sum_sum_type, _root_.GlobalTheory.RootEx.Radical.embX_val, hl, hr,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply,
      ite_self, Finset.sum_const_zero, add_zero, zero_add]
    have h : ∑ i : Fin l, ∑ j : Fin l,
        (if κ + (j : ℕ) = κ + i + 1 then (1 : Matrix (Fin l) (Fin l) k) i j else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      split_ifs with hij
      · exact Matrix.one_apply_ne fun h => by subst h; omega
      · rfl
    linear_combination h

  have superSum_framePos_eq_simpleSum_of_mem_N {u : GL (Fin κ ⊕ Fin l) k} (hu : u ∈ N k (Fin κ) l 1) :
      superSum (framePos κ l)
          (u : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) =
        simpleSum u := by
    rw [_root_.GlobalTheory.RootEx.Model.mem_N_iff] at hu
    unfold InN at hu
    unfold superSum simpleSum
    simp only [Fintype.sum_sum_type, hl, hr]
    have h₁ : ∑ i : Fin κ, ∑ j : Fin κ, (if (j : ℕ) = i + 1 then
        (u : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) (Sum.inl i) (Sum.inl j) else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      split_ifs with hij
      · rw [hu _ _ (by simp [lev])]
        exact Matrix.one_apply_ne fun h => by
          have := congrArg (fun x : Fin κ ⊕ Fin l => Sum.elim (fun a : Fin κ => (a : ℕ)) (fun _ => 0) x) h
          simp at this
          omega
      · rfl
    have h₂ : ∑ i : Fin κ, ∑ j : Fin l, (if κ + (j : ℕ) = i + 1 then
        (u : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) (Sum.inl i) (Sum.inr j) else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      split_ifs with hij
      · rw [hu _ _ (by simp [lev]; omega)]
        simp
      · rfl
    have h₃ : ∑ i : Fin l, ∑ j : Fin κ, (if (j : ℕ) = κ + i + 1 then
        (u : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) (Sum.inr i) (Sum.inl j) else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      rw [ite_eq_right (by omega)]
    have h₄ : ∀ i j : Fin l, (κ + (j : ℕ) = κ + i + 1) ↔ ((j : ℕ) = i + 1) := fun i j => by omega
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [h₄]
    linear_combination h₁ + h₂ + h₃
  unfold IsGenericLevel at h
  obtain ⟨hJ, hlam⟩ := h
  refine ⟨fun u hu γ hm => ?_, fun γ gb hred hup => ?_, fun u hu hm => ?_⟩
  · obtain ⟨gb', ⟨g₀, hg₀, hres₀⟩, hup'⟩ := (hJ _).1 hm
    refine reduces_of_corner hg₀ (toBlocks₁₁_mul_embX_of_mem_N hu γ) fun r s hsr => ?_
    rw [← map_residue_apply, hres₀]
    exact (hup' (Sum.inl r) (Sum.inl s) (by simpa [framePos] using hsr)).trans
      (one_apply_inl_inl r s)
  · have hm : embX l γ ∈ P.J := by
      refine (hJ _).2 ⟨embX l gb, reduces_embX_of_reduces hred, ?_⟩
      intro r s hrs
      rcases r with r | r <;> rcases s with s | s
      · have h' : (s : ℕ) ≤ r := by simpa [framePos] using hrs
        rw [_root_.GlobalTheory.RootEx.Radical.embX_val, fromBlocks_apply₁₁]
        exact (hup r s h').trans (one_apply_inl_inl r s).symm
      · have h' : κ + (s : ℕ) ≤ r := by simpa [framePos] using hrs
        omega
      · rw [_root_.GlobalTheory.RootEx.Radical.embX_val, fromBlocks_apply₂₁]
        simp
      · rw [_root_.GlobalTheory.RootEx.Radical.embX_val, fromBlocks_apply₂₂]
        exact (one_apply_inr_inr r s).symm
    refine ⟨hm, ?_⟩
    rw [hlam ⟨_, hm⟩]
    simp only [superSum_framePos_embX]
  · rw [hlam ⟨u, hm⟩, superSum_framePos_eq_simpleSum_of_mem_N hu]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermFormEqOfImEqOnSpanningLattice
section
namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable def hermFormImPullback {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm (h y) (h w)).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by
      rw [show h (c • a) = (c : ℂ) • h a by rw [← map_smul]; rfl]
      simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      rw [show h (c • a) = (c : ℂ) • h a by rw [← map_smul]; rfl]
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul])

theorem hermForm_eq_of_im_eq_on_spanning_lattice :
    ∀ {g : ℕ} {L : Type} [AddCommGroup L] (P : L →+ (Fin g → ℂ)), Submodule.span ℝ (Set.range P) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (h h' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ a b, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h (P a)) (h (P b))).im = (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' (P a)) (h' (P b))).im) → ∀ x y, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h x) (h y) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' x) (h' y) := by
  intro g L _ P hsp Hm h h' hab
  have hB : hermFormImPullback Hm h = hermFormImPullback Hm h' := by
    refine LinearMap.ext_on hsp ?_
    rintro _ ⟨a, rfl⟩
    refine LinearMap.ext_on hsp ?_
    rintro _ ⟨b, rfl⟩
    exact hab a b
  have him : ∀ x y, (hermForm Hm (h x) (h y)).im = (hermForm Hm (h' x) (h' y)).im := by
    intro x y
    exact LinearMap.congr_fun₂ hB x y
  intro x y
  have hI : ∀ (k : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (hermForm Hm (k (Complex.I • x)) (k y)).im = (hermForm Hm (k x) (k y)).re := by
    intro k
    simp [hermForm, map_smul, smul_dotProduct]
  apply Complex.ext
  · rw [← hI h, ← hI h']
    exact him _ _
  · exact him x y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralTranslateIndicatorStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_indicator_Cgrp_translate_eq_deltaR_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ), 1 ≤ c → ∀ (J : Subgroup (GL (n ⊕ Fin c) k)), IsCO J → ∀ (h : GL (n ⊕ Fin c) k), IsCO (prX (Cgrp J h)) → ∀ (m : Measure (GL n k)) [m.IsHaarMeasure], ∀ u₀ ∈ N k n c 1, ∀ g₀ : GL n k, ∫ g, (∫ u : N k n c 1, (Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (embX c g * (u : GL (n ⊕ Fin c) k) * (u₀ * embX c g₀)) ∂(volN ν n c 1)) ∂m = ((deltaR c g₀ * ((volN ν n c 1 ((Cgrp J h).subgroupOf (N k n c 1))).toReal * (m (prX (Cgrp J h))).toReal) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.StepAvg.integral_translate_indicator | exact GlobalTheory.StepAvg.integral_translate_indicator | (intros; apply GlobalTheory.StepAvg.integral_translate_indicator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCOPrXCgrpStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCO_prX_Cgrp_and_det_valuation_deltaR_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)), IsCO J → ∀ h : GL (n ⊕ Fin c) k, IsCO (prX (Cgrp J h)) ∧ ∀ g ∈ prX (Cgrp J h), valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 ∧ deltaR c g = 1 := by
  first | exact @GlobalTheory.PrCompactOpen.isCO_prX_Cgrp | exact GlobalTheory.PrCompactOpen.isCO_prX_Cgrp | (intros; apply GlobalTheory.PrCompactOpen.isCO_prX_Cgrp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsQuotIntCosetFnStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQuotInt_cosetFn_alt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)), IsCO J → ∀ (h : GL (n ⊕ Fin c) k) (m : Measure (GL n k)) (v : ℝ), v ≠ 0 → (∀ u₀ ∈ N k n c 1, ∀ g₀ : GL n k, ∫ g, (∫ u : N k n c 1, (Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (embX c g * (u : GL (n ⊕ Fin c) k) * (u₀ * embX c g₀)) ∂(volN ν n c 1)) ∂m = ((deltaR c g₀ * v : ℝ) : ℂ)) → ∀ (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f : GL (n ⊕ Fin c) k → ℂ), IsCosetFn J h f → IsQuotInt ν m μG 1 f ((((μG J).toReal / v : ℝ) : ℂ) * f h) := by
  first | exact @GlobalTheory.CosetQuotInt.isQuotInt_cosetFn | exact GlobalTheory.CosetQuotInt.isQuotInt_cosetFn | (intros; apply GlobalTheory.CosetQuotInt.isQuotInt_cosetFn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentExistsResidueCardPowMemNhdsStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootExchangeUnipotent_exists_residueCardPow_mem_nhds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), (resCard k).Prime → ∀ u ∈ N k n c p, ∀ U ∈ 𝓝 (1 : GL (n ⊕ Fin c) k), ∃ m : ℕ, u ^ (resCard k ^ m) ∈ U := by
  first | exact @GlobalTheory.RootEx.UnipPow.exists_pow_mem_nhds | exact GlobalTheory.RootEx.UnipPow.exists_pow_mem_nhds | (intros; apply GlobalTheory.RootEx.UnipPow.exists_pow_mem_nhds <;> assumption)
end

