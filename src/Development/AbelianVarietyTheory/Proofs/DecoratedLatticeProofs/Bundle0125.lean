module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0114
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittFlagUnipotentFixerFundamentalDomainLayersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittFlagUnipotentFixer_fundamentalDomain_layers : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d), (∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1)) → ∀ (lC : Measure (skewA D ρ)) (𝓒 : Set (skewA D ρ)), lC.IsAddHaarMeasure → SFinite lC → IsAddFundamentalDomain ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) 𝓒 lC → ∀ (vb : VolM D ρ V₀.rank) (ν : Measure (UX D ρ)), SFinite vb.μ → SFinite ν → IsFundamentalDomain ((GQ V ⊓ radX d).subgroupOf (flagN d)) (e '' (𝓒 ×ˢ (vb.𝓕 ×ˢ Set.univ))) ((lC.prod (vb.μ.prod ν)).map e) := by
  intro D V V₀ ρ d e he lC 𝓒 _ _ hC vb ν _ _
  have : IsTopologicalAddGroup (Mx D ρ ρ) := (lattice_Mx D ρ ρ).1
  have : SecondCountableTopology (Mx D ρ ρ) := (lattice_Mx D ρ ρ).2.2.1
  have : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Mx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).1
  have : SecondCountableTopology (Mx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).2.2.1
  have : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  have : DiscreteTopology (ratMx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).2.2.2.2.1
  have : Countable (ratMx D ρ V₀.rank) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  have : SecondCountableTopology (skewA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  have : IsTopologicalAddGroup (skewA D ρ) := inferInstance
  have : MeasurableAdd₂ (skewA D ρ) := ⟨continuous_add.measurable⟩
  have rat_coords {b : Mx D ρ V₀.rank} {c : skewA D ρ}
      (h : d.nB b * d.nC c ∈ GQ V) : b ∈ ratMx D ρ V₀.rank ∧ c.1 ∈ ratMx D ρ ρ := by
    have hm := (mem_GQ_iff V _).1 h
    have hb : b ∈ ratMx D ρ V₀.rank := by
      have e1 : d.pX ⬝ (mt V (d.nB b * d.nC c) ⬝ d.j0) = b := by
        rw [mt_mul, Matrix.mul_assoc, d.nC_j0, d.nB_j0, Matrix.mul_add, d.pX_j0, ← Matrix.mul_assoc, d.pX_jX,
          Matrix.one_mul, zero_add]
      rw [← e1]
      exact ratMx_mul (rat_mem _) (ratMx_mul hm (rat_mem _))
    refine ⟨hb, ?_⟩
    have hc : d.nC c ∈ GQ V := by
      have := mul_mem (inv_mem (d.nB_mem_GQ hb)) h
      rwa [inv_mul_cancel_left] at this
    have hm2 := (mem_GQ_iff V _).1 hc
    have e2 : d.pX ⬝ (mt V (d.nC c) ⬝ d.jY) = c.1 := by
      rw [d.nC_jY, Matrix.mul_add, d.pX_jY, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul, zero_add]
    rw [← e2]
    exact ratMx_mul (rat_mem _) (ratMx_mul hm2 (rat_mem _))
  have act_coords (c' c : skewA D ρ) (b' b : Mx D ρ V₀.rank) (u : GL (Fin ρ) (AE D)) :
      d.nC c' * d.nB b' * (d.nC c * (d.nB b * d.levi u)) =
        d.nC (c' + c + cComm V₀ b' b) * (d.nB (b' + b) * d.levi u) := by
    have h1 : d.nB b' * d.nC c = d.nC c * d.nB b' := (d.nC_mul_nB b' c).symm
    have h2 : d.nB (b' + b) * d.nC (cComm V₀ b' b) = d.nC (cComm V₀ b' b) * d.nB (b' + b) :=
      (d.nC_mul_nB _ _).symm
    calc d.nC c' * d.nB b' * (d.nC c * (d.nB b * d.levi u))
        = d.nC c' * (d.nB b' * d.nC c) * d.nB b * d.levi u := by simp only [mul_assoc]
      _ = d.nC c' * d.nC c * (d.nB b' * d.nB b) * d.levi u := by rw [h1]; simp only [mul_assoc]
      _ = d.nC c' * d.nC c * d.nC (cComm V₀ b' b) * d.nB (b' + b) * d.levi u := by
          rw [d.nB_mul_nB, h2]; simp only [mul_assoc]
      _ = d.nC (c' + c + cComm V₀ b' b) * (d.nB (b' + b) * d.levi u) := by
          rw [d.nC_add, d.nC_add]; simp only [mul_assoc]
  have mem_radX_iff (n : GA D V) : n ∈ radX d ↔ ∃ b c, n = d.nB b * d.nC c := by
    constructor
    · intro hn
      obtain ⟨hf, hx⟩ := Subgroup.mem_inf.1 hn
      obtain ⟨⟨c, b, u⟩, hu⟩ := e.surjective ⟨n, hf⟩
      have hn' : n = d.nC c * (d.nB b * d.levi u.1) :=
        (congrArg Subtype.val hu).symm.trans (he (c, b, u))
      change mt V n ⬝ d.jX = d.jX at hx
      have hX : mt V n ⬝ d.jX = d.jX ⬝ u.1.1 := by
        rw [hn', mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.levi_jX,
          ← Matrix.mul_assoc (mt V (d.nB b)), d.nB_jX,
          ← Matrix.mul_assoc (mt V (d.nC c)), d.nC_jX]
      have hmat : d.pX ⬝ (d.jX ⬝ u.1.1) = d.pX ⬝ d.jX :=
        congrArg (fun X => d.pX ⬝ X) (hX.symm.trans hx)
      rw [← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul] at hmat
      have hu' : u.1 = 1 := Units.ext hmat
      exact ⟨b, c, by rw [hn', hu', map_one, mul_one, d.nC_mul_nB]⟩
    · rintro ⟨b, c, rfl⟩
      refine Subgroup.mem_inf.2 ⟨mul_mem (d.nB_mem_NFlag b) (d.nC_mem_NFlag c), ?_⟩
      change mt V (d.nB b * d.nC c) ⬝ d.jX = d.jX
      rw [mt_mul, Matrix.mul_assoc, d.nC_jX, d.nB_jX]
  have hκ : ∀ b' : Mx D ρ V₀.rank, Measurable (cComm V₀ b') := by
    intro b'
    have : ContinuousSub (Mx D ρ ρ) := IsTopologicalAddGroup.to_continuousSub
    have hp : Continuous (plus V₀ : Mx D ρ V₀.rank → _) := continuous_const.matrix_mul continuous_adj
    have h1 : Continuous fun b : Mx D ρ V₀.rank => half D • (b ⬝ plus V₀ b' - b' ⬝ plus V₀ b) :=
      ((continuous_id.matrix_mul continuous_const).sub (continuous_const.matrix_mul hp)).const_smul (half D)
    exact (h1.subtype_mk _).measurable
  have key : ∀ (c' : skewA D ρ) (b' : Mx D ρ V₀.rank) (p : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ)),
      d.nC c' * d.nB b' * (e p : GA D V) = (e (c' + p.1 + cComm V₀ b' p.2.1, b' + p.2.1, p.2.2) : GA D V) := by
    intro c' b' p
    rw [he p, he (c' + p.1 + cComm V₀ b' p.2.1, b' + p.2.1, p.2.2)]
    exact act_coords c' p.1 b' p.2.1 p.2.2.1
  have hsm : ∀ (g : ↥((GQ V ⊓ radX d).subgroupOf (flagN d))) (x : flagN d),
      ((g • x : flagN d) : GA D V) = ((g : flagN d) : GA D V) * (x : GA D V) := fun _ _ => rfl
  refine GlobalTheory.Layers.isFundamentalDomain_layers (mA := lC) (mB := vb.μ) (ν := ν) ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) (ratMx D ρ V₀.rank) (cComm V₀) hκ e
    ?_ ?_ ?_ hC vb.covol.2.1
  · intro g g' x h
    rw [Subgroup.smul_def, Subgroup.smul_def] at h
    exact Subtype.ext (mul_right_cancel h)
  · rintro ⟨⟨γ, hγN⟩, hγ⟩
    rw [Subgroup.mem_subgroupOf] at hγ
    obtain ⟨b, c, hbc⟩ := (mem_radX_iff γ).1 (Subgroup.mem_inf.1 hγ).2
    subst hbc
    have hr := rat_coords (Subgroup.mem_inf.1 hγ).1
    refine ⟨⟨c, AddSubgroup.mem_addSubgroupOf.2 hr.2⟩, ⟨b, hr.1⟩, fun p => Subtype.ext ?_⟩
    rw [Subgroup.smul_def]
    have h := key c b p
    rw [d.nC_mul_nB] at h
    exact h
  · rintro ⟨c', hc'⟩ ⟨b', hb'⟩
    have hrad : d.nC c' * d.nB b' ∈ radX d := (mem_radX_iff _).2 ⟨b', c', d.nC_mul_nB b' c'⟩
    have hQ : d.nC c' * d.nB b' ∈ GQ V :=
      mul_mem (d.nC_mem_GQ (AddSubgroup.mem_addSubgroupOf.1 hc')) (d.nB_mem_GQ hb')
    have hN : d.nC c' * d.nB b' ∈ flagN d := (Subgroup.mem_inf.1 hrad).1
    let g : ((GQ V ⊓ radX d).subgroupOf (flagN d)) :=
      ⟨⟨d.nC c' * d.nB b', hN⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hQ, hrad⟩)⟩
    refine ⟨g, fun p => Subtype.ext ((hsm g (e p)).trans (key c' b' p))⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedCoordsConjHermitianAdjoint
section
namespace I195MixedCoordinates_8df3303fbb03152b340aba95

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_8df3303fbb03152b340aba95

public noncomputable abbrev _root_.I195MixedCoordinates_79cab7195843a34bfe21655d.source :=
  @_root_.I195MixedCoordinates_8df3303fbb03152b340aba95.source

public noncomputable abbrev _root_.I195MixedCoordinates_79cab7195843a34bfe21655d.target :=
  @_root_.I195MixedCoordinates_8df3303fbb03152b340aba95.target

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.MixSwap

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger (dagger dagger_dagger cj)

variable {D : D7}

theorem dagger_add (S T : HSp D) (x y : WO S T) : dagger S T (x + y) = dagger S T x + dagger S T y := by
  simp only [dagger, adj_add, Matrix.add_mul, Matrix.mul_add]

theorem hO_dagger (S T : HSp D) (x y : WO S T) : hO T S (dagger S T x) (dagger S T y) = hO S T y x := by
  simp only [hO_eq_trace, dagger, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_gA_cancel]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem symplOH_dagger (S T : HSp D) (x y : WO S T) :
    symplOH T S (dagger S T x) (dagger S T y) = -symplOH S T x y := by
  rw [symplOH_eq, hO_dagger, ← symplOH_eq, symplOH_skew]

theorem conj_psi_of_std {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h3 : ψ a * starRingEnd ℂ (ψ a) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
  have hne : ψ a ≠ 0 := by intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  exact mul_left_cancel₀ hne (h3.trans h2.symm)

theorem adelicConj_incl_neg_inv_hermitianScalar : cA D (incA D (-D.host.xi0⁻¹)) = incA D D.host.xi0⁻¹ := by
  rw [GlobalTheory.DualPairCheck.cA_incA, star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, neg_neg]

section Target

variable {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)

theorem dagger_incAdj (y : Mx D S.rank ρ) :
    dagger S T (d.incAdj S y) = d.extX S (incA D D.host.xi0⁻¹ • y) := by
  rw [dagger, HypDec.incAdj_apply, HypDec.incY_apply, HypDec.extX_apply, d.pX_eq, adj_mul, adj_smul, adj_mul, adj_adj,
    adj_gA, adelicConj_incl_neg_inv_hermitianScalar]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, giA_gA_cancel]

theorem dagger_incX (ξ : Mx D ρ S.rank) : dagger S T (d.incX S ξ) = d.extY S (giA S ⬝ adj ξ) := by
  simp only [dagger, HypDec.incX_apply, HypDec.extY_apply, d.pY_eq, adj_mul, Matrix.mul_assoc]

theorem hermitianAdjointHomSpace_wittCoreInclusion (w : WO S T₀) : dagger S T (d.inc0 S w) = d.ext0 S (dagger S T₀ w) := by
  simp only [dagger, HypDec.wittDecomp_inclAnisotropicHom_apply, HypDec.matrixExtendByZero_apply, d.p0_eq, adj_mul, Matrix.mul_assoc, gA_giA_cancel]

end Target

end GlobalTheory.MixSwap

end

noncomputable section

namespace GlobalTheory.MixSwap

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger (dagger dagger_dagger cj)
open scoped Pointwise

variable {D : D7}

theorem borelMx (m n : ℕ) : BorelSpace (Mx D m n) := ⟨rfl⟩

attribute [local instance] borelMx

def adjE (S : HSp D) (ρ : ℕ) : Mx D ρ S.rank ≃+ Mx D S.rank ρ where
  toFun ξ := giA S ⬝ adj ξ
  invFun a := adj (gA S ⬝ a)
  left_inv ξ := by simp only [gA_giA_cancel, adj_adj]
  right_inv a := by simp only [adj_adj, giA_gA_cancel]
  map_add' ξ ξ' := by simp only [adj_add, Matrix.mul_add]

theorem continuous_adjE (S : HSp D) (ρ : ℕ) : Continuous (adjE S ρ) :=
  continuous_const.matrix_mul continuous_adj

theorem continuous_adjE_symm (S : HSp D) (ρ : ℕ) : Continuous (adjE S ρ).symm :=
  continuous_adj.comp (continuous_const.matrix_mul continuous_id)

def adjM (S : HSp D) (ρ : ℕ) : Mx D ρ S.rank ≃ᵐ Mx D S.rank ρ :=
  (Homeomorph.mk (adjE S ρ).toEquiv (continuous_adjE S ρ) (continuous_adjE_symm S ρ)).toMeasurableEquiv

theorem coe_adjM (S : HSp D) (ρ : ℕ) : ⇑(adjM S ρ) = ⇑(adjE S ρ) := rfl

theorem coe_adjM_symm (S : HSp D) (ρ : ℕ) : ⇑(adjM S ρ).symm = ⇑(adjE S ρ).symm := rfl

theorem adjE_mem {S : HSp D} {ρ : ℕ} {ξ : Mx D ρ S.rank} (h : ξ ∈ ratMx D ρ S.rank) : adjE S ρ ξ ∈ ratMx D S.rank ρ :=
  ratMx_mul (rat_mem _) (ratMx_adj h)

theorem adjE_symm_mem {S : HSp D} {ρ : ℕ} {a : Mx D S.rank ρ} (h : a ∈ ratMx D S.rank ρ) :
    (adjE S ρ).symm a ∈ ratMx D ρ S.rank :=
  ratMx_adj (ratMx_mul (rat_mem _) h)

theorem isCovolOne_map {S : HSp D} {ρ : ℕ} {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)}
    (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) :
    IsCovolOne (ratMx D S.rank ρ) (μ.map (adjM S ρ)) (adjM S ρ '' 𝓕) := by
  obtain ⟨hH, hF, h1⟩ := hμ
  have P : MeasurePreserving (adjM S ρ) μ (μ.map (adjM S ρ)) := (adjM S ρ).measurable.measurePreserving μ
  have Q : MeasurePreserving (adjM S ρ).symm (μ.map (adjM S ρ)) μ := P.symm (adjM S ρ)
  refine ⟨?_, ?_, ?_⟩
  · rw [coe_adjM]
    exact (adjE S ρ).isAddHaarMeasure_map μ (continuous_adjE S ρ) (continuous_adjE_symm S ρ)
  · rw [MeasurableEquiv.image_eq_preimage_symm]
    refine ⟨hF.nullMeasurableSet.preimage Q.quasiMeasurePreserving, ?_, ?_⟩
    · filter_upwards [Q.quasiMeasurePreserving.ae hF.ae_covers] with a ha
      obtain ⟨g, hg⟩ := ha
      refine ⟨⟨adjE S ρ g, adjE_mem g.2⟩, ?_⟩
      rw [Set.mem_preimage, AddSubgroup.vadd_def, vadd_eq_add, coe_adjM_symm, map_add (f := _),
        AddEquiv.symm_apply_apply]
      rw [AddSubgroup.vadd_def, vadd_eq_add, coe_adjM_symm] at hg
      exact hg
    · have key : ∀ g : ratMx D S.rank ρ, g +ᵥ ((adjM S ρ).symm ⁻¹' 𝓕) =
          (adjM S ρ).symm ⁻¹' ((⟨(adjE S ρ).symm g, adjE_symm_mem g.2⟩ : ratMx D ρ S.rank) +ᵥ 𝓕) := by
        intro g
        ext x
        simp only [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem, AddSubgroup.vadd_def, vadd_eq_add,
          coe_adjM_symm, map_add, map_neg]
      intro g g' hne
      have hne' : (⟨(adjE S ρ).symm g, adjE_symm_mem g.2⟩ : ratMx D ρ S.rank) ≠ ⟨(adjE S ρ).symm g', adjE_symm_mem g'.2⟩ := by
        intro h
        apply hne
        exact Subtype.ext ((adjE S ρ).symm.injective (congrArg Subtype.val h))
      show AEDisjoint _ (g +ᵥ _) (g' +ᵥ _)
      rw [key g, key g']
      exact (hF.aedisjoint hne').preimage Q.quasiMeasurePreserving
  · rw [MeasurableEquiv.map_apply, MeasurableEquiv.preimage_image, h1]

end GlobalTheory.MixSwap

end

noncomputable section

namespace GlobalTheory.MixSwap

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger (dagger dagger_dagger cj)

attribute [local instance] borelMx

theorem mixS_cj_dagger : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)), IsCovolOne (ratMx D ρ S.rank) μ 𝓕 → ∃ (μ' : Measure (Mx D S.rank ρ)) (𝓕' : Set (Mx D S.rank ρ)), IsCovolOne (ratMx D S.rank ρ) μ' 𝓕' ∧ (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T (d.incAdj S y) = d.extX S (incA D D.host.xi0⁻¹ • y)) ∧ (∀ ξ, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T (d.incX S ξ) = d.extY S (giA S ⬝ adj ξ)) ∧ (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T (d.inc0 S w) = d.ext0 S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T₀ w)) ∧ ∀ (f : WO S T → ℂ) y, (_root_.I195MixedCoordinates_8df3303fbb03152b340aba95.source d) S ψ μ' 𝓕' (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) (incA D D.host.xi0⁻¹ • y) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T₀ S) ((_root_.I195MixedCoordinates_8df3303fbb03152b340aba95.target d) S ψ μ 𝓕 f y) := by
  intro D ψ hψ S T T₀ ρ d μ 𝓕 hμ
  refine ⟨μ.map (adjM S ρ), adjM S ρ '' 𝓕, isCovolOne_map hμ, dagger_incAdj d S, dagger_incX d S, hermitianAdjointHomSpace_wittCoreInclusion d S, ?_⟩
  intro f y
  funext w
  have P : MeasurePreserving (adjM S ρ) μ (μ.map (adjM S ρ)) := (adjM S ρ).measurable.measurePreserving μ
  have hint : ∀ G : Mx D S.rank ρ → ℂ,
      ∫ a in adjM S ρ '' 𝓕, G a ∂(μ.map (adjM S ρ)) = ∫ ξ in 𝓕, G (adjM S ρ ξ) ∂μ :=
    fun G => P.setIntegral_image_emb (adjM S ρ).measurableEmbedding G 𝓕
  simp only [_root_.I195MixedCoordinates_8df3303fbb03152b340aba95.source, _root_.I195MixedCoordinates_8df3303fbb03152b340aba95.target, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [hint, ← integral_conj]
  congr 1
  funext ξ
  change heisO ψ T S (d.extY S (adjM S ρ ξ))
    (heisO ψ T S (d.extX S (incA D D.host.xi0⁻¹ • y))
      (heisO ψ T S (d.ext0 S w) (cj (dagger T S) f))) 0 =
    starRingEnd ℂ (heisO ψ S T (d.incX S ξ)
      (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S (dagger T₀ S w)) f)) 0)
  rw [d.integrandS_eq (cj (dagger T S) f) (incA D D.host.xi0⁻¹ • y) (adjM S ρ ξ) w,
    d.integrandT_eq f y ξ (dagger T₀ S w)]
  have e1 : d.extY S (adjM S ρ ξ) = dagger S T (d.incX S ξ) := (dagger_incX d S ξ).symm
  have e2 : d.extX S (incA D D.host.xi0⁻¹ • y) = dagger S T (d.incAdj S y) := (dagger_incAdj d S y).symm
  have e3 : d.ext0 S w = dagger S T (d.inc0 S (dagger T₀ S w)) := by rw [hermitianAdjointHomSpace_wittCoreInclusion, dagger_dagger]
  rw [e1, e2, e3, symplOH_dagger, ← dagger_add, ← dagger_add]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_dagger, map_mul, conj_psi_of_std hψ]

end GlobalTheory.MixSwap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestriction
section
namespace I195MixedCoordinates_16b53debd46a2c18720dfcab

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_16b53debd46a2c18720dfcab

public noncomputable abbrev _root_.I195MixedCoordinates_61fbc522a99e851221ffe16d.source :=
  @_root_.I195MixedCoordinates_16b53debd46a2c18720dfcab.source

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Bridge

open GlobalTheory.MixModel

variable {D : D7}

theorem isIsoSplit_hyp {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (hρ : 0 < ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit S S₀ d.e d.i₀ := by
  have hq : d.qX * d.e = 1 := d.e'e
  refine ⟨⟨hρ, ?_, ?_⟩, ?_, ?_, d.rank_add.symm⟩
  · exact Matrix.mulVec_injective_iff.1 fun x y h => by
      have := congrArg (d.qX *ᵥ ·) h
      simpa only [Matrix.mulVec_mulVec, hq, Matrix.one_mulVec] using this
  · rw [cT_sig]; exact d.ee
  · simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, cT_sig]; exact d.iso
  · simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, cT_sig]
    apply rat_injective
    rw [rat_mul, rat_mul, rat_conjTranspose, rat_zero, Matrix.mul_assoc]
    exact d.wittDecomp_gram_X_anisotropic

set_option maxHeartbeats 1000000 in
theorem mem_NI_hyp {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (g : GA D S) (h1 : mt S g ⬝ d.jX = d.jX)
    (h2 : d.pY ⬝ mt S g = d.pY) (B : Mx D ρ S₀.rank) (h3 : mt S g ⬝ d.j0 = d.j0 + d.jX ⬝ B) : g ∈ NI S d.e := by
  apply Subgroup.subset_closure
  have hm1 : (mt S g - 1) ⬝ d.jX = 0 := by rw [Matrix.sub_mul, h1, Matrix.one_mul, sub_self]
  have hm0 : (mt S g - 1) ⬝ d.j0 = d.jX ⬝ B := by rw [Matrix.sub_mul, h3, Matrix.one_mul, add_sub_cancel_left]
  refine ⟨hm1, ?_, ?_⟩
  · rw [cT_sig]
    change d.pY ⬝ (mt S g - 1) = 0
    rw [Matrix.mul_sub, h2, Matrix.mul_one, sub_self]
  · intro x hx
    rw [cT_sig] at hx
    refine ⟨B *ᵥ (d.p0 *ᵥ fun i => incA D (x i)), ?_⟩
    have hv : d.pY *ᵥ (fun i => incA D (x i)) = 0 := by
      funext i
      have := RingHom.map_mulVec (incA D) d.qY x i
      change incA D (((d.eᴴ * HSpace.gram S) *ᵥ x) i) = _ at this
      rw [hx, Pi.zero_apply, map_zero] at this
      exact this.symm
    have hsum : (fun i => incA D (x i)) = d.jX *ᵥ (d.pX *ᵥ fun i => incA D (x i)) +
        d.j0 *ᵥ (d.p0 *ᵥ fun i => incA D (x i)) := by
      have h := congrArg (· *ᵥ fun i => incA D (x i)) d.sum_eq_one
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, add_zero] at h
      exact h.symm
    have hX : ∀ a, mt S g *ᵥ (d.jX *ᵥ a) = d.jX *ᵥ a := fun a => by rw [Matrix.mulVec_mulVec, h1]
    have h0 : ∀ a, mt S g *ᵥ (d.j0 *ᵥ a) = d.j0 *ᵥ a + d.jX *ᵥ (B *ᵥ a) := fun a => by
      rw [Matrix.mulVec_mulVec, h3, Matrix.add_mulVec, Matrix.mulVec_mulVec]
    have final : (mt S g - 1) *ᵥ (fun i => incA D (x i)) = d.jX *ᵥ (B *ᵥ (d.p0 *ᵥ fun i => incA D (x i))) := by
      have hs := Matrix.sub_mulVec (mt S g) (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) (fun i => incA D (x i))
      rw [Matrix.one_mulVec] at hs
      rw [hs]
      conv_lhs => rw [hsum]
      rw [Matrix.mulVec_add, hX, h0]
      abel
    exact final

end GlobalTheory.Bridge

namespace GlobalTheory.Bridge
open GlobalTheory.MixModel
variable {D : D7}

theorem orthProjPartHomToHermitian_eq_wittDecompositionCore {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (w : WO S₀ T) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart S S₀ T d.i₀ w = d.ext0 T w := by
  rw [HypDec.matrixExtendByZero_apply]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, cT_sig, Matrix.mul_assoc]
  rfl

theorem integrand_eq {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ)
    (x a : Mx D T.rank ρ) (w : WO S₀ T) :
    heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0 =
      heisO ψ S T (d.extX T x) f (d.extY T a + d.ext0 T w) := by
  rw [d.integrandS_eq]
  simp only [heisO]
  rw [GlobalTheory.OrientedHeis.symplOH_add_left, symplOH_skew S T (d.extX T x) (d.ext0 T w), d.wittDecomp_sympl_extIsotropic_extAnisotropic T x w,
    neg_zero, add_zero, add_right_comm]

theorem mixS_eq_res {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) :
    (_root_.I195MixedCoordinates_16b53debd46a2c18720dfcab.source d) T ψ μ 𝓕 f x = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res S S₀ T d.e d.i₀ μ 𝓕 (heisO ψ S T (d.extX T x) f) := by
  funext w
  simp only [_root_.I195MixedCoordinates_16b53debd46a2c18720dfcab.source, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res, orthProjPartHomToHermitian_eq_wittDecompositionCore]
  congr 1
  funext a
  exact integrand_eq d ψ f x a w

theorem mixS_heis {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) :
    (_root_.I195MixedCoordinates_16b53debd46a2c18720dfcab.source d) T ψ μ 𝓕 f x = (_root_.I195MixedCoordinates_16b53debd46a2c18720dfcab.source d) T ψ μ 𝓕 (heisO ψ S T (d.extX T x) f) 0 := by
  funext w
  simp only [_root_.I195MixedCoordinates_16b53debd46a2c18720dfcab.source]
  congr 1
  funext a
  change heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0 =
    heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T 0) (heisO ψ S T (d.ext0 T w) (heisO ψ S T (d.extX T x) f))) 0
  rw [integrand_eq d ψ f x a w, integrand_eq d ψ _ 0 a w, map_zero]
  simp only [heisO, add_zero, GlobalTheory.OrientedHeis.symplOH_add_left]
  rw [symplOH_skew S T 0 (d.extY T a), symplOH_skew S T 0 (d.ext0 T w)]
  simp only [symplOH_zero_left, neg_zero, zero_add, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.Bridge

namespace GlobalTheory.Bridge

open GlobalTheory.MixModel

theorem heis_bridge : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), (0 < ρ → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit S S₀ d.e d.i₀) ∧ GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ = ratMx D T.rank ρ ∧ (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart S T d.e y = d.extY T y) ∧ (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart S T d.e' y = d.extX T y) ∧ (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart S S₀ T d.i₀ w = d.ext0 T w) ∧ (∀ μ 𝓕 f x, (_root_.I195MixedCoordinates_16b53debd46a2c18720dfcab.source d) T ψ μ 𝓕 f x = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res S S₀ T d.e d.i₀ μ 𝓕 (heisO ψ S T (d.extX T x) f)) ∧ (∀ μ 𝓕 f x, (_root_.I195MixedCoordinates_16b53debd46a2c18720dfcab.source d) T ψ μ 𝓕 f x = (_root_.I195MixedCoordinates_16b53debd46a2c18720dfcab.source d) T ψ μ 𝓕 (heisO ψ S T (d.extX T x) f) 0) ∧ (∀ b, d.nB b ∈ NI S d.e) ∧ ∀ c, d.nC c ∈ NI S d.e := by
  intro D ψ S S₀ T ρ d
  exact ⟨isIsoSplit_hyp d, rfl, fun _ => rfl, fun _ => rfl, orthProjPartHomToHermitian_eq_wittDecompositionCore d T,
    fun μ 𝓕 f x => mixS_eq_res d ψ μ 𝓕 f x, fun μ 𝓕 f x => mixS_heis d ψ μ 𝓕 f x,
    fun b => mem_NI_hyp d _ (d.nB_jX b) (d.pY_nB b) b (d.nB_j0 b),
    fun c => mem_NI_hyp d _ (d.nC_jX c) (d.pY_nC c) 0 (by rw [d.nC_j0, Matrix.mul_zero, add_zero])⟩

end GlobalTheory.Bridge

end
end

