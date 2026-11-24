module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
public import GroundTheory.GlobalFields.Adele.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMeanVanishingOnStripsAtOne
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.StripVanish


set_option maxHeartbeats 1000000 in
theorem mean_eq_zero_of_strips : ∀ (D : D7) (W : HSp D) (vW : GlobalTheory.Unf.Vol W) (R K : Subgroup (GA D W)), IsClosed (R : Set (GA D W)) → (∀ a ∈ GinfC W, ∀ b ∈ GfC W, a * b ∈ R → a ∈ R ∧ b ∈ R) → K ≤ GfC W → IsCompact (K : Set (GA D W)) → IsOpen ((K.subgroupOf (GfC W) : Subgroup (GfC W)) : Set (GfC W)) → ∀ (μR : Measure R), μR.IsHaarMeasure → μR.IsInvInvariant → ∀ (𝓡 : Set R) (𝓑 : Set (GA D W)), IsFundamentalDomain ((GQ W ⊓ R).subgroupOf R) 𝓡 μR → IsFundamentalDomain (GQ W ⊓ R : Subgroup (GA D W)) 𝓑 vW.μ → ∀ f : GA D W → ℂ, Measurable f → (∀ γ ∈ GQ W ⊓ R, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓑 vW.μ → (∀ h, IntegrableOn (fun r : R => f (r * h)) 𝓡 μR) → (Continuous fun h => ∫ r in 𝓡, f ((r : GA D W) * h) ∂μR) → (∀ k ∈ K, ∀ g, f (g * k) = f g) → (∀ h, f h ≠ 0 → ∃ r ∈ R, ∃ a ∈ GinfC W, ∃ k ∈ K, h = r * a * k) → (∀ C : Set (GA D W), IsCompact C → C ⊆ GinfC W → MeasurableSet (strip W R C) ∧ ∫ h in 𝓑 ∩ strip W R C, f h ∂vW.μ = 0) → ∫ r in 𝓡, f r ∂μR = 0 := by
  intro D W vW R K hRc hsplit hKf hKc hKo μR hμR hμRinv 𝓡 𝓑 h𝓡 h𝓑 f hfm hfl hfi hfiR hTc hfK hsupp hstrip
  haveI := vW.haar
  haveI : LocallyCompactSpace R := hRc.locallyCompactSpace
  haveI : μR.IsMulRightInvariant := by rw [← Measure.inv_eq_self μR]; infer_instance
  obtain ⟨hinfC, -, hcomm, ⟨e, he⟩, -⟩ := GlobalTheory.AdelicSplit.adelic_split D W
  obtain ⟨hΓc, hΓd, -⟩ :=
    GlobalTheory.RationalSubgroupFund.countable_discrete_exists_fundamentalDomain D W (GQ W ⊓ R) inf_le_left
  set T : GA D W → ℂ := fun h => ∫ r in 𝓡, f ((r : GA D W) * h) ∂μR with hTdef
  have hQ := GlobalTheory.quot_fubini_mean (GA D W) vW.μ R (GQ W ⊓ R) inf_le_right hRc hΓc hΓd μR hμR 𝓡 𝓑 h𝓡 h𝓑 f hfm
    hfl hfi hfiR
  have hTl : ∀ s ∈ R, ∀ x, T (s * x) = T x := fun s hs x => hQ.left hs x
  have hTr : ∀ k ∈ K, ∀ x, T (x * k) = T x := by
    intro k hk x
    simp only [hTdef]
    congr 1
    funext r
    rw [← mul_assoc, hfK k hk]
  have h1 : T 1 = ∫ r in 𝓡, f (r : GA D W) ∂μR := by simp [hTdef]
  rw [← h1]
  by_contra hT1

  have hsupT : ∀ x, T x ≠ 0 → ∃ q ∈ R, ∃ a ∈ GinfC W, ∃ k ∈ K, x = q * a * k := by
    intro x hx
    by_contra hno
    apply hx
    have hz : ∀ r : R, f ((r : GA D W) * x) = 0 := by
      intro r
      by_contra hr
      obtain ⟨r₁, hr₁, a, ha, k, hk, hrx⟩ := hsupp _ hr
      refine hno ⟨(r : GA D W)⁻¹ * r₁, R.mul_mem (R.inv_mem r.2) hr₁, a, ha, k, hk, ?_⟩
      rw [show x = (r : GA D W)⁻¹ * ((r : GA D W) * x) by group, hrx]
      group
    simp [hTdef, hz]

  have hP : ∀ C : Set (GA D W), C ⊆ GinfC W → ∀ x ∈ strip W R C, T x ≠ 0 → ∃ c ∈ C, T x = T c := by
    rintro C hC x ⟨r, hr, c, hc, b, hb, rfl⟩ hx
    obtain ⟨q, hq, a, ha, k, hk, hx'⟩ := hsupT _ hx
    have hkb : k * b⁻¹ ∈ GfC W := (GfC W).mul_mem (hKf hk) ((GfC W).inv_mem hb)
    have hc' : c⁻¹ ∈ GinfC W := (GinfC W).inv_mem (hC hc)
    have hac : a * c⁻¹ ∈ GinfC W := (GinfC W).mul_mem ha hc'
    have e1 : c⁻¹ * (k * b⁻¹) = (k * b⁻¹) * c⁻¹ := hcomm _ hc' _ hkb
    have hmem : (a * c⁻¹) * (k * b⁻¹) ∈ R := by
      have : (a * c⁻¹) * (k * b⁻¹) = q⁻¹ * r := by
        calc (a * c⁻¹) * (k * b⁻¹) = a * (k * b⁻¹) * c⁻¹ := by rw [mul_assoc, e1, ← mul_assoc]
          _ = q⁻¹ * (q * a * k) * b⁻¹ * c⁻¹ := by group
          _ = q⁻¹ * (r * c * b) * b⁻¹ * c⁻¹ := by rw [hx']
          _ = q⁻¹ * r := by group
      rw [this]
      exact R.mul_mem (R.inv_mem hq) hr
    obtain ⟨hacR, -⟩ := hsplit _ hac _ hkb hmem
    refine ⟨c, hc, ?_⟩
    calc T (r * c * b) = T (q * (a * k)) := by rw [hx', mul_assoc]
      _ = T a := by rw [hTl q hq, hTr k hk]
      _ = T ((a * c⁻¹) * c) := by group
      _ = T c := hTl _ hacR c

  set U : Set (GA D W) := {h | (1 : ℝ) / 2 < (T h / T 1).re} with hUdef
  have hUo : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.comp (hTc.div_const (T 1)))
  have h1U : (1 : GA D W) ∈ U := by
    show (1 : ℝ) / 2 < (T 1 / T 1).re
    rw [div_self hT1]; norm_num
  haveI : LocallyCompactSpace (GinfC W) := hinfC.locallyCompactSpace
  have hU'o : IsOpen ((Subtype.val : GinfC W → GA D W) ⁻¹' U) := hUo.preimage continuous_subtype_val
  obtain ⟨C', hC'n, hC'U, hC'c⟩ :=
    local_compact_nhds (hU'o.mem_nhds (show ((1 : GinfC W) : GA D W) ∈ U from h1U))
  set C : Set (GA D W) := Subtype.val '' C' with hCdef
  have hCinf : C ⊆ GinfC W := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hCU : C ⊆ U := by rintro _ ⟨y, hy, rfl⟩; exact hC'U hy
  obtain ⟨hSm, hS0⟩ := hstrip C (hC'c.image continuous_subtype_val) hCinf
  set S := strip W R C with hSdef
  have hSinv : ∀ s ∈ R, ∀ x, s * x ∈ S ↔ x ∈ S := by
    intro s hs x
    constructor
    · rintro ⟨r, hr, c, hc, b, hb, hx⟩
      refine ⟨s⁻¹ * r, R.mul_mem (R.inv_mem hs) hr, c, hc, b, hb, ?_⟩
      rw [show x = s⁻¹ * (s * x) by group, hx]; group
    · rintro ⟨r, hr, c, hc, b, hb, rfl⟩
      exact ⟨s * r, R.mul_mem hs hr, c, hc, b, hb, by group⟩

  have hfSl : ∀ γ ∈ GQ W ⊓ R, ∀ g, S.indicator f (γ * g) = S.indicator f g := by
    intro γ hγ g
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hSinv γ hγ.2 g).2 hg), hfl γ hγ g]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt (hSinv γ hγ.2 g).1 hg)]
  have hfSi : ∀ h, IntegrableOn (fun r : R => S.indicator f ((r : GA D W) * h)) 𝓡 μR := by
      intro h
      by_cases hh : h ∈ S
      · have : (fun r : R => S.indicator f ((r : GA D W) * h)) = fun r : R => f ((r : GA D W) * h) :=
          funext fun r => Set.indicator_of_mem ((hSinv _ r.2 h).2 hh) _
        rw [this]; exact hfiR h
      · have : (fun r : R => S.indicator f ((r : GA D W) * h)) = fun _ => 0 :=
          funext fun r => by simp [Set.indicator_apply, hSinv _ r.2 h, hh]
        rw [this]; exact integrableOn_zero
  have hQS := GlobalTheory.quot_fubini_mean (GA D W) vW.μ R (GQ W ⊓ R) inf_le_right hRc hΓc hΓd μR hμR 𝓡 𝓑 h𝓡 h𝓑
    (S.indicator f) (hfm.indicator hSm) hfSl (hfi.indicator hSm) hfSi
  have hQS' : IsQuotIntL1 μR vW.μ (S.indicator T) 0 := by
    have e1 : (fun h => ∫ r in 𝓡, S.indicator f ((r : GA D W) * h) ∂μR) = S.indicator T := by
      funext h
      by_cases hh : h ∈ S
      · rw [Set.indicator_of_mem hh]
        simp only [hTdef]
        congr 1; funext r
        exact Set.indicator_of_mem ((hSinv _ r.2 h).2 hh) _
      · simp [Set.indicator_apply, hSinv _ (Subtype.property _) h, hh]
    have e2 : ∫ g in 𝓑, S.indicator f g ∂vW.μ = 0 := by rw [setIntegral_indicator hSm, hS0]
    rw [e1, e2] at hQS
    exact hQS
  obtain ⟨β, -, hβ⟩ := GlobalTheory.Tw.exists_isCosetCutoff (μT := μR) hRc
  obtain ⟨hβi, hβ0⟩ := hQS'.cutoff hβ

  have hre : ∀ x, 0 ≤ (S.indicator T x / T 1).re ∧ (x ∈ S → T x ≠ 0 → (1 : ℝ) / 2 < (S.indicator T x / T 1).re) := by
    intro x
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS]
      by_cases hx : T x = 0
      · simp [hx]
      · obtain ⟨c, hc, hTc'⟩ := hP C hCinf x hxS hx
        have h2 : (1 : ℝ) / 2 < (T x / T 1).re := by rw [hTc']; exact hCU hc
        exact ⟨by linarith, fun _ _ => h2⟩
    · simp [Set.indicator_of_notMem hxS, hxS]
  set φ : GA D W → ℝ := fun x => ((β x : ℝ) • S.indicator T x / T 1).re with hφdef
  have hφ : ∀ x, φ x = (β x : ℝ) * (S.indicator T x / T 1).re := by
    intro x
    simp only [hφdef, Complex.real_smul, mul_div_assoc, Complex.re_ofReal_mul]
  have hφnn : 0 ≤ φ := fun x => by rw [hφ]; exact mul_nonneg (NNReal.coe_nonneg _) (hre x).1
  have hφi : Integrable φ vW.μ := (hβi.div_const (T 1)).re
  have hφ0 : ∫ x, φ x ∂vW.μ = 0 := by
    have h := integral_re (hβi.div_const (T 1))
    simp only [RCLike.re_to_complex] at h
    simp only [hφdef]
    rw [h, integral_div, ← hβ0, zero_div, Complex.zero_re]
  have hφae := (integral_eq_zero_iff_of_nonneg hφnn hφi).1 hφ0
  set A : Set (GA D W) := S ∩ {x | T x ≠ 0} with hAdef
  have hAm : MeasurableSet A := hSm.inter (hTc.measurable (measurableSet_singleton (0 : ℂ)).compl)
  have hAinv : ∀ s ∈ R, ∀ x, s * x ∈ A ↔ x ∈ A := by
    intro s hs x
    simp only [hAdef, Set.mem_inter_iff, Set.mem_setOf_eq, hSinv s hs x, hTl s hs x]
  set g : GA D W → ENNReal := A.indicator fun x => (β x : ENNReal) with hgdef
  have hgm : Measurable g := hβ.1.coe_nnreal_ennreal.indicator hAm
  have hg0 : ∫⁻ x, g x ∂vW.μ = 0 := by
    rw [lintegral_eq_zero_iff hgm]
    filter_upwards [hφae] with x hx
    by_cases hxA : x ∈ A
    · have h2 := (hre x).2 hxA.1 hxA.2
      rw [Pi.zero_apply, hφ] at hx
      have : (β x : ℝ) = 0 := by
        rcases mul_eq_zero.1 hx with h | h
        · exact h
        · linarith
      simp [hgdef, Set.indicator_of_mem hxA, Pi.zero_apply, NNReal.coe_eq_zero.1 this]
    · simp [hgdef, Set.indicator_of_notMem hxA]

  have hA0 : vW.μ A = 0 := by
    have hmul : Measurable fun p : GA D W × R => (p.2 : GA D W) * p.1 :=
      (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
    have e1 : vW.μ A = ∫⁻ x, ∫⁻ t : R, g ((t : GA D W) * x) ∂μR ∂vW.μ := by
      rw [← lintegral_indicator_one hAm]
      refine lintegral_congr fun x => ?_
      by_cases hxA : x ∈ A
      · have : ∀ t : R, g ((t : GA D W) * x) = β ((t : GA D W) * x) := fun t => by
          simp [hgdef, Set.indicator_of_mem ((hAinv _ t.2 x).2 hxA)]
        simp only [this, hβ.2 x, Set.indicator_of_mem hxA, Pi.one_apply]
      · have : ∀ t : R, g ((t : GA D W) * x) = 0 := fun t => by
          simp [hgdef, Set.indicator_of_notMem (mt (hAinv _ t.2 x).1 hxA)]
        simp [this, Set.indicator_of_notMem hxA]
    rw [e1, lintegral_lintegral_swap (f := fun x (t : R) => g ((t : GA D W) * x)) (hgm.comp hmul).aemeasurable]
    have e2 : ∀ t : R, ∫⁻ x, g ((t : GA D W) * x) ∂vW.μ = 0 := fun t => by
      rw [lintegral_mul_left_eq_self, hg0]
    simp [e2]

  set O : Set (GA D W) := e '' (interior C' ×ˢ ((K.subgroupOf (GfC W) : Subgroup (GfC W)) : Set (GfC W))) with hOdef
  have hOo : IsOpen O := e.isOpenMap _ (isOpen_interior.prod hKo)
  have h1O : (1 : GA D W) ∈ O :=
    ⟨(1, 1), ⟨mem_interior_iff_mem_nhds.2 hC'n, (K.subgroupOf (GfC W)).one_mem⟩, by rw [he]; simp⟩
  have hOA : O ⊆ A := by
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    rw [he]
    have hk : (p.2 : GA D W) ∈ K := Subgroup.mem_subgroupOf.1 hp2
    refine ⟨⟨1, R.one_mem, p.1, ⟨p.1, interior_subset hp1, rfl⟩, p.2, p.2.2, by simp⟩, ?_⟩
    show T (p.1 * p.2) ≠ 0
    rw [hTr _ hk]
    intro h0
    have := hC'U (interior_subset hp1)
    simp only [Set.mem_preimage, hUdef, Set.mem_setOf_eq, h0, zero_div, Complex.zero_re] at this
    linarith
  have hpos := hOo.measure_pos vW.μ ⟨1, h1O⟩
  exact hpos.ne' (measure_mono_null hOA hA0)

end GlobalTheory.StripVanish
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOneParameterArchimedeanWeilOperator
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

noncomputable section

namespace GlobalTheory.ArchLine.OpCont

theorem evI_fin {F : Type} [Field F] [NumberField F] : evI F ((0, 1) : AF F) = 0 :=
  map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem snd_eq_zero_of_at {F : Type} [Field F] [NumberField F] {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) :
    (z i).2 = 0 := by
  have := congrArg Prod.snd (congrFun (hz (0, 1) evI_fin) i)
  change (((0, 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F).2 * (z i).2) = (0 : AF F).2 at this
  rw [one_mul] at this
  exact this

def intInd {F : Type} [Field F] [NumberField F] (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))).indicator 1

theorem intInd_mem {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    intInd (F := F) κ ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  set B := Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) with hB
  have hO : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ => GroundTheory.Global.isOpen_integralFiniteAdeles
  have hK : IsCompact B := isCompact_univ_pi fun _ => GroundTheory.Global.isCompact_integralFiniteAdeles F
  have hC : IsClosed B := hK.isClosed
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ B
  · refine ⟨_, hO, hx, fun y hy => ?_⟩
    simp only [intInd, ← hB, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]
  · refine ⟨_, hC.isOpen_compl, hx, fun y hy => ?_⟩
    simp only [intInd, ← hB, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

end GlobalTheory.ArchLine.OpCont

namespace GlobalTheory.ArchLine

theorem archOp_apply_continuous : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) → ∀ γ ∈ Lines σ W,
    ∀ (f : SInf F (Fin n × Fin d)) (x : Fin n × Fin d → mixedEmbedding.mixedSpace F),
      Continuous fun t : ℝ => archOp om (γ (Multiplicative.ofAdd t)) f x := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hW hex γ hγ f x
  have hC := hW.2.2

  set r₀ : (Fin n × Fin d → AF F) → ℂ := fun y => GlobalTheory.ArchLine.OpCont.intInd (F := F) (Fin n × Fin d) (fun i => (y i).2)
    with hr₀
  have hr₀1 : ∀ y : Fin n × Fin d → AF F, (∀ i, (y i).2 = 0) → r₀ y = 1 := by
    intro y hy
    have : (fun i => (y i).2) = 0 := funext hy
    simp only [hr₀, this, GlobalTheory.ArchLine.OpCont.intInd]
    rw [Set.indicator_of_mem (show (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
      fun _ : Fin n × Fin d => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) from
        fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
    rfl
  have hrest : ∀ g : SInf F (Fin n × Fin d), Rest (evI F) (g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r₀ := by
    intro g
    refine ⟨fun y z hz => ?_, ?_⟩
    · have : (fun i => ((y + z) i).2) = fun i => (y i).2 := by
        funext i
        change (y i).2 + (z i).2 = (y i).2
        rw [GlobalTheory.ArchLine.OpCont.snd_eq_zero_of_at hz i, add_zero]
      simp only [hr₀, this]
    · exact Submodule.subset_span ⟨g, GlobalTheory.ArchLine.OpCont.intInd _, GlobalTheory.ArchLine.OpCont.intInd_mem _, rfl⟩

  let l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => Φ (liftV x), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hl : l ∈ (adeleClass F).adm (Fin n × Fin d) := by
    intro g _
    refine ⟨g 0 • ((BoundedContinuousFunction.evalCLM ℂ x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)), fun f' => ?_⟩
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    show pureA F f' g (liftV x) = _
    simp only [pureA, liftV, RingEquiv.apply_symm_apply]
    change f' x * g 0 = g 0 * f' x
    ring
  have hφ : tens (evI F) (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r₀ ∈ (adeleClass F).sp (Fin n × Fin d) :=
    (hrest f).2
  have hcont := hC l hl _ hφ
  have hpath : Continuous fun t : ℝ => (((1 : UA σ X.J), γ (Multiplicative.ofAdd t)) : UA σ X.J × UA σ W.J) :=
    continuous_const.prodMk (hγ.1.comp continuous_ofAdd)
  have key := hcont.comp hpath
  convert key using 1
  funext t
  have hh : γ (Multiplicative.ofAdd t) ∈ UAt σ W (evI F) := hγ.2 _
  have ha := acts_archOp om (γ (Multiplicative.ofAdd t)) f (hex _ hh f) r₀ (hrest f)
  simp only [Function.comp_apply]
  show _ = om _ _ (liftV x)
  change _ = om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑f) r₀) (liftV x)
  rw [ha]
  have h1 : r₀ (liftV x) = 1 := hr₀1 _ fun i => rfl
  have h2 : (fun i => evI F (liftV x i)) = x := by
    funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _
  simp only [tens, h1, h2, mul_one]

end GlobalTheory.ArchLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOneParameterUnitaryCoordinateAction
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

namespace GlobalTheory.ArchLine

theorem continuous_archAct_line : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W), ∀ γ ∈ Lines σ W,
    ∀ v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
      Continuous fun t : ℝ => archAct M (γ (Multiplicative.ofAdd t)) v := by
  intro F E _ _ _ _ _ σ n d X W M γ hγ v
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have hγc : Continuous fun t : ℝ => γ (Multiplicative.ofAdd t) := hγ.1.comp continuous_ofAdd
  have hm : Continuous fun t : ℝ => (mat (γ (Multiplicative.ofAdd t)))ᵀ :=
    ((Units.continuous_val.comp continuous_subtype_val).comp hγc).matrix_transpose
  have he : Continuous M.co.e := IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hev : Continuous (evI F) := by
    change Continuous fun a : AF F => InfiniteAdeleRing.ringEquiv_mixedSpace F a.1
    refine Continuous.comp ?_ continuous_fst
    change Continuous fun x : InfiniteAdeleRing F =>
      ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
       (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
  have hl : Continuous (locV : (Fin n × Fin d → AF F) → _) := continuous_pi fun i => hev.comp (continuous_apply i)
  show Continuous fun t : ℝ =>
    (locV (M.co.e (mat (1 : UA σ X.J) * M.co.e.symm (liftV v.1, liftV v.2) * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1,
     locV (M.co.e (mat (1 : UA σ X.J) * M.co.e.symm (liftV v.1, liftV v.2) * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2)
  exact ((hl.comp continuous_fst).prodMk (hl.comp continuous_snd)).comp
    (he.comp (continuous_const.matrix_mul hm))

end GlobalTheory.ArchLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.SeeConjRead

open Classical

variable {D : D7}

def diagGL {κ : Type} [CommRing κ] {r : ℕ} (d : Fin r → κˣ) : GL (Fin r) κ :=
  Units.map (Matrix.diagonalRingHom (Fin r) κ).toMonoidHom (MulEquiv.piUnits.symm d)

theorem diagGL_val {κ : Type} [CommRing κ] {r : ℕ} (d : Fin r → κˣ) :
    ((diagGL d : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) = Matrix.diagonal fun i => (d i : κ) := rfl

def flagV {M : Type} [Zero M] (ρ k n : ℕ) (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n) : M :=
  if h1 : i.1 < ρ then e ⟨i.1, h1⟩
  else if h2 : i.1 < ρ + k then b ⟨i.1 - ρ, by omega⟩
  else if h4 : i.1 = ρ + k then z
  else if h3 : i.1 < 2 * ρ + k + 1 then f ⟨2 * ρ + k - i.1, by omega⟩
  else 0

def e0T (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin D.R.rS → Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin D.R.rS → Formalism.L2.SG.HidaSetting.VA I) h) X.e0

def f0T (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin D.R.rS → Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin D.R.rS → Formalism.L2.SG.HidaSetting.VA I) h) X.f0

def z0T (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h) X.z0

def bwT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin D.R.k → Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin D.R.k → Formalism.L2.SG.HidaSetting.VA I) h) X.bw

def bwdT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin D.R.k → Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin D.R.k → Formalism.L2.SG.HidaSetting.VA I) h) X.bwd

def ewT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) : EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h) X.ew

def flagAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) :
    Fin (Yc D 0).rank → Fin (Yc D 0).rank → EAf D :=
  if GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 then
    flagV D.R.rS D.R.k (Yc D 0).rank (e0T X h) (f0T X h) (bwT X h) (z0T X h)
  else flagV D.R.rS D.R.k (Yc D 0).rank (e0T X h) (f0T X h) (fun i => bwdT X h (Fin.rev i)) (z0T X h)

def RedIs {n : ℕ} (β : GL (Fin n) (EAf D)) (PP : Pl D.host.E) (w : Fin n → Fin n → EAf D) : Prop :=
  ∀ i j, ∃ hm : Matrix.mulVec (β⁻¹).val (w j) i ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E,
    Formalism.L2.DIV.resS D.host.F PP ⟨_, hm⟩ = if i = j then 1 else 0

end GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjRead

theorem diagGL_inv {κ : Type} [CommRing κ] {r : ℕ} (d : Fin r → κˣ) : (diagGL d)⁻¹ = diagGL (fun i => (d i)⁻¹) := by
  unfold diagGL
  rw [← map_inv, ← map_inv]
  rfl

theorem diagGL_conj_apply {κ : Type} [CommRing κ] {r : ℕ} (d : Fin r → κˣ) (u : GL (Fin r) κ) (i j : Fin r) :
    (((diagGL d)⁻¹ * u * diagGL d : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j =
      (((d i)⁻¹ : κˣ) : κ) * (u : Matrix (Fin r) (Fin r) κ) i j * (d j : κ) := by
  rw [diagGL_inv, Units.val_mul, Units.val_mul, diagGL_val, diagGL_val, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem unipSym_conj_of {κ : Type} [CommRing κ] {r : ℕ} (ρ k : ℕ) (d : Fin r → κˣ) {u : GL (Fin r) κ}
    (hu : u ∈ unipSym κ r ρ k) : (diagGL d)⁻¹ * u * diagGL d ∈ unipSym κ r ρ k := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hu
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j a b c => ?_⟩
  · show (((diagGL d)⁻¹ * u * diagGL d : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j = 0
    rw [diagGL_conj_apply, h1 hij, mul_zero, zero_mul]
  · rw [diagGL_conj_apply, h2, mul_one, Units.inv_mul]
  · rw [diagGL_conj_apply, h3 i j a b c, mul_zero, zero_mul]

theorem unipSym_conj_iff {κ : Type} [CommRing κ] {r : ℕ} (ρ k : ℕ) (d : Fin r → κˣ) (u : GL (Fin r) κ) :
    u ∈ unipSym κ r ρ k ↔ (diagGL d)⁻¹ * u * diagGL d ∈ unipSym κ r ρ k := by
  refine ⟨unipSym_conj_of ρ k d, fun h => ?_⟩
  have h' := unipSym_conj_of ρ k (fun i => (d i)⁻¹) h
  rw [← diagGL_inv, inv_inv] at h'
  simpa [mul_assoc] using h'

end GlobalTheory.SeeConjRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceModelIndicatorThetaFockLatticeVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeModel_indicator_theta_fock_latticeVacuum : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ f₀ : WO S T → ℂ, IsVacO C.ψ C.θ S T (fun _ => 1) (C.sB B) (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f₀ → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel C.ψ (symplO S T) (heisO C.ψ S T) (cA D e) (latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm → ∀ L : AddSubgroup (WO S T), (∀ x ∈ L, IsHalf (cA D e) x) → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ L) → IsSBHalf (cA D e) (latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) (GlobalTheory.LiftLevel.indL L) ∧ C.IsTh (Tm (GlobalTheory.LiftLevel.indL L)) ∧ C.IsFock B (Tm (GlobalTheory.LiftLevel.indL L)) ∧ ∀ Λ'' : AddSubgroup (WO S T), (∀ u ∈ Λ'', GlobalTheory.LiftLevel.partAt (cA D e) u ∈ L ∧ (∀ t ∈ L, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1) ∧ GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) → IsLatVac (heisO C.ψ S T) Λ'' (Tm (GlobalTheory.LiftLevel.indL L)) := by
  first | exact @GlobalTheory.IndVac.indL_theta_fock_latVac | exact GlobalTheory.IndVac.indL_theta_fock_latVac | (intros; apply GlobalTheory.IndVac.indL_theta_fock_latVac <;> assumption)
end

