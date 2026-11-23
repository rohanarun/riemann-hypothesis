module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022
public import GroundTheory.GlobalFields.Adele.Bundle0001
public import GroundTheory.GlobalFields.Adele.Approximation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0761
public import Formalism.LocalToGlobal.Columns.RowFormsLemmas
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Formalism.SatakeDualWeyl.Bundle0001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveStrongApproximationAvoidingFinset
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
open Filter

namespace GlobalTheory.AddApproxPlaces


open NumberField.mixedEmbedding MeasureTheory in
theorem exists_small_of_infinitePlace (F : Type) [Field F] [NumberField F] (w₀ : InfinitePlace F)
    (f : InfinitePlace F → NNReal) (hf : ∀ w, f w ≠ 0) :
    ∃ g : F, g ≠ 0 ∧ (∀ w : InfinitePlace F, w ≠ w₀ → w g < f w) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F g ≤ 1 := by
  classical
  obtain ⟨g, hg, hB⟩ := adjust_f F (f := f) (w₁ := w₀) ((minkowskiBound F 1).toNNReal + 1) (fun w _ => hf w)
  have h : minkowskiBound F 1 < volume (convexBodyLT F g) := by
    rw [convexBodyLT_volume, hB, ← ENNReal.coe_toNNReal (minkowskiBound_lt_top F 1).ne, ← ENNReal.coe_mul,
      ENNReal.coe_lt_coe, ENNReal.toNNReal_coe]
    exact (lt_add_one _).trans_le (le_mul_of_one_le_left zero_le (one_le_convexBodyLTFactor F))
  obtain ⟨a, ha, hlt⟩ := exists_ne_zero_mem_ringOfIntegers_lt F h
  refine ⟨a, RingOfIntegers.coe_ne_zero_iff.2 ha, fun w hw => ?_, fun v => v.valuation_le_one a⟩
  rw [← hg w hw]; exact hlt w


open NumberField.mixedEmbedding MeasureTheory nonZeroDivisors in
theorem exists_small_of_finitePlace (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (f : InfinitePlace F → NNReal) (hf : ∀ w, f w ≠ 0) :
    ∃ g : F, g ≠ 0 ∧ (∀ w : InfinitePlace F, w g < f w) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ p → v.valuation F g ≤ 1 := by
  classical
  set P : NNReal := convexBodyLTFactor F * ∏ w, (f w) ^ (w.mult) with hP
  have hP0 : 0 < P := pos_iff_ne_zero.2 (mul_ne_zero (convexBodyLTFactor_ne_zero F)
    (Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (hf w)))
  set B : NNReal := (minkowskiBound F 1).toNNReal with hB
  have hN : (1 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((B : ℝ) / P) hN
  have hJ : ((p.asIdeal ^ k : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (pow_ne_zero _ p.ne_bot)
  let I : (FractionalIdeal (𝓞 F)⁰ F)ˣ := (Units.mk0 _ hJ)⁻¹
  have hI : minkowskiBound F I = ENNReal.ofReal (((Ideal.absNorm p.asIdeal : ℝ) ^ k)⁻¹) * minkowskiBound F 1 := by
    unfold minkowskiBound
    rw [volume_fundamentalDomain_fractionalIdealLatticeBasis F 1]
    simp only [volume_fundamentalDomain_fractionalIdealLatticeBasis, I, Units.val_inv_eq_inv_val,
      Units.val_mk0, map_inv₀, FractionalIdeal.coeIdeal_absNorm, Units.val_one, map_one, map_pow]
    simp [mul_assoc]
  have h : minkowskiBound F I < volume (convexBodyLT F f) := by
    have hpos : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) ^ k := by positivity
    rw [hI, convexBodyLT_volume, ← ENNReal.coe_toNNReal (minkowskiBound_lt_top F 1).ne, ← hB, ← ENNReal.coe_mul, ← hP,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hP0), inv_mul_lt_iff₀ hpos]
    exact (div_lt_iff₀ (by exact_mod_cast hP0)).1 hk
  obtain ⟨a, ha, ha0, hlt⟩ := exists_ne_zero_mem_ideal_lt F I h
  refine ⟨a, ha0, hlt, fun v hv => ?_⟩
  have hnle : ¬ p.asIdeal ^ k ≤ v.asIdeal := fun hle =>
    hv (HeightOneSpectrum.ext (p.isMaximal.eq_of_le v.isPrime.ne_top (v.isPrime.le_of_pow_le hle)).symm)
  obtain ⟨b, hb, hbv⟩ := SetLike.not_le_iff_exists.1 hnle
  have ha' : a ∈ ((p.asIdeal ^ k : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    simpa [I] using ha
  have hab := (FractionalIdeal.mem_inv_iff hJ).1 ha' (algebraMap (𝓞 F) F b)
    (FractionalIdeal.mem_coeIdeal_of_mem _ hb)
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hab
  have h1 : v.valuation F (algebraMap (𝓞 F) F b) = 1 :=
    le_antisymm (v.valuation_le_one b) (not_lt.1 fun h => hbv ((v.valuation_lt_one_iff_mem b).1 h))
  have h2 : v.valuation F (algebraMap (𝓞 F) F c) ≤ 1 := v.valuation_le_one c
  rwa [hc, map_mul, h1, mul_one] at h2

theorem exists_int_nhds_finite (F : Type) [Field F] [NumberField F] (N : Set (Af F)) (hN : N ∈ 𝓝 (0 : Af F)) :
    ∃ m : 𝓞 F, m ≠ 0 ∧ ∀ y : Af F,
      (∀ v, Valued.v (evalV F v y) ≤ v.valuation F (algebraMap (𝓞 F) F m)) → y ∈ N := by
  have hM : ∀ᶠ a in 𝓝 (0 : Af F), ∀ c ∈ {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F}, a * c ∈ N := by
    refine (GlobalTheory.AdeleCocompact.isCompact_integral F).eventually_forall_of_forall_eventually fun c _ => ?_
    have hcont : Continuous (fun p : Af F × Af F => p.1 * p.2) := by fun_prop
    exact hcont.continuousAt.eventually_mem (by simpa using hN)
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele F).eventually hM).exists
  have h0 : ((n.factorial : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  refine ⟨(n.factorial : ℕ), Nat.cast_ne_zero.2 n.factorial_ne_zero, fun y hy => ?_⟩
  have e : y = ((n.factorial : ℕ) : Af F) * (algebraMap F (Af F) ((n.factorial : ℕ) : F)⁻¹ * y) := by
    rw [← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul, mul_inv_cancel₀ h0, map_one, one_mul]
  rw [e]
  refine hn _ fun v => ?_
  have e' : (algebraMap F (Af F) ((n.factorial : ℕ) : F)⁻¹ * y) v =
      (((((n.factorial : ℕ) : F)⁻¹ : F)) : v.adicCompletion F) * evalV F v y := rfl
  rw [e', HeightOneSpectrum.mem_adicCompletionIntegers, map_mul,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
  have h1 := hy v
  rw [map_natCast] at h1
  have h2 : v.valuation F ((n.factorial : ℕ) : F) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  exact (inv_mul_le_one₀ (pos_iff_ne_zero.2 h2)).2 h1

theorem exists_delta_nhds_infinite (F : Type) [Field F] [NumberField F] (N : Set (Ainf F))
    (hN : N ∈ 𝓝 (0 : Ainf F)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : Ainf F, (∀ w, ‖y w‖ < δ) → y ∈ N := by
  have hN' : N ∈ 𝓝 (0 : (w : InfinitePlace F) → w.Completion) := hN
  obtain ⟨δ, hδ, h⟩ := Metric.mem_nhds_iff.1 hN'
  exact ⟨δ, hδ, fun y hy => h (mem_ball_zero_iff.2 ((pi_norm_lt_iff hδ).2 hy))⟩

theorem exists_small (F : Type) [Field F] [NumberField F] (S₁ : Finset (InfinitePlace F))
    (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (hS : S₁.Nonempty ∨ S₂.Nonempty)
    (m : 𝓞 F) (hm : m ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ g : F, g ≠ 0 ∧ (∀ w, w ∉ S₁ → w g < δ) ∧
      ∀ v, v ∉ S₂ → v.valuation F g ≤ v.valuation F (algebraMap (𝓞 F) F m) := by
  have hm' : algebraMap (𝓞 F) F m ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hm
  have hw : ∀ w : InfinitePlace F, 0 < w (algebraMap (𝓞 F) F m) := fun w => InfinitePlace.pos_iff.2 hm'
  let f : InfinitePlace F → NNReal := fun w => ⟨δ / w (algebraMap (𝓞 F) F m), (div_pos hδ (hw w)).le⟩
  have hf : ∀ w, f w ≠ 0 := fun w => NNReal.coe_ne_zero.1 (div_pos hδ (hw w)).ne'
  obtain ⟨g, hg, h1, h2⟩ : ∃ g : F, g ≠ 0 ∧ (∀ w, w ∉ S₁ → w g < f w) ∧ ∀ v, v ∉ S₂ → v.valuation F g ≤ 1 := by
    rcases hS with ⟨w₀, hw₀⟩ | ⟨p, hp⟩
    · obtain ⟨g, hg, h1, h2⟩ := exists_small_of_infinitePlace F w₀ f hf
      exact ⟨g, hg, fun w hw => h1 w (fun h => hw (h ▸ hw₀)), fun v _ => h2 v⟩
    · obtain ⟨g, hg, h1, h2⟩ := exists_small_of_finitePlace F p f hf
      exact ⟨g, hg, fun w _ => h1 w, fun v hv => h2 v (fun h => hv (h ▸ hp))⟩
  refine ⟨g * algebraMap (𝓞 F) F m, mul_ne_zero hg hm', fun w hw' => ?_, fun v hv => ?_⟩
  · rw [map_mul]
    exact (lt_div_iff₀ (hw w)).1 (h1 w hw')
  · rw [map_mul]
    exact mul_le_of_le_one_left' (h2 v hv)

theorem exists_small_adele (F : Type) [Field F] [NumberField F] (S₁ : Finset (InfinitePlace F))
    (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F) (hε : IsPlacesIdem S₁ S₂ ε)
    (hS : S₁.Nonempty ∨ S₂.Nonempty) (N : Set (AF F)) (hN : N ∈ 𝓝 (0 : AF F)) :
    ∃ f : F, f ≠ 0 ∧ (1 - ε) * algebraMap F (AF F) f ∈ N := by
  have hN' : N ∈ 𝓝 ((0 : Ainf F), (0 : Af F)) := hN
  obtain ⟨N₁, hN₁, N₂, hN₂, hsub⟩ := mem_nhds_prod_iff.1 hN'
  obtain ⟨δ, hδ, hδN⟩ := exists_delta_nhds_infinite F N₁ hN₁
  obtain ⟨m, hm, hmN⟩ := exists_int_nhds_finite F N₂ hN₂
  obtain ⟨g, hg, h1, h2⟩ := exists_small F S₁ S₂ hS m hm δ hδ
  refine ⟨g, hg, hsub ⟨?_, ?_⟩⟩
  · apply hδN
    intro w
    have e : ((1 - ε) * algebraMap F (AF F) g).1 w = (1 - fstA F ε w) * (algebraMap F (Ainf F) g) w := by
      change (fstA F ((1 - ε) * algebraMap F (AF F) g)) w = _
      rw [map_mul, map_sub, map_one, AlgHom.commutes]
      rfl
    rw [e]
    by_cases hw : w ∈ S₁
    · rw [hε.1 w hw, sub_self, zero_mul, norm_zero]; exact hδ
    · rw [hε.2.1 w hw, sub_zero, one_mul]
      have := GroundTheory.Global.norm_algebraMap_apply (K := F) g w
      exact this.trans_lt (h1 w hw)
  · apply hmN
    intro v
    have e : evalV F v ((1 - ε) * algebraMap F (AF F) g).2 =
        (1 - evalV F v (sndA F ε)) * (g : v.adicCompletion F) := by
      change evalV F v (sndA F ((1 - ε) * algebraMap F (AF F) g)) = _
      rw [map_mul, map_mul, map_sub, map_sub, map_one, map_one, AlgHom.commutes, AlgHom.commutes]
      rfl
    rw [e]
    by_cases hv : v ∈ S₂
    · rw [hε.2.2.1 v hv, sub_self, zero_mul, map_zero]; exact zero_le'
    · rw [hε.2.2.2 v hv, sub_zero, one_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact h2 v hv

theorem exists_approx_notMem : ∀ (F : Type) [Field F] [NumberField F], ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ (x : AF F) (U : Set (AF F)), U ∈ 𝓝 x → ∀ Z : Finset F, ∃ t : F, t ∉ Z ∧ ∃ s : AF F, algebraMap F (AF F) t + ε * s ∈ U := by
  intro F _ _ S₁ S₂ ε hε hS x U hU Z
  have hc : Tendsto (fun p : AF F × AF F => x + (p.1 + p.2)) (𝓝 ((0 : AF F), (0 : AF F))) (𝓝 x) := by
    have : Continuous (fun p : AF F × AF F => x + (p.1 + p.2)) := by fun_prop
    simpa using this.tendsto ((0 : AF F), (0 : AF F))
  obtain ⟨V₁, hV₁, V₂, hV₂, hV⟩ := mem_nhds_prod_iff.1 (hc hU)
  obtain ⟨C, hC, hCF⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  have hM : ∀ᶠ a in 𝓝 (0 : AF F), ∀ c ∈ C, -(a * c) ∈ V₁ := by
    refine hC.eventually_forall_of_forall_eventually fun c _ => ?_
    have hcont : Continuous (fun p : AF F × AF F => -(p.1 * p.2)) := by fun_prop
    exact hcont.continuousAt.eventually_mem (by simpa using hV₁)
  obtain ⟨f, hf, hfM⟩ := exists_small_adele F S₁ S₂ ε hε hS _ hM
  obtain ⟨t₀, ht₀⟩ := hCF (algebraMap F (AF F) f⁻¹ * x)
  set c := algebraMap F (AF F) f⁻¹ * x - algebraMap F (AF F) t₀ with hc_def
  have hd₁ : -((1 - ε) * algebraMap F (AF F) f * c) ∈ V₁ := hfM c ht₀
  have hff : algebraMap F (AF F) f * algebraMap F (AF F) f⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hf, map_one]
  have e₁ : algebraMap F (AF F) (f * t₀) + ε * (algebraMap F (AF F) f * c) =
      x + -((1 - ε) * algebraMap F (AF F) f * c) := by
    rw [hc_def, map_mul]
    linear_combination x * hff

  set n := Z.card with hn
  have hM₂ : ∀ᶠ a in 𝓝 (0 : AF F), ∀ q ∈ Finset.range (n + 1), ((q : ℕ) : AF F) * a ∈ V₂ := by
    refine (Filter.eventually_all_finset _).2 fun q _ => ?_
    have hcont : Continuous (fun a : AF F => ((q : ℕ) : AF F) * a) := by fun_prop
    exact hcont.continuousAt.eventually_mem (by simpa using hV₂)
  obtain ⟨f₂, hf₂, hf₂M⟩ := exists_small_adele F S₁ S₂ ε hε hS _ hM₂
  obtain ⟨q, hq, hqZ⟩ : ∃ q ∈ Finset.range (n + 1), f * t₀ + (q : F) * f₂ ∉ Z := by
    by_contra hcon
    push_neg at hcon
    have hinj : Set.InjOn (fun q : ℕ => f * t₀ + (q : F) * f₂) (Finset.range (n + 1) : Set ℕ) := by
      intro a _ b _ hab
      have : (a : F) * f₂ = (b : F) * f₂ := add_left_cancel hab
      exact_mod_cast mul_right_cancel₀ hf₂ this
    have := Finset.card_le_card_of_injOn _ (fun a ha => hcon a ha) hinj
    simp [hn] at this
  refine ⟨f * t₀ + (q : F) * f₂, hqZ, algebraMap F (AF F) f * c - algebraMap F (AF F) ((q : F) * f₂), ?_⟩
  have e₂ : algebraMap F (AF F) (f * t₀ + (q : F) * f₂) +
      ε * (algebraMap F (AF F) f * c - algebraMap F (AF F) ((q : F) * f₂)) =
      x + (-((1 - ε) * algebraMap F (AF F) f * c) + ((q : ℕ) : AF F) * ((1 - ε) * algebraMap F (AF F) f₂)) := by
    rw [map_add (f := _), map_mul (algebraMap F (AF F)) (q : F) f₂, map_natCast]
    linear_combination e₁
  rw [e₂]
  exact hV (Set.mk_mem_prod hd₁ (hf₂M q hq))

end GlobalTheory.AddApproxPlaces

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantFourth
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms.MovedDatum

section Gen

variable {E K : Type} [Field E] [NumberField E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem norm_unitV (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (h : IsUnit (redP P a)) (σ : K →+* ℂ) :
    ‖σ (LocE.unitV χ a)‖ = 1 := by
  unfold LocE.unitV
  rw [dite_eq_left h]
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hc : 0 < Nat.card (𝓞 E ⧸ P.asIdeal)ˣ := Nat.card_pos
  have h1 : ((χ h.unit : Kˣ) : K) ^ Nat.card (𝓞 E ⧸ P.asIdeal)ˣ = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  have h2 : ‖σ ((χ h.unit : Kˣ) : K)‖ ^ Nat.card (𝓞 E ⧸ P.asIdeal)ˣ = 1 := by
    rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hc.ne').1 h2

variable [StarRing E]

theorem locSmall_om {a b : ℕ} {e e' : ℕ → ℤ} (cq sq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {g : Sp E a ≃ₗ[E] Sp E a} {g' : Sp E b ≃ₗ[E] Sp E b}
    (hg : g ∈ stabL E a (LocE.sclLat P (qOf P) a e)) (hg' : g' ∈ stabL E b (LocE.sclLat P (qOf P) b e'))
    {Φ : HomE E a b → K} {β : ℝ}
    (hΦ : LocSmall (qOf P) (LocE.sclLat P (qOf P) a e) (LocE.sclLat P (qOf P) b e') Φ β) :
    LocSmall (qOf P) (LocE.sclLat P (qOf P) a e) (LocE.sclLat P (qOf P) b e')
      (Loc.om (LocE.locChar (qOf P) cq χ) (LocE.vP P (qOf P)) sq g g' Φ) β := by
  have hu := GlobalTheory.LastSteps.isUnit_det_of_stab hg
  have hu' := GlobalTheory.LastSteps.isUnit_det_of_stab hg'
  obtain ⟨h1, h2, h3⟩ := hΦ
  refine ⟨fun x hx y hy => ?_, fun x z hz => ?_, fun σ x => ?_⟩
  · unfold Loc.om at hx
    have h4 := h1 _ (right_ne_zero_of_mul hx) (g.symm y) ((hg _).1 (by simpa using hy))
    have h5 := (hg' _).2 h4
    simpa using h5
  · unfold Loc.om
    congr 1
    have h4 := h2 (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) (g'.symm.toLinearMap ∘ₗ z ∘ₗ g.toLinearMap) fun y hy =>
      (hg' _).1 (by simpa using hz _ ((hg y).2 hy))
    rw [← h4]
    congr 1
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smul]
  · have locChar_eq_unitV {x : E} (hx : IsUnit (redP P x)) :
        LocE.locChar (qOf P) cq χ x = LocE.unitV χ x := by
      simp [LocE.locChar, GlobalTheory.LastSteps.vP_unit hx]
    unfold Loc.om
    rw [locChar_eq_unitV hu, locChar_eq_unitV hu', GlobalTheory.LastSteps.vP_unit hu,
      GlobalTheory.LastSteps.vP_unit hu']
    simp only [neg_zero, zero_mul, zpow_zero, mul_one, map_mul, map_inv₀, norm_mul, norm_inv, norm_unitV χ hu,
      norm_unitV χ hu', inv_one, one_mul]
    exact h3 σ _

end Gen

end GlobalTheory.ColNorms.MovedDatum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantTenth
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ChainClassNumbers

theorem card_orbits_le_principal {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {G' D' : Type} [Group G'] [MulAction G' D']
    (p : D' → DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (hp : Function.Injective p)
    (h : ∀ (g : UF E n) (x : D'), ∃ g' : G', p (g' • x) = (g, (1 : GLG (E := E) (n := n) (SG := SG))) • p x)
    [Finite (MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF E n)).prod (⊥ : Subgroup (GLG (E := E) (n := n) (SG := SG)))) (DecoSet (E := E) (n := n) (ST := ST) (SG := SG)))] :
    Nat.card (MulAction.orbitRel.Quotient G' D') ≤
      Nat.card (MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF E n)).prod (⊥ : Subgroup (GLG (E := E) (n := n) (SG := SG)))) (DecoSet (E := E) (n := n) (ST := ST) (SG := SG))) := by
  refine Nat.card_le_card_of_injective
    (fun c : MulAction.orbitRel.Quotient G' D' =>
      (Quotient.mk (MulAction.orbitRel _ _) (p (Quotient.out c)) :
        MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF E n)).prod (⊥ : Subgroup (GLG (E := E) (n := n) (SG := SG)))) (DecoSet (E := E) (n := n) (ST := ST) (SG := SG)))) ?_
  intro c c' hcc
  obtain ⟨⟨⟨g, k⟩, hgk⟩, hg⟩ := Quotient.exact hcc
  have hk : k = 1 := (Subgroup.mem_prod.1 hgk).2
  subst hk
  obtain ⟨g', hg'⟩ := h g (Quotient.out c')
  have he : g' • Quotient.out c' = Quotient.out c := hp (hg'.trans hg)
  rw [← Quotient.out_eq c, ← Quotient.out_eq c']
  exact Quotient.sound ⟨g', he⟩

end GlobalTheory.ChainClassNumbers
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientGramPosSemidefAndNormAtPlace
section
namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem pairVr_one_eq {E K : Type} [Field E] [Field K] [StarRing K] {ι : Type} [Fintype ι] (emb : ι → E →+* K) {n : ℕ}
    (lam : ι → DomWeight n) :
    pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) = pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) K)) := by
  have e : gramKd emb (1 : Matrix (Fin n) (Fin n) E) = fun _ => 1 := by
    funext τ
    rw [gramKd, Matrix.map_one _ (map_zero _) (map_one _), inv_one, Matrix.transpose_one]
  rw [← e]
  rfl

theorem gram_posSemidef_and_sqAt : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (emb : ι → E →+* K) (n : ℕ) (lam : ι → DomWeight n) (σ : K →+* ℂ), ((Matrix.of fun i j => pairVr emb lam 1 (bVV K lam i) (bVV K lam j)).map σ).PosSemidef ∧ ∀ x : Formalism.L2.DIV.VV K lam, (∑ i, ∑ j, starRingEnd ℂ ((InfinitePlace.mk σ).embedding ((bVV K lam).repr x i)) * (InfinitePlace.mk σ).embedding (pairVr emb lam 1 (bVV K lam i) (bVV K lam j)) * (InfinitePlace.mk σ).embedding ((bVV K lam).repr x j)).re = sqAt σ lam x := by
  intro E K _ _ _ _ _ ι _ emb n lam σ
  rw [pairVr_one_eq]
  refine ⟨?_, fun x => ?_⟩
  · simp only [GlobalTheory.PeriodClassSum.pairK_one_basis]
    exact (GlobalTheory.PeriodClassSum.gramB_posDef lam σ).posSemidef
  · unfold sqAt
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h, ← Complex.conj_re]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

end GlobalTheory.ColNorms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaHalfMulUnrTorus
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp ValuativeRel NumberField IsDedekindDomain
open scoped NNReal

noncomputable section
namespace GlobalTheory.LGrp.BorelCompletion

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem ordV_eq (x : v.adicCompletion F) : Formalism.UG.ordV F v x = -WithZero.log (Valued.v x) := by
  unfold Formalism.UG.ordV
  split_ifs with h
  · simp [h]
  · rw [WithZero.toAdd_unzero_eq_log]

theorem nabs_completion (x : (v.adicCompletion F)ˣ) :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    GlobalTheory.SplitWeil.nabs (v.adicCompletion F) x =
      (Formalism.UG.qV F v : ℝ) ^ (WithZero.log (Valued.v (x : v.adicCompletion F))) := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))
  have hO : 𝒪[v.adicCompletion F] = (v.adicCompletionIntegers F).toSubring := by
    ext y
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
    exact Iff.rfl
  have hq : GlobalTheory.SplitWeil.resCard (v.adicCompletion F) = Formalism.UG.qV F v := by
    rw [← Formalism.UG.P.tjcosets_card_residue]
    exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (RingEquiv.subringCongr hO)).toEquiv
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero (hπ.symm.trans (map_zero _))
  have hle : ∀ y : 𝒪[v.adicCompletion F], Valued.v (y : v.adicCompletion F) ≤ 1 := fun y =>
    he.le_one_iff_le_one.1 ((Valuation.mem_integer_iff _ _).1 y.2)
  have hunit : ∀ y : 𝒪[v.adicCompletion F], IsUnit y ↔ Valued.v (y : v.adicCompletion F) = 1 := fun y => by
    rw [← he.eq_one_iff_eq_one]
    exact (Valuation.integer.integers (valuation (v.adicCompletion F))).isUnit_iff_valuation_eq_one
  have hπO : π ∈ 𝒪[v.adicCompletion F] := by
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  have hirr : Irreducible (⟨π, hπO⟩ : 𝒪[v.adicCompletion F]) := by
    refine ⟨?_, fun a b hab => ?_⟩
    · rw [hunit]
      show Valued.v π ≠ 1
      rw [hπ, ← WithZero.exp_zero, Ne, WithZero.exp_inj]
      norm_num
    · have h1 : Valued.v (a : v.adicCompletion F) * Valued.v (b : v.adicCompletion F) =
          WithZero.exp (-1 : ℤ) := by
        rw [← hπ, ← map_mul]
        exact congrArg _ (congrArg Subtype.val hab).symm
      have ha : Valued.v (a : v.adicCompletion F) ≠ 0 := left_ne_zero_of_mul (by rw [h1]; simp)
      have hb : Valued.v (b : v.adicCompletion F) ≠ 0 := right_ne_zero_of_mul (by rw [h1]; simp)
      have ha1 := hle a
      have hb1 := hle b
      rw [hunit, hunit]
      rw [← WithZero.exp_log ha] at h1 ha1 ⊢
      rw [← WithZero.exp_log hb] at h1 hb1 ⊢
      rw [← WithZero.exp_add, WithZero.exp_inj] at h1
      rw [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1 hb1
      rw [← WithZero.exp_zero, WithZero.exp_inj, WithZero.exp_inj]
      omega
  have h1 := GlobalTheory.SplitWeil.nabs_uniformiser hirr (x := Units.mk0 π hπ0) rfl
  rw [hq] at h1
  set m := WithZero.log (Valued.v (x : v.adicCompletion F)) with hm
  have hx : Valued.v (x : v.adicCompletion F) = WithZero.exp m := (WithZero.exp_log (by simp)).symm
  have h2 : GlobalTheory.SplitWeil.nabs (v.adicCompletion F) (x * (Units.mk0 π hπ0) ^ m) = 1 := by
    apply GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one
    rw [he.eq_one_iff_eq_one, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0,
      hπ, hx, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have h3 : GlobalTheory.SplitWeil.nabs (v.adicCompletion F) ((Units.mk0 π hπ0) ^ m) = ((Formalism.UG.qV F v : ℝ)⁻¹) ^ m := by
    rw [← h1]
    simp only [GlobalTheory.SplitWeil.nabs, map_zpow, NNReal.coe_zpow]
  rw [GlobalTheory.SplitWeil.nabs_mul, h3, inv_zpow] at h2
  exact (eq_inv_of_mul_eq_one_left h2).trans (inv_inv _)

theorem sqrt_zpow_eq (q : ℕ) (m e : ℤ) :
    ((Real.sqrt (((q : ℝ) ^ m) ^ e) : ℝ) : ℂ) = (q : ℂ) ^ ((m : ℂ) * ((e : ℂ) / 2)) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [Real.sqrt_eq_rpow, ← zpow_mul, ← Real.rpow_intCast, ← Real.rpow_mul hq, Complex.ofReal_cpow hq]
  congr 1
  push_cast
  ring

theorem deltaHalf_mul_unrTorus : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) [LocallyCompactSpace (v.adicCompletion F)] (n : ℕ) (α : Fin n → ℂˣ) (b : (borelGL (v.adicCompletion F) (Fin n)).Q), (((borelGL (v.adicCompletion F) (Fin n)).deltaHalf b : ℂˣ) : ℂ) * ((unrTorus (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom α ((borelGL (v.adicCompletion F) (Fin n)).p b) : ℂˣ) : ℂ) = Formalism.UG.chiDelta F v (fun i => (α i : ℂ)) b.1 := by
  intro F _ _ v _ n α b
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  have h := GlobalTheory.BorelModulus.delta_borelGL (v.adicCompletion F) n b
  rw [LeviDatum.deltaHalf_coe, h, Real.sqrt_prod _ (fun i _ => zpow_nonneg (GlobalTheory.SplitWeil.nabs_pos _ _).le _),
    unrTorus_apply, Formalism.UG.chiDelta, Complex.ofReal_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : (((borelGL (v.adicCompletion F) (Fin n)).p b i : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      (b.1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i := rfl
  rw [nabs_completion, sqrt_zpow_eq, unrChar_apply, ordV_eq, e, mul_comm, Units.val_zpow_eq_zpow_val]
  congr 2
  push_cast
  ring

end GlobalTheory.LGrp.BorelCompletion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalToUnitTensorIsPullbackIsIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) (T X' : Scheme.{0}) (φ : X' ⟶ A.left) (p : X' ⟶ T) (t : T ⟶ Sp Rg), (IsPullback φ p A.hom t → IsPullback (φ ≫ GlobalTheory.HomFixUniv.θ A) p (GlobalTheory.HomFixUniv.fA A) t) ∧ GlobalTheory.HomFixUniv.θ A ≫ GlobalTheory.HomFixUniv.fA A = A.hom ∧ IsIso (GlobalTheory.HomFixUniv.θ A) := by
  first | (exact @GlobalTheory.HomFixUniv.θ_pullback) | (exact GlobalTheory.HomFixUniv.θ_pullback) | (intros; apply GlobalTheory.HomFixUniv.θ_pullback  <;> assumption)
end

