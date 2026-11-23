module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1872
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegrality
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1856
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0779
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1893
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
public import Formalism.LocalToGlobal.ProjectiveLattices.TieGenDense
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationValuesIntOfAdmissibleBase

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormClearDenominatorsAwayFromPlace
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.Clear


set_option maxHeartbeats 800000 in
theorem clear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (G : WTZ E) (f : cuspW Xo c U G) (m : HeightOneSpectrum (𝓞 c.F) → ℝ), (Function.support m).Finite → (∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, ((m w : ℝ) : EReal) ≤ v f) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (k : ℤ), (∀ v ∈ valSet Xo c (algCls Xo c) la, ((k : ℝ) : EReal) ≤ v f) → ∃ s : c.F, s ≠ 0 ∧ vLa la s = -k ∧ ∃ g ∈ latW U G, (g : Rul Xo c) = s • (f : Rul Xo c) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro r U G f m hm hmv la k hk
  classical
  set ρ : HeightOneSpectrum (𝓞 c.F) → ℝ := Function.update m la (k : ℝ) with hρ
  have hsupp : (Function.support ρ).Finite := by
    refine (hm.insert la).subset ?_
    intro w hw
    by_cases h : w = la
    · exact Or.inl h
    · right
      simpa [hρ, Function.mem_support, Function.update_of_ne h] using hw
  obtain ⟨a, ha0, hala, hapos⟩ := GlobalTheory.RefSum.ScalApprox.exists_scal c.F ρ hsupp la
  have hρla : ρ la = (k : ℝ) := by simp [hρ]
  have hvla : vAdd la a = -k := by
    rw [hρla, Int.floor_intCast] at hala
    exact_mod_cast hala
  have hle : ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, ((ρ w : ℝ) : EReal) ≤ v (f : Rul Xo c) := by
    intro w v hv
    by_cases h : w = la
    · subst h; rw [hρla]; exact hk v hv
    · rw [show ρ w = m w by simp [hρ, Function.update_of_ne h]]; exact hmv w v hv
  refine ⟨a, ha0, hvla, ⟨a • f, (cuspW Xo c U G).smul_mem a f.2⟩, ?_, rfl⟩
  show _ ∈ GlobalTheory.AllWt.supLat _
  rw [GlobalTheory.AllWt.mem_supLat]
  intro w v hv
  show 0 ≤ v (a • (f : Rul Xo c))
  rw [(isVal_valSet w v hv).smul a _ ha0]
  have h1 : (0 : EReal) ≤ (((vAdd w a : ℤ) : ℝ) : EReal) + ((ρ w : ℝ) : EReal) := by
    rw [← EReal.coe_add]; exact_mod_cast hapos w
  exact h1.trans (add_le_add le_rfl (hle w v hv))

end GlobalTheory.RefSum.Clear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGrowthLeImageDegreeLowerWeight
section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

theorem growthOn_le_compDeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ (Z : Comp Xo c) (G G' : WTZ E), Even G.2 → Even G'.2 → growthOn U Z G ≠ ⊤ → BirOn U Z G → ValMult U Z G G' → growthOn U Z G' ≤ (compDeg U Z G : ℝ≥0∞) := by
  set_option synthInstance.maxHeartbeats 400000 in
    intro E _ _ _ H Dw l Xo c r U hU Z G G' hG hG' hfin hB hM
    rcases eq_or_ne (growthOn U Z G') 0 with h0 | h0
    · rw [h0]; exact bot_le
    obtain ⟨a, θ, ha, hθ, hmul⟩ := hM
    letI : FiniteDimensional c.F (cuspOn U Z G) :=
      GlobalTheory.DegTop.finiteDimensional_of_growthOn (U := U) (Z := Z) hG hfin
    have hR := _root_.GlobalTheory.DegVal.ratioOn_of_birOn E H Dw l Xo c r U Z G hB
    have hFG := _root_.GlobalTheory.DegVal.om_fg E H Dw l Xo c r U hU Z
    set ev := genPoint Z (cuspOn U Z G) with hev
    let S : ℕ → Submodule c.F (Om Z) := fun k =>
      if k = 0 then ⊥ else (cuspOn U Z ((a * k) • G')).map ((genVal Z).toLinearMap ∘ₗ LinearMap.mulLeft c.F (θ ^ k))
    have h1 := _root_.GlobalTheory.ConeDeg.degree_growth_integral.2.2.1 c.F _ _ ev (dimFlag Dw) a ha S (by
      intro k t ht
      by_cases hk : k = 0
      · simp only [S, hk, if_true, Submodule.mem_bot] at ht
        subst ht
        refine ⟨?_, ⟨0, 1, by simp [Submodule.one_eq_span], one_ne_zero, by simp⟩⟩
        rw [IsIntDeg, map_zero, mul_zero]
        exact isIntegral_zero
      · simp only [S, hk, if_false] at ht
        obtain ⟨f, hf, rfl⟩ := ht
        have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk
        obtain ⟨hc, hv⟩ := hmul k hk1 f hf
        exact ⟨_root_.GlobalTheory.DegVal.ValInt.isIntDeg_of_valBound c.F _ _ ev inferInstance inferInstance hFG _ _ hv, hR _ _ hc⟩)
    have hθk : ∀ k : ℕ, genVal Z (θ ^ k) ≠ 0 := fun k => by rw [map_pow]; exact pow_ne_zero _ hθ
    have h2 : growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k) • G')))) ≤
        growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (S k))) :=
      GlobalTheory.DegTop.growth_mono _ fun k hk => by
        have hk0 : k ≠ 0 := by omega
        show _ ≤ Cardinal.toENat (Module.rank c.F (S k))
        have hS : S k = (cuspOn U Z ((a * k) • G')).map ((genVal Z).toLinearMap ∘ₗ LinearMap.mulLeft c.F (θ ^ k)) := if_neg hk0
        rw [hS, GlobalTheory.DegTop.rank_map_mul (U := U) (G := (a * k) • G') (hθk k)]
    have hmulG : ∀ G₀ : WTZ E, growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k) • G₀)))) =
        growthOn U Z (a • G₀) := fun G₀ => by
      rw [growthOn]
      congr 1
      funext k
      rw [mul_nsmul]
    have h3 : growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k) • G')))) =
        (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G' := by
      rw [hmulG, _root_.GlobalTheory.GrowthMul.growthOn_nsmul E H Dw l Xo c r U hU Z G' hG' a ha]
    have h4 : growth (dimFlag Dw) (fun k => hilb ev (a * k)) ≤ (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G := by
      rw [← _root_.GlobalTheory.GrowthMul.growthOn_nsmul E H Dw l Xo c r U hU Z G hG a ha, ← hmulG]
      exact GlobalTheory.DegTop.growth_mono _ fun k hk => GlobalTheory.DegTop.hilb_le hG (Nat.mul_pos ha hk)
    have haD0 : (a : ℝ≥0∞) ^ dimFlag Dw ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
    have haDT : (a : ℝ≥0∞) ^ dimFlag Dw ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
    have hlow : (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G' ≤ growth (dimFlag Dw) (fun k => hilb ev (a * k)) :=
      h3 ▸ h2.trans h1
    have hne0 : growth (dimFlag Dw) (fun k => hilb ev (a * k)) ≠ 0 :=
      ne_bot_of_le_ne_bot (mul_ne_zero haD0 h0) hlow
    have hneT : growth (dimFlag Dw) (fun k => hilb ev (a * k)) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top haDT hfin) h4
    obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.ConeDeg.degree_growth_integral.2.1 c.F _ _ ev (dimFlag Dw) a ha hne0 hneT
    rw [_root_.GlobalTheory.ConeDeg.degree_growth_integral.1 c.F _ _ ev (dimFlag Dw) a ha δ hδ] at hlow
    rw [compDeg, ← hev, hδ.imageDeg_eq]
    first | exact (ENNReal.mul_le_mul_iff_right haD0 haDT).1 hlow | exact (ENNReal.mul_le_mul_iff_left haD0 haDT).1 hlow

end GlobalTheory.DegVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRatiosGenerateAtFlagSpaceGenericPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_ratios_generate_at_flagSpace_genericPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw), Nonempty (Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) → GlobalTheory.DegVal.BirOn U Z (wtOf Dw la 0) → RatGen X Z U la := by
  first | exact @GlobalTheory.HSApp.ratGen_of_birOn | exact GlobalTheory.HSApp.ratGen_of_birOn | (intros; apply GlobalTheory.HSApp.ratGen_of_birOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSupLatticeDegreeTwistLowerBound
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.FlatTw

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

theorem degOn_add_rank_mul_degLo_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E) (B : Finset ℕ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → (∀ p ∈ B, p.Prime) → IntOff B s.lo → GoodOn U x V dict Z G → degOn U x V dict Z G + (rankOn U Z G : ℝ) * (s.degLo - logSum B) ≤ degOn U x V dict Z (G + G₀) := by
  intro E _ _ _ H Dw l Xo c r U x D V dict Z G₀ s G B hU hG hB hInt hGood
  haveI : IsTotallyComplex c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => CompHt.conj_comp_ne (c := c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  obtain ⟨a, 𝔞, ha, h𝔞, hint, hsum⟩ := GlobalTheory.T.exists_ideal_rounding_realExponents_badPrimes c.F B s.lo hB s.finite_lo hInt
  obtain ⟨φ, hφ, -, hlat, -⟩ := _root_.GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ s G hG
  have hPres : GoodOn U x V dict Z (G + G₀) ∧ rankOn U Z (G + G₀) = rankOn U Z G :=
    _root_.GlobalTheory.FlatTw.Good.twist_goodOn E H Dw l Xo c r U x D V dict Z G₀ s G hU hG hGood
  have hGood' : GoodOn U x V dict Z (G + G₀) := hPres.1
  have hrk : rankOn U Z (G + G₀) = rankOn U Z G := hPres.2
  have hna : ∀ σ : c.F →+* ℂ, 0 < ‖σ a‖ := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 ha)
  set t : (c.F →+* ℂ) → ℝ := fun σ => ‖σ a‖ * s.cInf σ with ht
  have ht0 : ∀ σ, 0 < t σ := fun σ => mul_pos (hna σ) (s.cInf_pos σ)
  have htc : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ := fun σ => by
    simp only [ht, RingHom.comp_apply, Complex.norm_conj]
    rw [s.cInf_congr (CompHt.goodOf_conj σ)]
  let ψ : cuspOn U Z G →ₗ[c.F] cuspOn U Z (G + G₀) := a • φ.toLinearMap
  have hψ : Function.Injective ψ := fun f g h => φ.injective (smul_right_injective _ ha h)
  have hN : ∀ σ f, normOn U x V dict Z (G + G₀) σ (ψ f) ≤ t σ * normOn U x V dict Z G σ f := by
    intro σ f
    apply le_of_eq
    have e : ((ψ f : cuspOn U Z (G + G₀)) : Rul Xo c) = a • ((f : Rul Xo c) * s.sig) := by
      simp [ψ, hφ]
    simp only [normOn]
    rw [e, petOn_smul, petOn, petOn, _root_.GlobalTheory.FlatTw.PetTw.petAt_mul_sig E H Dw l Xo c r U x Z G₀ s G hG f f.2.2 σ D _ _ _]
    simp only [ht]
    ring
  have hL : 𝔞 • (latOn U Z G).map (ψ.restrictScalars (𝓞 c.F)) ≤ latOn U Z (G + G₀) := by
    rw [Submodule.smul_le]
    rintro b hb _ ⟨f, hf, rfl⟩
    by_cases hb0 : b = 0
    · rw [hb0, zero_smul]; exact zero_mem _
    · have hb' : (b : c.F) ≠ 0 := by simpa using hb0
      refine hlat ((b : c.F) * a) (mul_ne_zero hb' ha) (hint b hb hb0) f hf _ ?_
      rw [← IsScalarTower.algebraMap_smul c.F b]
      simp [ψ, mul_smul]
      rfl
  have key := _root_.GlobalTheory.TwistIdeal.deg_add_le_deg_of_ideal_smul_le c.F _ _ (normOn U x V dict Z G) (normOn U x V dict Z (G + G₀)) ψ t (latOn U Z G)
    (latOn U Z (G + G₀)) 𝔞 hGood.1 hGood'.1 hψ ht0 htc hN hGood.2.1 hGood'.2.1 h𝔞 hL hrk
  have hlog : ∑ σ, Real.log (t σ) = ∑ σ : c.F →+* ℂ, Real.log ‖σ a‖ + ∑ σ, Real.log (s.cInf σ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => Real.log_mul (hna σ).ne' (s.cInf_pos σ).ne'
  have hdeg : s.degLo - logSum B ≤ -((∑ σ, Real.log (t σ)) / (Module.finrank ℚ c.F : ℝ)) -
      Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ c.F : ℝ) := by
    rw [hlog, add_div]
    unfold TwSec.degLo lineDeg logSum
    linarith [hsum]
  exact le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdeg (Nat.cast_nonneg _))) key

end GlobalTheory.FlatTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspSectionAnnihilator
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore Filter Topology

namespace GlobalTheory.FlatCore

theorem exists_ringHom_ne_zero_of_not_isNilpotent {K R : Type} [Field K] [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (σ : K →+* ℂ) {b : R} (hb : ¬ IsNilpotent b) :
    ∃ φ : R →+* ℂ, φ.comp (algebraMap K R) = σ ∧ φ b ≠ 0 := by
  haveI hJ : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  have hrad : b ∉ (⊥ : Ideal R).jacobson := by
    rw [← Ideal.radical_eq_jacobson]
    intro h
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 h
    exact hb ⟨n, by simpa using hn⟩
  rw [Ideal.jacobson, Submodule.mem_sInf] at hrad
  push_neg at hrad
  obtain ⟨m, ⟨-, hm⟩, hbm⟩ := hrad
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType K (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective _ _)
  haveI : Module.Finite K (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ m)
  haveI : Algebra.IsAlgebraic K (R ⧸ m) := Algebra.IsAlgebraic.of_finite K (R ⧸ m)
  letI : Algebra K ℂ := σ.toAlgebra
  let ψ : (R ⧸ m) →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨ψ.toRingHom.comp (Ideal.Quotient.mk m), ?_, ?_⟩
  · ext a
    show ψ (Ideal.Quotient.mkₐ K m (algebraMap K R a)) = σ a
    rw [AlgHom.commutes, AlgHom.commutes]
    rfl
  · show ψ (Ideal.Quotient.mk m b) ≠ 0
    rw [map_ne_zero_iff ψ ψ.toRingHom.injective]
    exact fun h => hbm (Ideal.Quotient.eq_zero_iff_mem.1 h)

theorem differentiableOn_of_mem_holSub {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {C : Type}
    {X : C → Data E r} {la : ∀ k, Wt (X k).Ψ r} {P : FDSec X} (hP : P ∈ holSub X la) (k : C) :
    DifferentiableOn ℂ (P k) (X k).dom := by
  induction hP using Submodule.span_induction with
  | mem P h => exact (h k).1.1.1
  | zero => exact differentiableOn_const 0
  | add P Q _ _ hP hQ => exact hP.add hQ
  | smul a P _ hP => exact hP.const_smul a

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c}

theorem genVal_ne_zero_of_mem_cuspOn (hf : f ∈ cuspOn U Z G) (hf0 : f ≠ 0) : genVal Z f ≠ 0 := by
  have hG : GenFrEx Xo c := (GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  intro h0
  refine hf0 (secZ_eq_zero_of_genVal (cuspW_le_secZ G (Submodule.mem_inf.1 hf).1) fun Z' => ?_)
  by_cases hZ : Z' = Z
  · rw [hZ]; exact h0
  · rw [genVal_apply hG]; exact evC_eq_zero hG hZ (Submodule.mem_inf.1 hf).2

theorem idem_mul_eq_zero_of_mul_eq_zero (hf : f ∈ cuspOn U Z G) (hf0 : f ≠ 0) {e' : Ix Dw → ℤ} {s : Rul Xo c}
    (hs : s ∈ secZ Xo c e') (hsf : s * f = 0) : idem Z * s = 0 := by
  have hG : GenFrEx Xo c := (GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  have h1 : genVal Z s = 0 := by
    have h2 := congrArg (genVal Z) hsf
    rw [map_mul, map_zero] at h2
    exact (mul_eq_zero.1 h2).resolve_right (genVal_ne_zero_of_mem_cuspOn hf hf0)
  refine secZ_eq_zero_of_genVal (mul_mem_secZ (idem_mem_secZ Z) hs) fun Z' => ?_
  rw [map_mul]
  by_cases hZ : Z' = Z
  · rw [hZ, h1, mul_zero]
  · rw [genVal_apply hG Z' (idem Z), evC_eq_zero hG hZ (idem_mem_suppOn Z), zero_mul]

end GlobalTheory.FlatCore

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepExistenceStatement
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.DeepExist

theorem floorThreeLOverLogThree_mul_log_fifteen_le {L : ℝ} (hL : 0 ≤ L) : (expL L : ℝ) * Real.log 15 ≤ 9 * L := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have he : (expL L : ℝ) ≤ 3 * L / Real.log 3 := Nat.floor_le (by positivity)
  have he' : (expL L : ℝ) * Real.log 3 ≤ 3 * L := (le_div_iff₀ h3).1 he
  have h15 : Real.log 15 ≤ 3 * Real.log 3 := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 15) (by norm_num : (15 : ℝ) ≤ 3 ^ 3)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have he0 : (0 : ℝ) ≤ expL L := Nat.cast_nonneg _
  nlinarith

theorem size_le {D : D7} {L : SizeData₂ D} {PP A M o : ℝ} (hN : HostNum D L PP A M) (hF : o ≤ 217 * zBase L ^ 2) :
    o + 20 * (Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * 15 ^ expL L.sc.L) + Real.log D.host.d + 1) ≤
      391 * zBase L ^ 2 := by
  have hL10 := hN.big.2.1
  have hcop := hN.cop
  have h01 : D.host.g 0 * D.host.g 1 ≠ 0 := fun h => by
    rw [h, Nat.coprime_zero_right] at hcop
    norm_num at hcop
  have hg0 : ((D.host.g 0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (mul_ne_zero_iff.1 h01).1
  have hg1 : ((D.host.g 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (mul_ne_zero_iff.1 h01).2
  have h15 : ((15 : ℝ) ^ expL L.sc.L) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hlog : Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * 15 ^ expL L.sc.L) =
      Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ) + expL L.sc.L * Real.log 15 := by
    rw [Real.log_mul (mul_ne_zero hg0 hg1) h15, Real.log_mul hg0 hg1, Real.log_pow]
  have he := floorThreeLOverLogThree_mul_log_fifteen_le (L := L.sc.L) (by linarith)
  have a0 := hN.logg 0
  have a1 := hN.logg 1
  have ad := hN.logd
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hN.f8
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hZ : 8 * L.sc.L ≤ zBase L := by
    unfold zBase
    have : (8 : ℝ) ≤ D.R.f * D.R.r := by nlinarith
    nlinarith
  rw [hlog]
  nlinarith

end GlobalTheory.CovTop.DeepExist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationValuesNormsEqUniformizerZpow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow.DiscNorm

theorem norm_eq_zpow {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    {C : Type} [NormedField C] (f : FractionRing V →+* C) (hf : ∀ r : V, ‖f (algebraMap V _ r)‖ ≤ 1)
    {k : FractionRing V} (hk : k ≠ 0) : ∃ n : ℤ, ‖f k‖ = ‖f (algebraMap V _ ϖ)‖ ^ n := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) k
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hk
  set g : V →+* C := f.comp (algebraMap V _)
  have key : ∀ x : V, x ≠ 0 → ∃ m : ℕ, ‖g x‖ = ‖g ϖ‖ ^ m := fun x hx => by
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    refine ⟨m, ?_⟩
    rw [map_mul, norm_mul, map_pow, norm_pow, GlobalTheory.Ex.IntVal.norm_unit g hf u.isUnit, _root_.one_mul]
  obtain ⟨ma, ea⟩ := key a ha0
  obtain ⟨mb, eb⟩ := key b hb0
  have ht : ‖g ϖ‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    exact hϖ.ne_zero (IsFractionRing.injective V (FractionRing V) (f.injective (by simpa [g] using h)))
  refine ⟨(ma : ℤ) - mb, ?_⟩
  show ‖f (algebraMap V _ a / algebraMap V _ b)‖ = ‖g ϖ‖ ^ ((ma : ℤ) - mb)
  rw [map_div₀, norm_div]
  show ‖g a‖ / ‖g b‖ = _
  rw [zpow_sub₀ ht, zpow_natCast, zpow_natCast]
  exact congrArg₂ (· / ·) ea eb

theorem vF_eq_alg {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → ((TK R).left ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (J : (Sp F ⟶ X) → L.ι)
    (hW : ⊤ ≤ jFK (R := R) F ⁻¹ᵁ LB.wchart L φ (fun k => J (jFK (R := R) F ≫ φ k))) :
    ∃ k : FractionRing R, k ≠ 0 ∧ vF t (jFK (R := R) F) J = algebraMap (FractionRing R) F k := by
  set W := LB.wchart L φ (fun k => J (jFK (R := R) F ≫ φ k))
  have h' : ⊤ ≤ (𝟙 (TK R).left) ⁻¹ᵁ W := by
    intro x _
    obtain ⟨y⟩ : Nonempty (Sp F) := inferInstance
    have hy := hW (Set.mem_univ y)
    have hs : Subsingleton (PrimeSpectrum (FractionRing R)) := inferInstance
    have : (jFK (R := R) F).base y = x := @Subsingleton.elim (PrimeSpectrum (FractionRing R)) hs _ _
    rw [← this]; exact hy
  refine ⟨GlobalTheory.Ex.IntVal.evR (𝟙 _) W h' (t.s _).val, ?_, ?_⟩
  · exact ((Units.isUnit _).map _).ne_zero
  · have := GlobalTheory.Ex.IntVal.valF_comp (algebraMap (FractionRing R) F) (𝟙 (TK R).left) W h' (t.s _).val
    have e : spMap (algebraMap (FractionRing R) F) ≫ 𝟙 (TK R).left = jFK (R := R) F := Category.comp_id _
    rw [e] at this
    exact this

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ‖ν.rg‖ = 1 ∧ ∀ χ, ∃ n : ℤ, ‖(N.ψ χ : C)‖ = ‖toF V C ϖ‖ ^ n := by
  intro V _ _ _ ϖ hϖ D C _ _ _ hC N ν hν
  obtain ⟨S, hS, hI⟩ := hν
  let f : V →+* C := toF V C
  let g : V →+* S := f.codRestrict S fun x => (hS _).2 (hC.1 x)
  have hg : spMap S.subtype ≫ spMap g = (TF (R := V) C).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  have hrig : ‖ν.rg‖ = 1 := GlobalTheory.Ex.IntVal.norm_vF hS hI _ _ (spMap g) hg fun _ =>
      (congrArg ((TF (R := V) C).hom ≫ ·) (Over.w η[D.toPre.P.A])).trans (Category.comp_id _)
  refine ⟨hrig, fun χ => ?_⟩
  have hW : ⊤ ≤ jFK (R := V) C ⁻¹ᵁ LB.wchart D.toPre.P.L (fun _ : PUnit => D.toPre.xK (ν.eX χ))
      (fun _ => ν.J (jFK (R := V) C ≫ D.toPre.xK (ν.eX χ))) := fun y hy => Set.mem_iInter.2 fun _ => ν.good _ hy
  obtain ⟨k, hk, ek⟩ := vF_eq_alg (D.toPre.psi (ν.eX χ)) ν.J hW
  obtain ⟨n, hn⟩ := norm_eq_zpow hϖ (algebraMap (FractionRing V) C) hC.1 hk
  refine ⟨n, ?_⟩
  rw [ν.ψ_eq, norm_mul]
  change _ * ‖ν.rg‖ = _
  rw [hrig, _root_.mul_one, ek, hn]
  rfl

end GlobalTheory.MBLow.DiscNorm
end
end

