module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingReindex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalOfConvolutionFixedModerateGrowth
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.CuspFixed

theorem isHaarSub_map_emb {H G : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (ι : H →* G) (hι : Topology.IsClosedEmbedding ι) (N : Subgroup H)
    (hN : IsClosed (N : Set H)) (ν : Measure H) (hν : IsHaarSub (N : Set H) ν) :
    IsClosed ((N.map ι : Subgroup G) : Set G) ∧ IsHaarSub ((N.map ι : Subgroup G) : Set G) (ν.map ι) := by
  have hme : MeasurableEmbedding ι := hι.measurableEmbedding
  have hS : ((N.map ι : Subgroup G) : Set G) = ι '' (N : Set H) := Subgroup.coe_map ι N
  obtain ⟨hne, hfc, hnull, hinv⟩ := hν
  refine ⟨by rw [hS]; exact hι.isClosedMap _ hN, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply hne
    rwa [Measure.map_eq_zero_iff hme.measurable.aemeasurable] at h0
  · refine ⟨fun K hK => ?_⟩
    rw [hme.map_apply]
    exact hfc.lt_top_of_isCompact (hι.isCompact_preimage hK)
  · rw [hme.map_apply, Set.preimage_compl, hS, Set.preimage_image_eq _ hι.injective]
    exact hnull
  · intro m hm
    rw [hS] at hm
    obtain ⟨k, hk, rfl⟩ := hm
    have hcomm : (fun z : G => ι k * z) ∘ ι = ι ∘ (fun z : H => k * z) := by
      funext z
      simp only [Function.comp_apply, map_mul]
    rw [Measure.map_map (continuous_const_mul (ι k)).measurable hme.measurable, hcomm,
      ← Measure.map_map hme.measurable (continuous_const_mul k).measurable, hinv k hk]

theorem constTerm_repro {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ ν : Measure G) [SFinite μ]
    [μ.IsMulLeftInvariant] [IsFiniteMeasure ν] (f φ : G → ℂ) (hf : Continuous f) (hφ : Measurable φ) (x : G)
    (Φ : G → ℝ) (hΦ : Integrable Φ μ) (hb : ∀ᵐ m ∂ν, ∀ g, ‖φ g * f (m * x * g)‖ ≤ Φ g)
    (hr : ∀ z, f z = ∫ g, φ g * f (z * g) ∂μ) :
    Integrable (fun y => (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y)) μ ∧
      ∫ m, f (m * x) ∂ν = ∫ y, (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y) ∂μ := by
  have hmeas : Measurable (Function.uncurry fun (m g : G) => φ g * f (m * x * g)) := by
    apply Measurable.mul
    · exact hφ.comp measurable_snd
    · exact (hf.comp (by fun_prop : Continuous fun p : G × G => p.1 * x * p.2)).measurable
  have hint : Integrable (Function.uncurry fun (m g : G) => φ g * f (m * x * g)) (ν.prod μ) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod hΦ) hmeas.aestronglyMeasurable ?_
    have hae := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := μ)).ae hb
    filter_upwards [hae] with p hp
    simpa [Function.uncurry] using hp p.2
  have hH : (fun g => ∫ m, φ g * f (m * x * g) ∂ν) =
      fun g => (fun y => (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y)) (x * g) := by
    funext g
    beta_reduce
    rw [integral_const_mul, inv_mul_cancel_left, mul_comm]
    simp_rw [mul_assoc]
  have hI : Integrable (fun g => ∫ m, φ g * f (m * x * g) ∂ν) μ := hint.integral_prod_right
  rw [hH] at hI
  have hI2 := hI.comp_mul_left x⁻¹
  simp only [mul_inv_cancel_left] at hI2
  refine ⟨hI2, ?_⟩
  calc ∫ m, f (m * x) ∂ν = ∫ m, ∫ g, φ g * f (m * x * g) ∂μ ∂ν := by
        congr 1; funext m; exact hr (m * x)
    _ = ∫ g, ∫ m, φ g * f (m * x * g) ∂ν ∂μ := integral_integral_swap hint
    _ = ∫ g, (fun y => (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y)) (x * g) ∂μ := by rw [hH]
    _ = ∫ y, (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y) ∂μ :=
        integral_mul_left_eq_self (fun y => (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y)) x

theorem continuous_phe (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (hd : IsDSData B d) : Continuous (phe B d) := by
  have he : Continuous B.e := (rowsAut_idem_elementary B).2.2.2
  have hv : ∀ v, Continuous (fun g : B.I.Ginf => B.σ v (uMat (g v)) (B.w v)) := by
    intro v
    have hc := ((hd v).2.1.2.2.1).2.2 (B.w v)
    exact hc.comp_continuous ((Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v))
      (fun g => (g v).2)
  have hph : Continuous (ph B d) := by
    unfold ph
    exact continuous_const.mul
      (continuous_star.comp (continuous_finsetProd _ fun v _ => continuous_const.inner (hv v)))
  unfold phe
  exact (hph.comp continuous_fst).mul (he.comp continuous_snd)

theorem one_le_of_isIsot (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (hW : I.IsIsot W) : 1 ≤ I.n := by
  rcases Nat.eq_zero_or_pos I.n with h0 | hpos
  · exfalso
    apply hW.1
    rw [Submodule.eq_bot_iff]
    intro x _
    funext i
    exact absurd i.isLt (by omega)
  · exact hpos


open Classical in
noncomputable def incl (I : AutInst) (v : InfinitePlace I.F) : UJ (I.ε v) →* I.GA :=
  (MonoidHom.inl I.Ginf I.Gf).comp (MonoidHom.mulSingle (fun v => UJ (I.ε v)) v)

theorem isClosedEmbedding_incl (I : AutInst) (v : InfinitePlace I.F) : Topology.IsClosedEmbedding (incl I v) := by
  obtain ⟨hT2, -⟩ := CongTop.adelic_topology I
  haveI := hT2
  classical
  refine Function.LeftInverse.isClosedEmbedding (f := fun p : I.GA => p.1 v) ?_ ?_ ?_
  · intro m
    simp [incl]
  · exact (continuous_apply v).comp continuous_fst
  · exact (continuous_mulSingle (A := fun w : InfinitePlace I.F => UJ (I.ε w)) v).prodMk continuous_const

theorem cusp_of_fixed : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0) → LocDec B h → HBig B 40 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ) (C : ℝ), T y = y → IsContRep B y f → (∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)) → (∀ W, B.I.IsIsot W → ∀ ν : Measure B.I.GA, B.I.IsNQuotMeas W ν → ∀ x, ∫ m, f (m * x) ∂ν = 0) ∧ B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext y) := by
  intro B d h hd hfib hloc hbig T hT y f C hfix hrep hgr
  obtain ⟨hT2, hLC, hSC, -⟩ := CongTop.adelic_topology B.I
  haveI := hT2
  haveI := hLC
  haveI := hSC
  haveI hHaar : (B.I.muA B.μf).IsHaarMeasure := by
    haveI h1 : ∀ w, (muG (B.I.ε w)).IsHaarMeasure := fun w => inferInstance
    haveI h2 : ∀ w, SigmaFinite (muG (B.I.ε w)) := fun w => inferInstance
    haveI h3 : (Measure.pi fun w => muG (B.I.ε w)).IsHaarMeasure := Measure.pi.isHaarMeasure _
    haveI h4 : SFinite (Measure.pi fun w => muG (B.I.ε w)) := inferInstance
    haveI h5 : SFinite B.μf := inferInstance
    unfold AutInst.muA
    exact Measure.prod.instIsHaarMeasure _ _
  have main : ∀ W, B.I.IsIsot W → ∀ ν : Measure B.I.GA, B.I.IsNQuotMeas W ν →
      ∀ x, ∫ m, f (m * x) ∂ν = 0 := by
    intro W hW ν hνW x
    have hn : 1 ≤ B.I.n := one_le_of_isIsot B.I W hW
    obtain ⟨⟨Φ, hΦi, hΦb⟩, hrepf⟩ := _root_.GlobalTheory.ReproducingFixed.reproducing_fixed B d h hd hn hloc hbig T hT y f C hfix hrep hgr
    obtain ⟨hfin, -, hconc, hinvN⟩ := hνW
    haveI := hfin
    obtain ⟨c, hc0, hc⟩ := exists_pos_le_tau1_mul_of_mem_NA_of_isIsot B.I W x hW
    have hbd : ∀ᵐ m ∂ν, ∀ g, ‖phe B d g * f (m * x * g)‖ ≤
        c⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g := by
      filter_upwards [mem_ae_iff.mpr hconc] with m hm g
      have ht : c ≤ tau1 B.I (m * x) := hc m hm
      have htpos : 0 < tau1 B.I (m * x) := hc0.trans_le ht
      have hb1 := hΦb (m * x) g
      have hpow : 0 < (tau1 B.I (m * x))⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) :=
        pow_pos (inv_pos.mpr htpos) _
      have hΦ0 : 0 ≤ Φ g := (mul_nonneg_iff_of_pos_left hpow).mp ((norm_nonneg _).trans hb1)
      exact hb1.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (inv_nonneg.mpr htpos.le) (inv_anti₀ hc0 ht) _) hΦ0)
    obtain ⟨hint, heq⟩ := constTerm_repro (B.I.muA B.μf) ν f (phe B d) hrep.1
      (continuous_phe B d hd).measurable x (fun g => c⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g)
      (hΦi.const_mul _) hbd hrepf
    rw [heq]
    obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
    obtain ⟨Wv, hWv, hemb⟩ := RadEmb.radical_embeds B.I W v hW
    obtain ⟨νv, hνv⟩ := exists_isHaarSub_NW (B.I.ε v) Wv
    have hNcl : IsClosed ((nwSub (B.I.ε v) Wv : Subgroup (UJ (B.I.ε v))) : Set (UJ (B.I.ε v))) := by
      rw [coe_nwSub]
      exact isClosed_NW _ _
    have hνv' : IsHaarSub ((nwSub (B.I.ε v) Wv : Subgroup (UJ (B.I.ε v))) : Set (UJ (B.I.ε v))) νv := by
      rw [coe_nwSub]
      exact hνv
    have hemb' := isClosedEmbedding_incl B.I v
    obtain ⟨hNcl', hHs⟩ := isHaarSub_map_emb (incl B.I v) hemb' _ hNcl νv hνv'
    refine weilVanish B.I.GA (B.I.muA B.μf) _ _ hNcl' hHs (fun z => ∫ m, f (m * z) ∂ν)
      (fun z => phe B d (x⁻¹ * z)) ?_ ?_ ?_ hint ?_
    · exact (StronglyMeasurable.integral_prod_right' (ν := ν)
        (f := fun p : B.I.GA × B.I.GA => f (p.2 * p.1))
        (hrep.1.comp (continuous_snd.mul continuous_fst)).stronglyMeasurable).measurable
    · exact ((continuous_phe B d hd).comp (continuous_const.mul continuous_id)).measurable
    · intro n hn z
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hn
      have hk' : k ∈ NW (B.I.ε v) Wv := by
        rw [← coe_nwSub]
        exact hk
      have hkNA : incl B.I v k ∈ B.I.NA W := hemb k hk'
      have hsh := hinvN (fun m => f (m * z)) (fun γ hγ w => by
        show f (γ * w * z) = f (w * z)
        rw [mul_assoc]
        exact hrep.2.1 γ hγ.1 (w * z)) (incl B.I v k) hkNA
      show ∫ m, f (m * (incl B.I v k * z)) ∂ν = ∫ m, f (m * z) ∂ν
      simpa only [mul_assoc] using hsh
    · intro z
      rw [hemb'.measurableEmbedding.integral_map]
      have hz := hfib v Wv hWv νv hνv x⁻¹ z
      simp only [← mul_assoc]
      exact hz
  refine ⟨main, ?_⟩
  intro W hW ν hνW
  have hae := (ExtContRep.ext_ae_eq_contRep B y f hrep).2.2.2 ν hνW.1
  filter_upwards [hae] with x hx
  rw [integral_congr_ae hx]
  exact main W hW ν hνW x

end GlobalTheory.CuspFixed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativeClosedClassBoundedByInverseLeastSize
section
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

namespace GlobalTheory.SobolevBound

private lemma exists_re_trace_orthonormal_gLie {n : ℕ} (ε : Fin n → Bool) :
    ∃ E : Fin (n ^ 2) → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε,
      ∀ i j, (((E i : Matrix (Fin n) (Fin n) ℂ) * (E j : Matrix (Fin n) (Fin n) ℂ)ᴴ).trace).re =
        if i = j then 1 else 0 := by

  classical
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJJ' : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hmem : ∀ X : Matrix (Fin n) (Fin n) ℂ,
      X ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε ↔ Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := fun X => Iff.rfl

  have hA : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      Z - Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε := by
    intro Z
    rw [hmem]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hJh, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hJJ, Matrix.mul_one, hJJ']
    abel
  have hB : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      Complex.I • (Z + Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε := by
    intro Z
    rw [hmem]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hJh, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hJJ,
      Matrix.mul_one, hJJ', smul_mul_assoc, mul_smul_comm, Complex.star_def, Complex.conj_I, neg_smul,
      smul_add, neg_mul]
    abel
  let L : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε × GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun p => (p.1 : Matrix (Fin n) (Fin n) ℂ) + Complex.I • (p.2 : Matrix (Fin n) (Fin n) ℂ)
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
        abel
      map_smul' := fun r p => by
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, smul_add]
        rw [smul_comm r Complex.I] }
  have hsurj : Function.Surjective L := by
    intro Z
    refine ⟨(⟨(2⁻¹ : ℝ) • (Z - Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε),
      (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε).smul_mem _ (hA Z)⟩,
      ⟨(-2⁻¹ : ℝ) • (Complex.I • (Z + Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε)),
      (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε).smul_mem _ (hB Z)⟩), ?_⟩
    change (2⁻¹ : ℝ) • (Z - Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε) +
      Complex.I • ((-2⁻¹ : ℝ) • (Complex.I • (Z + Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε))) = Z
    generalize Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε = W
    ext a b
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    linear_combination (-(1 : ℂ) / 2 * (Z a b + W a b)) * Complex.I_sq
  have hfin : n ^ 2 ≤ Module.finrank ℝ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε) := by
    have h1 := LinearMap.finrank_le_finrank_of_surjective hsurj
    rw [Module.finrank_prod, Module.finrank_matrix, Fintype.card_fin, Complex.finrank_real_complex] at h1
    nlinarith [h1]

  let Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin n × Bool) :=
    { toFun := fun X => WithLp.toLp 2 (fun q => if q.2.2 then (X q.1 q.2.1).re else (X q.1 q.2.1).im)
      map_add' := fun X Y => by
        ext q
        by_cases h : q.2.2 <;> simp [h]
      map_smul' := fun r X => by
        ext q
        by_cases h : q.2.2 <;> simp [h] }
  have hΦapp : ∀ X q, (Φ X) q = if q.2.2 then (X q.1 q.2.1).re else (X q.1 q.2.1).im := fun _ _ => rfl
  have hΦ : ∀ X Y, inner ℝ (Φ X) (Φ Y) = ((X * Yᴴ).trace).re := by
    intro X Y
    rw [PiLp.inner_apply]
    simp only [hΦapp, Fintype.sum_prod_type, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
      Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hΦinj : Function.Injective Φ := by
    intro X Y h
    ext a b
    apply Complex.ext
    · have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin n × Fin n × Bool) => v (a, b, true)) h
      simpa [hΦapp] using h1
    · have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin n × Fin n × Bool) => v (a, b, false)) h
      simpa [hΦapp] using h1
  let Ψ := Φ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε).subtype
  have hΨ : Function.Injective Ψ := by
    intro x y h
    apply Subtype.ext
    apply hΦinj
    simpa [Ψ] using h
  have hS : n ^ 2 ≤ Module.finrank ℝ (LinearMap.range Ψ) := by
    rw [LinearMap.finrank_range_of_inj hΨ]
    exact hfin
  let b := stdOrthonormalBasis ℝ (LinearMap.range Ψ)
  have hbo : Orthonormal ℝ (fun i => ((b i : LinearMap.range Ψ) : EuclideanSpace ℝ (Fin n × Fin n × Bool))) :=
    b.orthonormal.comp_linearIsometry (LinearMap.range Ψ).subtypeₗᵢ
  have hpre : ∀ i, ∃ X : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε, Φ (X : Matrix (Fin n) (Fin n) ℂ) = b i := by
    intro i
    obtain ⟨X, hX⟩ := LinearMap.mem_range.1 (b i).2
    exact ⟨X, by simpa [Ψ] using hX⟩
  choose X hX using hpre
  refine ⟨fun j => X (Fin.castLE hS j), fun i j => ?_⟩
  dsimp only
  rw [← hΦ, hX, hX]
  have h2 := orthonormal_iff_ite.1 hbo (Fin.castLE hS i) (Fin.castLE hS j)
  rw [h2]
  simp

theorem derivative_closed_class_bound : ∀ (B : RowsAut), 1 ≤ B.I.n → 1 ≤ B.g → ∃ m : ℕ, ∀ W : Set (B.I.GA → ℂ), (∀ f ∈ W, (∃ F, GlobalTheory.Dec.IsContRep B F f) ∧ (∀ k ∈ B.I.Kg B.g, ∀ y, f (y * (1, k)) = f y) ∧ ∀ (v : InfinitePlace B.I.F) (E : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (B.I.ε v)), ∃ f' ∈ W, ∀ y, HasDerivAt (fun t : ℝ => f (y * GlobalTheory.SobolevBound.onePar B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace B v E) t)) (f' y) 0) → ∀ f ∈ W, ∃ C : ℝ, ∀ y, ‖f y‖ ≤ C * (GlobalTheory.Count.tau1 B.I y)⁻¹ ^ m := by
  intro B hn hg
  classical
  refine ⟨2 * (B.I.n ^ 2 * B.I.f), ?_⟩
  intro W hW f hf

  choose E hE using fun v : InfinitePlace B.I.F => exists_re_trace_orthonormal_gLie (B.I.ε v)
  choose c hc using fun v : InfinitePlace B.I.F => GlobalTheory.GaugeConst.gauge_exists_pos_unique B.I.n (B.I.ε v)
  let e : Fin (Fintype.card (InfinitePlace B.I.F)) ≃ InfinitePlace B.I.F :=
    (Fintype.equivFin (InfinitePlace B.I.F)).symm

  have hnr : (1 : ℝ) ≤ B.I.n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < B.I.n := by linarith
  have hp5 : (0 : ℝ) < (B.I.n : ℝ) ^ 5 := pow_pos hn0 5
  have h35 : (B.I.n : ℝ) ^ 3 ≤ (B.I.n : ℝ) ^ 5 := pow_le_pow_right₀ hnr (by norm_num)
  have hden : (0 : ℝ) < 12 * (B.I.n : ℝ) ^ 5 := by linarith
  have hs : (0 : ℝ) < 1 / (12 * (B.I.n : ℝ) ^ 5) := div_pos one_pos hden
  have h3 : 12 * (B.I.n : ℝ) ^ 3 * (1 / (12 * (B.I.n : ℝ) ^ 5)) ≤ 1 := by
    rw [mul_one_div, div_le_one hden]
    linarith
  have h5 : 8 * (B.I.n : ℝ) ^ 5 * (1 / (12 * (B.I.n : ℝ) ^ 5)) ≤ 1 := by
    rw [mul_one_div, div_le_one hden]
    linarith
  obtain ⟨C0, hC0, hsob⟩ := GlobalTheory.sobolev_iterated_one_parameter_subgroups_words B.I.GA
    (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2)
    (fun l => onePar B (atPlace B (e l.divNat) (E _ l.modNat))) (1 / (12 * (B.I.n : ℝ) ^ 5)) hs
    (fun l => onePar_spec B _)

  have hder : ∀ g ∈ W, ∀ l : Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2), ∃ g' ∈ W, ∀ y,
      HasDerivAt (fun t : ℝ => g (y * onePar B (atPlace B (e l.divNat) (E _ l.modNat)) t)) (g' y) 0 :=
    fun g hgW l => (hW g hgW).2.2 (e l.divNat) (E _ l.modNat)
  choose! D hDW hD using hder
  let F : List (Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2)) → B.I.GA → ℂ :=
    fun l => l.foldr (fun i g => D g i) f
  have hFW : ∀ l, F l ∈ W := by
    intro l
    induction l with
    | nil => exact hf
    | cons i l ih => exact hDW _ ih i
  have hrep : ∀ l, ∃ Fv, GlobalTheory.Dec.IsContRep B Fv (F l) := fun l => (hW (F l) (hFW l)).1
  choose Fv hFv using hrep

  set Mx : ℝ := ∑ k ∈ Finset.range ((Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) + 1), ∑ w : Fin k → Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2), ‖Fv (List.ofFn w)‖ ^ 2 with hMx
  have hMx0 : 0 ≤ Mx := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hle : ∀ l : List (Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2)), l.length ≤ (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) → ‖Fv l‖ ^ 2 ≤ Mx := by
    intro l hl
    calc ‖Fv l‖ ^ 2 = ‖Fv (List.ofFn l.get)‖ ^ 2 := by rw [List.ofFn_get]
      _ ≤ ∑ w : Fin l.length → Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2), ‖Fv (List.ofFn w)‖ ^ 2 :=
          Finset.single_le_sum (f := fun w : Fin l.length → Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) => ‖Fv (List.ofFn w)‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
      _ ≤ Mx :=
          Finset.single_le_sum (f := fun k => ∑ w : Fin k → Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2), ‖Fv (List.ofFn w)‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
            (Finset.mem_range.2 (Nat.lt_succ_of_le hl))
  have hP : 0 ≤ ∏ v, c v := Finset.prod_nonneg fun v _ => (hc v).1.le
  set K : ℝ := Real.exp B.I.f * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal with hK
  have hK0 : 0 ≤ K := div_nonneg (mul_nonneg (Real.exp_pos _).le hP) ENNReal.toReal_nonneg
  set a : ℝ := 4 * Real.sqrt B.I.n with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  set p := 2 * (B.I.n ^ 2 * B.I.f) with hp
  refine ⟨Real.sqrt (C0 * K * Mx * (1 + a) ^ p), fun y => ?_⟩
  have hτ : 0 < tau1 B.I y := GlobalTheory.TauLipschitz.trunc_pos B.I hn y
  have hτ1 : tau1 B.I y ≤ 1 := by
    have : tau1 B.I y ≤ 1 / 2 := by
      unfold GlobalTheory.Count.tau1
      exact min_le_left _ _
    linarith
  have hu0 : 0 < (tau1 B.I y)⁻¹ := inv_pos.2 hτ
  have hu1 : 1 ≤ (tau1 B.I y)⁻¹ := by
    have h1 := mul_le_mul_of_nonneg_right hτ1 hu0.le
    rw [mul_inv_cancel₀ hτ.ne', one_mul] at h1
    exact h1
  have hu2 : 1 ≤ ((tau1 B.I y)⁻¹) ^ 2 := by nlinarith
  have hfrac : a / tau1 B.I y ^ 2 = a * ((tau1 B.I y)⁻¹) ^ 2 := by rw [div_eq_mul_inv, inv_pow]
  have hbase : 1 + a / tau1 B.I y ^ 2 ≤ (1 + a) * ((tau1 B.I y)⁻¹) ^ 2 := by
    rw [hfrac]
    nlinarith
  have hX1 : 0 ≤ 1 + a / tau1 B.I y ^ 2 := by
    have := div_nonneg ha0 (sq_nonneg (tau1 B.I y))
    linarith
  have hpow : (1 + a / tau1 B.I y ^ 2) ^ p ≤ (1 + a) ^ p * (((tau1 B.I y)⁻¹) ^ p) ^ 2 := by
    calc (1 + a / tau1 B.I y ^ 2) ^ p ≤ ((1 + a) * ((tau1 B.I y)⁻¹) ^ 2) ^ p :=
          pow_le_pow_left₀ hX1 hbase p
      _ = (1 + a) ^ p * (((tau1 B.I y)⁻¹) ^ p) ^ 2 := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 p]

  have hcube : ∀ l : List (Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2)), l.length ≤ (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) →
      ∫ t in Set.pi Set.univ (fun _ : Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) => Set.Icc (0 : ℝ) (1 / (12 * (B.I.n : ℝ) ^ 5))),
        ‖F l (y * (List.ofFn fun i => onePar B (atPlace B (e i.divNat) (E _ i.modNat)) (t i)).prod)‖ ^ 2 ≤
        K * (1 + a / tau1 B.I y ^ 2) ^ p * Mx := by
    intro l hl
    have h1 := cube_bound B c (1 / (12 * (B.I.n : ℝ) ^ 5)) e E hn hg (fun v => (hc v).2.1) hE hs h3 h5
      (Fv l) (F l) (hFv l) (hW (F l) (hFW l)).2.1 y
    have h2 : Real.exp B.I.f * (1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) *
        (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal = K * (1 + a / tau1 B.I y ^ 2) ^ p := by
      rw [hK, ha, hp]
      ring
    rw [h2] at h1
    refine h1.trans ?_
    have hX0 : 0 ≤ K * (1 + a / tau1 B.I y ^ 2) ^ p := mul_nonneg hK0 (pow_nonneg hX1 _)
    exact mul_le_mul_of_nonneg_left (hle l hl) hX0
  have hmain := hsob F (fun l => (hFv l).1) (fun l i x => hD (F l) (hFW l) i x) y
    (K * (1 + a / tau1 B.I y ^ 2) ^ p * Mx) hcube
  have hsq : ‖f y‖ ^ 2 ≤ (Real.sqrt (C0 * K * Mx * (1 + a) ^ p) * ((tau1 B.I y)⁻¹) ^ p) ^ 2 := by
    have hA : 0 ≤ C0 * K * Mx * (1 + a) ^ p :=
      mul_nonneg (mul_nonneg (mul_nonneg hC0 hK0) hMx0) (pow_nonneg (by linarith) _)
    rw [mul_pow, Real.sq_sqrt hA]
    have hQ : 0 ≤ C0 * K * Mx := mul_nonneg (mul_nonneg hC0 hK0) hMx0
    calc ‖f y‖ ^ 2 ≤ C0 * (K * (1 + a / tau1 B.I y ^ 2) ^ p * Mx) := hmain
      _ = (C0 * K * Mx) * (1 + a / tau1 B.I y ^ 2) ^ p := by ring
      _ ≤ (C0 * K * Mx) * ((1 + a) ^ p * (((tau1 B.I y)⁻¹) ^ p) ^ 2) :=
          mul_le_mul_of_nonneg_left hpow hQ
      _ = C0 * K * Mx * (1 + a) ^ p * (((tau1 B.I y)⁻¹) ^ p) ^ 2 := by ring
  have hnn : 0 ≤ Real.sqrt (C0 * K * Mx * (1 + a) ^ p) * ((tau1 B.I y)⁻¹) ^ p :=
    mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hu0.le _)
  calc ‖f y‖ = Real.sqrt (‖f y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Real.sqrt (C0 * K * Mx * (1 + a) ^ p) * ((tau1 B.I y)⁻¹) ^ p) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (C0 * K * Mx * (1 + a) ^ p) * (tau1 B.I y)⁻¹ ^ p := Real.sqrt_sq hnn

end GlobalTheory.SobolevBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.JEqOrbInt
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.AmpTK

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

variable {k r : ℕ}

def rep (L : LocBessel k r) : BranchingSupport.Rep k r := ⟨L.Hs, L.σ⟩

def BeTK (L : LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) : Prop :=
  (∀ x ∈ (rep L).sm, ∀ v ∈ (rep L).TK,
    Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) ∧
  (∀ x ∈ (rep L).sm, ∀ v ∈ (rep L).TK,
    Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))

def SmCW (L : LocBessel k r) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (l : L.Hs → V) : Prop :=
  (∀ v ∈ (rep L).sm, ∀ w ∈ (rep L).sm, l (v + w) = l v + l w) ∧ (∀ (a : ℂ), ∀ v ∈ (rep L).sm, l (a • v) = a • l v) ∧
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) L.σ l

def OneAt (L : LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ν : Measure (PairSp k r)) : Prop :=
  ∃ A : L.Wq →L[ℂ] L.Wp, ∀ F s, IsCoef (rep L) l l' F s → OrbInt L F g ν = s • A

theorem J_eq_orbInt (L : LocBessel k r)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : L.J F g = OrbInt L F g (pairMeas L) := rfl

end GlobalTheory.AmpTK
end
end

