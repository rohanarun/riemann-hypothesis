module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterization
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactArrFiniteDimensional
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarCompactLtTop
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf

variable {k r : ℕ}

def oneM (k r : ℕ) : Mt k r := fun i j => (1 : Mat k r) i j

def nbd (k r : ℕ) (j : ℕ) : Set (Mt k r) := Metric.closedBall (oneM k r) (1 / ((j : ℝ) + 1))

def avgR {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℝ Wp] (μ : Measure (Mt k r)) (j : ℕ)
    (g : Mt k r → Wp) (x : Mt k r) : Wp :=
  ((μ (nbd k r j)).toReal)⁻¹ • ∫ y in nbd k r j, g (rmulM (Matrix.of x) y) ∂μ

theorem isCompact_nbd (j : ℕ) : IsCompact (nbd k r j) := by
  unfold nbd
  exact isCompact_closedBall _ _

theorem oneM_mem_nbd (j : ℕ) : oneM k r ∈ nbd k r j := by
  unfold nbd
  exact Metric.mem_closedBall_self (by positivity)

private lemma single_mem_inWb_and_Tz_pos (k r : ℕ) :
    Formalism.QuantumDeterminants.inWb k r (Pi.single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1)) 1) ∧
      0 < Formalism.QuantumDeterminants.Tz k r (Pi.single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1)) 1) := by
  constructor
  · intro i hi
    have hne : i ≠ ⟨r + k, by omega⟩ := by
      rintro rfl
      simp at hi
    simp [hne]
  · simp only [Formalism.QuantumDeterminants.Tz, Formalism.QuantumDeterminants.herm, Formalism.QuantumDeterminants.Hpk, dotProduct, mulVec, Pi.single_apply,
      Pi.star_apply, Complex.re_sum, neg_pos]
    rw [Finset.sum_eq_single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1))]
    · have h1 : ¬ (r + k < r) := by omega
      simp [h1, Finset.sum_ite_eq']
    · intro b _ hb
      simp [hb]
    · simp

theorem gg_closedSub (k r : ℕ) : IsClosedSub k r (GG k r) :=
  (_root_.GlobalTheory.SgInf.closedSub_groups k r _ (single_mem_inWb_and_Tz_pos k r).1 (single_mem_inWb_and_Tz_pos k r).2).1

theorem haar_compact_lt_top {μ : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μ) {C : Set (Mt k r)}
    (hC : IsCompact C) : μ C < ⊤ :=
  (_root_.GlobalTheory.SgInf.haarOn_locFinite_openPos k r (GG k r) μ (gg_closedSub k r) hμ).1 C hC

theorem nbd_pos {μ : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μ) (j : ℕ) : 0 < μ (nbd k r j) := by
  have h1 : Matrix.of (oneM k r) = (1 : Mat k r) := by
    ext a b
    simp [oneM]
  have hone : Matrix.of (oneM k r) ∈ GG k r := by
    rw [h1]
    exact (gg_closedSub k r).2.2.1
  have hU := (_root_.GlobalTheory.SgInf.haarOn_locFinite_openPos k r (GG k r) μ (gg_closedSub k r) hμ).2
    (Metric.ball (oneM k r) (1 / ((j : ℝ) + 1))) Metric.isOpen_ball
    ⟨oneM k r, Metric.mem_ball_self (by positivity), hone⟩
  unfold nbd
  exact lt_of_lt_of_le hU (measure_mono Metric.ball_subset_closedBall)

end GlobalTheory.SgInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtCompletedTensorOrbitSmoothAverage
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.AverageDeriv

theorem hasDerivAt_average {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : G → (H →L[ℂ] H)} (hσ : IsURep σ) (w : H) {a : ℝ → G} (ha : Continuous a) (ha0 : a 0 = 1)
    {f f' : G → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (hf' : Continuous f')
    (hfc' : HasCompactSupport f')
    (hd : ∀ g t, HasDerivAt (fun s => f ((a s)⁻¹ * g)) (f' ((a t)⁻¹ * g)) t) :
    HasDerivAt (fun t => σ (a t) (∫ g, f g • σ g w ∂μ)) (∫ g, f' g • σ g w ∂μ) 0 := by
  obtain ⟨-, hmul, hnorm, hcont⟩ := hσ
  have hcw : Continuous fun g => σ g w := hcont w

  have key : ∀ t, σ (a t) (∫ g, f g • σ g w ∂μ) = ∫ g, f ((a t)⁻¹ * g) • σ g w ∂μ := by
    intro t
    have hint : Integrable (fun g => f g • σ g w) μ :=
      (hf.smul hcw).integrable_of_hasCompactSupport (hfc.smul_right)
    rw [← (σ (a t)).integral_comp_comm hint]
    rw [← integral_mul_left_eq_self (fun g => f ((a t)⁻¹ * g) • σ g w) (a t)]
    congr 1
    funext g
    rw [map_smul, inv_mul_cancel_left, hmul]
    rfl

  obtain ⟨C, hC⟩ := hf'.bounded_above_of_compact_support hfc'
  set K : Set G := (fun p : ℝ × G => a p.1 * p.2) '' (Set.Icc (-1 : ℝ) 1 ×ˢ tsupport f') with hK
  have hKc : IsCompact K :=
    (isCompact_Icc.prod hfc').image ((ha.comp continuous_fst).mul continuous_snd)
  have hsupp : ∀ s ∈ Metric.ball (0 : ℝ) 1, ∀ g, g ∉ K → f' ((a s)⁻¹ * g) = 0 := by
    intro s hs g hg
    by_contra h
    apply hg
    refine ⟨(s, (a s)⁻¹ * g), ⟨?_, subset_tsupport _ h⟩, by simp⟩
    rw [Real.ball_eq_Ioo, zero_sub, zero_add] at hs
    exact Set.Ioo_subset_Icc_self hs
  have hbound_int : Integrable (K.indicator fun _ => C * ‖w‖) μ :=
    (continuousOn_const.integrableOn_compact hKc).integrable_indicator hKc.isClosed.measurableSet
  have hcont_tr : ∀ (k : G → ℂ), Continuous k → ∀ s : ℝ, Continuous fun g => k ((a s)⁻¹ * g) • σ g w :=
    fun k hk s => (hk.comp (continuous_const.mul continuous_id)).smul hcw
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun s g => f ((a s)⁻¹ * g) • σ g w) (F' := fun s g => f' ((a s)⁻¹ * g) • σ g w)
    (bound := K.indicator fun _ => C * ‖w‖) (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun s => (hcont_tr f hf s).aestronglyMeasurable)
    (by
      simp only [ha0, inv_one, one_mul]
      exact (hf.smul hcw).integrable_of_hasCompactSupport (hfc.smul_right))
    (hcont_tr f' hf' 0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g s hs => by
      by_cases hg : g ∈ K
      · rw [Set.indicator_of_mem hg, norm_smul, hnorm]
        exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
      · rw [Set.indicator_of_notMem hg, hsupp s hs g hg, zero_smul, norm_zero])
    hbound_int
    (Filter.Eventually.of_forall fun g s _ => (hd g s).smul_const (σ g w))
  have hfun : (fun t => σ (a t) (∫ g, f g • σ g w ∂μ)) = fun t => ∫ g, f ((a t)⁻¹ * g) • σ g w ∂μ :=
    funext key
  rw [hfun]
  simpa only [ha0, inv_one, one_mul] using hder.2

theorem expU_zero {n : ℕ} {ε : Fin n → Bool} : expU (0 : gLie ε) = 1 := by
  apply Subtype.ext
  apply Units.ext
  refine (uMat_expU _).trans ?_
  simp

theorem expU_add {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (a b : ℝ) :
    expU ((a + b) • X) = expU (a • X) * expU (b • X) := by
  apply Subtype.ext
  apply Units.ext
  refine (uMat_expU _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (uMat_expU (a • X)).symm (uMat_expU (b • X)).symm)
  rw [Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left a).smul_right b)

theorem expU_inv {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (t : ℝ) : (expU (t • X))⁻¹ = expU ((-t) • X) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← expU_add, add_neg_cancel, zero_smul, expU_zero]

theorem continuous_expU {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) : Continuous fun t : ℝ => expU (t • X) := by
  have hcexp : ∀ A : Matrix (Fin n) (Fin n) ℂ, Continuous fun t : ℝ => NormedSpace.exp (t • A) := by
    intro A
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    exact (differentiable_exp_smul_const ℝ A).continuous
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · have e : (fun t : ℝ => (((expU (t • X) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) = fun t : ℝ => NormedSpace.exp (t • X.1) := by
      funext t
      rw [← Submodule.coe_smul]
      exact uMat_expU (t • X)
    have h := hcexp X.1
    rw [← e] at h
    exact h
  · have e : (fun t : ℝ => ((((expU (t • X) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ :
        (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
        fun t : ℝ => NormedSpace.exp (t • (-X.1)) := by
      funext t
      have h1 := congrArg (fun g : Formalism.REAL.UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) (expU_inv X t)
      refine h1.trans ((uMat_expU _).trans ?_)
      rw [Submodule.coe_smul, neg_smul, smul_neg]
    have h := hcexp (-X.1)
    rw [← e] at h
    exact h

theorem hasDerivAt_exp_mul_entry {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) * Y) i j) ((X * (NormedSpace.exp (t • X) * Y)) i j) t := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X t).mul_const Y
  let l : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h2 := (LinearMap.toContinuousLinearMap l).hasFDerivAt.comp_hasDerivAt t h
  have h3 : HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) * Y) i j)
      ((X * NormedSpace.exp (t • X) * Y) i j) t := h2
  rw [← mul_assoc]
  exact h3

theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (t : ℝ) (g : UJ ε) :
    uMat ((expU (t • X))⁻¹ * g) = NormedSpace.exp (t • (-X.1)) * uMat g := by
  rw [expU_inv]
  show uMat (expU ((-t) • X)) * uMat g = _
  rw [uMat_expU, Submodule.coe_smul, neg_smul, smul_neg]

theorem hasDerivAt_orbit_average : ∀ (B : RowsAut) (F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ) (E : gInf B) (w : B.Hs), IsURep B.σs → ContDiff ℝ ∞ F → HasCompactSupport F → ∃ F' : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F' ∧ HasCompactSupport F' ∧ HasDerivAt (orbit B E (∫ g, F (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I))) (∫ g, F' (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I)) 0 := by
  intro B F E w hσ hF hFc

  have hμ : muInf B.I = Measure.pi (fun v => Formalism.REAL.muG (B.I.ε v)) := rfl
  haveI : (muInf B.I).IsMulLeftInvariant := by rw [hμ]; infer_instance
  haveI : IsFiniteMeasureOnCompacts (muInf B.I) := by rw [hμ]; infer_instance
  let c : B.I.Ginf → (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) :=
    fun g v i j => uMat (g v) i j
  have hc : Topology.IsClosedEmbedding c :=
    Topology.IsClosedEmbedding.piMap fun v => (Formalism.REAL.isClosedEmbeddingMatrix B.I.n (B.I.ε v)).1

  let Lm : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) →ₗ[ℝ]
      (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) :=
    { toFun := fun M v i j => ∑ k, (-(E v).1) i k * M v k j
      map_add' := by
        intro M N
        funext v i j
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r M
        funext v i j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Complex.real_smul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _ }
  let L := LinearMap.toContinuousLinearMap Lm
  let F' : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ := fun M => fderiv ℝ F M (L M)
  have hF's : ContDiff ℝ ∞ F' := (contDiff_infty_iff_fderiv.1 hF).2.clm_apply L.contDiff
  have hF'c : HasCompactSupport F' := by
    refine (hFc.fderiv (𝕜 := ℝ)).mono' fun M hM => subset_tsupport _ ?_
    intro h0
    apply hM
    show fderiv ℝ F M (L M) = 0
    rw [h0]
    rfl
  refine ⟨F', hF's, hF'c, ?_⟩
  let a : ℝ → B.I.Ginf := fun t v => expU (t • E v)
  have ha : Continuous a := continuous_pi fun v => continuous_expU (E v)
  have ha0 : a 0 = 1 := by
    funext v
    show expU ((0 : ℝ) • E v) = 1
    rw [zero_smul, expU_zero]
  have hcc : Continuous c := hc.continuous
  have hd : ∀ g t, HasDerivAt (fun s => F (c ((a s)⁻¹ * g))) (F' (c ((a t)⁻¹ * g))) t := by
    intro g t
    let p : ℝ → (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) :=
      fun s v i j => (NormedSpace.exp (s • (-(E v).1)) * uMat (g v)) i j
    have hp : ∀ s, c ((a s)⁻¹ * g) = p s := by
      intro s
      funext v i j
      show uMat ((expU (s • E v))⁻¹ * g v) i j = _
      rw [uMat_inv_mul]
    have hp' : HasDerivAt p (L (p t)) t := by
      refine hasDerivAt_pi.2 fun v => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
      exact hasDerivAt_exp_mul_entry _ _ t i j
    have hFd : HasFDerivAt F (fderiv ℝ F (p t)) (p t) :=
      (hF.differentiable (by simp)).differentiableAt.hasFDerivAt
    have h := hFd.comp_hasDerivAt t hp'
    simp only [hp]
    exact h
  have main := hasDerivAt_average (muInf B.I) hσ w (a := a) ha ha0 (f := fun g => F (c g))
    (f' := fun g => F' (c g)) (hF.continuous.comp hcc) (hFc.comp_isClosedEmbedding hc)
    (hF's.continuous.comp hcc) (hF'c.comp_isClosedEmbedding hc) hd
  exact main

end GlobalTheory.AverageDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDualVectorNormInvNotMemLocal
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.St.G.LocNot

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_of_tmul_mem (v : HeightOneSpectrum (𝓞 F)) (t : v.adicCompletion F)
    (ht : (1 : E) ⊗ₜ[F] t ∈ intV E v) : t ∈ v.adicCompletionIntegers F := by
  classical
  let ι : v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F := Algebra.TensorProduct.includeRight
  letI : Algebra (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) :=
    (ι.toRingHom.comp (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).toAlgebra
  let ιO : v.adicCompletion F →ₐ[v.adicCompletionIntegers F] E ⊗[F] v.adicCompletion F :=
    { ι.toRingHom with commutes' := fun _ => rfl }
  have hinj : Function.Injective ιO :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F E).injective
  have hle : intV E v ≤
      (integralClosure (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F)).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨⟨e, he⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · obtain ⟨a, rfl⟩ := he
      obtain ⟨p, hp, hpe⟩ := RingOfIntegers.isIntegral_coe a
      refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      let g : E →+* E ⊗[F] v.adicCompletion F := Algebra.TensorProduct.includeLeftRingHom
      have hc : (algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F)).comp
          (Int.castRingHom _) = g.comp (algebraMap ℤ E) := RingHom.ext_int _ _
      have h3 := congrArg g hpe
      rw [Polynomial.hom_eval₂, map_zero] at h3
      rw [hc]
      exact h3
    · exact isIntegral_algebraMap (x := (⟨c, hc⟩ : v.adicCompletionIntegers F))
  have hi : IsIntegral (v.adicCompletionIntegers F) t := (isIntegral_algHom_iff ιO hinj).1 (hle ht)
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact b.2

end GlobalTheory.St.G.LocNot

namespace GlobalTheory.St.G

theorem dual_not_loc_of_norm_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), (∀ x ∈ L, x ∈ dualSet (cm.sig : E →+* E) J L) → ∀ (d : Fin n → E) (T : ℕ), 0 < T → d ∈ dualL cm.sig J L → Formalism.UG.hform (cm.sig : E →+* E) J d d - ((T : E))⁻¹ ∈ (algebraMap (𝓞 E) E).range → ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∃ x ∈ loc v (dualL cm.sig J L), x ∉ loc v L := by
  intro F E _ _ _ _ _ _ cm n J L hL d T hT hd hdd v hv
  let x : Fin n → E ⊗[F] v.adicCompletion F := fun i => inclE (F := F) (v.adicCompletion F) (d i)
  refine ⟨x, Submodule.subset_span ⟨d, hd, rfl⟩, fun hx => ?_⟩
  have hLd : L ≤ dualL cm.sig J L := fun y hy => Submodule.subset_span (hL y hy)
  have hx' : x ∈ loc v (dualL cm.sig J L) := Submodule.span_mono (Set.image_mono hLd) hx
  have hxx := Dual.fwd cm.sig J (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring L x hx' x hx
  rw [Dual.hR_incl] at hxx
  obtain ⟨a, ha⟩ := hdd
  have h1 : inclE (F := F) (v.adicCompletion F) ((T : E)⁻¹) ∈ intV E v := by
    have he : Formalism.UG.hform (cm.sig : E →+* E) J d d = algebraMap (𝓞 E) E a + (T : E)⁻¹ := by
      rw [ha]; ring
    rw [he, map_add (f := _)] at hxx
    have ha' : inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E a) ∈ intV E v :=
      Subring.subset_closure (Or.inl ⟨⟨_, a, rfl⟩, rfl⟩)
    have := sub_mem hxx ha'
    rwa [add_sub_cancel_left] at this
  have h2 : inclE (F := F) (v.adicCompletion F) ((T : E)⁻¹) =
      (1 : E) ⊗ₜ[F] ((T : v.adicCompletion F)⁻¹) := by
    have e1 : ((T : E))⁻¹ = ((T : F))⁻¹ • (1 : E) := by
      rw [Algebra.smul_def, mul_one, map_inv₀, map_natCast]
    have e2 : ((T : v.adicCompletion F))⁻¹ = ((T : F))⁻¹ • (1 : v.adicCompletion F) := by
      rw [Algebra.smul_def, mul_one, map_inv₀, map_natCast]
    rw [e1, e2]
    show ((T : F)⁻¹ • (1 : E)) ⊗ₜ[F] (1 : v.adicCompletion F) = _
    rw [TensorProduct.smul_tmul]
  rw [h2] at h1
  have h3 := LocNot.mem_of_tmul_mem v _ h1
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h3
  have hval : Valued.v (T : v.adicCompletion F) < 1 := by
    have hv1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (T : 𝓞 F)
    have hv2 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (T : 𝓞 F)).2 hv
    rw [← hv1] at hv2
    convert hv2 using 2
    simp
  have hne : (T : v.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (v.adicCompletion F))]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hT.ne')
  rw [map_inv₀] at h3
  have hpos : 0 < Valued.v (T : v.adicCompletion F) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hne)
  have h4 : 1 ≤ Valued.v (T : v.adicCompletion F) := (inv_le_one₀ hpos).1 h3
  exact absurd hval (not_lt.2 h4)

end GlobalTheory.St.G
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsoPartStable
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.VminusComp

def ht {n : ℕ} (μ : Fin n → ℝ) : ℝ := ∑ i : Fin n, ((i : ℕ) : ℝ) * μ i

theorem ht_add {n : ℕ} (μ ν : Fin n → ℝ) : ht (μ + ν) = ht μ + ht ν := by
  simp [ht, mul_add, Finset.sum_add_distrib]

theorem ht_sub {n : ℕ} (μ ν : Fin n → ℝ) : ht (μ - ν) = ht μ - ht ν := by
  simp [ht, mul_sub, Finset.sum_sub_distrib]

theorem ht_root {n : ℕ} (a b : Fin n) : ht (Formalism.REAL.root a b) = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [ht, Formalism.REAL.root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem weight_shift {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} (hF : Formalism.REAL.KRel ε F) {ν : Fin n → ℝ} {x : W}
    (hx : Formalism.REAL.IsWeight F ν x) {a b : Fin n} (hab : ε a = ε b) :
    Formalism.REAL.IsWeight F (ν + Formalism.REAL.root a b) (F a b x) := by
  intro c
  have h := congrArg (fun T : Module.End ℂ W => T x) (hF c c a b rfl hab)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hx c, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases h1 : c = a <;> by_cases h2 : b = c
  · subst h1; subst h2; simp [Formalism.REAL.root]
  · subst h1
    simp [Formalism.REAL.root, h2, Pi.single_apply, Ne.symm h2, add_smul, add_comm]
  · subst h2
    simp [Formalism.REAL.root, h1, Pi.single_apply, add_smul, sub_smul, add_comm]
  · simp [Formalism.REAL.root, h1, h2, Pi.single_apply, Ne.symm h2]

theorem word_weight {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} (hF : Formalism.REAL.KRel ε F) {μ : Fin n → ℝ} {x : W}
    (hx : Formalism.REAL.IsWeight F μ x) (w : List (Fin n × Fin n))
    (hw : ∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) :
    ∃ ν, ht μ ≤ ht ν ∧ Formalism.REAL.IsWeight F ν (ew F w x) := by
  induction w with
  | nil => exact ⟨μ, le_rfl, by simpa [ew] using hx⟩
  | cons p w ih =>
    obtain ⟨ν, h1, h2⟩ := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
    have hp := hw p (List.mem_cons_self ..)
    refine ⟨ν + Formalism.REAL.root p.1 p.2, ?_, ?_⟩
    · rw [ht_add, ht_root]
      have : ((p.2 : ℕ) : ℝ) < ((p.1 : ℕ) : ℝ) := by exact_mod_cast hp.2
      linarith
    · simpa only [ew, Module.End.mul_apply] using weight_shift hF h2 hp.1

theorem comp_weight {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {E : Fin n → Fin n → Module.End ℂ V} {ν : Fin n → ℝ} {G : Arr V n 1}
    (hG : Formalism.REAL.IsWeight (arrE E 1) ν G) (a b : Fin n) :
    Formalism.REAL.IsWeight E (ν - Formalism.REAL.root a b) (G (fun _ => (a, b))) := by
  intro c
  have h1 := congrArg (fun G : Arr V n 1 => G (fun _ => (a, b))) (hG c)
  simp only at h1
  rw [arr_operator_one_apply, PiLp.smul_apply, add_comm, ← eq_sub_iff_add_eq] at h1
  rw [h1]
  by_cases h1 : a = c <;> by_cases h2 : b = c
  · subst h1; subst h2; simp [Formalism.REAL.root]
  · subst h1
    simp [Formalism.REAL.root, h2, Pi.single_apply, Ne.symm h2, sub_smul]
  · subst h2
    simp [Formalism.REAL.root, h1, Pi.single_apply, Ne.symm h1, add_smul, sub_smul]
  · simp [Formalism.REAL.root, h1, h2, Pi.single_apply, Ne.symm h2, Ne.symm h1]

theorem isoPart_stable {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} (T : Set (Fin n → ℝ)) (S : Submodule ℂ W) :
    Formalism.REAL.KStable ε F (isoPart ε F T S) := by
  intro a b hab x hx
  have : isoPart ε F T S ≤ (isoPart ε F T S).comap (F a b) := by
    apply isotypic_part_le_of_forall
    intro y hy μ hμ hyh z hz
    exact compact_span_le_isotypic_part hy hμ hyh (compact_span_stable_general y a b hab z hz)
  exact this hx

theorem vminus_comp : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (abelian₂ : Fin n → ℝ) (u : V), GlRel E → IsUnitary ε E → KHighest ε E abelian₂ u → FiniteDimensional ℂ (kSpan ε E u) → KStable ε (arrE E 1) (Vminus ε E abelian₂ u) ∧ Vminus ε E abelian₂ u ≤ arrV0 ε E u 1 ∧ FiniteDimensional ℂ (Vminus ε E abelian₂ u) ∧ ∀ G ∈ Vminus ε E abelian₂ u, ∀ a b, ¬ b < a → ⟪u, at1 G a b⟫_ℂ = 0 := by
  intro V _ _ n ε E abelian₂ u hg hu hΛ hfd
  have hle : Vminus ε E abelian₂ u ≤ arrV0 ε E u 1 := by
    apply isotypic_part_le_of_forall
    intro y hy μ _ _
    exact compact_span_le_of_stable noncompact_arr_one_compact_stable hy
  have hfd0 := noncompact_arr_finite_dimensional (j := 1) hfd
  refine ⟨isoPart_stable _ _, hle, Submodule.finiteDimensional_of_le hle, ?_⟩
  intro G hG a b hab
  have hKR := glRel_kRel ε _ ((arrModule V n ε E 1).1 hg).1
  let ℓ : Arr V n 1 →ₗ[ℂ] ℂ := (innerₛₗ ℂ u) ∘ₗ
    (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 → Fin n × Fin n => V) (fun _ => (a, b)) ∘ₗ arrOf V n 1)
  have hℓ : ∀ G : Arr V n 1, ℓ G = ⟪u, G (fun _ => (a, b))⟫_ℂ := fun G => rfl
  have hker : Vminus ε E abelian₂ u ≤ LinearMap.ker ℓ := by
    apply isotypic_part_le_of_forall
    rintro y - μ ⟨a', b', hba, -, rfl⟩ hyh
    rw [(kLow _ n ε _ _ y hKR hyh).1, lowSpan, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨ν, h1, h2⟩ := word_weight hKR hyh.1 w hw
    rw [SetLike.mem_coe, LinearMap.mem_ker, hℓ]
    refine kWtOrth V n ε E _ _ _ _ (isUnitary_kUnit ε E hu) hΛ.1 (comp_weight h2 a b) ?_
    intro h
    have h3 := congrArg ht h
    rw [ht_sub, ht_root] at h3
    rw [ht_add, ht_root] at h1
    have e1 : ((b' : ℕ) : ℝ) < ((a' : ℕ) : ℝ) := by exact_mod_cast hba
    have e2 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast not_lt.mp hab
    linarith
  exact hker hG

end GlobalTheory.Jet.VminusComp
end
end

