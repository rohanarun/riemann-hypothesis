module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0161
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0070
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagStabilizerMulInvLeviComponentMemUnipotentStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagStabilizer_mul_inv_leviComponent_mem_unipotent : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (A₀ : Matrix (Fin n) (Fin n₀) ℂ) (p : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ) (d : ∀ k, Matrix (Fin (j k)) (Fin n₀) ℂ) (s h : Formalism.REAL.UJ ε₀) (y : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g m : Formalism.REAL.UJ ε), SpansFlag A W → SpansFlag B W → (∀ k i, i < k → p k i = 0) → (∀ i, (p i i).det ≠ 0) → (∀ i, A i = ∑ k, B k * p k i) → A₀ = B₀ * uMat s + ∑ k, B k * d k → (∀ i, (y i).det ≠ 0) → (∀ i, uMat g * A i = A i * y i) → uMat g * A₀ = A₀ * uMat h → uMat m = lev ε B B₀ (fun i => p i i * y i * (p i i)⁻¹) (uMat (s * h * s⁻¹)) → g * m⁻¹ ∈ flagN ε W := by
  first | exact @GlobalTheory.LeviUnip.mul_inv_mem_flagN | exact GlobalTheory.LeviUnip.mul_inv_mem_flagN | (intros; apply GlobalTheory.LeviUnip.mul_inv_mem_flagN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasEuclideanBallVolumeHaarComplexGLInverseStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasEuclideanBallVolume_haarComplexGL_inverse : ∀ j : ℕ, IsRadial (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j) (fun x => Formalism.REAL.hs (Matrix.of x - 1) + Formalism.REAL.hs ((Matrix.of x)⁻¹ - 1)) (2 * j ^ 2) := by
  first | exact @GlobalTheory.LeviIso.isRadial_haarLoc | exact GlobalTheory.LeviIso.isRadial_haarLoc | (intros; apply GlobalTheory.LeviIso.isRadial_haarLoc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClosedEmbeddingEntriesInf
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.StepAverage

theorem isClosedEmbedding_entries {n : ℕ} (ε : Fin n → Bool) :
    Topology.IsClosedEmbedding (fun g : UJ ε => (fun i j => umat g i j : Fin n → Fin n → ℂ)) := by
  have key := (uJEmb n ε).1
  exact key

theorem isClosedEmbedding_entries_inf (I : AutInst) :
    Topology.IsClosedEmbedding (fun g : I.Ginf =>
      (fun v i j => uMat (g v) i j : InfinitePlace I.F → Fin I.n → Fin I.n → ℂ)) := by
  have h : ∀ v : InfinitePlace I.F, Topology.IsClosedEmbedding
      (fun g : Formalism.REAL.UJ (I.ε v) => (fun i j => uMat g i j : Fin I.n → Fin I.n → ℂ)) :=
    fun v => isClosedEmbedding_entries (I.ε v)
  exact Topology.IsClosedEmbedding.piMap h

theorem integrable_loc {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H)
    {F : (Fin n → Fin n → ℂ) → ℂ} (hF : Continuous F) (hc : HasCompactSupport F) :
    Integrable (fun g : UJ ε => F (fun i j => umat g i j) • σ (umat g) w) (muG ε) := by
  have hemb := isClosedEmbedding_entries ε
  have hrep : Continuous (fun g : UJ ε => σ (umat g) w) :=
    (hσ.2.2 w).comp_continuous hemb.continuous (fun g => g.2)
  have hcs : HasCompactSupport (fun g : UJ ε => F (fun i j => umat g i j) • σ (umat g) w) :=
    (hc.comp_isClosedEmbedding hemb).smul_right
  exact ((hF.comp hemb.continuous).smul hrep).integrable_of_hasCompactSupport hcs

theorem integrable_inf (B : RowsAut) (hσ : IsURep B.σs) (w : B.Hs)
    {F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ} (hF : Continuous F) (hc : HasCompactSupport F) :
    Integrable (fun g : B.I.Ginf => F (fun v i j => uMat (g v) i j) • B.σs g w) (muInf B.I) := by
  have hemb := isClosedEmbedding_entries_inf B.I
  have hrep : Continuous (fun g : B.I.Ginf => B.σs g w) := hσ.2.2.2 w
  have hμ : muInf B.I = Measure.pi fun v => muG (B.I.ε v) := rfl
  haveI : IsFiniteMeasureOnCompacts (muInf B.I) := by
    rw [hμ]
    infer_instance
  have hcs : HasCompactSupport (fun g : B.I.Ginf => F (fun v i j => uMat (g v) i j) • B.σs g w) :=
    (hc.comp_isClosedEmbedding hemb).smul_right
  exact ((hF.comp hemb.continuous).smul hrep).integrable_of_hasCompactSupport hcs

theorem tens_average (B : RowsAut) (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v)) (hσ : IsURep B.σs)
    (w : ∀ v, B.H v) (F : InfinitePlace B.I.F → (Fin B.I.n → Fin B.I.n → ℂ) → ℂ)
    (hF : ∀ v, ContDiff ℝ ∞ (F v)) (hc : ∀ v, HasCompactSupport (F v)) :
    ∃ G : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      B.tens (fun v => ∫ g : UJ (B.I.ε v), F v (fun i j => umat g i j) • B.σ v (umat g) (w v) ∂(muG (B.I.ε v))) =
        ∫ g, G (fun v i j => uMat (g v) i j) • B.σs g (B.tens w) ∂(muInf B.I) := by
  classical
  obtain ⟨hin, hact, hden⟩ := B.tens_spec
  set G : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ := fun x => ∏ v, F v (x v) with hGdef
  have hGs : ContDiff ℝ ∞ G :=
    contDiff_prod (fun v _ => (hF v).comp (contDiff_apply ℝ (fun _ => (Fin B.I.n → Fin B.I.n → ℂ)) v))
  have hGc : HasCompactSupport G := by
    refine HasCompactSupport.intro' (isCompact_univ_pi fun v => hc v)
      (isClosed_set_pi fun v _ => isClosed_tsupport (F v)) ?_
    intro x hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
    obtain ⟨v, hv⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ v) (image_eq_zero_of_notMem_tsupport hv)
  refine ⟨G, hGs, hGc, ?_⟩
  refine eq_of_inner_eq_on_dense_span hden ?_
  rintro y ⟨x, rfl⟩
  have hloc : ∀ v, ⟪x v, ∫ g : UJ (B.I.ε v), F v (fun i j => umat g i j) • B.σ v (umat g) (w v)
        ∂(muG (B.I.ε v))⟫_ℂ =
      ∫ g : UJ (B.I.ε v), F v (fun i j => umat g i j) * ⟪x v, B.σ v (umat g) (w v)⟫_ℂ ∂(muG (B.I.ε v)) := by
    intro v
    rw [← integral_inner (integrable_loc (hU v) (w v) (hF v).continuous (hc v))]
    simp only [inner_smul_right]
  have hglob : ⟪B.tens x, ∫ g, G (fun v i j => uMat (g v) i j) • B.σs g (B.tens w) ∂(muInf B.I)⟫_ℂ =
      ∫ g : B.I.Ginf, ∏ v, (F v (fun i j => uMat (g v) i j) * ⟪x v, B.σ v (uMat (g v)) (w v)⟫_ℂ)
        ∂(muInf B.I) := by
    rw [← integral_inner (integrable_inf B hσ (B.tens w) hGs.continuous hGc)]
    congr 1
    funext g
    rw [inner_smul_right, hact, hin, Finset.prod_mul_distrib]
  have hμ : muInf B.I = Measure.pi fun v => muG (B.I.ε v) := rfl
  have hprod := integral_fintype_prod_eq_prod (μ := fun v => muG (B.I.ε v))
    (fun v (h : UJ (B.I.ε v)) => F v (fun i j => uMat h i j) * ⟪x v, B.σ v (uMat h) (w v)⟫_ℂ)
  rw [hglob, hin, hμ]
  refine Eq.trans ?_ hprod.symm
  exact Finset.prod_congr rfl (fun v _ => hloc v)

theorem exists_smooth_average : GlobalTheory.DSId.StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → ∀ P : ℕ, ∀ u ∈ VP B P, ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I) := by
  intro hSL B d hd P u hu
  have hσ : IsURep B.σs := (tensorRep B d hd).1
  have hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v) := fun v => (hd v).2.1.2.2.1

  let Av : B.Hs → Prop := fun y => ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ,
    ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      y = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I)
  have hzero : Av 0 := by
    refine ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, ?_⟩
    simp only [zero_smul, integral_zero]
  have hadd : ∀ a b, Av a → Av b → Av (a + b) := by
    rintro a b ⟨F₁, hF₁, hc₁, rfl⟩ ⟨F₂, hF₂, hc₂, rfl⟩
    refine ⟨F₁ + F₂, hF₁.add hF₂, hc₁.add hc₂, ?_⟩
    rw [← integral_add (integrable_inf B hσ _ hF₁.continuous hc₁)
      (integrable_inf B hσ _ hF₂.continuous hc₂)]
    congr 1
    funext g
    rw [Pi.add_apply, add_smul]
  have hsmul : ∀ (c : ℂ) a, Av a → Av (c • a) := by
    rintro c a ⟨F₁, hF₁, hc₁, rfl⟩
    refine ⟨fun x => c * F₁ x, contDiff_const.mul hF₁, hc₁.mul_left, ?_⟩
    rw [← integral_smul]
    congr 1
    funext g
    rw [mul_smul]

  have hbase : ∀ x : ∀ v, B.H v, (∀ v, x v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) → Av (B.tens x) := by
    intro x hx
    have hloc : ∀ v, ∃ F : (Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
        x v = ∫ g : UJ (B.I.ε v), F (fun i j => umat g i j) • B.σ v (umat g) (B.w v) ∂(muG (B.I.ε v)) := by
      intro v
      have hlow := (hd v).2.2.1
      have hw0 : B.w v ≠ 0 := by
        intro h0
        have h1 := hlow.1
        rw [h0, norm_zero] at h1
        exact zero_ne_one h1
      have hK := (hSL B.I.n (B.I.ε v) (B.lam v) (hd v).1 (B.H v) (B.σ v) (hd v).2.1).1
      exact _root_.GlobalTheory.exists_smooth_average_eq_of_mem_lowKSub B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v) (B.w v) (hU v) hK hlow.2 hw0 (x v) (hx v)
    choose Fl hFl hcl hxl using hloc
    obtain ⟨G, hG, hcG, hEq⟩ := tens_average B hU hσ B.w Fl hFl hcl
    refine ⟨G, hG, hcG, ?_⟩
    rw [← hEq]
    congr 1
    funext v
    exact hxl v

  have hstep : ∀ (E : gInf B) y, Av y → Av (dAct B E y) := by
    rintro E y ⟨F₁, hF₁, hc₁, rfl⟩
    obtain ⟨F', hF', hc', hder⟩ := _root_.GlobalTheory.AverageDeriv.hasDerivAt_orbit_average B F₁ E (B.tens B.w) hσ hF₁ hc₁
    exact ⟨F', hF', hc', hder.deriv⟩
  have hword : ∀ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (x : ∀ v, B.H v),
      (∀ v, x v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) → Av (wordAct B l (B.tens x)) := by
    intro l x hx
    induction l with
    | nil => exact hbase x hx
    | cons X l ih => exact hstep (atPlace B X.1 X.2) _ ih
  have hu' : u ∈ Submodule.span ℂ {y | ∃ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v)))
      (x : ∀ v, B.H v), l.length ≤ P ∧ (∀ v, x v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) ∧
        y = wordAct B l (B.tens x)} := hu
  clear hu
  induction hu' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, x, -, hx, rfl⟩ := hy
    exact hword l x hx
  | zero => exact hzero
  | add a b _ _ ha hb => exact hadd a b ha hb
  | smul c a _ ha => exact hsmul c a ha

end GlobalTheory.StepAverage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeLatIn
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S IsDedekindDomain
open scoped ENNReal Classical

namespace GlobalTheory.Mass.DetAgree

section
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]

theorem genIdxH_eq_idxN {A B : Submodule (𝓞 K) V} (hBA : B ≤ A) (h0 : idxN A B ≠ 0) :
    Lat.genIdxH A B = (idxN A B : ℝ) := by
  obtain ⟨k, hk, hc⟩ := Formalism.LFunctionChainParameters.LLcv.card_pLen _ A B hBA rfl h0
  let e : HeightOneSpectrum (𝓞 K) ≃ {p : Ideal (𝓞 K) // p.IsMaximal} :=
    { toFun := fun P => ⟨P.asIdeal, P.isMaximal⟩
      invFun := fun p => ⟨p.1, p.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField K)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hl : ∀ P : HeightOneSpectrum (𝓞 K), (haveI := P.isPrime; lidx P.asIdeal A B) = (k (e P) : ℤ) := by
    intro P
    have a := hk (e P)
    unfold Formalism.LFunctionChainParameters.LLcv.pLen at a
    unfold lidx
    rw [inf_eq_right.mpr hBA, indexBasic_locLen_self]
    unfold locLen
    erw [a]
    simp
  unfold Lat.genIdxH
  simp only [hl, zpow_natCast]
  have := finprod_comp_equiv (f := fun w : {p : Ideal (𝓞 K) // p.IsMaximal} =>
    ((Ideal.absNorm w.1 : ℕ) : ℝ) ^ k w) e
  refine this.trans ?_
  rw [idxN, hc, finprod_eq_prod_of_mulSupport_subset (s := k.support), Finsupp.prod, Nat.cast_prod]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [Nat.cast_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · intro w hw
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h
    apply hw
    simp [h]

variable [Module K V] [IsScalarTower (𝓞 K) K V]

theorem span_inf_eq (L : Submodule (𝓞 K) V) (hL : Submodule.IsFullLattice K L) (U : Submodule K V) :
    Submodule.span K ((L ⊓ U.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) = U := by
  refine le_antisymm (Submodule.span_le.2 fun x hx => hx.2) fun u hu => ?_
  obtain ⟨r, hr, hru⟩ := Formalism.LFunctionChainParameters.LLcv.span_le_locS (K := K) L (x := u) (by rw [hL.span_eq_top]; trivial)
  have h1 : algebraMap (𝓞 K) K r ≠ 0 := by simpa using nonZeroDivisors.ne_zero hr
  have h2 : r • u ∈ Submodule.span K ((L ⊓ U.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) :=
    Submodule.subset_span ⟨hru, (U.restrictScalars (𝓞 K)).smul_mem r hu⟩
  rw [← algebraMap_smul K r] at h2
  exact (Submodule.smul_mem_iff _ h1).1 h2

theorem isLattice_latIn (L : Submodule (𝓞 K) V) (hL : Submodule.IsFullLattice K L) (U : Submodule K V) :
    Submodule.IsFullLattice K (latIn U L) := by
  haveI : Submodule.IsLattice K (latIn U L) := by
    apply Submodule.IsLattice.of_fg K
    refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_
    exact hL.fg.of_le (Submodule.map_comap_le _ _)
  refine ⟨?_⟩
  apply Submodule.map_injective_of_injective U.injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  refine (congrArg (Submodule.span K) ?_).trans (span_inf_eq L hL U)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.2⟩
  · rintro ⟨hx, hxU⟩
    exact ⟨⟨x, hxU⟩, hx, rfl⟩

variable [StarRing K]

theorem nondeg_of_pd {h : V →ₗ⋆[K] V →ₗ[K] K} (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have key : ∀ x, h x x = 0 → x = 0 := fun x hx => by
    by_contra h0
    have := hp τ x h0
    rw [hx] at this
    simp at this
  exact ⟨fun x hx => key x (hx x), fun x hx => key x (hx x)⟩

theorem idxN_dualInH (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (hL : Submodule.IsFullLattice K L)
    (U : Submodule K V) :
    idxN (Lat.dualInH h (L ⊓ U.restrictScalars (𝓞 K))) (L ⊓ U.restrictScalars (𝓞 K)) =
      discN (hRes h U) (latIn U L) := by
  have e1 : (L ⊓ U.restrictScalars (𝓞 K)).toAddSubgroup =
      (latIn U L).toAddSubgroup.map U.subtype.toAddMonoidHom := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
  have e2 : (Lat.dualInH h (L ⊓ U.restrictScalars (𝓞 K))).toAddSubgroup =
      (dual (hRes h U) (latIn U L)).toAddSubgroup.map U.subtype.toAddMonoidHom := by
    unfold Lat.dualInH
    rw [span_inf_eq L hL U]
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨x, h2⟩, (dualBasic_mem_dual _ _ _).2 fun y hy => ?_, rfl⟩
      exact (dualBasic_mem_dual _ _ _).1 h1 y ⟨hy, y.2⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(dualBasic_mem_dual _ _ _).2 fun z hz => ?_, y.2⟩
      exact (dualBasic_mem_dual _ _ _).1 hy ⟨z, hz.2⟩ hz.1
  rw [discN, idxN, idxN, e1, e2, AddSubgroup.relIndex_map_map_of_injective _ _ U.injective_subtype]

theorem discGen_iff (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (hle : L ≤ dual h L) (e : ℕ) :
    Cnt.DiscGen h L e ↔ ∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V) := by
  set D := dual h L with hD
  set q : D →ₗ[𝓞 K] Cnt.discMod h L := (L.comap D.subtype).mkQ with hq
  have key : ∀ s : Finset D, Submodule.span (𝓞 K) ((s.image q : Finset _) : Set (Cnt.discMod h L)) = ⊤ ↔
      D = L ⊔ Submodule.span (𝓞 K) ((s.image D.subtype : Finset V) : Set V) := by
    intro s
    rw [Finset.coe_image, Finset.coe_image, ← Submodule.map_span, ← Submodule.map_span, hq,
      Submodule.map_mkQ_eq_top, ← (Submodule.map_injective_of_injective D.injective_subtype).eq_iff,
      Submodule.map_sup, Submodule.map_comap_subtype, inf_eq_right.2 hle, Submodule.map_top,
      Submodule.range_subtype, eq_comm]
  constructor
  · rintro ⟨s, hs, hsp⟩
    have hsurj : Function.Surjective q := Submodule.mkQ_surjective _
    refine ⟨(s.image (Function.surjInv hsurj)).image D.subtype,
      Finset.card_image_le.trans (Finset.card_image_le.trans hs), (key _).1 ?_⟩
    rw [Finset.image_image, (Function.rightInverse_surjInv hsurj).comp_eq_id, Finset.image_id, hsp]
  · rintro ⟨t, ht, hsp⟩
    have htD : ∀ x ∈ t, x ∈ D := fun x hx => by
      rw [hsp]; exact Submodule.mem_sup_right (Submodule.subset_span hx)
    have ee : (t.subtype (· ∈ D)).image D.subtype = t := by
      ext x
      simp only [Finset.mem_image, Finset.mem_subtype]
      exact ⟨fun ⟨y, hy, e⟩ => e ▸ hy, fun hx => ⟨⟨x, htD x hx⟩, hx, rfl⟩⟩
    refine ⟨(t.subtype (· ∈ D)).image q, Finset.card_image_le.trans ?_, (key _).2 (by rw [ee]; exact hsp)⟩
    rw [Finset.card_subtype]
    exact (Finset.card_filter_le _ _).trans ht

end

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, IsIntLat h L → Lat.latDetH h L ^ 2 = (discN h L : ℝ) ∧ 0 < Lat.latDetH h L ∧ (∀ j de : ℕ, Cnt.cntPrim h L j de = (primSp h L j (de ^ 2)).encard) ∧ (∀ e : ℕ, Cnt.DiscGen h L e ↔ (∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V))) ∧ ∀ (U : Submodule K V), Lat.latDetH h (L ⊓ U.restrictScalars (𝓞 K)) ^ 2 = (discN (hRes h U) (latIn U L) : ℝ) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp L hL
  have hFull : Submodule.IsFullLattice K L := hL.1
  have hle : L ≤ dual h L := fun x hx => (dualBasic_mem_dual _ _ _).2 fun y hy => hL.2 y hy x hx
  have hn := nondeg_of_pd hp
  have h0 := (DiscOrder.main K V h hK hs hn L hL).1
  have hd : Lat.dualInH h L = dual h L := by
    unfold Lat.dualInH
    rw [hFull.span_eq_top]
    simp
  have h1 : Lat.latDetH h L = Real.sqrt (discN h L : ℝ) := by
    rw [Lat.latDetH, hd, genIdxH_eq_idxN hle h0, discN]
  have hU : ∀ U : Submodule K V, Lat.latDetH h (L ⊓ U.restrictScalars (𝓞 K)) =
      Real.sqrt (discN (hRes h U) (latIn U L) : ℝ) := by
    intro U
    have hsU : (hRes h U).IsSymm := ⟨fun x y => hs.eq x y⟩
    have hpU : PD (hRes h U) := fun τ x hx => hp τ x fun e => hx (Subtype.ext e)
    have hI : IsIntLat (hRes h U) (latIn U L) :=
      ⟨isLattice_latIn L hFull U, fun x hx y hy => hL.2 x hx y hy⟩
    have n0 := (DiscOrder.main K U _ hK hsU (nondeg_of_pd hpU) _ hI).1
    rw [← idxN_dualInH h L hFull U] at n0 ⊢
    rw [Lat.latDetH, genIdxH_eq_idxN _ n0]
    intro x hx
    exact ⟨(dualBasic_mem_dual _ _ _).2 fun y hy => hL.2 y hy.1 x hx.1, Submodule.subset_span hx⟩
  refine ⟨by rw [h1, Real.sq_sqrt (Nat.cast_nonneg _)], ?_, fun j de => ?_, discGen_iff h L hle,
    fun U => by rw [hU, Real.sq_sqrt (Nat.cast_nonneg _)]⟩
  · rw [h1]
    exact Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero h0)
  · have hinj : Function.Injective fun U : Submodule K V => L ⊓ U.restrictScalars (𝓞 K) :=
      Function.LeftInverse.injective (g := fun M : Submodule (𝓞 K) V => Submodule.span K (M : Set V))
        (span_inf_eq L hFull)
    have hsq : ∀ n : ℕ, Real.sqrt (n : ℝ) = de ↔ n = de ^ 2 := fun n => by
      rw [Real.sqrt_eq_iff_eq_sq (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      exact_mod_cast Iff.rfl
    rw [Cnt.cntPrim, ← hinj.encard_image]
    congr 1
    ext M
    constructor
    · rintro ⟨⟨-, a⟩, b, c⟩
      refine ⟨Submodule.span K (M : Set V), ⟨b, ?_⟩, a.symm⟩
      rw [← hsq, ← hU, ← a, c]
    · rintro ⟨U, ⟨a, b⟩, rfl⟩
      refine ⟨⟨inf_le_left, ?_⟩, ?_, ?_⟩
      · simp only
        rw [span_inf_eq L hFull]
      · simp only
        rw [span_inf_eq L hFull, a]
      · simp only
        rw [hU, hsq, b]

end GlobalTheory.Mass.DetAgree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsOrthComplementOfUnitVectorAtRealPlaceStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOrthComplementOfUnitVector_at_real_place : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ v, qEps (I.ε v) (infVec I v x) = sgn ℝ s ∧ star (infVec I v x) ᵥ* (Formalism.REAL.Jm (I.ε v) * infMat D v A) = 0 ∧ (infMat D v A)ᴴ * Formalism.REAL.Jm (I.ε v) * infMat D v A = Formalism.REAL.Jm (D.ε v) := by
  first | exact @GlobalTheory.StabUnfold.isPerp_at_place | exact GlobalTheory.StabUnfold.isPerp_at_place | (intros; apply GlobalTheory.StabUnfold.isPerp_at_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LiftedFlagLatticeChainSpans
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.LatChain

section
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem mem_orth {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem exists_mul_mem {Λ : Submodule (𝓞 E) S.V} (hΛ : Submodule.IsFullLattice E Λ) (v : S.V) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (Λ : Set S.V) := by
    letI := hΛ
    rw [Submodule.IsFullLattice.span_eq_top]; trivial
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ v hv
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩

theorem le_spanE {Λ M : Submodule (𝓞 E) S.V} (hΛ : Submodule.IsFullLattice E Λ) {U : Submodule E S.V}
    (h : Λ ⊓ toO S U ≤ M) : U ≤ spanE S M := by
  intro v hv
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem hΛ v
  have h0 : d • v ∈ toO S U := (toO S U).smul_mem d hv
  have h1 : d • v ∈ M := h ⟨hd, h0⟩
  have h2 := Submodule.smul_mem _ (algebraMap (𝓞 E) E d)⁻¹ (Submodule.subset_span (R := E) h1)
  rwa [← algebraMap_smul E d v, inv_smul_smul₀
    ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)] at h2

theorem spanE_le {M : Submodule (𝓞 E) S.V} {U : Submodule E S.V} (h : M ≤ toO S U) : spanE S M ≤ U :=
  Submodule.span_le.2 h

variable {r : ℕ} {T T' : E} {Λ : Submodule (𝓞 E) S.V}

theorem mem_L0sub {F : LFlag S r T} {x : S.V} (hx : x ∈ Lrep Λ F) (hz : S.hT F.fl.z x = 0) :
    x ∈ L0sub Λ F :=
  ⟨⟨Submodule.mem_sup_left hx, hx.2⟩, hz⟩

theorem thp_le_la (g : ℕ) {F : LFlag S r T} {F' : LFlag S r T'} (hΛ : Submodule.IsFullLattice E Λ)
    (hF : IsLift Λ F) (hF' : IsLift Λ F') : Thp Λ F F' ≤ La Λ g F F' := by
  intro x hx
  have hperp : ∀ y ∈ UUE Λ F F', S.hT y x = 0 := mem_orth.1 hx.2
  have hX : Xsp F ≤ UUE Λ F F' :=
    le_spanE hΛ (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
  have hX' : Xsp F' ≤ UUE Λ F F' := le_spanE hΛ (le_sup_of_le_left le_sup_right)
  have hz : F.fl.z ∈ UUE Λ F F' := by
    rw [← hF.2]
    exact Submodule.subset_span (Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))))
  have hz' : F'.fl.z ∈ UUE Λ F F' := by
    rw [← hF'.2]
    exact Submodule.subset_span (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have h1 : x ∈ Lrep Λ F := ⟨hx.1, mem_orth.2 fun y hy => hperp y (hX hy)⟩
  have h2 : x ∈ Lrep Λ F' := ⟨hx.1, mem_orth.2 fun y hy => hperp y (hX' hy)⟩
  refine Submodule.subset_span ⟨hx.2, mem_L0sub h1 (hperp _ hz), mem_L0sub h2 (hperp _ hz'),
    x, h1, ?_, x, h2, ?_, ?_⟩ <;> rw [sub_self] <;> exact Submodule.zero_mem _

end

theorem lattice_chain_spans : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T'), Submodule.IsFullLattice E Λ → IsLift Λ F → IsLift Λ F' → Thp Λ F F' ≤ La Λ g F F' ∧ La Λ g F F' ≤ L0sub Λ F ⊓ toO S (Hp Λ F F') ∧ spanE S (Thp Λ F F') = Hp Λ F F' ∧ ∀ (F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V), spanE S (Mlat Λ F F' F'' β g) = Th Λ F F' F'' β := by
  intro E _ _ _ S r T T' Λ g F F' hΛ hF hF'
  have h1 := thp_le_la g hΛ hF hF'
  refine ⟨h1, Submodule.span_le.2 fun x hx => ⟨hx.2.1, hx.1⟩,
    le_antisymm (spanE_le inf_le_right) (le_spanE hΛ le_rfl), fun F'' β =>
    le_antisymm (spanE_le inf_le_right) (le_spanE hΛ fun x hx => ⟨h1 ⟨hx.1, ?_⟩, hx.2⟩)⟩
  obtain ⟨p, hp, e⟩ := hx.2
  have : p.1 = x := e
  rw [← this]
  exact hp.1.1.1

end GlobalTheory.LoopC.LatChain
end

