module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLattice
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0267
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0002
public import Formalism.PeriodIntegrals.AdmissibleModel.WeylDim
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesSameGramDifferBySkewSolution
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.FrameDiff

theorem dd_zpow_le (D : D7) (a : Fin D.R.rS) :
    (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤
      ddS D ^ (-(D.R.rS : ℤ)) := by
  have ha := a.2
  by_cases h0 : ddS D = 0
  · rw [h0, _root_.zero_zpow _ (by omega)]
    exact FractionalIdeal.zero_le _
  · have h1 : (-((D.R.rS : ℤ) - (a : ℕ))) = -(D.R.rS : ℤ) + ((a : ℕ) : ℤ) := by ring
    rw [h1, zpow_add₀ h0, zpow_natCast]
    have h2 : ddS D ^ (a : ℕ) ≤ 1 := by
      unfold ddS
      rw [← FractionalIdeal.coeIdeal_pow]
      exact FractionalIdeal.coeIdeal_le_one
    calc _ ≤ ddS D ^ (-(D.R.rS : ℤ)) * 1 := by gcongr
      _ = _ := mul_one _

theorem coords_of_mem_XS (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (y : (VS D).V)
    (hy : y ∈ XS D F0) :
    ∃ c : Fin D.R.rS → D.host.E,
      (∀ a, c a ∈ (ddS D ^ (-(D.R.rS : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧
      y = ∑ a, c a • F0.e a := by
  unfold XS at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, x, hx, rfl⟩ := hy
    refine ⟨Pi.single a x, fun a' => ?_, ?_⟩
    · by_cases h : a' = a
      · subst h
        rw [Pi.single_eq_same]
        exact dd_zpow_le D a' hx
      · rw [Pi.single_eq_of_ne h]
        exact FractionalIdeal.zero_mem _
    · rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
  | zero => exact ⟨0, fun _ => FractionalIdeal.zero_mem _, by simp⟩
  | add y y' _ _ h h' =>
    obtain ⟨c, hc, rfl⟩ := h
    obtain ⟨c', hc', rfl⟩ := h'
    refine ⟨c + c', fun a => ?_, by simp [add_smul, Finset.sum_add_distrib]⟩
    exact Submodule.add_mem (FractionalIdeal.coeToSubmodule _) (hc a) (hc' a)
  | smul o y _ h =>
    obtain ⟨c, hc, rfl⟩ := h
    refine ⟨o • c, fun a => ?_, by simp [Finset.smul_sum, smul_assoc]⟩
    exact Submodule.smul_mem (FractionalIdeal.coeToSubmodule _) o (hc a)

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem star_hT (x y : S.V) : star (S.hT x y) = S.hT y x := S.herm.eq x y

theorem gram_eq (F F' : FlagG S r T) (b b' : Fin (r + 1)) :
    S.hT (F.fvec b) (F.fvec b') = S.hT (F'.fvec b) (F'.fvec b') := by
  have hz : ∀ (G : FlagG S r T) a, S.hT G.z (G.e a) = 0 := fun G a => by
    rw [← star_hT, G.z_orth, star_zero]
  induction b using Fin.lastCases <;> induction b' using Fin.lastCases <;>
    simp [FlagG.fvec, F.e_iso, F'.e_iso, F.z_orth, F'.z_orth, F.z_norm, F'.z_norm, hz]

theorem mem_orth_iff (U : Submodule E S.V) (v : S.V) : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem hT_X_eq_zero (F : FlagG S r T) (v : S.V) (hv : ∀ a, S.hT (F.e a) v = 0) (x : S.V) (hx : x ∈ F.X) :
    S.hT x v = 0 := by
  unfold FlagG.X at hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact hv a
  | zero => simp
  | add y y' _ _ h h' => simp [h, h']
  | smul c y _ h => simp [h]

theorem frame_mem (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (h : IsLift Λ F) (he : ∀ a, F.fl.e a ∈ Λ)
    (b : Fin (r + 1)) : frame F b ∈ Λ := by
  induction b using Fin.lastCases with
  | last => simpa [FlagG.fvec] using h.1
  | cast a => simpa [FlagG.fvec] using he a

end Gen

theorem mem_perpE_iff (D : D7) (P : LatW D) (w : (D.sp.X 0).V) :
    w ∈ perpE D P ↔ ∀ p ∈ P, (D.sp.X 0).hT p w = 0 := by
  simp [perpE, Submodule.mem_iInf]

theorem frame_diff : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ (P : LatW D) (φ : P →ₗ[𝓞 D.host.E] (hS D).V) (Z : GramM D), (∀ p, φ p ∈ XLam Λ (lf D F0)) → ∀ F₁ ∈ FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ, ∀ F₂ ∈ FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ, (∀ b, ∃ w, IsWcomp D P (frame F₁ b) w ∧ IsWcomp D P (frame F₂ b) w) → ∃ x : Matrix (Fin D.R.rS) (Fin (D.R.rS + 1)) D.host.E, (∀ b, frame F₂ b = frame F₁ b + ∑ a, x a b • F0.e a) ∧ (∀ a b, x a b ∈ (ddS D ^ (-(D.R.rS : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧ xᴴ * Z.submatrix Fin.castSucc id + (Z.submatrix Fin.castSucc id)ᴴ * x = 0 := by
  intro D u u' F0 Λ hst hb hrow P φ Z hφ F₁ h₁ F₂ h₂ hw
  obtain ⟨hW, -, hpos, -⟩ := _root_.GlobalTheory.LoopC.Base.main D u u' F0 Λ hst hb hrow
  obtain ⟨l₁, e₁, z₁, o₁⟩ := h₁
  obtain ⟨l₂, e₂, z₂, o₂⟩ := h₂
  have hiso : ∀ x y, (hS D).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y :=
    D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega)
  have hZ₁ : ∀ a b, (hS D).hT (F0.fvec a) (frame F₁ b) = Z a b := fun a b => by rw [← z₁]; rfl
  have hZ₂ : ∀ a b, (hS D).hT (F0.fvec a) (frame F₂ b) = Z a b := fun a b => by rw [← z₂]; rfl
  have hWX : ∀ (w : (D.sp.X 0).V), ∀ x ∈ F0.X, (hS D).hT (D.sp.iXY 0 w) x = 0 := by
    intro w x hx
    rw [← star_hT, hT_X_eq_zero F0 (D.sp.iXY 0 w) (fun a => ?_) x hx, star_zero]
    rw [← star_hT, hb.1, (D.sp.hyp_orthX a w).1, star_zero]
  have hd : ∀ b, frame F₂ b - frame F₁ b ∈ XS D F0 := by
    intro b
    rw [← hrow.2.2]
    refine ⟨Λ.sub_mem (frame_mem Λ F₂ l₂ e₂ b) (frame_mem Λ F₁ l₁ e₁ b), ?_⟩
    set d := frame F₂ b - frame F₁ b with hdd
    have hf : ∀ a, (hS D).hT (F0.fvec a) d = 0 := fun a => by rw [hdd, map_sub, hZ₁, hZ₂, sub_self]
    have hX : ∀ x ∈ F0.X, (hS D).hT x d = 0 :=
      hT_X_eq_zero F0 d (fun a => by simpa [FlagG.fvec] using hf a.castSucc)
    have hz : (hS D).hT F0.z d = 0 := by simpa [FlagG.fvec] using hf (Fin.last _)
    have hmem : d ∈ Wsp D ⊔ Xsp (lf D F0) := by
      rw [hW.1, mem_orth_iff]
      intro y hy
      obtain ⟨x, hx, y', hy', rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy'
      simp [hX x hx, hz]
    obtain ⟨_, ⟨w, rfl⟩, x, hx, hwx⟩ := Submodule.mem_sup.1 hmem
    have hwd : ∀ σ, (hS D).hT (D.sp.iXY 0 σ) d = (D.sp.X 0).hT σ w := fun σ => by
      rw [← hwx, map_add (f := _), hiso, hWX σ x hx, add_zero]
    have hwP : w ∈ perpE D P := by
      rw [mem_perpE_iff]
      intro p hp
      have h1 : (hS D).hT (D.sp.iXY 0 p + φ ⟨p, hp⟩) d = 0 := by
        rw [hdd, map_sub, o₁ ⟨p, hp⟩ b, o₂ ⟨p, hp⟩ b, sub_self]
      rw [map_add (f := _), LinearMap.add_apply, hX _ (hφ ⟨p, hp⟩).2, add_zero, hwd] at h1
      exact h1
    obtain ⟨w', c₁, c₂⟩ := hw b
    have hww : (D.sp.X 0).hT w w = 0 := by
      rw [← hwd, hdd, map_sub, c₁.2 w hwP, c₂.2 w hwP, sub_self]
    have hw0 : w = 0 := by
      by_contra hne
      obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
      have := hpos τ w hne
      rw [hww] at this
      simp at this
    rw [hw0, map_zero, zero_add] at hwx
    rw [← hwx]
    exact hx
  choose c hc hcd using fun b => coords_of_mem_XS D F0 _ (hd b)
  have hfr : ∀ b, frame F₂ b = frame F₁ b + ∑ a, c b a • F0.e a := fun b => by
    rw [← hcd]; abel
  refine ⟨Matrix.of fun a b => c b a, hfr, fun a b => hc b a, ?_⟩
  refine Matrix.ext fun b b' => ?_
  have hg : (hS D).hT (frame F₂ b) (frame F₂ b') = (hS D).hT (frame F₁ b) (frame F₁ b') :=
    gram_eq F₂.fl F₁.fl b b'
  have hY : ∀ a b, (hS D).hT (F0.e a) (frame F₁ b) = Z a.castSucc b := fun a b => by
    simpa [FlagG.fvec] using hZ₁ a.castSucc b
  have hY' : ∀ a b, (hS D).hT (frame F₁ b) (F0.e a) = star (Z a.castSucc b) := fun a b => by
    rw [← hY, star_hT]
  rw [hfr b, hfr b'] at hg
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, LinearMap.add_apply, LinearMap.sum_apply, map_smul, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, hY, hY', F0.e_iso, smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero,
    starRingEnd_apply] at hg
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.submatrix_apply, id, Matrix.zero_apply]
  have : ∑ a, star (Z a.castSucc b) * c b' a = ∑ a, c b' a * star (Z a.castSucc b) :=
    Finset.sum_congr rfl fun a _ => mul_comm _ _
  rw [this]
  linear_combination hg

end GlobalTheory.LoopC.FrameDiff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePh
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.KernelExpansion

theorem exists_mem_of_dense {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    [FiniteDimensional ℂ (LinearMap.range (T : H →ₗ[ℂ] H))] (S : Submodule ℂ H) (hS : Dense (S : Set H))
    (x : H) : ∃ g ∈ S, T g = T x := by
  have : FiniteDimensional ℂ (S.map (T : H →ₗ[ℂ] H)) :=
    Submodule.finiteDimensional_of_le LinearMap.map_le_range
  have hc : IsClosed ((fun z => T z) ⁻¹' (S.map (T : H →ₗ[ℂ] H) : Set H)) :=
    (Submodule.closed_of_finiteDimensional _).preimage T.continuous
  have hx : x ∈ closure (S : Set H) := hS x
  exact hc.closure_subset_iff.2 (fun z hz => ⟨z, hz, rfl⟩) hx

theorem exists_orthonormal {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    [FiniteDimensional ℂ (LinearMap.range (T : H →ₗ[ℂ] H))]
    (hT : IsOrthProjOnto T (LinearMap.range (T : H →ₗ[ℂ] H))) (D : ℕ)
    (hD : Module.finrank ℂ (LinearMap.range (T : H →ₗ[ℂ] H)) = D) :
    ∃ y : Fin D → H, Orthonormal ℂ y ∧ Submodule.span ℂ (Set.range y) = LinearMap.range (T : H →ₗ[ℂ] H) ∧
      (∀ i, T (y i) = y i) ∧ ∀ g, T g = ∑ i, ⟪y i, g⟫_ℂ • y i := by
  subst hD
  let b := stdOrthonormalBasis ℂ (LinearMap.range (T : H →ₗ[ℂ] H))
  have hfix : ∀ i, T (b i : H) = b i := by
    intro i
    obtain ⟨z, hz⟩ := (b i).2
    have := congrArg (fun A : H →L[ℂ] H => A z) hT.1
    rw [← hz]
    exact this
  have hexp : ∀ g, T g = ∑ i, ⟪(b i : H), g⟫_ℂ • (b i : H) := by
    intro g
    have h := congrArg Subtype.val (b.sum_repr' ⟨T g, g, rfl⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hT.2.1, hfix]
  refine ⟨fun i => b i, b.orthonormal.comp_linearIsometry (Submodule.subtypeₗᵢ _), ?_, hfix, hexp⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (b i).2
  · rintro _ ⟨g, rfl⟩
    show T g ∈ _
    rw [hexp]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def compactSub {X : Type} [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X) : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {y | ∃ C : Set X, IsCompact C ∧ ∀ᵐ z ∂μ, z ∉ C → (y : X → ℂ) z = 0}
  add_mem' := by
    rintro a b ⟨C, hC, ha⟩ ⟨C', hC', hb⟩
    refine ⟨C ∪ C', hC.union hC', ?_⟩
    filter_upwards [ha, hb, Lp.coeFn_add a b] with z h1 h2 h3 hz
    rw [Set.mem_union, not_or] at hz
    rw [h3, Pi.add_apply, h1 hz.1, h2 hz.2, add_zero]
  zero_mem' := ⟨∅, isCompact_empty, by
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with z h _
    rw [h]; rfl⟩
  smul_mem' := by
    rintro c a ⟨C, hC, ha⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [ha, Lp.coeFn_smul c a] with z h1 h2 hz
    rw [h2, Pi.smul_apply, h1 hz, smul_zero]

theorem coeFn_sum_smul {X ι : Type} [MeasurableSpace X] (μ : Measure X) (s : Finset ι) (c : ι → ℂ)
    (y : ι → Lp ℂ 2 μ) (F : ι → X → ℂ) (h : ∀ i, (y i : X → ℂ) =ᵐ[μ] F i) :
    ((∑ i ∈ s, c i • y i : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] fun x => ∑ i ∈ s, c i * F i x := by
  exact _root_.GlobalTheory.SumSmulAeEq.coeFn_sum_smul_ae_eq μ s c y F h

theorem ae_eq_of_pairing {X ι : Type} [Fintype ι] [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsLocallyFiniteMeasure μ] (k : X → ℂ) (hk : Continuous k)
    (c : ι → ℂ) (y : ι → Lp ℂ 2 μ) (F : ι → X → ℂ) (hF : ∀ i, Continuous (F i))
    (h : ∀ i, (y i : X → ℂ) =ᵐ[μ] F i)
    (hp : ∀ g ∈ compactSub μ, ∫ z, k z * (g : X → ℂ) z ∂μ = ∑ i, ⟪y i, g⟫_ℂ * c i) :
    (fun z => k z - ∑ i, c i * star (F i z)) =ᵐ[μ] 0 := by
  have hc : ∀ i, Continuous fun z => c i * star (F i z) := fun i => continuous_const.mul (hF i).star
  refine ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'
    (hk.sub (continuous_finsetSum _ fun i _ => hc i)).locallyIntegrable fun s hs => ?_
  have hm : MeasurableSet s := hs.isClosed.measurableSet
  have hg := indicatorConstLp_coeFn (p := 2) (hs := hm) (hμs := hs.measure_lt_top.ne) (c := (1 : ℂ)) (μ := μ)
  have h1 := hp (indicatorConstLp 2 hm hs.measure_lt_top.ne (1 : ℂ)) ⟨s, hs, by
    filter_upwards [hg] with z hz hzs
    rw [hz, Set.indicator_of_notMem hzs]⟩
  have e : ∀ u : X → ℂ, ∫ z, u z * (indicatorConstLp 2 hm hs.measure_lt_top.ne (1 : ℂ) : Lp ℂ 2 μ) z ∂μ =
      ∫ z in s, u z ∂μ := by
    intro u
    rw [← integral_indicator hm]
    refine integral_congr_ae ?_
    filter_upwards [hg] with z hz
    rw [hz]
    by_cases hzs : z ∈ s <;> simp [hzs]
  rw [integral_sub (hk.continuousOn.integrableOn_compact hs)
    ((continuous_finsetSum _ fun i _ => hc i).continuousOn.integrableOn_compact hs),
    integral_finsetSum _ fun i _ => (hc i).continuousOn.integrableOn_compact hs, ← e, h1, sub_eq_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, ← e, mul_comm, L2.inner_def]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h i] with z hz
  rw [hz]
  simp [mul_comm]

theorem integral_mul_star {X : Type} [MeasurableSpace X] (μ : Measure X) (y : Lp ℂ 2 μ) (F : X → ℂ)
    (h : (y : X → ℂ) =ᵐ[μ] F) (hy : ‖y‖ = 1) :
    Integrable (fun x => F x * star (F x)) μ ∧ ∫ x, F x * star (F x) ∂μ = 1 := by
  have e : (fun x => ⟪(y : X → ℂ) x, (y : X → ℂ) x⟫_ℂ) =ᵐ[μ] fun x => F x * star (F x) := by
    filter_upwards [h] with z hz
    rw [hz, RCLike.inner_apply]
    rfl
  refine ⟨(L2.integrable_inner y y).congr e, ?_⟩
  rw [← integral_congr_ae e, ← L2.inner_def, inner_self_eq_norm_sq_to_K, hy]
  simp

theorem norm_sum_sq_le {ι : Type} [Fintype ι] (c F : ι → ℂ) :
    ‖∑ i, c i * F i‖ ^ 2 ≤ (∑ i, ‖c i‖ ^ 2) * ‖∑ i, F i * star (F i)‖ := by
  have e : ∑ i, F i * star (F i) = ((∑ i, ‖F i‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Complex.mul_conj' (F i)
  rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq univ (fun i => ‖c i‖) (fun i => ‖F i‖))
  gcongr
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp

theorem two_mul_rank_le {n : ℕ} (ε : Fin n → Bool) : 2 * rkR ε ≤ n := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun a => ε a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h
  unfold rkR
  omega

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d) (hdec : LocDec B h)
    (hb : HBig B 32 h) : Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hc, hle, hi⟩ := _root_.GlobalTheory.Dec.PhMajProof.phMaj B d h hd hdec
  have h1 := hi 0 le_rfl fun v => by
    rcases Nat.eq_zero_or_pos (rkR (B.I.ε v)) with h0 | h0
    · exact Or.inl h0
    · right
      have h2 : (2 : ℝ) * rkR (B.I.ε v) ≤ B.I.n := by exact_mod_cast two_mul_rank_le _
      have h3 : (0 : ℝ) < rkR (B.I.ε v) := by exact_mod_cast h0
      have h4 := Real.sqrt_pos.2 h3
      refine lt_of_lt_of_le ?_ (hb v)
      have h5 : (B.I.n : ℝ) * rkR (B.I.ε v) < (B.I.n : ℝ) ^ 2 := by nlinarith
      nlinarith [mul_lt_mul_of_pos_right h5 h4]
  refine h1.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
  simpa using hle g

theorem kernelB : KernelB := by
  intro B d h hd hn hdec hb hfin T hT
  obtain ⟨hT2, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  have : BorelSpace B.I.GA := inferInstance
  have : (Measure.pi fun v => Formalism.REAL.muG (B.I.ε v)).IsHaarMeasure := Measure.pi.isHaarMeasure _
  have : (B.I.muA B.μf).IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  obtain ⟨-, -, -, hP⟩ := _root_.GlobalTheory.GlobProj.globalProj_holds B d hd (integrable_ph B d h hd hdec hb)
  obtain ⟨hproj, -, -, hfd, hD⟩ := hP T hT
  have := hfd hfin
  obtain ⟨hbd, hKc, hKi, -⟩ := _root_.GlobalTheory.KernelConv.kernelA B d h hd hn hdec hb
  obtain ⟨y, hy, hspan, hfix, hexp⟩ := exists_orthonormal T hproj B.D hD
  have hrep : ∀ g ∈ compactSub ((B.I.muA B.μf).restrict B.fund), IsContRep B (T g)
      (fun x => ∫ z in B.fund, kern B.I (phe B d) x z * (g : B.I.GA → ℂ) z ∂(B.I.muA B.μf)) := by
    rintro g ⟨C, hC, hg⟩
    exact _root_.GlobalTheory.KernelContRep.isContRep_integral_kernel B d h hd hn hdec hb T hT g C hC hg
  have huniq : ∀ (u : B.I.L2 B.μf B.fund) f f', IsContRep B u f → IsContRep B u f' → f' = f :=
    fun u f f' h1 h2 => (GlobalTheory.ExtContRep.ext_ae_eq_contRep B u f h1).2.1 f' h2
  have hF : ∀ i, ∃ F, IsContRep B (y i) F := by
    intro i
    obtain ⟨g, hg, e⟩ := exists_mem_of_dense T (compactSub _) (_root_.GlobalTheory.CompactDense.dense_compact_support B) (y i)
    exact ⟨_, hfix i ▸ e ▸ hrep g hg⟩
  choose F hF using hF
  have hK : ∀ x z, kern B.I (phe B d) x z = ∑ i, F i x * star (F i z) := by
    intro x z
    have hkx : Continuous fun z => kern B.I (phe B d) x z :=
      Continuous.comp (g := fun p : B.I.GA × B.I.GA => kern B.I (phe B d) p.1 p.2) (f := fun z => (x, z)) hKc
        (Continuous.prodMk_right x)
    have h0 := ae_eq_of_pairing ((B.I.muA B.μf).restrict B.fund) _ hkx (fun i => F i x) y F
      (fun i => (hF i).1) (fun i => (hF i).2.2) fun g hg => by
        have h1 : IsContRep B (T g) fun x => ∑ i, ⟪y i, g⟫_ℂ * F i x := by
          refine ⟨continuous_finsetSum _ fun i _ => continuous_const.mul (hF i).1, fun γ hγ x => ?_, ?_⟩
          · exact Finset.sum_congr rfl fun i _ => by rw [(hF i).2.1 γ hγ]
          · rw [hexp]
            exact coeFn_sum_smul _ _ _ y F fun i => (hF i).2.2
        exact congrFun (huniq _ _ _ h1 (hrep g hg)) x
    have z0 : IsContRep B 0 0 := ⟨continuous_const, fun _ _ _ => rfl, Lp.coeFn_zero _ _ _⟩
    have z1 : IsContRep B 0 fun z => kern B.I (phe B d) x z - ∑ i, F i x * star (F i z) := by
      refine ⟨hkx.sub (continuous_finsetSum _ fun i _ => continuous_const.mul (hF i).1.star),
        fun γ hγ w => ?_, (Lp.coeFn_zero _ _ _).trans h0.symm⟩
      beta_reduce
      rw [(hKi γ hγ x w).2]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [(hF i).2.1 γ hγ]
    exact sub_eq_zero.1 (congrFun (huniq _ _ _ z0 z1) z)
  have hI := fun i => integral_mul_star _ (y i) (F i) (hF i).2.2 (hy.1 i)
  refine ⟨y, F, hy, hspan, hF, hK, ?_, ?_, fun c x => ?_⟩
  · simp only [hK]
    exact integrable_finsetSum _ fun i _ => (hI i).1
  · simp only [hK]
    rw [integral_finsetSum _ fun i _ => (hI i).1]
    simp only [(hI _).2]
    simp
  · refine (norm_sum_sq_le c fun i => F i x).trans ?_
    rw [← hK]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_tsum_le_tsum_norm (hbd x x).1).trans ((hbd x x).2.trans (le_of_eq ?_))
    rw [mul_inv, ← sq, ← pow_mul]
    congr 2
    ring

end GlobalTheory.KernelExpansion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdSubEqProdFactorial
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.WeylDimU

theorem prod_sub_eq_prod_factorial (k : ℕ) :
    ∏ a : Fin k, ∏ b ∈ Finset.univ.filter (fun b : Fin k => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  rcases k with _ | m
  · simp
  have h := Matrix.det_vandermonde_id_eq_superFactorial (R := ℝ) m
  rw [Matrix.det_vandermonde, ← Nat.prod_range_succ_factorial, Nat.cast_prod] at h
  simp only [Finset.filter_lt_eq_Ioi]
  rw [← h]

theorem finrank_space {k : ℕ} (lam : Formalism.BasicNotions.DomWeight k) (u : Fin k → ℝ)
    (hu : ∀ a, (lam.w a : ℝ) = u a - (((k : ℝ) - 1) / 2 - (a : ℕ))) :
    (Module.finrank ℂ (GlobalTheory.DualWeyl.Space lam.natW) : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  have h := Formalism.L2.G.Model.weyl_dualWeyl ℂ k lam.natW (Formalism.BasicNotions.factNatW k lam).1
  have h2 := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [Rat.cast_natCast, Rat.cast_prod] at h2
  refine Eq.trans h2 ?_
  rw [← prod_sub_eq_prod_factorial, vand, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_div_distrib, Finset.prod_filter]
  refine Finset.prod_congr rfl fun b _ => ?_
  split_ifs
  · push_cast
    congr 1
    linarith [hu a, hu b, GlobalTheory.NablaType.natW_add lam a, GlobalTheory.NablaType.natW_add lam b]
  · simp

theorem finrank_eq (k : ℕ) (u : Fin k → ℝ) (hu : IsHCParam u) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (hπ : IsHCTypeU k u π) :
    (Module.finrank ℂ H : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  obtain ⟨hs, hm⟩ := hu
  choose m hm using hm
  have hm' : StrictAnti m := fun a b hab => by
    have := hs hab
    have h2 : (m b : ℝ) < m a := by linarith [hm a, hm b]
    exact_mod_cast h2
  have hL : Antitone fun a : Fin k => m a + (a : ℕ) := by
    rcases k with _ | n
    · exact fun a => a.elim0
    rw [Fin.antitone_iff_succ_le]
    intro i
    have := hm' (Fin.castSucc_lt_succ (i := i))
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  let lam : Formalism.BasicNotions.DomWeight k := ⟨fun a => m a + (a : ℕ), hL⟩
  have hw : ∀ a, (lam.w a : ℝ) = u a - (((k : ℝ) - 1) / 2 - (a : ℕ)) := fun a => by
    simp only [lam]
    push_cast
    linarith [hm a]
  have hK := GlobalTheory.NablaType.isKTypeOf_act lam
  have hT : IsHCTypeU k u (GlobalTheory.NablaType.act lam) := by
    refine ⟨?_, inferInstance, GlobalTheory.NablaType.isURepOn_act lam, ?_⟩
    · obtain ⟨v, -, hv, -⟩ := hK.2.2.2.1
      exact ⟨v, 0, hv⟩
    · convert hK using 1
      funext a
      unfold allPos
      rw [GlobalTheory.DefiniteCheck.lowK_const, hw]
  obtain ⟨A, -⟩ := GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU k u _ _ _ _ hπ hT
  rw [A.finrank_eq]
  exact finrank_space lam u hw

theorem weyl_dimension : ∀ (k : ℕ) (u : Fin k → ℝ), IsHCParam u → (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsHCTypeU k u π → (Module.finrank ℂ H : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ)) ∧ (dimPiU k u : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  intro k u hu
  refine ⟨fun H _ _ π hπ => finrank_eq k u hu H π hπ, ?_⟩
  obtain ⟨H, _, _, π, hπ⟩ := GlobalTheory.CompactDS.exists_isHCTypeU k u hu
  have hne : {d | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsHCTypeU k u π ∧ Module.finrank ℂ H = d}.Nonempty :=
    ⟨_, H, _, _, π, hπ, rfl⟩
  obtain ⟨H', _, _, π', hπ', e⟩ := Nat.sInf_mem hne
  rw [dimPiU, ← e]
  exact finrank_eq k u hu H' π' hπ'

end GlobalTheory.WeylDimU
end

