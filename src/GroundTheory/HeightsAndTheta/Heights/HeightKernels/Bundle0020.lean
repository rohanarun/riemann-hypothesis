module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassGeomDegChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Geo hiding fibre

noncomputable section

namespace GrassmannianGeometricDegreeChart

variable {n : ℕ}

def single1 (c : Fin (1 + n)) : PlIdx 1 n := ⟨{c}, Finset.card_singleton c⟩

theorem eq_single1 (I : PlIdx 1 n) : I = single1 (I.1.orderEmbOfFin I.2 0) := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp I.2
  have h2 : ∀ x ∈ I.1, x = c := fun x hx => by rw [hc] at hx; exact Finset.mem_singleton.mp hx
  apply Subtype.ext
  rw [h2 _ (Finset.orderEmbOfFin_mem I.1 I.2 0)]
  exact hc

theorem fin_one_fun_eq_const {α : Type*} (i : Fin 1 → α) : (fun _ => i 0) = i :=
  funext fun k => congrArg i (Subsingleton.elim 0 k)

def a0 : Σ _ : Fin 1, PlIdx 1 n := ⟨0, single1 (Fin.castAdd n 0)⟩

def chartPt (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) : Fin 1 → Matrix (Fin 1) (Fin n) ℂ :=
  fun _ _ b => z ⟨0, single1 (Fin.natAdd 1 b)⟩ / z a0

theorem rootCoord_mul (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) (ht : z a0 ≠ 0) :
    (fun p => rootCoord (chartPt z) p * z a0) = z := by
  funext p
  obtain ⟨k, I⟩ := p
  obtain rfl : k = 0 := Subsingleton.elim _ _
  conv_rhs => rw [eq_single1 I]
  simp only [rootCoord, colsOf, onePipe, Matrix.det_unique, Matrix.submatrix_apply, Matrix.of_apply, id]
  generalize I.1.orderEmbOfFin I.2 0 = c
  refine Fin.addCases (fun a => ?_) (fun b => ?_) c
  · obtain rfl : a = 0 := Subsingleton.elim _ _
    simp only [Fin.append_left]
    rw [show (default : Fin 1) = 0 from rfl, Matrix.one_apply_eq, one_mul]
    rfl
  · simp only [Fin.append_right, chartPt]
    exact div_mul_cancel₀ _ ht

theorem eval_eq_zero {g : MRing (plBlocks 1 1 n)} (hg : g ∈ grassIdeal 1 1 n) (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) :
    MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) g) = 0 := by
  have key : ∀ z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ, z a0 ≠ 0 →
      MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) g) = 0 := by
    intro z hz
    have h0 : mConeMap (rootCoord (chartPt z)) g = 0 := GrassLeRoot.proof 1 1 n _ hg
    have h1 := congrArg ((MvPolynomial.aeval fun _ : Fin 1 => z a0).restrictScalars ℤ) h0
    rw [map_zero, mConeMap] at h1
    rw [show ((MvPolynomial.aeval fun _ : Fin 1 => z a0).restrictScalars ℤ)
        ((MvPolynomial.aeval fun p => MvPolynomial.C (rootCoord (chartPt z) p) * MvPolynomial.X p.1) g) =
        (((MvPolynomial.aeval fun _ : Fin 1 => z a0).restrictScalars ℤ).comp
          (MvPolynomial.aeval fun p => MvPolynomial.C (rootCoord (chartPt z) p) * MvPolynomial.X p.1)) g from rfl,
      MvPolynomial.comp_aeval] at h1
    simp only [AlgHom.restrictScalars_apply, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Algebra.algebraMap_self, RingHom.id_apply] at h1
    rw [rootCoord_mul z hz] at h1
    rw [MvPolynomial.eval_map, ← h1, MvPolynomial.aeval_def]
    rfl
  have hq : MvPolynomial.map (Int.castRingHom ℂ) g * MvPolynomial.X a0 = 0 := by
    apply MvPolynomial.funext
    intro z
    rw [map_mul, MvPolynomial.eval_X, map_zero]
    by_cases hz : z a0 = 0
    · rw [hz, mul_zero]
    · rw [key z hz, zero_mul]
  rcases mul_eq_zero.mp hq with h | h
  · rw [h, map_zero]
  · exact absurd h (MvPolynomial.X_ne_zero a0)

theorem mem_mcPts (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) :
    z ∈ mcPts (grassIdeal 1 1 n) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ hf => eval_eq_zero hf z⟩⟩

theorem segre_eq (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) (i : Fin 1 → PlIdx 1 n) :
    segre (ι := plBlocks 1 1 n) z i = z ⟨0, i 0⟩ := by
  simp [segre]

theorem apply_eq_segre (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) (p : Σ _ : Fin 1, PlIdx 1 n) :
    z p = segre (ι := plBlocks 1 1 n) z (fun _ => p.2) := by
  obtain ⟨k, I⟩ := p
  obtain rfl : k = 0 := Subsingleton.elim _ _
  rw [segre_eq]

def blockLift (x : PlIdx 1 n → ℂ) : (Σ _ : Fin 1, PlIdx 1 n) → ℂ := fun p => x p.2

theorem segre_blockLift (x : PlIdx 1 n → ℂ) :
    segre (ι := plBlocks 1 1 n) (blockLift x) = fun i => x (i 0) := by
  funext i
  rw [segre_eq]
  rfl

theorem card_seg : Fintype.card (Fin 1 → PlIdx 1 n) = n + 1 := by
  simp [PlIdx, Fintype.card_subtype, Finset.card_powersetCard, add_comm]

theorem exists_of_ne_zero {w : (Fin 1 → PlIdx 1 n) → ℂ} (hw : w ≠ 0) :
    blockLift (fun I => w fun _ => I) ∈ mcPts (grassIdeal 1 1 n) ∧
      segre (ι := plBlocks 1 1 n) (blockLift fun I => w fun _ => I) = w := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  refine ⟨(mem_mcPts _).2 fun _ => ⟨i 0, ?_⟩, ?_⟩
  · simpa [blockLift, fin_one_fun_eq_const] using hi
  · rw [segre_blockLift]
    funext i'
    simp only [fin_one_fun_eq_const]

theorem injective_of_good {Ψ : (((k : Fin 1) → plBlocks 1 1 n k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)}
    (hΨ : IsGoodProj (grassIdeal 1 1 n) Ψ) : Function.Injective Ψ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  by_contra hne
  obtain ⟨hm, hs⟩ := exists_of_ne_zero hne
  exact hΨ _ hm (by rw [hs]; exact hw)

theorem exists_good (n : ℕ) :
    ∃ Ψ : (((k : Fin 1) → plBlocks 1 1 n k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ), IsGoodProj (grassIdeal 1 1 n) Ψ := by
  let Ψ0 := LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFinOfCardEq (card_seg (n := n))).symm
  refine ⟨Ψ0.toLinearMap, fun z hz h0 => ?_⟩
  obtain ⟨i, hi⟩ := hz.1 0
  have hs : segre (ι := plBlocks 1 1 n) z = 0 := Ψ0.map_eq_zero_iff.mp h0
  exact hi (by rw [apply_eq_segre z ⟨0, i⟩, hs]; rfl)

theorem ptsIntegralAt_eq {Ψ : (((k : Fin 1) → plBlocks 1 1 n k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)}
    (hΨ : IsGoodProj (grassIdeal 1 1 n) Ψ) :
    ∃ B : Matrix (PlIdx 1 n) (Fin (n + 1)) ℂ, Function.Bijective B.mulVec ∧
      ptsIntegralAt (grassIdeal 1 1 n) Ψ (fun _ z => Real.log ((fsMulti (plBlocks 1 1 n)).h z)) (fun _ => 1) =
        chartMass (Bᴴ * B) := by
  have hinj := injective_of_good hΨ
  have hrank : Module.finrank ℂ ((Fin 1 → PlIdx 1 n) → ℂ) = Module.finrank ℂ (Fin (n + 1) → ℂ) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, card_seg, Fintype.card_fin]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  set L := (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm with hL
  have hΨL : ∀ v, Ψ (L v) = v := (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).apply_symm_apply
  have hLΨ : ∀ w, L (Ψ w) = w := (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm_apply_apply
  set M := L.trans (LinearEquiv.funCongrLeft ℂ ℂ (Equiv.funUnique (Fin 1) (PlIdx 1 n))).symm with hM
  set B := LinearMap.toMatrix' M.toLinearMap with hB
  have hmv : ∀ v, B *ᵥ v = M v := fun v => LinearMap.toMatrix'_mulVec _ _
  have hMapp : ∀ v I, M v I = L v fun _ => I := fun v I => rfl
  refine ⟨B, ?_, ?_⟩
  · convert M.bijective using 1
    funext v
    exact hmv v
  have hseg : ∀ v, segre (ι := plBlocks 1 1 n) (blockLift (M v)) = L v := by
    intro v
    rw [segre_blockLift]
    funext i
    rw [hMapp, fin_one_fun_eq_const]
  have hMdiff : Differentiable ℂ fun v => M v := (LinearMap.toContinuousLinearMap M.toLinearMap).differentiable
  have hcons : Differentiable ℂ fun y' : Fin n → ℂ => (Fin.cons 1 y' : Fin (n + 1) → ℂ) := by
    rw [differentiable_pi]
    intro c
    refine Fin.cases ?_ (fun i => ?_) c
    · simp only [Fin.cons_zero]
      exact differentiable_const _
    · simp only [Fin.cons_succ]
      exact differentiable_apply i
  set γ0 : (Fin n → ℂ) → (Σ _ : Fin 1, PlIdx 1 n) → ℂ := fun y' => blockLift (M (Fin.cons 1 y')) with hγ0
  have hγ0d : ∀ y', DifferentiableAt ℂ γ0 y' := by
    intro y'
    rw [differentiableAt_pi]
    intro p
    exact ((differentiable_apply p.2).comp (hMdiff.comp hcons)) y'
  have hγ0mem : ∀ y', γ0 y' ∈ mcPts (grassIdeal 1 1 n) := by
    intro y'
    have hv : (Fin.cons 1 y' : Fin (n + 1) → ℂ) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
    obtain ⟨I, hI⟩ := Function.ne_iff.mp ((M.map_ne_zero_iff).mpr hv)
    exact (mem_mcPts _).2 fun _ => ⟨I, hI⟩
  have hpot : ∀ y', Real.log ((fsMulti (plBlocks 1 1 n)).h (γ0 y')) = hermChartPot (Bᴴ * B) y' := by
    intro y'
    set v : Fin (n + 1) → ℂ := Fin.cons 1 y'
    have h1 : (fsMulti (plBlocks 1 1 n)).h (γ0 y') = ‖WithLp.toLp 2 (B *ᵥ v)‖ := by
      rw [hmv]
      simp [fsMulti, HermLine.ofMetrics, fsMetric, hγ0, blockLift, v]
    have h2 : (star v ⬝ᵥ ((Bᴴ * B) *ᵥ v)).re = ∑ I, ‖(B *ᵥ v) I‖ ^ 2 := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
      simp [dotProduct, Complex.re_sum, Complex.conj_mul']
      norm_cast
    rw [hermChartPot, h1, h2, EuclideanSpace.norm_eq]
  unfold ptsIntegralAt chartMass
  congr 1
  funext y
  have hfib : _root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre (grassIdeal 1 1 n) Ψ y = {L (Fin.cons 1 y)} := by
    ext w
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, -, -, hw⟩
      rw [← hw, hLΨ]
    · rintro rfl
      exact ⟨γ0 y, hγ0mem y, hseg _, hΨL _⟩
  have hsheet : IsSheet (grassIdeal 1 1 n) Ψ y (L (Fin.cons 1 y)) γ0 :=
    ⟨hseg _, Eventually.of_forall fun y' => ⟨hγ0d y', hγ0mem y', by rw [hseg, hΨL]⟩⟩
  rw [hfib, finsum_mem_singleton]
  unfold sheetDensity
  split_ifs with hγ
  · have hev : (fun y' => Real.log ((fsMulti (plBlocks 1 1 n)).h (hγ.choose y'))) =ᶠ[𝓝 y]
        hermChartPot (Bᴴ * B) := by
      filter_upwards [hγ.choose_spec.2] with y' hy'
      have hs : segre (ι := plBlocks 1 1 n) (hγ.choose y') = segre (ι := plBlocks 1 1 n) (γ0 y') := by
        rw [hseg, ← hy'.2.2, hLΨ]
      have he : hγ.choose y' = γ0 y' := by
        funext p
        rw [apply_eq_segre (hγ.choose y') p, apply_eq_segre (γ0 y') p, hs]
      rw [he, hpot]
    simp only [one_mul, maDensity, cxHessian_congr hev]
  · exact absurd ⟨γ0, hsheet⟩ hγ

end GrassmannianGeometricDegreeChart


open GrassmannianGeometricDegreeChart in
theorem GrassGeomDegChart.proof : GrassGeomDegChart.Statement := by
  intro n
  have hex := exists_good n
  obtain ⟨B, hB, hval⟩ := ptsIntegralAt_eq hex.choose_spec
  refine ⟨B, hB, ?_⟩
  unfold geomDeg ptsIntegral
  rw [dite_eq_left hex]
  exact hval

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLatticeBasis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem LinesLatticeBasis.proof (V : Type) [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (ι : Type) [Fintype ι]
    (hcard : Fintype.card ι = Module.finrank ℚ V) (M : Submodule ℤ V)
    (hM : Submodule.IsFullLattice ℚ M) :
    ∃ b : Module.Basis ι ℚ V, M = Submodule.span ℤ (Set.range b) := by
  have : Module.Free ℤ M := Submodule.IsLattice.free ℚ M
  have : Module.Finite ℤ M := Submodule.IsLattice.finite ℚ M
  let b0 := Module.finBasis ℤ M
  let B := b0.extendOfIsFullLattice ℚ
  have hc : Fintype.card (Fin (Module.finrank ℤ M)) = Fintype.card ι := by
    rw [hcard, Module.finrank_eq_card_basis B]
  let e := Fintype.equivOfCardEq hc
  refine ⟨B.reindex e, ?_⟩
  rw [Module.Basis.range_reindex]
  have hB : Set.range B = M.subtype '' Set.range b0 := by
    rw [← Set.range_comp']
    exact congrArg Set.range (funext (b0.extendOfIsFullLattice_apply ℚ))
  rw [hB, ← Submodule.map_span, b0.span_eq, Submodule.map_top, Submodule.range_subtype]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLineDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix
open scoped nonZeroDivisors

noncomputable section

namespace KLinesLineDegree

variable {K : Type} [Field K] {n : ℕ}

theorem genIndex_map_of_injective {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G →+ G')
    (hf : Function.Injective f) (A B : AddSubgroup G) :
    genIndex (A.map f) (B.map f) = genIndex A B := by
  unfold genIndex
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hf,
    AddSubgroup.relIndex_map_map_of_injective _ _ hf]

end KLinesLineDegree


end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPtsIntegralZeroLowerNE
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory

noncomputable section

namespace PtsIntegralZeroLowerNEAux

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem rel_of_mk_eq {W : Ideal (MRing ι)} {a b : mcPts W}
    (h : (Quot.mk _ a : McClasses W) = Quot.mk _ b) :
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
      (b : (Σ k, ι k) → ℂ) = fun p => c p.1 * (a : (Σ k, ι k) → ℂ) p := by
  have hg := Quot.eqvGen_exact h
  clear h
  induction hg with
  | rel x y hxy => exact hxy
  | refl x => exact ⟨1, fun _ => one_ne_zero, by funext p; simp⟩
  | symm x y _ ih =>
    obtain ⟨c, hc, e⟩ := ih
    refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
    funext p
    rw [e]
    field_simp [hc p.1]
  | trans x y w _ _ ih1 ih2 =>
    obtain ⟨c, hc, e⟩ := ih1
    obtain ⟨d, hd, e'⟩ := ih2
    refine ⟨fun k => d k * c k, fun k => mul_ne_zero (hd k) (hc k), ?_⟩
    funext p
    rw [e', e]
    ring

theorem maDensity_zero (φ : Fin 0 → (Fin 0 → ℂ) → ℝ) (z : Fin 0 → ℂ) : maDensity φ z = 1 := by
  simp [maDensity, mixedDisc, Matrix.det_fin_zero]

theorem integral_fin_zero (F : (Fin 0 → ℂ) → ℝ) (y : Fin 0 → ℂ) : ∫ y', F y' = F y := by
  rw [Measure.volume_pi_eq_dirac y, integral_dirac]


omit [∀ k, Fintype (ι k)] in
theorem segre_ne_zero {W : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts W) : segre z ≠ 0 := by
  intro h0
  choose p hp using hz.1
  have h := congrFun h0 p
  simp only [segre, Pi.zero_apply] at h
  exact (Finset.prod_ne_zero_iff.mpr fun k _ => hp k) h

theorem exists_goodProj {W : Ideal (MRing ι)} (hfin : Finite (McClasses W)) :
    ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ), IsGoodProj W Ψ := by
  classical
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℂ)
    (fun q : McClasses W => segre (q.out : (Σ k, ι k) → ℂ)) (fun q => segre_ne_zero q.out.2)
  refine ⟨LinearMap.pi fun _ => f, fun z hz h => ?_⟩
  obtain ⟨c, hc, e⟩ := rel_of_mk_eq (Quot.out_eq (Quot.mk _ ⟨z, hz⟩ : McClasses W))
  have e' : z = fun p => c p.1 * ((Quot.mk _ ⟨z, hz⟩ : McClasses W).out : (Σ k, ι k) → ℂ) p := e
  have h0 := congrFun h 0
  rw [LinearMap.pi_apply, Pi.zero_apply, e', segre_smul, map_smul, smul_eq_mul] at h0
  exact hf _ ((mul_eq_zero.mp h0).resolve_left (Finset.prod_ne_zero_iff.mpr fun k _ => hc k))

theorem bij_fibre [Nonempty K] {W : Ideal (MRing ι)} (hW : IsMultiHomogIdeal W)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)) (hΨ : IsGoodProj W Ψ) (y : Fin 0 → ℂ) :
    ∃ M : McClasses W → _root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre W Ψ y, Function.Bijective M := by
  classical
  set a : ((Σ k, ι k) → ℂ) → ℂ := fun z => Ψ (segre z) 0 with ha_def
  have ha : ∀ z ∈ mcPts W, a z ≠ 0 := fun z hz h0 =>
    hΨ z hz (funext fun i => by rw [Fin.fin_one_eq_zero i]; exact h0)
  set N : ((Σ k, ι k) → ℂ) → (((k : K) → ι k) → ℂ) := fun z => (a z)⁻¹ • segre z with hN
  have hNmem : ∀ z (hz : z ∈ mcPts W), N z ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre W Ψ y := by
    intro z hz
    obtain ⟨k0⟩ := ‹Nonempty K›
    let u : K → ℂ := Pi.mulSingle k0 (a z)⁻¹
    have hu : ∀ k, u k ≠ 0 := fun k => by
      by_cases hk : k = k0
      · subst hk; simp [u, ha z hz]
      · simp [u, Pi.mulSingle_eq_of_ne hk]
    refine ⟨fun p => u p.1 * z p, mcPts_smul hW u hu hz, ?_, ?_⟩
    · rw [segre_smul]
      simp [u, N]
    · funext i
      rw [Fin.fin_one_eq_zero i]
      simp [N, a, ha z hz]
  have hNrel : ∀ z z' : mcPts W, (∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
      (z' : (Σ k, ι k) → ℂ) = fun p => c p.1 * (z : (Σ k, ι k) → ℂ) p) → N z = N z' := by
    rintro ⟨z, hz⟩ ⟨z', hz'⟩ ⟨c, hc, e⟩
    simp only at e
    subst e
    have hpc : (∏ k, c k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
    simp only [N, a, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_smul]
    congr 1
    field_simp [hpc, ha z hz]
  let M : McClasses W → _root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre W Ψ y :=
    Quot.lift (fun z => ⟨N z, hNmem z z.2⟩) (fun z z' h => Subtype.ext (hNrel z z' h))
  refine ⟨M, ?_, ?_⟩
  · intro q q'
    induction q using Quot.ind with | mk z => ?_
    induction q' using Quot.ind with | mk z' => ?_
    intro h
    have h' : N z = N z' := congrArg Subtype.val h
    have hs : segre (z : (Σ k, ι k) → ℂ) = (a z * (a z')⁻¹) • segre (z' : (Σ k, ι k) → ℂ) := by
      have := congrArg (fun v => a z • v) h'
      simp only [N, smul_smul] at this
      rw [mul_inv_cancel₀ (ha z z.2), one_smul] at this
      exact this
    obtain ⟨c, hc, e⟩ :=
      sameOrbit_of_segre z'.2.1 _ (mul_ne_zero (ha z z.2) (inv_ne_zero (ha z' z'.2))) hs
    exact (Quot.sound ⟨c, hc, e⟩).symm
  · rintro ⟨w, z, hz, rfl, hw⟩
    refine ⟨Quot.mk _ ⟨z, hz⟩, Subtype.ext ?_⟩
    show N z = segre z
    have h1 : a z = 1 := by
      show Ψ (segre z) 0 = 1
      rw [hw]
      rfl
    simp [N, h1]


omit [∀ k, Fintype (ι k)] in
theorem density_ge {W : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)}
    {φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ} {g : ((Σ k, ι k) → ℂ) → ℝ} {c : ℝ}
    (hc : ∀ z ∈ mcPts W, c ≤ g z) {y : Fin 0 → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre W Ψ y) :
    c ≤ sheetDensity W Ψ φ g y w := by
  classical
  obtain ⟨z, hz, rfl, hΨz⟩ := hw
  have hex : ∃ γ, IsSheet W Ψ y (segre z) γ :=
    ⟨fun _ => z, rfl, Filter.Eventually.of_forall fun y' =>
      ⟨differentiableAt_const _, hz, by rw [Subsingleton.elim y' y]; exact hΨz⟩⟩
  unfold sheetDensity
  rw [dite_eq_left hex, maDensity_zero, mul_one]
  exact hc _ hex.choose_spec.2.self_of_nhds.2.1

end PtsIntegralZeroLowerNEAux


open PtsIntegralZeroLowerNEAux in
theorem PtsIntegralZeroLowerNE.proof : PtsIntegralZeroLowerNE.Statement := by
  intro K _ _ ι _ W φ g c hW hfin _ hc
  classical
  obtain ⟨Ψ0, hΨ0⟩ := exists_goodProj hfin
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ), IsGoodProj W Ψ := ⟨Ψ0, hΨ0⟩
  unfold ptsIntegral
  rw [dite_eq_left hex]
  have hΨ : IsGoodProj W hex.choose := hex.choose_spec
  let y : Fin 0 → ℂ := fun i => i.elim0
  unfold ptsIntegralAt
  rw [integral_fin_zero _ y]
  obtain ⟨M, hM⟩ := bij_fibre hW hex.choose hΨ y
  have := hfin
  have : Finite (_root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre W hex.choose y) := Finite.of_surjective M hM.2
  have hF : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre W hex.choose y).Finite := Set.toFinite _
  have hcard : degC W = hF.toFinset.card := by
    rw [← Nat.card_eq_card_finite_toFinset hF, ← Nat.card_eq_of_bijective M hM]
    rfl
  rw [finsum_mem_eq_finite_toFinset_sum _ hF, hcard]
  have h := Finset.card_nsmul_le_sum hF.toFinset (fun w => sheetDensity W hex.choose φ g y w) c
    (fun w hw => density_ge hc ((Set.Finite.mem_toFinset hF).mp hw))
  rw [nsmul_eq_mul] at h
  linarith

end

end GroundTheory.Heights₂.Heights
end

