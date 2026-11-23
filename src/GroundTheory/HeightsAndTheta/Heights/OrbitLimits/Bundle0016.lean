module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0013

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreCoordGoodProj
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo

namespace SegreCoordGoodProj

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_monic_coeff_zero_ne {A R : Type*} [CommRing A] [Nontrivial A] [CommRing R] [IsDomain R]
    (f : A →+* R) {x : R} (hx : x ≠ 0) (h : f.IsIntegralElem x) :
    ∃ p : Polynomial A, p.Monic ∧ p.eval₂ f x = 0 ∧ p.coeff 0 ≠ 0 := by
  obtain ⟨p, hpm, hp⟩ := h
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases h0 : p.coeff 0 = 0
    · obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.mpr h0
      have hqm : q.Monic := Polynomial.Monic.of_mul_monic_left Polynomial.monic_X hpm
      have hq : q.eval₂ f x = 0 := by
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_X] at hp
        exact (mul_eq_zero.mp hp).resolve_left hx
      refine ih q.natDegree ?_ q hqm hq rfl
      rw [← hn, Polynomial.Monic.natDegree_mul Polynomial.monic_X hqm, Polynomial.natDegree_X]
      omega
    · exact ⟨p, hpm, hp, h0⟩

theorem evQ_segQ (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) (t : (k : K) → ι k) :
    evQ P z hz (segQ P t) = segre z t := by
  rw [segQ, evQ_mk, segMon, eval₂_prod]
  simp [segre]

omit [∀ k, Fintype (ι k)] in
theorem segre_scaleBlock (k0 : K) (c : ℂ) (z : (Σ k, ι k) → ℂ) (t : (k : K) → ι k) :
    segre (scaleBlock k0 c z) t = c * segre z t := by
  simp only [segre, scaleBlock, Finset.prod_mul_distrib]
  congr 1
  simp

theorem evQ_forms (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) {r : ℕ}
    (L : Fin r → ((k : K) → ι k) → ℚ) (j : Fin r) :
    evQ P z hz (forms (segQ P) L j) = ∑ t, (L j t : ℂ) * segre z t := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [forms, map_sum, map_rat_smul, evQ_segQ, Rat.smul_def]

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem evQ_aeval (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) {r : ℕ}
    (ℓ : Fin r → MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P) (F : MvPolynomial (Fin r) ℚ) :
    evQ P z hz (aeval ℓ F) = aeval (fun j => evQ P z hz (ℓ j)) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp => simp [hp]

theorem false_of_forms_vanish (P : Ideal (MRing ι)) (hhom : IsMultiHomogIdeal P) (k0 : K) {r : ℕ}
    (L : Fin r → ((k : K) → ι k) → ℚ) (hL : ∀ t, IntOver ℚ (forms (segQ P) L) (segQ P t))
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (hV : ∀ j, ∑ t, (L j t : ℂ) * segre z t = 0) : False := by
  choose i1 hi1 using hz.1
  have hs : segre z i1 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hi1 k
  obtain ⟨p, hpm, hp⟩ := hL i1
  let g0 : MvPolynomial (Fin r) ℚ →+* ℂ := eval₂Hom (algebraMap ℚ ℂ) 0
  have key : ∀ c : ℂ, c ≠ 0 → Polynomial.eval (c * segre z i1) (p.map g0) = 0 := by
    intro c hc
    have hzc := scaleBlock_mem_zeroLocus P hhom k0 hc hz
    have hcomp : (evQ P _ hzc).comp
        ((aeval (forms (segQ P) L) : MvPolynomial (Fin r) ℚ →ₐ[ℚ] _) : MvPolynomial (Fin r) ℚ →+* _) =
        g0 := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [g0]
      · intro j
        have h1 : ∑ t, (L j t : ℂ) * (c * segre z t) = c * ∑ t, (L j t : ℂ) * segre z t := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by ring
        simp [g0, evQ_forms, segre_scaleBlock, h1, hV j]
    have := congrArg (evQ P _ hzc) hp
    rw [Polynomial.hom_eval₂, hcomp, evQ_segQ, segre_scaleBlock, map_zero] at this
    rw [Polynomial.eval_map]
    exact this
  have hinf : {x : ℂ | (p.map g0).IsRoot x}.Infinite := by
    refine Set.Infinite.mono ?_ (Set.finite_singleton (0 : ℂ)).infinite_compl
    intro x hx
    have hx0 : x ≠ 0 := hx
    have := key (x / segre z i1) (div_ne_zero hx0 hs)
    rw [div_mul_cancel₀ x hs] at this
    exact this
  exact (hpm.map g0).ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ hinf)

end SegreCoordGoodProj

theorem SegreCoordGoodProj.proof : SegreCoordGoodProj.Statement := by
  intro K _ ι _ P e i hP ⟨z0, hz0, hz0i⟩
  classical
  obtain ⟨r, hr, L, hL⟩ := exists_linear_normalization (k := ℚ) (segQ P) (e + 1)
    (fun r L hr => forms_not_algebraicIndependent P e hP hr L)
  obtain ⟨⟨k0⟩, ⟨hprime, hhom, -⟩, hH, -⟩ := hP
  have := isDomain_qQuot P hprime hH
  cases r with
  | zero => exact (SegreCoordGoodProj.false_of_forms_vanish P hhom k0 L hL hz0 fun j => j.elim0).elim
  | succ r' =>
  have hw : segQ P i ≠ 0 := fun h =>
    hz0i (by rw [← SegreCoordGoodProj.evQ_segQ P z0 hz0, h, map_zero])
  obtain ⟨p, hpm, hp, hc0⟩ := SegreCoordGoodProj.exists_monic_coeff_zero_ne _ hw (hL i)
  set c0 := p.coeff 0 with hc0def
  have hsupp : ∀ m ∈ (homogeneousComponent c0.totalDegree c0).support,
      Finsupp.degree m = c0.totalDegree := by
    intro m hm
    rw [mem_support_iff, coeff_homogeneousComponent] at hm
    by_contra hne
    exact hm (if_neg hne)
  obtain ⟨lam, hlam⟩ := exists_eval_cons_one_ne_zero _ _ hsupp
    (homogeneousComponent_totalDegree_ne_zero hc0)
  let Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
    { toFun := fun w j => Fin.cases (w i) (fun j' : Fin e => if h : (j' : ℕ) < r' then
          ∑ t, ((L (Fin.succ ⟨j', h⟩) t - lam ⟨j', h⟩ * L 0 t : ℚ) : ℂ) * w t else 0) j
      map_add' := by
        intro w w'
        funext j
        refine Fin.cases ?_ (fun j' => ?_) j
        · simp
        · simp only [Fin.cases_succ, Pi.add_apply]
          split_ifs <;> simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c w
        funext j
        refine Fin.cases ?_ (fun j' => ?_) j
        · simp
        · simp only [Fin.cases_succ, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          split_ifs <;> simp [Finset.mul_sum, mul_left_comm] }
  refine ⟨Ψ, fun z hz hΨ => ?_, fun w => rfl⟩
  set V : Fin (r' + 1) → ℂ := fun j => ∑ t, (L j t : ℂ) * segre z t with hVdef
  have hzi : segre z i = 0 := congrFun hΨ 0
  have hVs : ∀ j : Fin r', V j.succ = lam j * V 0 := by
    intro j
    have h := congrFun hΨ (Fin.succ ⟨j, by omega⟩)
    simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, Fin.cases_succ, dif_pos j.2, Fin.eta,
      Pi.zero_apply] at h
    simp only [hVdef]
    rw [← sub_eq_zero, Finset.mul_sum, ← Finset.sum_sub_distrib, ← h]
    refine Finset.sum_congr rfl fun t _ => ?_
    push_cast
    ring
  by_cases hs : V 0 = 0
  · refine SegreCoordGoodProj.false_of_forms_vanish P hhom k0 L hL hz fun j => ?_
    refine Fin.cases hs (fun j => ?_) j
    exact (hVs j).trans (by rw [hs, mul_zero])
  let g : Polynomial ℂ := (subst lam c0).map
    ((aeval (0 : Fin r' → ℂ) : MvPolynomial (Fin r') ℚ →ₐ[ℚ] ℂ) : MvPolynomial (Fin r') ℚ →+* ℂ)
  have hgD : g.coeff c0.totalDegree ≠ 0 := by
    simp only [g, Polynomial.coeff_map, subst_coeff_totalDegree]
    simpa using hlam
  have hroot : ∀ x : ℂ, x ≠ 0 → g.eval x = 0 := by
    intro x hx
    have hc : x / V 0 ≠ 0 := div_ne_zero hx hs
    have hzc := scaleBlock_mem_zeroLocus P hhom k0 hc hz
    set u : Fin (r' + 1) → ℂ := fun j => x / V 0 * V j with hudef
    have hu0 : u 0 = x := div_mul_cancel₀ x hs
    have hu' : (fun j : Fin r' => u j.succ - lam j • u 0) = 0 := by
      funext j
      simp only [hudef, hVs j, Rat.smul_def, Pi.zero_apply]
      ring
    have h1 : aeval u c0 = 0 := by
      have := congrArg (evQ P _ hzc) hp
      rw [Polynomial.hom_eval₂, SegreCoordGoodProj.evQ_segQ, SegreCoordGoodProj.segre_scaleBlock, hzi,
        mul_zero, Polynomial.eval₂_at_zero, RingHom.comp_apply] at this
      rw [map_zero (evQ P _ hzc)] at this
      change evQ P _ hzc (aeval (forms (segQ P) L) c0) = 0 at this
      rw [← this, SegreCoordGoodProj.evQ_aeval]
      refine congrArg (fun v => aeval v c0) (funext fun j => ?_)
      rw [SegreCoordGoodProj.evQ_forms]
      simp only [SegreCoordGoodProj.segre_scaleBlock, hudef, hVdef, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    have h2 := eval₂_subst lam u c0
    rw [hu', hu0, h1] at h2
    rw [Polynomial.eval_map]
    exact h2
  have hg0 : g = 0 := Polynomial.eq_zero_of_infinite_isRoot g
    (Set.Infinite.mono (fun x hx => hroot x hx) (Set.finite_singleton (0 : ℂ)).infinite_compl)
  exact hgD (by rw [hg0, Polynomial.coeff_zero])

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PoincareLelongLimit
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def PoincareLelongLimit.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    B.a = 0 → IsSectionOn P A s →
    Tendsto (fun ε => ptsIntegral P (Fin.cons (regLog A s ε) (pot L)) (fun z => Real.log (B.h z)))
      (𝓝[>] 0)
      (𝓝 ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
          (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z))) -
        ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (fun z => Real.log (B.h z))))

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PoincareLelongRegularised
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def PoincareLelongRegularised.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    B.a = 0 → IsSectionOn P A s →
    Tendsto (fun ε => ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L)) (regLog A s ε))
      (𝓝[>] 0) (𝓝 (ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L)) (logNorm A s)))

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm pot segre)
open ComplexSets Matrix

section Proj

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]


open Classical in
def chartProjMatrix {m d : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ)) : Matrix (Fin d) (Fin m) ℂ :=
  fun r a => Ψ (fun i' => if σ a = i' then 1 else 0) r.succ

theorem chartProjMatrix_mulVec {m d : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ)) (x : Fin m → ℂ) (r : Fin d) :
    (chartProjMatrix σ Ψ *ᵥ x) r = Ψ (fun i' => x (σ.symm i')) r.succ := by
  classical
  have hv : (fun i' => x (σ.symm i')) = ∑ a, x a • fun i' => if σ a = i' then (1 : ℂ) else 0 := by
    rw [pi_eq_sum_univ (fun i' => x (σ.symm i'))]
    exact (Equiv.sum_comp σ _).symm.trans (by simp)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hv, map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, chartProjMatrix]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]

end Proj

section Chart

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def chartLiftDom {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) : Set (Fin m → ℂ) :=
  {x | ∀ k, ∃ j, chartLift σ i x ⟨k, j⟩ ≠ 0}

theorem isOpen_chartLiftDom {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    IsOpen (chartLiftDom σ i) :=
  ReciprocityTheory.ChartRestriction.G.Geo.isOpen_blockNonzero.preimage (contDiff_chartLift σ i (n := 0)).continuous

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_chartLiftDom_of_coord {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    {x : Fin m → ℂ} (hx : x (σ.symm i) = 1) : x ∈ chartLiftDom σ i :=
  chartLift_blockNonzero σ i hx


open Classical in
def chartWeight {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : (Fin m → ℂ) → ℝ :=
  (chartLiftDom σ i).piecewise (g ∘ chartLift σ i) 0

def chartPot {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) :
    Fin e → (Fin m → ℂ) → ℝ :=
  fun j => pot L j ∘ chartLift σ i

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem chartWeight_of_mem {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    (g : ((Σ k, ι k) → ℂ) → ℝ) {x : Fin m → ℂ} (hx : x ∈ chartLiftDom σ i) :
    chartWeight σ i g x = g (chartLift σ i x) := by
  classical
  simp only [chartWeight]
  rw [Set.piecewise_eq_of_mem _ _ _ hx]
  rfl


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem chartWeight_of_coord {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    (g : ((Σ k, ι k) → ℂ) → ℝ) {x : Fin m → ℂ} (hx : x (σ.symm i) = 1) :
    chartWeight σ i g x = g (chartLift σ i x) :=
  chartWeight_of_mem g (mem_chartLiftDom_of_coord hx)

theorem measurable_chartWeight {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) : Measurable (chartWeight σ i g) := by
  classical
  have hc : ContinuousOn (g ∘ chartLift σ i) (chartLiftDom σ i) :=
    hg.1.continuousOn.comp (contDiff_chartLift σ i (n := 0)).continuous.continuousOn fun _ hx => hx
  unfold chartWeight
  exact hc.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) (isOpen_chartLiftDom σ i).measurableSet

theorem smoothNear_chartPot {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    {L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {T : Set (Fin m → ℂ)}
    (hT : ∀ x ∈ T, x (σ.symm i) = 1) (j : Fin e) : SmoothNear T (chartPot σ i L j) := by
  refine ⟨chartLiftDom σ i, isOpen_chartLiftDom σ i, fun x hx => mem_chartLiftDom_of_coord (hT x hx), ?_⟩
  have hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (L j).h (chartLift σ i x)) (chartLiftDom σ i) :=
    (hL j).comp (contDiff_chartLift σ i).contDiffOn fun _ hx => hx
  exact hh.log fun x hx => ((L j).pos _ hx).ne'

end Chart

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartSection
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn PBlk fsLine Xc)

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def chartSection {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (s : MRing ι) :
    MvPolynomial (Fin m) ℂ :=
  bind₁ (fun p : Σ k, ι k => (X (σ.symm (Function.update i p.1 p.2)) : MvPolynomial (Fin m) ℂ))
    (map (Int.castRingHom ℂ) s)


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem eval_chartSection {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (s : MRing ι)
    (x : Fin m → ℂ) :
    eval x (chartSection σ i s) = eval (chartLift σ i x) (map (Int.castRingHom ℂ) s) := by
  show eval₂Hom (RingHom.id ℂ) x _ = _
  rw [chartSection, eval₂Hom_bind₁]
  simp only [eval₂Hom_X']
  rfl

def ChartSectionNotMem.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι),
    IsArithVar P (e + 1) → IsSectionOn P A s → ∀ J ∈ segreChartComponents P σ i, chartSection σ i s ∉ J

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsIntegralProjIndep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj ptsIntegralAt pot PBlk oneLine
  isSmoothHerm_oneLine)

def PtsIntegralProjIndep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → IsGoodProj P Ψ' → (∀ j, IsSmoothHerm (L j)) →
    IsDegZeroSmooth g → ptsIntegralAt P Ψ (pot L) g = ptsIntegralAt P Ψ' (pot L) g

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsIntegralSegreChartProj
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj ptsIntegralAt pot segre PBlk oneLine
  isSmoothHerm_oneLine)

def PtsIntegralSegreChartProj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin (e + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1 + 1) → ℂ))
    (G : (Fin m → ℂ) → ℝ) (Φ : Fin (e + 1) → (Fin m → ℂ) → ℝ),
    IsArithVar P (e + 2) → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth g →
    IsGoodProj P Ψ → (∀ w, Ψ w 0 = w i) →
    (∀ x ∈ segreChartSet P σ i,
      G =ᶠ[𝓝 x] g ∘ chartLift σ i ∧ ∀ j, Φ j =ᶠ[𝓝 x] pot L j ∘ chartLift σ i) →
      ptsIntegralAt P Ψ (pot L) g = ∑ J ∈ segreChartComponents P σ i, varInt J (e + 1) G Φ

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsPosPartProjIndep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj sheetDensity fibre pot PBlk oneLine
  isSmoothHerm_oneLine)

def ptsPosDens {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ} (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ) : ℝ :=
  ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, max (sheetDensity P Ψ φ g y w) 0

def PtsPosPartProjIndep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → IsGoodProj P Ψ' → (∀ j, IsSmoothHerm (L j)) →
    Measurable g → (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
      ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) g y) = ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ' (pot L) g y)

end GroundTheory.Heights₂.Heights
end
end

