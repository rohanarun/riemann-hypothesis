module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0159
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0157
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierDescendedFunctionEqPartialFourier
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.FourDesc

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem continuous_of_isStdChar {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : Continuous (fun x => ψ x) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have h : ∀ᶠ z in 𝓝 x, ψ x = ψ z := by
    filter_upwards [Metric.closedBall_mem_nhds x one_pos] with z hz
    have hz' : ‖z - x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have e : z = x + (z - x) := by abel
    rw [e, AddChar.map_add_eq_mul, hψ.1 (z - x) hz', mul_one]
  exact continuousAt_const.congr h

theorem continuous_star_E [Unram F E] : Continuous (star : E → E) :=
  (Isometry.of_dist_eq fun a b => by
    rw [dist_eq_norm, dist_eq_norm, ← star_sub, Unram.norm_star (F := F)]).continuous

end GlobalTheory.JR.FourDesc

set_option synthInstance.maxHeartbeats 200000 in
open GlobalTheory.JR.FourDesc in
theorem GlobalTheory.JR.fourB_descFn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → ∀ (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → fourB μ (A.kerL ψ x) (A.descFn M Ax j lam α f) = A.descFn M Ax j lam α (fourU M ψ f) := by
  intro F E _ _ _ _ _ A ψ hψ r M x j hx μ hμ Ax lam α hα hαc f hf
  haveI : LocallyCompactSpace E := Unram.lcE (F := F) (E := E)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : LocallyCompactSpace F := Unram.lcF (F := F) (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  letI := M.mE
  haveI := M.bE
  letI := M.mU
  haveI := M.bU
  haveI := M.haarE
  haveI := M.haarU
  haveI : SigmaFinite M.μE := sigmaFinite_of_locallyFinite
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ (Unram.finrank_eq (F := F) (E := E))
  haveI : ContinuousStar E := ⟨continuous_star_E (F := F)⟩
  obtain ⟨P, hP⟩ : ∃ P : Measure (Fin r → E), P = Measure.pi fun _ => M.μE := ⟨_, rfl⟩
  haveI : SigmaFinite P := by rw [hP]; infer_instance
  haveI : IsFiniteMeasureOnCompacts P := by rw [hP]; infer_instance
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (Matrix.unitaryGroup (Fin r) E), ν = M.μU.restrict (tsupport α) := ⟨_, rfl⟩
  haveI : IsFiniteMeasure ν := by
    rw [hν]; exact isFiniteMeasure_restrict.2 hαc.isCompact.measure_lt_top.ne
  have : IsFiniteMeasureOnCompacts ν := ⟨fun _ _ => measure_lt_top ν _⟩
  have : SigmaFinite ν := IsFiniteMeasure.toSigmaFinite ν
  have : SecondCountableTopologyEither (Fin r → E) (Matrix.unitaryGroup (Fin r) E) :=
    secondCountableTopologyEither_of_left _ _
  haveI : IsFiniteMeasureOnCompacts (P.prod ν) := inferInstance
  have hψc := continuous_of_isStdChar hψ
  have htr : Continuous (fun e : E => Algebra.trace F E e) :=
    LinearMap.continuous_of_finiteDimensional (Algebra.trace F E)
  have hfc : Continuous f := hf.1.continuous
  have hαcont : Continuous α := hα.continuous
  have hstar : ∀ (g : Matrix.unitaryGroup (Fin r) E) (v w : Fin r → E),
      star (g.1 *ᵥ v) ⬝ᵥ (g.1 *ᵥ w) = star v ⬝ᵥ w := by
    intro g v w
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
      Unitary.star_mul_self_of_mem g.2, Matrix.one_mulVec]
  let jg : Matrix.unitaryGroup (Fin r) E → (A.L ≃ₗ[E] (Fin r → E)) :=
    fun g => j.trans (Matrix.UnitaryGroup.toLinearEquiv g)
  have hjg : ∀ g y, jg g y = g.1 *ᵥ j y := fun g y => rfl
  have hjgI : ∀ g, A.IsIsom x (jg g) := fun g y y' => by rw [hjg, hjg, hstar, hx]
  have I := GlobalTheory.T.map_isIsom_selfDualMeasure_kerL_eq_pi_haar F E A ψ hψ r M x
  have hker : ∀ y' y, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y)) := (I j hx).1
  have hmapj : Measure.map j μ = P := by rw [hP]; exact (I j hx).2 μ hμ
  have hmapg : ∀ g, Measure.map (jg g) μ = P := fun g => by rw [hP]; exact (I (jg g) (hjgI g)).2 μ hμ
  have hjc : Continuous j :=
    IsModuleTopology.continuous_of_linearMap (R := F) ((j : A.L →ₗ[E] (Fin r → E)).restrictScalars F)
  have hjm : Measurable j := hjc.measurable
  have hgc : ∀ g : Matrix.unitaryGroup (Fin r) E, Continuous (fun v : Fin r → E => g.1 *ᵥ v) :=
    fun g => continuous_const.matrix_mulVec continuous_id
  have hPg : ∀ g : Matrix.unitaryGroup (Fin r) E, Measure.map (fun v => g.1 *ᵥ v) P = P := by
    intro g
    have e : (fun v => g.1 *ᵥ v) ∘ j = ⇑(jg g) := funext fun y => (hjg g y).symm
    conv_lhs => rw [← hmapj]
    rw [Measure.map_map (hgc g).measurable hjm, e, hmapg g]
  have hres : ∀ h : Matrix.unitaryGroup (Fin r) E → ℂ, (∀ g, g ∉ tsupport α → h g = 0) →
      ∫ g, h g ∂ν = ∫ g, h g ∂M.μU := by
    intro h hh
    rw [hν]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hh
  funext y
  let G : (Fin r → E) → Matrix.unitaryGroup (Fin r) E → ℂ := fun v g =>
    f (actU g (Ax, v, lam)) * (α g : ℂ) * ψ (Algebra.trace F E (star v ⬝ᵥ j y))
  have hact : Continuous (fun p : (Fin r → E) × Matrix.unitaryGroup (Fin r) E => actU p.2 (Ax, p.1, lam)) := by
    unfold actU
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.prodMk ?_ continuous_const)
    · fun_prop
    · fun_prop
  have hGc : Continuous (Function.uncurry G) := by
    have h1 : Continuous (fun p : (Fin r → E) × Matrix.unitaryGroup (Fin r) E => star p.1 ⬝ᵥ j y) := by fun_prop
    exact ((hfc.comp hact).mul (Complex.continuous_ofReal.comp (hαcont.comp continuous_snd))).mul
      (hψc.comp (htr.comp h1))
  have hGs : HasCompactSupport (Function.uncurry G) := by
    refine HasCompactSupport.intro (((hf.2.isCompact.prod hαc.isCompact).image
      (f := fun q : Hn r F E × Matrix.unitaryGroup (Fin r) E => (star q.2.1 *ᵥ q.1.2.1, q.2)) (by fun_prop))) ?_
    rintro ⟨v, g⟩ hvg
    by_contra hne
    apply hvg
    have h1 : f (actU g (Ax, v, lam)) ≠ 0 := fun h => hne (by simp [G, h])
    have h2 : α g ≠ 0 := fun h => hne (by simp [G, h])
    refine ⟨(actU g (Ax, v, lam), g), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, ?_⟩
    simp only [actU, Prod.mk.injEq, and_true]
    rw [Matrix.mulVec_mulVec, Unitary.star_mul_self_of_mem g.2, Matrix.one_mulVec]
  have hGi : Integrable (Function.uncurry G) (P.prod ν) := hGc.integrable_of_hasCompactSupport hGs
  have hL : fourB μ (A.kerL ψ x) (A.descFn M Ax j lam α f) y = ∫ v, ∫ g, G v g ∂ν ∂P := by
    have e : ∀ y', A.descFn M Ax j lam α f y' * A.kerL ψ x y' y = (fun v => ∫ g, G v g ∂ν) (j y') := by
      intro y'
      simp only [Et.descFn, hker, G]
      rw [← hres _ (fun g hg => by simp [image_eq_zero_of_notMem_tsupport hg]), ← integral_mul_const]
    simp only [fourB, e]
    rw [← hmapj, integral_map hjm.aemeasurable (by
      rw [hmapj]; exact (hGc.stronglyMeasurable.integral_prod_right (ν := ν)).aestronglyMeasurable)]
  rw [hL, integral_integral_swap hGi]
  simp only [Et.descFn]
  rw [← hres _ (fun g hg => by simp [image_eq_zero_of_notMem_tsupport hg])]
  congr 1
  funext g
  have e1 : ∀ v, G v g = (f ((actU g (Ax, j y, lam)).1, g.1 *ᵥ v, lam) *
      ψ (Algebra.trace F E (star (g.1 *ᵥ v) ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) * (α g : ℂ) := by
    intro v
    simp only [G, actU, hstar]
    ring
  simp_rw [e1]
  rw [integral_mul_const]
  congr 1
  have hHc : Continuous (fun c : Fin r → E => f ((actU g (Ax, j y, lam)).1, c, lam) *
      ψ (Algebra.trace F E (star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) := by
    have h1 : Continuous (fun c : Fin r → E => star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1) := by fun_prop
    have h2 : Continuous (fun c : Fin r → E => ((actU g (Ax, j y, lam)).1, c, lam)) := by fun_prop
    exact (hfc.comp h2).mul (hψc.comp (htr.comp h1))
  have key : ∫ c, (fun c : Fin r → E => f ((actU g (Ax, j y, lam)).1, c, lam) *
      ψ (Algebra.trace F E (star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) c ∂(Measure.map (fun v => g.1 *ᵥ v) P) =
      ∫ v, (fun c : Fin r → E => f ((actU g (Ax, j y, lam)).1, c, lam) *
      ψ (Algebra.trace F E (star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) (g.1 *ᵥ v) ∂P :=
    integral_map (hgc g).measurable.aemeasurable (by rw [hPg g]; exact hHc.aestronglyMeasurable)
  rw [hPg g] at key
  rw [key.symm]
  simp only [fourU]
  rw [hP]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModUniformiserCocyclesFiniteClassesLocal
section
open ReciprocityTheory.Gal

namespace GlobalTheory

theorem modpi_cocycles_finite_classes : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}, FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [CompactSpace M] {G : Type} [Group G] [TopologicalSpace G] (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) (ρ : Representation O G M), ContAction ρ → ∀ (ϖ : O), (p : O) ∈ Ideal.span {ϖ} → IsOpen (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) → ∃ s : Finset (Z1 ρ), ∀ c : Z1 ρ, ∃ i ∈ s, ∃ x : M, ∀ g, (c : G → M) g - (i : G → M) g - (ρ g x - x) ∈ LinearMap.range (LinearMap.lsmul O M ϖ) := by
  classical
  intro hT p _ K hK O _ M _ _ _ _ _ _ G _ _ e ρ hρ ϖ hp hN
  set N : Submodule O M := LinearMap.range (LinearMap.lsmul O M ϖ) with hNdef
  have hmemN : ∀ m : M, ϖ • m ∈ N := fun m => ⟨m, rfl⟩
  have hstab : ∀ g : G, N ≤ N.comap (ρ g) := by
    rintro g _ ⟨m, rfl⟩
    show ρ g (ϖ • m) ∈ N
    rw [map_smul]; exact hmemN _
  haveI hdisc : DiscreteTopology (M ⧸ N) :=
    QuotientAddGroup.discreteTopology (N := N.toAddSubgroup) hN
  haveI : CompactSpace (M ⧸ N) :=
    (Submodule.Quotient.mk_surjective N).compactSpace (Submodule.isOpenQuotientMap_mkQ N).continuous
  haveI : Finite (M ⧸ N) := finite_of_compact_of_discrete
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hp
  obtain ⟨k, hk1⟩ : ∃ k : ℕ, k = 1 := ⟨1, rfl⟩
  have hkill : ∀ q : M ⧸ N, (p ^ k : ℕ) • q = 0 := by
    intro q
    subst hk1
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N q
    rw [pow_one, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have : (p • m : M) = ϖ • (r • m) := by
      rw [← Nat.cast_smul_eq_nsmul O, ← hr, smul_smul, mul_comm]
    rw [this]; exact hmemN _
  haveI : Module (ZMod (p ^ k)) (M ⧸ N) := AddCommGroup.zmodModule (n := p ^ k) hkill
  haveI : ContinuousConstSMul (ZMod (p ^ k)) (M ⧸ N) := ⟨fun _ => continuous_of_discreteTopology⟩
  let f : Formalism.GaloisCohomology.GK p K → Module.End (ZMod (p ^ k)) (M ⧸ N) := fun h =>
    (N.mapQ N (ρ (e.symm h)) (hstab _)).toAddMonoidHom.toZModLinearMap (p ^ k)
  have hf1 : f 1 = 1 := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N q
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    simp
  have hfm : ∀ a b, f (a * b) = f a * f b := by
    intro a b; refine LinearMap.ext fun q => ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N q
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    simp
  let ρ' : Representation (ZMod (p ^ k)) (Formalism.GaloisCohomology.GK p K) (M ⧸ N) := MonoidHom.mk (OneHom.mk f hf1) hfm
  have hρ'mk : ∀ h m, ρ' h (Submodule.Quotient.mk m) = Submodule.Quotient.mk (ρ (e.symm h) m) := fun h m => rfl
  have hρ' : ContAction ρ' := by
    have hq : Topology.IsQuotientMap (Prod.map (id : Formalism.GaloisCohomology.GK p K → Formalism.GaloisCohomology.GK p K) (N.mkQ)) :=
      (IsOpenQuotientMap.id.prodMap (Submodule.isOpenQuotientMap_mkQ N)).isQuotientMap
    show Continuous _
    rw [hq.continuous_iff]
    have : ((fun x : Formalism.GaloisCohomology.GK p K × (M ⧸ N) => ρ' x.1 x.2) ∘ Prod.map id N.mkQ)
        = fun x => Submodule.Quotient.mk (p := N) (ρ (e.symm x.1) x.2) := by
      funext x; rfl
    rw [this]
    exact (Submodule.isOpenQuotientMap_mkQ N).continuous.comp
      (hρ.comp ((e.symm.continuous.comp continuous_fst).prodMk continuous_snd))
  have hfin := (GlobalTheory.finite_H1_H2_of_localTateDuality hT p K hK k (M ⧸ N) ρ' (by omega) hρ').1
  let cb : Z1 ρ → (Formalism.GaloisCohomology.GK p K → M ⧸ N) := fun c h => Submodule.Quotient.mk ((c : G → M) (e.symm h))
  have hcb : ∀ c, cb c ∈ Z1 ρ' := by
    intro c
    refine ⟨(Submodule.isOpenQuotientMap_mkQ N).continuous.comp (c.2.1.comp e.symm.continuous), ?_⟩
    intro a b
    simp only [cb, map_mul, c.2.2, Submodule.Quotient.mk_add, hρ'mk]
  let κ : Z1 ρ → H1 ρ' := fun c => Submodule.Quotient.mk ⟨cb c, hcb c⟩
  haveI := Fintype.ofFinite (H1 ρ')
  let pick : H1 ρ' → Z1 ρ := fun y => if hy : ∃ c, κ c = y then hy.choose else 0
  refine ⟨Finset.univ.image pick, fun c => ?_⟩
  have hex : ∃ c', κ c' = κ c := ⟨c, rfl⟩
  have hpick : pick (κ c) = hex.choose := dif_pos hex
  refine ⟨pick (κ c), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  set c₀ := pick (κ c)
  have heq : κ c₀ = κ c := by rw [hpick]; exact hex.choose_spec
  have hB := (Submodule.Quotient.eq _).mp heq.symm
  rw [Submodule.mem_comap] at hB
  obtain ⟨q, hq⟩ := (mem_coboundaries1 ρ' _).mp hB
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
  refine ⟨x, fun g => ?_⟩
  have := hq (e g)
  simp only [Submodule.coe_subtype, Submodule.coe_sub, Pi.sub_apply, cb, hρ'mk,
    MulEquiv.symm_apply_apply, ContinuousMulEquiv.symm_apply_apply] at this
  rw [← Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.Quotient.mk_sub]
  rw [this]; abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMemCyclotomicLayerPrimeRpow
section
noncomputable section

namespace GlobalTheory.Cyc

open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open scoped IntermediateField

variable {l : ℕ} [Fact l.Prime]

theorem norm_aeval_of_norm_eq (K : FinExt l) (N : ℕ) (π : Om l)
    (hπ : ‖π‖ = (l : ℝ) ^ (-(1 : ℝ) / (N : ℝ))) (p : (↥(K0 K))[X]) (hp : p ≠ 0)
    (hd : p.natDegree < N) : ∃ n : ℤ, ‖aeval π p‖ = (l : ℝ) ^ ((n : ℝ) / (N : ℝ)) := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_le _).trans_lt hd
  have key : ∀ i ∈ p.support, ∃ n : ℤ,
      ‖p.coeff i • π ^ i‖ = (l : ℝ) ^ ((n : ℝ) - (i : ℝ) / N) := by
    intro i hi
    have h0 : ((p.coeff i : ↥(K0 K)) : Om l) ≠ 0 := by
      have := mem_support_iff.1 hi
      exact fun h => this (Subtype.ext h)
    obtain ⟨n, hn⟩ := GlobalTheory.UnramValue.norm_of_mem_unramified_subfield l K _ (p.coeff i).2 h0
    refine ⟨n, ?_⟩
    change ‖((p.coeff i : ↥(K0 K)) : Om l) * π ^ i‖ = _
    rw [norm_mul, norm_pow, hn, hπ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le,
      ← Real.rpow_intCast, ← Real.rpow_add hl0]
    congr 1
    ring
  have hpw : Set.Pairwise (p.support : Set ℕ)
      (fun i k => ‖p.coeff i • π ^ i‖₊ ≠ ‖p.coeff k • π ^ k‖₊) := by
    intro i hi k hk hik h
    obtain ⟨n, hn⟩ := key i hi
    obtain ⟨m, hm⟩ := key k hk
    have h' : ‖p.coeff i • π ^ i‖ = ‖p.coeff k • π ^ k‖ := congrArg NNReal.toReal h
    rw [hn, hm] at h'
    have h2 := (Real.rpow_right_inj hl0 hl1.ne').1 h'
    have h3 : ((n - m) * N : ℝ) = i - k := by
      field_simp at h2
      linarith
    have h4 : ((n - m) * N : ℤ) = i - k := by exact_mod_cast h3
    have hi' : i < N := (le_natDegree_of_mem_supp i hi).trans_lt hd
    have hk' : k < N := (le_natDegree_of_mem_supp k hk).trans_lt hd
    have h5 : (i : ℤ) - k = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd (m := N) ⟨n - m, by rw [← h4]; ring⟩
      rw [abs_lt]; constructor <;> omega
    omega
  have hs : ∑ i ∈ p.support, p.coeff i • π ^ i = aeval π p := by
    rw [aeval_eq_sum_range' (Nat.lt_succ_self _)]
    apply Finset.sum_subset supp_subset_range_natDegree_succ
    intro i _ hi
    rw [notMem_support_iff.1 hi, zero_smul]
  have h6 := IsUltrametricDist.nnnorm_sum_eq_sup_of_pairwise_ne hpw
  rw [hs] at h6
  obtain ⟨i, hi, hi'⟩ := Finset.exists_mem_eq_sup p.support (support_nonempty.2 hp)
    (fun i => ‖p.coeff i • π ^ i‖₊)
  obtain ⟨n, hn⟩ := key i hi
  refine ⟨n * N - i, ?_⟩
  have h7 : ‖aeval π p‖ = ‖p.coeff i • π ^ i‖ := congrArg NNReal.toReal (h6.trans hi')
  rw [h7, hn]
  congr 1
  push_cast
  field_simp

theorem norm_of_mem_Ks : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (j : ℕ), 1 ≤ j →
    ∀ x : Om l, x ∈ Ks K j → x ≠ 0 →
      ∃ n : ℤ, ‖x‖ = (l : ℝ) ^ ((n : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) := by
  intro l _ K j hj x hx hx0
  have hlp : l.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_Om (l := l) j
  have hint : IsIntegral ↥(K0 K) ζ := Algebra.IsIntegral.isIntegral ζ
  rw [Ks_eq_restrictScalars K j ζ hζ, IntermediateField.mem_restrictScalars] at hx
  have hx' : x ∈ Algebra.adjoin ↥(K0 K) {ζ} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hx
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx'
  obtain ⟨q, hq⟩ := hx'
  have hcast : ((Nat.totient (l ^ j) : ℕ) : ℝ) = (l : ℝ) ^ (j - 1) * ((l : ℝ) - 1) := by
    rw [Nat.totient_prime_pow hlp hj]
    push_cast [Nat.cast_sub hlp.one_le]
    rfl
  have hnorm : ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((Nat.totient (l ^ j) : ℕ) : ℝ)) := by
    have h1 := norm_primitiveRoot_sub_one l j hj (ζ : PadicComplex l)
      (hζ.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _))
    rw [hcast, ← h1, ← PadicComplex.norm_extends]
    congr 1
    exact (map_sub (algebraMap (Om l) (PadicComplex l)) ζ 1).trans (by rw [map_one]; rfl)
  set r := q %ₘ minpoly ↥(K0 K) ζ with hr
  have hrx : aeval ζ r = x := by
    rw [hr, aeval_modByMonic_eq_self_of_root (minpoly.aeval _ _)]
    exact hq
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, map_zero] at hrx
    exact hx0 hrx.symm
  have hdeg : r.natDegree < Nat.totient (l ^ j) := by
    have := natDegree_lt_natDegree hr0 (degree_modByMonic_lt q (minpoly.monic hint))
    rwa [minpoly_unramifiedSubfield_eq_cyclotomic K j hj ζ hζ, natDegree_cyclotomic] at this
  obtain ⟨n, hn⟩ := norm_aeval_of_norm_eq K _ (ζ - 1) hnorm (taylor 1 r)
    (fun h => hr0 (taylor_injective 1 (by rw [h, map_zero]))) (by rwa [natDegree_taylor])
  refine ⟨n, ?_⟩
  rw [← hcast, ← hn, ← hrx, taylor_apply, aeval_comp]
  simp

end GlobalTheory.Cyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomTiltMapTiltFrobeniusIntegerPower
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem map_pw_eq_pw (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] [CharP F l] [PerfectRing F l]
    (ι : Fl l →+* F) (k : ℤ) (x : Fl l) : ι (GlobalTheory.PSer.pw k x) = GlobalTheory.PMonE.pw l k (ι x) := by
  have hsymm : ∀ y : Fl l, ι ((frobeniusEquiv (Fl l) l).symm y) = (frobeniusEquiv F l).symm (ι y) :=
    fun y => RingHom.map_frobeniusEquiv_symm l ι y
  have hit : ∀ (n : ℕ) (y : Fl l), ι (((frobeniusEquiv (Fl l) l).symm)^[n] y) = ((frobeniusEquiv F l).symm)^[n] (ι y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih => intro y; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hsymm, ih]
  have hpos : ∀ (n : ℕ) (y : Fl l), ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ n) y = y ^ l ^ n := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ']
      change (frobeniusEquiv (Fl l) l) (((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ n) y) = _
      rw [ih, frobeniusEquiv_apply, frobenius_def, ← pow_mul, pow_succ]
  have hneg : ∀ (n : ℕ) (y : Fl l), ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ (-(n : ℤ))) y
      = ((frobeniusEquiv (Fl l) l).symm)^[n] y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [Nat.cast_succ, neg_add, zpow_add, Function.iterate_succ_apply]
      change ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ (-(n : ℤ)))
        (((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ (-1 : ℤ)) y) = _
      rw [ih, zpow_neg_one]
      rfl
  cases k with
  | ofNat n =>
    simp only [GlobalTheory.PSer.pw, GlobalTheory.PMonE.pw, Int.ofNat_eq_coe, zpow_natCast, hpos, map_pow]
    simp
  | negSucc n =>
    have hk : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := rfl
    simp only [GlobalTheory.PSer.pw, GlobalTheory.PMonE.pw]
    rw [if_neg (by omega), hk, hneg, hit]
    congr

end GlobalTheory.PSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoUntiltFrobeniusSeriesTermNormsZero
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem psers_norm_natCast_self (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends' l (l : ℚ_[l])
  rw [Padic.norm_p] at h
  simpa using h

theorem psers_terms_tendsto_zero : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ), 1 ≤ h → 0 ≤ r → r < 1 → Filter.Tendsto (fun n : ℤ => ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))) Filter.cofinite (nhds 0) := by
  intro l _ h j r h1 hr0 hr1
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hlR : (1 : ℝ) < l := by exact_mod_cast hl
  have ha := psers_norm_natCast_self l
  set a := ‖(l : ℂ_[l])‖ with ha_def
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have ha1 : a < 1 := by rw [ha]; exact inv_lt_one_of_one_lt₀ hlR
  rw [Int.cofinite_eq, Filter.tendsto_sup]
  constructor
  · rw [← Filter.map_neg_atTop, Filter.tendsto_map'_iff, ← Nat.map_cast_int_atTop,
      Filter.tendsto_map'_iff]
    refine squeeze_zero (fun k => ?_) (fun k => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1)
    · simp only [Function.comp_apply, neg_neg, zpow_natCast]
      exact mul_nonneg (pow_nonneg ha0 _) (Real.rpow_nonneg hr0 _)
    · simp only [Function.comp_apply, neg_neg, zpow_natCast]
      have : r ^ ((l : ℝ) ^ (-(k : ℤ) * h + j : ℤ)) ≤ 1 :=
        Real.rpow_le_one hr0 hr1.le (zpow_nonneg (by positivity) _)
      calc a ^ k * r ^ ((l : ℝ) ^ (-(k : ℤ) * h + j : ℤ)) ≤ a ^ k * 1 :=
            mul_le_mul_of_nonneg_left this (pow_nonneg ha0 _)
        _ = a ^ k := mul_one _
  · rw [← Nat.map_cast_int_atTop, Filter.tendsto_map'_iff]
    have hN : Filter.Tendsto (fun k : ℕ => l ^ (k * h + j)) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_mono (fun k => ?_) Filter.tendsto_id
      calc k ≤ l ^ k := (Nat.lt_pow_self hl).le
        _ ≤ l ^ (k * h + j) := Nat.pow_le_pow_right (by omega) (by nlinarith)
    refine squeeze_zero (fun k => ?_) (fun k => ?_)
      ((tendsto_self_mul_const_pow_of_lt_one hr0 hr1).comp hN)
    · exact mul_nonneg (zpow_nonneg ha0 _) (Real.rpow_nonneg hr0 _)
    · have e1 : a ^ (-((k : ℕ) : ℤ)) = (l : ℝ) ^ k := by
        rw [zpow_neg, zpow_natCast, ha, inv_pow, inv_inv]
      have e2 : (l : ℝ) ^ (((k : ℕ) : ℤ) * h + j : ℤ) = ((l ^ (k * h + j) : ℕ) : ℝ) := by
        rw [show (((k : ℕ) : ℤ) * h + j : ℤ) = ((k * h + j : ℕ) : ℤ) by push_cast; ring,
          zpow_natCast]
        push_cast; ring
      simp only [Function.comp_apply]
      rw [e1, e2, Real.rpow_natCast]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0 _)
      have : l ^ k ≤ l ^ (k * h + j) := Nat.pow_le_pow_right (by omega) (by nlinarith)
      exact_mod_cast this

end GlobalTheory
end

