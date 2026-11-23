module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0024
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0038
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0045
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0049
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionSmoothRightInvariant
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesSelfDual
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0110

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterOrthogonalIsRational
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann

section Core

open GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.SelfDual _root_.Topology

variable {F : Type} [Field F] [NumberField F]

theorem fin_eq_zero (ψf : AddChar (A F) ℂ) (hψ : GlobalTheory.CompanionTheory.SW.Core.IsStdChar F ψf) {y : A F}
    (hy : ∀ t : F, ψf (algebraMap F (A F) t * y) = 1) : y = 0 := by
  obtain ⟨hlc, hsc, ht2, hOc, hOo, hden, hint, hnb, hcp, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F
  have hall : ∀ z : A F, ψf (z * y) = 1 := by
    intro z
    have hcl : IsClosed {z : A F | ψf (z * y) = 1} :=
      isClosed_eq (hψ.1.comp (continuous_id.mul continuous_const)) continuous_const
    exact hden.induction_on (p := fun z => ψf (z * y) = 1) z hcl hy
  have hMc : IsCompact (MG ψf : Set (A F)) := by
    refine isCompact_of_relIndex (ohG_le_MG hψ) ?_ hOc
    rw [relIndex_MG hψ]
    exact Int.natAbs_ne_zero.2 (discr_ne_zero F)
  obtain ⟨N, hN, hNK⟩ := hcp _ hMc
  have hinv : ∀ m : ℕ, 0 < m → (m : A F) * algebraMap F (A F) (m : F)⁻¹ = 1 := by
    intro m hm
    have hm' : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    rw [← map_natCast (algebraMap F (A F)), ← map_mul, mul_inv_cancel₀ hm', map_one]
  have hmul : ∀ m : ℕ, 0 < m → algebraMap F (A F) (m : F)⁻¹ * ((N : A F) * y) ∈ Oh F := by
    intro m hm
    have h1 : algebraMap F (A F) (m : F)⁻¹ * y ∈ MG ψf := by
      intro z _
      show ψf (z * _) = 1
      rw [← mul_assoc]
      exact hall _
    have h2 := hNK _ h1
    rwa [mul_left_comm] at h2
  have hw : (N : A F) * y = 0 := by
    by_contra hne
    have hU : ({(N : A F) * y}ᶜ : Set (A F)) ∈ 𝓝 (0 : A F) :=
      isOpen_compl_singleton.mem_nhds (fun h => hne (Eq.symm h))
    obtain ⟨m, hm, hmU⟩ := hnb _ hU
    apply hmU _ (hmul m hm)
    rw [← mul_assoc, hinv m hm, one_mul]
    rfl
  calc y = algebraMap F (A F) (N : F)⁻¹ * ((N : A F) * y) := by
        rw [← mul_assoc, mul_comm (algebraMap F (A F) _), hinv N hN, one_mul]
    _ = 0 := by rw [hw, mul_zero]

theorem coeff_eq_zero (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (D : InfinitePlace F → ℝ)
    (h : ∀ t : F, ∑ w, ρ w t * D w = 0) : ∀ w, D w = 0 := by
  have hinj : Function.Injective (fun w => ((ρ w : F →+* ℝ) : F →* ℝ)) := by
    intro w w' hww
    have h1 : w.embedding = w'.embedding := by
      ext x
      rw [← hρ, ← hρ]
      have : ρ w x = ρ w' x := DFunLike.congr_fun hww x
      rw [this]
    rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h1]
  have hli := (linearIndependent_monoidHom F ℝ).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  refine hli D ?_
  ext t
  simpa [mul_comm] using h t

theorem real_eq_of_int (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (X : InfinitePlace F → ℝ)
    (hX : ∀ r : 𝓞 F, ∃ n : ℤ, ∑ w, ρ w (r : F) * X w = n) : ∃ c : F, ∀ w, X w = ρ w c := by
  classical
  set e := integralBasis F with he
  have hXe : ∀ i, ∃ n : ℤ, ∑ w, ρ w (e i) * X w = n := by
    intro i
    obtain ⟨n, hn⟩ := hX (RingOfIntegers.basis F i)
    refine ⟨n, ?_⟩
    rw [← hn, he, integralBasis_apply]
  choose n hn using hXe
  set c : F := e.traceDual.equivFun.symm (fun i => (n i : ℚ)) with hc
  have hrepr : ∀ i, Algebra.trace ℚ F (c * e i) = n i := by
    intro i
    have h1 := Module.Basis.traceDual_repr_apply e c i
    rw [Algebra.traceForm_apply] at h1
    rw [← h1, ← Module.Basis.equivFun_apply, hc, LinearEquiv.apply_symm_apply]
  refine ⟨c, fun w => ?_⟩
  have hz : ∀ t : F, ∑ w, ρ w t * (ρ w c - X w) = 0 := by
    let Lf : F →ₗ[ℚ] ℝ := ∑ w, (ρ w c - X w) • (ρ w).toRatAlgHom.toLinearMap
    have hL : Lf = 0 := by
      refine e.ext fun i => ?_
      have h2 := GlobalTheory.CompanionTheory.SW.CoefEis.sum_places_eq_trace F hF ρ hρ (c * e i)
      rw [hrepr] at h2
      simp only [Lf, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul,
        AlgHom.toLinearMap_apply, RingHom.toRatAlgHom_apply]
      simp only [map_mul] at h2
      have h3 : ∑ w, (ρ w c - X w) * ρ w (e i) = ∑ w, ρ w c * ρ w (e i) - ∑ w, ρ w (e i) * X w := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun w _ => by ring
      rw [h3, h2, hn]
      simp
    intro t
    have := LinearMap.congr_fun hL t
    simp only [Lf, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul,
      AlgHom.toLinearMap_apply, RingHom.toRatAlgHom_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun w _ => mul_comm _ _
  have := coeff_eq_zero ρ hρ _ hz w
  linarith

def eR (s : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))

theorem eR_add (s u : ℝ) : eR (s + u) = eR s * eR u := by
  simp only [eR, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eR_zero : eR 0 = 1 := by simp [eR]

theorem eR_int {s : ℝ} (h : eR s = 1) : ∃ n : ℤ, s = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  refine ⟨n, ?_⟩
  have h1 : (s : ℂ) = n := by
    refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
    rw [hn]
    ring
  exact_mod_cast h1

theorem sub_field (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (ψf : AddChar (A F) ℂ)
    (hstd : GlobalTheory.CompanionTheory.SW.Core.IsStdChar F ψf) {X : InfinitePlace F → ℝ} {y : A F}
    (H : ∀ t : F, eR (∑ w, ρ w t * X w) * ψf (algebraMap F (A F) t * y) = 1) (c : F) (t : F) :
    eR (∑ w, ρ w t * (X w - ρ w c)) * ψf (algebraMap F (A F) t * (y - algebraMap F (A F) c)) = 1 := by
  have hT : eR (∑ w, ρ w (t * c)) * ψf (algebraMap F (A F) (t * c)) = 1 := by
    rw [GlobalTheory.CompanionTheory.SW.CoefEis.sum_places_eq_trace F hF ρ hρ, hstd.2, eR, ← Complex.exp_add]
    have h0 : 2 * (Real.pi : ℂ) * Complex.I * (((Algebra.trace ℚ F (t * c) : ℚ) : ℝ) : ℂ) +
        -(2 * (Real.pi : ℂ) * Complex.I) * ((Algebra.trace ℚ F (t * c) : ℚ) : ℂ) = 0 := by
      push_cast
      ring
    rw [h0, Complex.exp_zero]
  have e1 : ∑ w, ρ w t * X w = ∑ w, ρ w t * (X w - ρ w c) + ∑ w, ρ w (t * c) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by rw [map_mul]; ring
  have e2 : algebraMap F (A F) t * y =
      algebraMap F (A F) t * (y - algebraMap F (A F) c) + algebraMap F (A F) (t * c) := by
    rw [map_mul]
    ring
  have h := H t
  rw [e1, e2, eR_add, AddChar.map_add_eq_mul] at h
  have key : ∀ p q r s : ℂ, (p * q) * (r * s) = 1 → q * s = 1 → p * r = 1 :=
    fun p q r s h1 h2 => by linear_combination h1 - p * r * h2
  exact key _ _ _ _ h hT

theorem core (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (ψf : AddChar (A F) ℂ)
    (hstd : GlobalTheory.CompanionTheory.SW.Core.IsStdChar F ψf) (X : InfinitePlace F → ℝ) (y : A F)
    (H : ∀ t : F, eR (∑ w, ρ w t * X w) * ψf (algebraMap F (A F) t * y) = 1) :
    ∃ c : F, (∀ w, X w = ρ w c) ∧ y = algebraMap F (A F) c := by
  obtain ⟨-, -, -, -, hOo, hden, hint, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F
  have hopen : IsOpen {z : A F | y - z ∈ Oh F} := hOo.preimage (continuous_const.sub continuous_id)
  obtain ⟨c1, hc1⟩ := hden.exists_mem_open hopen ⟨y, by
    show y - y ∈ Oh F
    rw [sub_self]
    exact (ohG F).zero_mem⟩
  have hc1' : y - algebraMap F (A F) c1 ∈ Oh F := hc1
  have H1 := sub_field hF ρ hρ ψf hstd H c1
  have hXint : ∀ r : 𝓞 F, ∃ n : ℤ, ∑ w, ρ w (r : F) * (X w - ρ w c1) = n := by
    intro r
    have h1 := H1 r
    rw [((GlobalTheory.T.standard_adelic_character F).2 ψf hstd).2.1 _ (oh_mul ((hint _).2 ⟨r, rfl⟩) hc1'), mul_one] at h1
    exact eR_int h1
  obtain ⟨c2, hc2⟩ := real_eq_of_int hF ρ hρ _ hXint
  have H2 := sub_field hF ρ hρ ψf hstd H1 c2
  have hy0 : y - algebraMap F (A F) c1 - algebraMap F (A F) c2 = 0 := fin_eq_zero ψf hstd fun t => by
    have h1 := H2 t
    have h0 : ∑ w, ρ w t * ((X w - ρ w c1) - ρ w c2) = 0 :=
      Finset.sum_eq_zero fun w _ => by rw [← hc2 w, sub_self, mul_zero]
    rwa [h0, eR_zero, one_mul] at h1
  refine ⟨c1 + c2, fun w => ?_, ?_⟩
  · have := hc2 w
    rw [map_add (f := _)]
    linarith
  · rw [map_add (f := _)]
    linear_combination hy0

end Core

theorem annihilator_eq : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ x : AF F, (∀ t : F, ψ (algebraMap F (AF F) t * x) = 1) → ∃ c : F, x = algebraMap F (AF F) c := by
  intro F _ _ hF ψ hψ x hx
  obtain ⟨ρ, e, hρ, he, heρ, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.real_iso F hF
  obtain ⟨a, ha, hinf, ψf, hstd, hfin⟩ := _root_.GlobalTheory.CompanionTheory.Glob.CharAF.exists_char_data F hF ρ e hρ he heρ ψ hψ
  have hsplit : ∀ (u : Ainf F) (v : Af F),
      ψ (u, v) = eR (∑ w, ρ w a * e u w) * ψf (algebraMap F (Af F) a * v) := by
    intro u v
    have h : ((u, v) : AF F) = pairA F u 0 + pairA F 0 v := by
      show ((u, v) : Ainf F × Af F) = ((u, 0) : Ainf F × Af F) + ((0, v) : Ainf F × Af F)
      rw [Prod.mk_add_mk, add_zero, zero_add]
    rw [h, AddChar.map_add_eq_mul, hinf, hfin]
    rfl
  have H : ∀ t : F, eR (∑ w, ρ w t * (ρ w a * e x.1 w)) *
      ψf (algebraMap F (Af F) t * (algebraMap F (Af F) a * x.2)) = 1 := by
    intro t
    have h := hx t
    have hm : algebraMap F (AF F) t * x =
        (algebraMap F (Ainf F) t * x.1, algebraMap F (Af F) t * x.2) := rfl
    rw [hm, hsplit] at h
    have e1 : ∑ w, ρ w a * e (algebraMap F (Ainf F) t * x.1) w = ∑ w, ρ w t * (ρ w a * e x.1 w) :=
      Finset.sum_congr rfl fun w _ => by rw [map_mul, Pi.mul_apply, heρ]; ring
    have e2 : algebraMap F (Af F) a * (algebraMap F (Af F) t * x.2) =
        algebraMap F (Af F) t * (algebraMap F (Af F) a * x.2) := mul_left_comm _ _ _
    rw [e1, e2] at h
    exact h
  obtain ⟨c, hc1, hc2⟩ := core hF ρ hρ ψf hstd _ _ H
  refine ⟨a⁻¹ * c, ?_⟩
  have hx1 : x.1 = algebraMap F (Ainf F) (a⁻¹ * c) := by
    apply e.injective
    funext w
    rw [heρ, map_mul, map_inv₀]
    have hne : ρ w a ≠ 0 := (map_ne_zero _).2 ha
    have h1 := hc1 w
    rw [← h1]
    field_simp
  have hx2 : x.2 = algebraMap F (Af F) (a⁻¹ * c) := by
    rw [map_mul, ← hc2, ← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  exact Prod.ext hx1 hx2

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CuspTranslateBoundedByDerivative
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HCCusp.Transl

open GlobalTheory.AutomorphicL2Unitary

theorem enorm_sub_sq_le {c f : ℝ → ℂ} (hf : Continuous f) (hd : ∀ t, HasDerivAt c (f t) t) :
    ‖c 1 - c 0‖ₑ ^ (2 : ℝ) ≤ ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖f t‖ₑ ^ (2 : ℝ) := by
  have e : c 1 - c 0 = ∫ t in (0 : ℝ)..1, f t :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hf.intervalIntegrable _ _)).symm
  have n1 : ‖c 1 - c 0‖ ≤ ∫ t in (0 : ℝ)..1, ‖f t‖ := by
    rw [e]
    exact intervalIntegral.norm_integral_le_integral_norm zero_le_one
  have hn : Continuous fun t => ‖f t‖ := hf.norm
  set A := ∫ t in (0 : ℝ)..1, ‖f t‖ with hA
  set B := ∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2 with hB
  have hA0 : 0 ≤ A := intervalIntegral.integral_nonneg zero_le_one fun _ _ => norm_nonneg _
  have hAB : A ^ 2 ≤ B := by
    have h0 : 0 ≤ ∫ t in (0 : ℝ)..1, (‖f t‖ - A) ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one fun _ _ => sq_nonneg _
    have h1 : (∫ t in (0 : ℝ)..1, (‖f t‖ - A) ^ 2) = B - 2 * A * A + A ^ 2 := by
      have : ∀ t, (‖f t‖ - A) ^ 2 = ‖f t‖ ^ 2 - 2 * A * ‖f t‖ + A ^ 2 := fun t => by ring
      simp only [this]
      have i1 : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume 0 1 := (hn.pow 2).intervalIntegrable _ _
      have i2 : IntervalIntegrable (fun t => 2 * A * ‖f t‖) volume 0 1 :=
        (continuous_const.mul hn).intervalIntegrable _ _
      rw [intervalIntegral.integral_add (f := fun t => ‖f t‖ ^ 2 - 2 * A * ‖f t‖) (g := fun _ => A ^ 2) (i1.sub i2)
        (continuous_const.intervalIntegrable _ _),
        intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul]
      simp [← hA, ← hB]
    nlinarith
  have hle : ‖c 1 - c 0‖ ^ 2 ≤ B := (pow_le_pow_left₀ (norm_nonneg _) n1 2).trans hAB
  have hBi : B = ∫ t in Set.Ioc (0 : ℝ) 1, ‖f t‖ ^ 2 := intervalIntegral.integral_of_le zero_le_one
  have hint : IntegrableOn (fun t => ‖f t‖ ^ 2) (Set.Ioc (0 : ℝ) 1) :=
    ((hn.pow 2).intervalIntegrable 0 1).1
  have hL : ENNReal.ofReal B = ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖f t‖ₑ ^ (2 : ℝ) := by
    rw [hBi, ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun t => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_ofNat]
  rw [← hL, ENNReal.rpow_ofNat, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hle

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G} [μ.IsMulLeftInvariant]
  {φ ψ : G → ℂ}

theorem ofReal_norm_sq (h : MemL2Quotient Γ μ φ) :
    ENNReal.ofReal (‖h.toL2‖ ^ 2) = ∫⁻ g in stdDom Γ, ‖φ g‖ₑ ^ (2 : ℝ) ∂μ := by
  have hE : eLpNorm (descend Γ φ) 2 (AutomorphicL2Unitary.quotMeasure Γ μ) ≠ ⊤ := h.2.ne
  have h1 : ‖h.toL2‖ = (eLpNorm (descend Γ φ) 2 (AutomorphicL2Unitary.quotMeasure Γ μ)).toReal := Lp.norm_toLp _ _
  have h2 := eLpNorm_nnreal_pow_eq_lintegral (f := descend Γ φ) (μ := AutomorphicL2Unitary.quotMeasure Γ μ) (p := 2) (by norm_num) h.2.aestronglyMeasurable
  have h3 := lintegral_quotMeasure (isFundamentalDomain_stdDom Γ μ) (fun q => ‖descend Γ φ q‖ₑ ^ (2 : ℝ))
  simp only [h.1.descend_mk] at h3
  rw [← h3, h1, ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hE]
  simpa using h2

theorem memL2_sub (h : MemL2Quotient Γ μ φ) (h' : MemL2Quotient Γ μ ψ) : MemL2Quotient Γ μ fun x => φ x - ψ x := by
  have hd := isFundamentalDomain_stdDom Γ μ
  exact (memL2_iff_fundamental_domain hd).2 ⟨fun γ hγ g => by simp only [h.1 γ hγ, h'.1 γ hγ], ((memL2_iff_fundamental_domain hd).1 h).2.sub ((memL2_iff_fundamental_domain hd).1 h').2⟩

theorem toL2_sub (h : MemL2Quotient Γ μ φ) (h' : MemL2Quotient Γ μ ψ) : (memL2_sub h h').toL2 = h.toL2 - h'.toL2 := by
  refine l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ?_
  have e1 := (memL2_sub h h').lift_toL2_ae_eq
  have e2 : lift Γ (h.toL2 - h'.toL2) =ᵐ[μ] lift Γ h.toL2 - lift Γ h'.toL2 :=
    ae_quotMeasure_iff.1 (Lp.coeFn_sub h.toL2 h'.toL2)
  exact e1.trans ((h.lift_toL2_ae_eq.sub h'.lift_toL2_ae_eq).symm.trans e2.symm)

variable [μ.IsMulRightInvariant]

theorem norm_R_sub_le [SFinite μ] {a : ℝ → G} {u : G} (ha : Continuous a) (h0 : a 0 = 1) (h1 : a 1 = u) (hφ : MemL2Quotient Γ μ φ) (hψ : MemL2Quotient Γ μ ψ)
    (hψc : Continuous ψ) (hd : ∀ g t, HasDerivAt (fun s => φ (g * a s)) (ψ (g * a t)) t) :
    ‖R Γ μ u hφ.toL2 - hφ.toL2‖ ≤ ‖hψ.toL2‖ := by
  subst h1
  have hm := hφ.mul_right (a 1)
  have hs := memL2_sub hm hφ
  rw [right_translate_toL2, ← toL2_sub hm hφ]
  have key : ∫⁻ g in stdDom Γ, ‖φ (g * a 1) - φ g‖ₑ ^ (2 : ℝ) ∂μ ≤ ∫⁻ g in stdDom Γ, ‖ψ g‖ₑ ^ (2 : ℝ) ∂μ := by
    have hpt : ∀ g, ‖φ (g * a 1) - φ g‖ₑ ^ (2 : ℝ) ≤ ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖ψ (g * a t)‖ₑ ^ (2 : ℝ) := fun g => by
      have := enorm_sub_sq_le (c := fun s => φ (g * a s)) (f := fun t => ψ (g * a t)) (by fun_prop) (hd g)
      simpa [h0] using this
    have hmeas : Measurable fun p : G × ℝ => ‖ψ (p.1 * a p.2)‖ₑ ^ (2 : ℝ) :=
      (Continuous.measurable (by fun_prop : Continuous fun p : G × ℝ => ψ (p.1 * a p.2))).enorm.pow_const _
    calc _ ≤ ∫⁻ g in stdDom Γ, (∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖ψ (g * a t)‖ₑ ^ (2 : ℝ)) ∂μ := lintegral_mono hpt
      _ = ∫⁻ t in Set.Ioc (0 : ℝ) 1, (∫⁻ g in stdDom Γ, ‖ψ (g * a t)‖ₑ ^ (2 : ℝ) ∂μ) :=
        lintegral_lintegral_swap hmeas.aemeasurable
      _ = ∫⁻ t in Set.Ioc (0 : ℝ) 1, (∫⁻ g in stdDom Γ, ‖ψ g‖ₑ ^ (2 : ℝ) ∂μ) := by
        refine lintegral_congr fun t => ?_
        rw [← ofReal_norm_sq (hψ.mul_right (a t)), ← ofReal_norm_sq hψ, ← right_translate_toL2, norm_R]
      _ = _ := by simp
  have h1 := (ofReal_norm_sq hs).le.trans (key.trans (ofReal_norm_sq hψ).ge)
  have h2 : ‖hs.toL2‖ ^ 2 ≤ ‖hψ.toL2‖ ^ 2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

end Abstract

end GlobalTheory.CompanionTheory.HCCusp.Transl

namespace GlobalTheory.CompanionTheory.HCCusp.Transl

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Mem.AutSpace GlobalTheory.SmoothForms

variable {D : D7} {θ : GlobalTheory.Mem.Th.InfF D} {V : HSp D}

theorem coe_derInf (hθ : IsInfFam θ) (X : LieN V) (φ : Mc θ V) :
    (derInf hθ X φ : GA D V → ℂ) = Der (expInf θ V) X φ.1 := by
  have R := (RealPts.realPoints D).2 θ hθ V
  have hs : Sm (expInf θ V) φ.1 := (smooth_iff R φ.1).1 (mem_Mc_iff.1 φ.2).1.smooth
  funext g
  have e1 : (derInf hθ X φ : GA D V → ℂ) g = ∑ τ, Rder θ V τ (X τ).1 φ.1 g := by
    simp only [derInf, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun τ _ => rfl
  rw [e1]
  have e2 : ∀ τ, Rder θ V τ (X τ).1 φ.1 g = Der (expInf θ V) (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ (X τ)) φ.1 g := fun τ =>
    congrFun (Rder_eq R τ (X τ) φ.1) g
  have hX : ∑ τ, (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ (X τ) : LieN V) = X := sum_atPlace X
  rw [Finset.sum_congr rfl fun τ _ => (e2 τ).trans (DerLinear.der_eq_fderiv hs _ g), DerLinear.der_eq_fderiv hs X g]
  exact (map_sum (fderiv ℝ (fun Z : LieN V => φ.1 (g * expInf θ V Z)) 0) (fun τ => (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ (X τ) : LieN V))
    Finset.univ).symm.trans (congrArg _ hX)

end GlobalTheory.CompanionTheory.HCCusp.Transl

theorem GlobalTheory.CompanionTheory.HCCusp.norm_Rcusp_expInf_sub_le : ∀ (D : D7) (θ : GlobalTheory.Mem.Th.InfF D) (hθ : IsInfFam θ) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : GlobalTheory.SmoothForms.LieN V) (φ : GlobalTheory.CompanionTheory.HCCusp.Mc θ V), ‖GlobalTheory.Cusp.Rcusp V μ (GlobalTheory.SmoothForms.expInf θ V X) (GlobalTheory.CompanionTheory.HCCusp.io μ hθ φ) - GlobalTheory.CompanionTheory.HCCusp.io μ hθ φ‖ ≤ ‖GlobalTheory.CompanionTheory.HCCusp.io μ hθ (GlobalTheory.CompanionTheory.HCCusp.derInf hθ X φ)‖ := by
  intro D θ hθ V μ _ _ X φ
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  let a : ℝ → GA D V := fun t => GlobalTheory.SmoothForms.expInf θ V (t • X)
  have ha : Continuous a := (GlobalTheory.CuspGeo.MeanValue.continuous_expInf hθ R).comp (continuous_id.smul continuous_const)
  have h0 : a 0 = 1 := by
    simpa [a] using GlobalTheory.CuspGeo.MeanValue.expInf_zero R
  have h1 : a 1 = GlobalTheory.SmoothForms.expInf θ V X := by simp [a]
  have hP := GlobalTheory.Grow.cuspRapidDecay_of_bound GlobalTheory.CuspGeo.cuspDecayBound
  have hφc := (GlobalTheory.Cusp.mem_cuspForms.1 φ.2).1
  set ψ := GlobalTheory.CompanionTheory.HCCusp.derInf hθ X φ with hψdef
  have hψf := (GlobalTheory.Cusp.mem_cuspForms.1 ψ.2).1
  have hs : GlobalTheory.SmoothForms.Sm (GlobalTheory.SmoothForms.expInf θ V) φ.1 :=
    (GlobalTheory.SmoothForms.smooth_iff R φ.1).1 (GlobalTheory.CompanionTheory.HCCusp.mem_Mc_iff.1 φ.2).1.smooth
  have d0 : ∀ h, HasDerivAt (fun t : ℝ => φ.1 (h * a t)) (ψ.1 h) 0 := fun h => by
    rw [hψdef, GlobalTheory.CompanionTheory.HCCusp.Transl.coe_derInf]
    exact DifferentiableAt.hasDerivAt
      ((((hs h).differentiable (by simp)).comp (differentiable_id.smul_const X)) 0)
  have hd : ∀ g t, HasDerivAt (fun s => φ.1 (g * a s)) (ψ.1 (g * a t)) t := fun g t => by
    have h2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact d0 (g * a t))
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [a, mul_assoc, ← GlobalTheory.CuspGeo.MeanValue.expInf_add R, add_sub_cancel]
  have := GlobalTheory.CompanionTheory.HCCusp.Transl.norm_R_sub_le ha h0 h1 (GlobalTheory.Cusp.memL2_of_cusp_form (μ := μ) hP hθ hφc)
    (GlobalTheory.Cusp.memL2_of_cusp_form (μ := μ) hP hθ hψf) hψf.1.cont hd
  exact this

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivativeSkewAdjointCuspForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.HCCusp
open GlobalTheory.Cusp GlobalTheory.Mem.AutSpace GlobalTheory.Mem.Lift ComplexConjugate

variable {D : D7} {θ : GlobalTheory.Mem.Th.InfF D} {V : HSp D}

theorem cont_bdd (hθ : IsInfFam θ) (φ : Mc θ V) :
    Continuous (φ : GA D V → ℂ) ∧ ∃ C : ℝ, ∀ g, ‖(φ : GA D V → ℂ) g‖ ≤ C :=
  ⟨(mem_Mc_iff.1 φ.2).1.cont, GlobalTheory.CuspDecay.bounded_of_cuspForm
    (GlobalTheory.Grow.cuspRapidDecay_of_bound GlobalTheory.CuspGeo.cuspDecayBound) hθ (mem_Mc_iff.1 φ.2).1 (mem_Mc_iff.1 φ.2).2⟩

theorem integrableOn_mul_conj {μ : Measure (GA D V)} [μ.IsHaarMeasure] {𝓕 : Set (GA D V)} (hfin : μ 𝓕 ≠ ⊤)
    (hθ : IsInfFam θ) (φ ψ : Mc θ V) :
    IntegrableOn (fun g => (φ : GA D V → ℂ) g * conj ((ψ : GA D V → ℂ) g)) 𝓕 μ := by
  obtain ⟨c1, B1, h1⟩ := cont_bdd hθ φ
  obtain ⟨c2, B2, h2⟩ := cont_bdd hθ ψ
  have hc : Continuous (fun g => (φ : GA D V → ℂ) g * conj ((ψ : GA D V → ℂ) g)) :=
    c1.mul (Complex.continuous_conj.comp c2)
  refine Measure.integrableOn_of_bounded (M := B1 * B2) hfin hc.measurable.aestronglyMeasurable (.of_forall fun g => ?_)
  rw [norm_mul, RCLike.norm_conj]
  exact mul_le_mul (h1 g) (h2 g) (norm_nonneg _) ((norm_nonneg _).trans (h1 g))

theorem setIntegral_der_mul_conj {μ : Measure (GA D V)} [μ.IsHaarMeasure] {𝓕 : Set (GA D V)}
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (φ ψ : Mc θ V) :
    ∫ g in 𝓕, (φ : GA D V → ℂ) g * conj ((der hθ τ hX ψ : GA D V → ℂ) g) ∂μ =
      -∫ g in 𝓕, (der hθ τ hX φ : GA D V → ℂ) g * conj ((ψ : GA D V → ℂ) g) ∂μ := by
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hH : μ.IsHaarMeasure := inferInstance
  have hfin : μ 𝓕 ≠ ⊤ := (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V μ 𝓕 ⟨hH, h𝓕⟩).2
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hH).1
  obtain ⟨c0, B0, b0⟩ := cont_bdd hθ φ
  obtain ⟨c1, B1, b1⟩ := cont_bdd hθ ψ
  obtain ⟨c2, B2, b2⟩ := cont_bdd hθ (der hθ τ hX φ)
  obtain ⟨c3, B3, b3⟩ := cont_bdd hθ (der hθ τ hX ψ)
  have cc : ∀ {f : GA D V → ℂ}, Continuous f → Continuous fun g => conj (f g) :=
    fun h => Complex.continuous_conj.comp h
  have nn : ∀ {f : GA D V → ℂ} {B : ℝ}, (∀ g, ‖f g‖ ≤ B) → 0 ≤ B :=
    fun h => (norm_nonneg _).trans (h 1)
  have sm : ∀ (f : Mc θ V) (g : GA D V), HasDerivAt (fun t : ℝ => (f : GA D V → ℂ) (g * oneP θ V τ X t))
      (Rder θ V τ X f.1 g) 0 := fun f g => hasDerivAt_Rder (mem_Mc_iff.1 f.2).1.smooth hX g
  have key := GlobalTheory.Mem.IntByParts.setIntegral_deriv_eq_zero (GQ V) μ h𝓕 hfin
    (Φ := fun g => (φ : GA D V → ℂ) g * conj ((ψ : GA D V → ℂ) g))
    (Φ' := fun g => (der hθ τ hX φ : GA D V → ℂ) g * conj ((ψ : GA D V → ℂ) g) +
      (φ : GA D V → ℂ) g * conj ((der hθ τ hX ψ : GA D V → ℂ) g))
    (B := B0 * B1) (B' := B2 * B1 + B0 * B3)
    (fun γ hγ g => by
      simp only [(mem_Mc_iff.1 φ.2).1.left γ hγ g, (mem_Mc_iff.1 ψ.2).1.left γ hγ g])
    (c0.mul (cc c1)) ((c2.mul (cc c1)).add (c0.mul (cc c3)))
    (fun g => by
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (b0 g) (b1 g) (norm_nonneg _) (nn b0))
    (fun g => by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, RCLike.norm_conj]
        exact mul_le_mul (b2 g) (b1 g) (norm_nonneg _) (nn b2)
      · rw [norm_mul, RCLike.norm_conj]
        exact mul_le_mul (b0 g) (b3 g) (norm_nonneg _) (nn b0))
    (oneP_zero (V := V) (τ := τ) (X := X) hθ)
    (fun g t => (hasDerivAt_oneP hθ hX (sm φ) g t).mul (hasDerivAt_oneP hθ hX (sm ψ) g t).star)
  rw [integral_add (integrableOn_mul_conj hfin hθ _ _) (integrableOn_mul_conj hfin hθ _ _)] at key
  exact eq_neg_of_add_eq_zero_right key

theorem inner_eq_petersson {μ : Measure (GA D V)} [μ.IsHaarMeasure] (hθ : IsInfFam θ) (φ ψ : Mc θ V) :
    ⟪io μ hθ φ, io μ hθ ψ⟫_ℂ = petersson V μ ψ.1 φ.1 :=
  petersson_inner_eq_integral_quotient _ hθ ψ φ

theorem inner_eq_setIntegral {μ : Measure (GA D V)} [μ.IsHaarMeasure] {𝓕 : Set (GA D V)}
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hθ : IsInfFam θ) (φ ψ : Mc θ V) :
    ⟪io μ hθ φ, io μ hθ ψ⟫_ℂ = ∫ g in 𝓕, (ψ : GA D V → ℂ) g * conj ((φ : GA D V → ℂ) g) ∂μ := by
  rw [inner_eq_petersson]
  exact petersson_eq h𝓕 (mem_Mc_iff.1 ψ.2).1.left (mem_Mc_iff.1 φ.2).1.left

theorem inner_io_der_skew : ∀ (D : D7) (θ : GlobalTheory.Mem.Th.InfF D) (hθ : IsInfFam θ) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) (ψ χ : GlobalTheory.CompanionTheory.HCCusp.Mc θ V), ⟪GlobalTheory.CompanionTheory.HCCusp.io μ hθ (GlobalTheory.CompanionTheory.HCCusp.der hθ τ hX ψ), GlobalTheory.CompanionTheory.HCCusp.io μ hθ χ⟫_ℂ = -⟪GlobalTheory.CompanionTheory.HCCusp.io μ hθ ψ, GlobalTheory.CompanionTheory.HCCusp.io μ hθ (GlobalTheory.CompanionTheory.HCCusp.der hθ τ hX χ)⟫_ℂ := by
  intro D θ hθ V μ _ τ X hX ψ χ
  obtain ⟨𝓕, h𝓕⟩ := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ inferInstance).2
  rw [inner_eq_setIntegral h𝓕, inner_eq_setIntegral h𝓕]
  exact setIntegral_der_mul_conj h𝓕 hθ τ hX χ ψ

end GlobalTheory.CompanionTheory.HCCusp
end
end

