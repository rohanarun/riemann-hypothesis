module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0307
public import ReciprocityTheory.GaloisValuations.Global
public import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0117
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0302
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharactersDetectRestrictNormalInfFiniteLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem detects_restrictNormal_inf : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)] (r : ℕ) (N N' : Subgroup (GQ l))
    (I : Subgroup (L ≃ₐ[ℚ_[l]] L)) (ι : Type) (x : ι → Om l) (a : ι → GQ l → ℤ),
    (∀ i, x i ∈ Set.range (algebraMap L (Om l))) →
    (∀ i, ∀ σ ∈ N, ‖σ (x i) - x i - (a i σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) →
    (∀ σ ∈ N, (∀ i, (l : ℤ) ^ r ∣ a i σ) → σ ∈ N') →
    Detects l r (N.map (AlgEquiv.restrictNormalHom L) ⊓ I) (N'.map (AlgEquiv.restrictNormalHom L) ⊓ I) := by
  intro l _ L _ _ _ _ _ _ _ _ _ _ r N N' I ι x a hx hN hN'
  classical
  intro σ₀ hσ₀ hσ₀B

  let lift : (L ≃ₐ[ℚ_[l]] L) → GQ l := fun s =>
    if h : ∃ σ ∈ N, AlgEquiv.restrictNormalHom L σ = s then h.choose else 1
  have hlift : ∀ s ∈ N.map (AlgEquiv.restrictNormalHom L),
      lift s ∈ N ∧ AlgEquiv.restrictNormalHom L (lift s) = s := by
    intro s hs
    have h : ∃ σ ∈ N, AlgEquiv.restrictNormalHom L σ = s := Subgroup.mem_map.mp hs
    simp only [lift, dif_pos h]
    exact h.choose_spec
  obtain ⟨hτN, hτ⟩ := hlift σ₀ hσ₀.1
  have hτN' : lift σ₀ ∉ N' := by
    intro h
    exact hσ₀B ⟨Subgroup.mem_map.mpr ⟨lift σ₀, h, hτ⟩, hσ₀.2⟩
  have hex : ∃ i, ¬ (l : ℤ) ^ r ∣ a i (lift σ₀) := by
    by_contra hc
    push_neg at hc
    exact hτN' (hN' _ hτN hc)
  obtain ⟨i, hi⟩ := hex
  obtain ⟨x', hx'⟩ := hx i
  have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hlL : (l : L) ^ r ≠ 0 := by
    refine pow_ne_zero _ ?_
    rw [← map_natCast (algebraMap ℚ_[l] L)]
    exact (map_ne_zero _).mpr (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have hnorm_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
    have h : (l : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := by simp
    rw [h, PadicAlgCl.norm_extends, Padic.norm_p]
  refine ⟨x', fun s => a i (lift s), ?_, hi⟩
  intro s hs
  obtain ⟨hσN, hσ⟩ := hlift s hs.1
  have key : algebraMap L (Om l) (s x') = lift s (x i) := by
    rw [← hx']
    conv_lhs => rw [← hσ]
    exact AlgEquiv.restrictNormal_commutes (lift s) L x'
  refine ⟨(s x' - x' - (a i (lift s) : L)) / (l : L) ^ r, ?_, ?_⟩
  · refine ((_root_.GlobalTheory.PMon.Ram.mem_integer_iff_norm_le_and_valuation_lt_one_iff_norm_lt l L _).1).mpr ?_
    rw [map_div₀, map_sub, map_sub, map_intCast, map_pow, map_natCast, key, hx', norm_div, norm_pow, hnorm_l]
    rw [div_le_one (by positivity)]
    exact hN i _ hσN
  · rw [mul_div_cancel₀ _ hlL]
    ring

end GlobalTheory.PMon.Ram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
section
noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Published

theorem chebotarevDegreeOne' : ChebotarevDegreeOne := by
  intro F Ω _ _ _ _ _ L _ _ g S hS
  have : IsGalois F Ω := {}
  obtain ⟨g', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := L) Ω g
  have : NumberField L := NumberField.of_module_finite F L
  obtain ⟨m, hm, hdvd, hirr⟩ := _root_.GlobalTheory.exists_prime_dvd_sub_one_irreducible_cyclotomic L (Module.finrank F L) Module.finrank_pos.ne'
  obtain ⟨Z, τ, hZ, hZirr, hcross⟩ := _root_.GlobalTheory.ChebCross.cross F Ω L g' m hm hdvd hirr
  have : NumberField Z := NumberField.of_module_finite F Z
  have : IsAlgClosure Z Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩
  have hfin := hS.union (GlobalTheory.T.finite_places_inertia_not_fixing_finiteExtension F Ω L)
  let u : HeightOneSpectrum (𝓞 Z) → HeightOneSpectrum (𝓞 F) := fun w => w.under (𝓞 F)
  have hu : ∀ w : HeightOneSpectrum (𝓞 Z), w.asIdeal.LiesOver (u w).asIdeal := fun w => ⟨rfl⟩
  have hfin' : (u ⁻¹' (S ∪ {v | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧
      ¬ Ine (F := F) B ≤ L.fixingSubgroup})).Finite := by
    refine hfin.preimage' fun v _ => ?_
    have := v.isMaximal
    refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 Z)).preimage
      (f := fun w : HeightOneSpectrum (𝓞 Z) => w.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro w rfl
    exact ⟨w.isPrime, hu w⟩
  obtain ⟨w, hw, hp, hτ⟩ := _root_.GlobalTheory.CyclotomicPrimes.exists_prime_absNorm_eq_of_irreducible_cyclotomic Z m hm hZirr τ _ hfin'
  obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := exists_isFrob hB
  obtain ⟨hN, hBv, hσv⟩ := GlobalTheory.T.isFrob_restrictScalars_of_prime_absNorm' F Ω Z w (u w) (hu w) hp B hB σ hσ
  simp only [Set.mem_preimage, Set.mem_union, not_or, Set.mem_ofPred_eq, not_exists, not_and, not_not] at hw
  refine ⟨u w, hw.1, ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 _).1 (hN ▸ hp),
    B, hBv, hw.2 B hBv, σ.restrictScalars F, hσv, ?_⟩
  have hmw : ((m : ℕ) : 𝓞 Z) ∉ w.asIdeal := by
    intro h
    have : Fact m.Prime := ⟨hm⟩
    have h1 : Ideal.absNorm w.asIdeal ∣ m ^ Module.finrank ℤ (𝓞 Z) := by
      rw [← Ideal.absNorm_span_natCast]
      exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
    have h2 := (Nat.prime_dvd_prime_iff_eq hp hm).1 (hp.dvd_of_dvd_pow h1)
    rw [h2, ZMod.natCast_self] at hτ
    exact τ.ne_zero hτ.symm
  have key := hcross (σ.restrictScalars F) (fun x => σ.commutes x) fun ζ hζ => by
    have hq : ζ ^ (τ : ZMod m).val = ζ ^ normV w := by
      rw [← hτ, ZMod.val_natCast]
      simpa only [normV, Ideal.absNorm_eq_natCard] using
        (pow_eq_pow_mod (Ideal.absNorm w.asIdeal) hζ).symm
    rw [hq]
    have h1 := not_valuation_lt_one_of_isPlaceOver hmw hB 1
    rw [pow_one] at h1
    refine eq_of_pow_eq_one B h1 ?_ ?_ (hσ.2 ζ (valuation_eq_one_of_pow_eq_one B hm.ne_zero hζ).le)
    · rw [← map_pow, hζ, map_one]
    · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  rwa [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv,
    mul_inv_eq_one] at key

theorem cheb_holds : GlobalTheory.TwSys.Cheb :=
  chebotarevDegreeOne_iff_cheb.1 chebotarevDegreeOne'

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryModIffForallTraceFormCoboundary
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory


open _root_.Submodule in
theorem cobO_iff_forall_lam : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL] (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL))),
    L1.T = LinearMap.range (Algebra.linearMap O LL) →
    ∀ (L1Z : Lattice (O := ℤ_[l]) (charRep (cycLL (P.PD K) ℚ_[l]))),
    L1Z.T = LinearMap.range (Algebra.linearMap ℤ_[l] ℚ_[l]) →
    ∀ (z : ↥(GK K) × ↥(GK K) → LL),
    (CobO (P.PD K) L1 z ↔ ∀ o : O, CobO (P.PD K) L1Z (fun x => lam (algebraMap O LL o * z x))) := by
  intro l _ P K LL _ _ O _ _ lam n e f h1 h2 h3 L1 hL1 L1Z hL1Z z
  classical
  have memT : ∀ x : LL, x ∈ L1.T ↔ ∃ o : O, algebraMap O LL o = x := by
    intro x; rw [hL1]; simp [LinearMap.mem_range]
  have memZ : ∀ q : ℚ_[l], q ∈ L1Z.T ↔ ∃ w : ℤ_[l], (w : ℚ_[l]) = q := by
    intro q; rw [hL1Z]; simp [LinearMap.mem_range]
  have actT : ∀ g (a : LL), (repD L1 g) (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (algebraMap ℚ_[l] LL ((P.PD K).χ g : ℚ_[l]) * a) := by
    intro g a
    simp [repD, Submodule.mapQ_apply, charRep, cycLL, Algebra.smul_def]
  have actZ : ∀ g (q : ℚ_[l]), (repD L1Z g) (Submodule.Quotient.mk q) =
      Submodule.Quotient.mk (((P.PD K).χ g : ℚ_[l]) * q) := by
    intro g q
    simp [repD, Submodule.mapQ_apply, charRep, cycLL]
  have lamc : ∀ (o : O) (c : ℚ_[l]) (y : LL),
      lam (algebraMap O LL o * (algebraMap ℚ_[l] LL c * y)) = c * lam (algebraMap O LL o * y) := by
    intro o c y
    have : algebraMap O LL o * (algebraMap ℚ_[l] LL c * y) = c • (algebraMap O LL o * y) := by
      rw [Algebra.smul_def]; ring
    rw [this, map_smul, smul_eq_mul]
  unfold CobO ReciprocityTheory.Def.B2
  constructor
  · intro H o
    obtain ⟨F, ⟨hFc, -⟩, hF⟩ := Submodule.mem_map.1 H
    choose Ft hFt using fun g => Submodule.Quotient.mk_surjective L1.T (F g)
    have hFeq : F = fun g => Submodule.Quotient.mk (Ft g) := funext fun g => (hFt g).symm
    subst hFeq
    let φ : LL ⧸ L1.T → ℚ_[l] ⧸ L1Z.T := fun q =>
      Submodule.Quotient.mk (lam (algebraMap O LL o * (Submodule.Quotient.mk_surjective L1.T q).choose))
    have hφ : ∀ a, φ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (lam (algebraMap O LL o * a)) := by
      intro a
      have hc := (Submodule.Quotient.mk_surjective L1.T (Submodule.Quotient.mk a)).choose_spec
      rw [Submodule.Quotient.eq] at hc
      obtain ⟨o', ho'⟩ := (memT _).1 hc
      obtain ⟨w, hw⟩ := h2 (o * o')
      show Submodule.Quotient.mk _ = _
      rw [Submodule.Quotient.eq, memZ]
      exact ⟨w, by rw [← hw, map_mul, ho', mul_sub, map_sub]⟩
    refine Submodule.mem_map.2 ⟨φ ∘ (fun g => Submodule.Quotient.mk (Ft g)), ⟨hFc.comp φ, fun _ => trivial⟩, ?_⟩
    funext x
    have hx := congrFun hF x
    simp only [ReciprocityTheory.Def.d1, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply] at hx ⊢
    rw [actT, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq] at hx
    obtain ⟨o', ho'⟩ := (memT _).1 hx
    obtain ⟨w, hw⟩ := h2 (o * o')
    rw [hφ, hφ, hφ, actZ, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, memZ]
    refine ⟨w, ?_⟩
    rw [← hw, map_mul, ho', mul_sub, mul_add, mul_sub, map_sub, map_add (f := _), map_sub, lamc]
  · intro H
    choose Fz hFzc hFz using fun i => Submodule.mem_map.1 (H (f i))
    choose Ft hFt using fun i g => Submodule.Quotient.mk_surjective L1Z.T (Fz i g)
    refine Submodule.mem_map.2 ⟨fun g => Submodule.Quotient.mk
      (∑ i, algebraMap ℚ_[l] LL (Ft i g) * algebraMap O LL (e i)), ⟨?_, fun _ => trivial⟩, ?_⟩
    · rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      have hev : ∀ᶠ y in nhds x, ∀ i, Fz i y = Fz i x :=
        Filter.eventually_all.2 fun i => (IsLocallyConstant.iff_eventually_eq _).1 (hFzc i).1 x
      filter_upwards [hev] with y hy
      rw [Submodule.Quotient.eq, ← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hyi := hy i
      rw [← hFt i y, ← hFt i x, Submodule.Quotient.eq, memZ] at hyi
      obtain ⟨w, hw⟩ := hyi
      obtain ⟨o, ho⟩ := h1 w
      rw [memT]
      exact ⟨o * e i, by rw [map_mul, ho, hw, ← sub_mul, map_sub]⟩
    · funext x
      have key : ∀ i, ∃ w : ℤ_[l], (w : ℚ_[l]) = ((P.PD K).χ x.1 : ℚ_[l]) * Ft i x.2 - Ft i (x.1 * x.2)
          + Ft i x.1 - lam (algebraMap O LL (f i) * z x) := by
        intro i
        have hx := congrFun (hFz i) x
        simp only [ReciprocityTheory.Def.d1, LinearMap.coe_mk, AddHom.coe_mk] at hx
        rw [← hFt i x.2, ← hFt i (x.1 * x.2), ← hFt i x.1, actZ, ← Submodule.Quotient.mk_sub,
          ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, memZ] at hx
        exact hx
      choose w hw using key
      choose o ho using fun i => h1 (w i)
      simp only [ReciprocityTheory.Def.d1, LinearMap.coe_mk, AddHom.coe_mk]
      rw [actT, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, memT]
      refine ⟨∑ i, o i * e i, ?_⟩
      have hl : ∀ i, lam (algebraMap O LL (f i) * z x) = ((P.PD K).χ x.1 : ℚ_[l]) * Ft i x.2
          - Ft i (x.1 * x.2) + Ft i x.1 - (w i : ℚ_[l]) := fun i => by rw [hw i]; ring
      conv_rhs => rw [h3 (z x)]
      simp_rw [hl]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ho, Algebra.smul_def]
      simp only [map_sub, map_add (f := _), map_mul]
      ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutatorMemOfCoboundaryDetectsQuotient
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem commutator_mem_of_detects : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → Detects p r A B → ∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ B := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E r A B hp hE hord hdet σ hσ τ hτ
  by_contra hc
  have hcA : σ * τ * σ⁻¹ * τ⁻¹ ∈ A :=
    A.mul_mem (A.mul_mem (A.mul_mem hσ hτ) (A.inv_mem hσ)) (A.inv_mem hτ)
  obtain ⟨x, a, hx, hnd⟩ := hdet _ hcA hc
  have hadd := GlobalTheory.PMon.Ram.coboundary_int_additive_mod K L p E r A x a hp hE hord hx
  have h1 : (p : ℤ) ^ r ∣ a 1 := by
    have := hadd 1 A.one_mem 1 A.one_mem
    simp only [mul_one] at this
    have h' : a 1 = -(a 1 - a 1 - a 1) := by ring
    rw [h']; exact this.neg_right
  have hinv : ∀ g ∈ A, (p : ℤ) ^ r ∣ a g⁻¹ + a g := by
    intro g hg
    have := hadd g⁻¹ (A.inv_mem hg) g hg
    rw [inv_mul_cancel] at this
    have h' : a g⁻¹ + a g = a 1 - (a 1 - a g⁻¹ - a g) := by ring
    rw [h']; exact dvd_sub h1 this
  have e1 := hadd (σ * τ * σ⁻¹) (A.mul_mem (A.mul_mem hσ hτ) (A.inv_mem hσ)) τ⁻¹ (A.inv_mem hτ)
  have e2 := hadd (σ * τ) (A.mul_mem hσ hτ) σ⁻¹ (A.inv_mem hσ)
  have e3 := hadd σ hσ τ hτ
  have e4 := hinv σ hσ
  have e5 := hinv τ hτ
  apply hnd
  have h' : a (σ * τ * σ⁻¹ * τ⁻¹) =
      (a (σ * τ * σ⁻¹ * τ⁻¹) - a (σ * τ * σ⁻¹) - a τ⁻¹) + (a (σ * τ * σ⁻¹) - a (σ * τ) - a σ⁻¹)
        + (a (σ * τ) - a σ - a τ) + (a σ⁻¹ + a σ) + (a τ⁻¹ + a τ) := by ring
  rw [h']
  exact dvd_add (dvd_add (dvd_add (dvd_add e1 e2) e3) e4) e5

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactSpaceATopStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactSpace_aTop' : ∀ {l : ℕ} [Fact l.Prime] {K LL : FinExt l} {e : ℕ} (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)), letI := aTop (K := K) bO; CompactSpace (AA K LL) := by
  first | exact @GlobalTheory.WeakClosed.compactSpace_aTop | exact GlobalTheory.WeakClosed.compactSpace_aTop | (intros; apply GlobalTheory.WeakClosed.compactSpace_aTop <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongrFiltrationDetectingCharactersCoboundary
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory

noncomputable def padicClampInt (l : ℕ) [Fact l.Prime] (x : ℚ_[l]) : ℤ_[l] :=
  ⟨if ‖x‖ ≤ 1 then x else 0, by split_ifs with h <;> simp [h]⟩

theorem padicClampInt_coe (l : ℕ) [Fact l.Prime] {x : ℚ_[l]} (h : ‖x‖ ≤ 1) :
    ((padicClampInt l x : ℤ_[l]) : ℚ_[l]) = x := by
  show (if ‖x‖ ≤ 1 then x else 0) = x
  rw [if_pos h]

theorem congrFiltration_detectingCharacters_coboundary : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]) (M : GL n ℂ_[l]), (∀ g : ↥(GK K), (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) * (M : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = M) → ∀ N : ℕ → Subgroup ↥(GK K), (∀ k g, g ∈ N k ↔ ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) → ∀ r : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ (ι : Type) (_ : Finite ι) (x : ι → ℂ_[l]) (a : ι → ↥(GK K) → ℤ_[l]), (∀ i, ∀ σ ∈ N k, ‖Formalism.Per.σC (σ : GQ l) (x i) - x i - algebraMap ℚ_[l] ℂ_[l] (a i σ : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧ ∀ σ ∈ N k, (∀ i, (l : ℤ_[l]) ^ r ∣ a i σ) → σ ∈ N (k + r) := by
  intro l _ n _ _ K ρ M hM N hN r
  obtain ⟨b, hb, hcob⟩ := _root_.GlobalTheory.ph_c_cob l n K ρ M hM
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  obtain ⟨k₀, hk₀⟩ := pow_unbounded_of_one_lt (b * (l : ℝ) ^ r) hl1
  refine ⟨k₀, fun k hk => ?_⟩
  set L : ℝ := (l : ℝ) ^ (k + 2) with hL
  have hLpos : 0 < L := by positivity
  set t : ℝ := (l : ℝ) ^ (-((k : ℤ) + 2)) with htdef
  have ht : t = L⁻¹ := by
    rw [htdef, hL, ← zpow_natCast, ← zpow_neg]; push_cast; rfl
  have htpos : 0 < t := by rw [ht]; positivity
  have hH : ∀ g ∈ N k, ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ t := fun g hg => (hN k g).1 hg
  choose y hy using hcob (N k) t htpos hH
  set c : ℚ_[l] := ((l : ℚ_[l]) ^ (k + 2))⁻¹ with hc
  have hcnorm : ‖c‖ = L := by
    rw [hc, norm_inv, norm_pow, Padic.norm_p, inv_pow, inv_inv]
  have hnorm : ∀ g ∈ N k, ∀ i j, ‖c * ((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ 1 := by
    intro g hg i j
    rw [norm_mul, hcnorm]
    calc L * ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ L * t :=
          mul_le_mul_of_nonneg_left (hH g hg i j) hLpos.le
      _ = 1 := by rw [ht]; field_simp
  classical
  let a : n × n → ↥(GK K) → ℤ_[l] := fun p g =>
    padicClampInt l (c * ((ρ g : Matrix n n ℚ_[l]) - 1) p.1 p.2)
  have ha : ∀ p, ∀ σ ∈ N k,
      ((a p σ : ℤ_[l]) : ℚ_[l]) = c * ((ρ σ : Matrix n n ℚ_[l]) - 1) p.1 p.2 := by
    intro p σ hσ
    exact padicClampInt_coe l (hnorm σ hσ p.1 p.2)
  let x : n × n → ℂ_[l] := fun p => algebraMap ℚ_[l] ℂ_[l] c * y p.1 p.2
  have hbt : b * t ≤ ((l : ℝ)⁻¹) ^ r := by
    have h1 : (l : ℝ) ^ k₀ ≤ L := pow_le_pow_right₀ hl1.le (by omega)
    have h2 : b * (l : ℝ) ^ r ≤ L := by linarith
    rw [ht, inv_pow, ← div_eq_mul_inv, div_le_iff₀ hLpos, ← div_eq_inv_mul,
      le_div_iff₀ (by positivity)]
    exact h2
  refine ⟨n × n, inferInstance, x, a, ?_, ?_⟩
  · intro p σ hσ
    have hfix : Formalism.Per.σC (σ : GQ l) (algebraMap ℚ_[l] ℂ_[l] c) = algebraMap ℚ_[l] ℂ_[l] c := by
      simp only [hc, map_inv₀, map_pow, map_natCast]
    simp only [x]
    rw [ha p σ hσ, map_mul (Formalism.Per.σC (σ : GQ l)), hfix, map_mul]
    rw [show ∀ u v w : ℂ_[l], u * v - u * w - u * algebraMap ℚ_[l] ℂ_[l] (((ρ σ : Matrix n n ℚ_[l]) - 1) p.1 p.2)
        = u * (v - w - algebraMap ℚ_[l] ℂ_[l] (((ρ σ : Matrix n n ℚ_[l]) - 1) p.1 p.2)) by
          intros; ring]
    rw [norm_mul, norm_algebraMap', hcnorm]
    calc L * ‖_‖ ≤ L * (b * t ^ 2) := mul_le_mul_of_nonneg_left (hy p.1 p.2 σ hσ) hLpos.le
      _ = b * t := by rw [ht]; field_simp
      _ ≤ ((l : ℝ)⁻¹) ^ r := hbt
  · intro σ hσ hdiv
    rw [hN]
    intro i j
    obtain ⟨q, hq⟩ := hdiv (i, j)
    have h1 : ‖((a (i, j) σ : ℤ_[l]) : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r := by
      rw [← PadicInt.norm_def, hq, norm_mul, norm_pow, PadicInt.norm_p]
      calc ((l : ℝ)⁻¹) ^ r * ‖q‖ ≤ ((l : ℝ)⁻¹) ^ r * 1 :=
            mul_le_mul_of_nonneg_left (PadicInt.norm_le_one q) (by positivity)
        _ = _ := mul_one _
    rw [ha (i, j) σ hσ, norm_mul, hcnorm] at h1
    have h3 : (l : ℝ) ^ (-(((k + r : ℕ) : ℤ) + 2)) = ((l : ℝ)⁻¹) ^ r * L⁻¹ := by
      rw [hL, ← zpow_natCast, ← zpow_natCast, inv_zpow', ← zpow_neg, ← zpow_add₀ hl0.ne']
      congr 1; push_cast; ring
    rw [h3, le_mul_inv_iff₀ hLpos, mul_comm]
    exact h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOfInvariantMod
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.FilInv

open GlobalTheory.DRFil

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem graded_const (TT : LocTied l P AI) (K : FinExt l) (n : ℤ)
    (e : P.R.BdR) (he : e ∈ (P.PD K).Fil n)
    (hg : ∀ g, (P.PD K).actdR g e - e ∈ (P.PD K).Fil (n + 1)) :
    ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil n ∧
      e - algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil (n + 1) := by
  obtain ⟨Θ⟩ := GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l P AI TT
  by_cases hn : n = 0
  · subst hn
    rw [zero_add] at hg ⊢
    obtain ⟨y, hy, ey⟩ := GlobalTheory.MemLoc.invariants_finExt l K (Θ.θ e) (fun g hg' => by
      have h := (theta_sub_iff Θ K ((P.PD K).Fil_G _ _ _ he) he).1 (hg ⟨g, hg'⟩)
      rwa [P.PD_actdR, Θ.θ_act _ _ ((fil_iff _ _ _ _).1 he), GlobalTheory.MemLoc.locAinf_actC] at h)
    refine ⟨⟨y, hy⟩, alg_mem_fil_zero K _, ?_⟩
    rw [theta_sub_iff Θ K he (alg_mem_fil_zero K _), ← ey]
    exact (Θ.θ_Om y).symm
  · obtain ⟨κ, -, -, h0, h⟩ := graded_invariants TT Θ K n e he hg
    rw [h0 hn] at h
    exact ⟨0, by rw [map_zero]; exact Submodule.zero_mem _, by rwa [map_zero]⟩

theorem const_of_invariant_mod : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (a b : ℤ) (x : P.R.BdR), x ∈ (P.PD K).Fil a → (∀ g, (P.PD K).actdR g x - x ∈ (P.PD K).Fil b) → ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil a ∧ x - algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil b := by
  intro l _ P AI TT K a b x hx hg
  have hFa : Antitone fun a => (P.PD K).Fil a :=
    antitone_int_of_succ_le fun a => (P.PD K).Fil_anti a
  have h0 : ∀ m, m ≤ a → ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil a ∧
      x - algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil m := fun m hm =>
    ⟨0, by rw [map_zero]; exact Submodule.zero_mem _, by rw [map_zero, sub_zero]; exact hFa hm hx⟩
  rcases le_total b a with hba | hab
  · exact h0 b hba
  have key : ∀ m, a ≤ m → m ≤ b → ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil a ∧
      x - algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil m := by
    intro m hm
    induction m, hm using Int.leInduction with
    | base => exact fun _ => h0 a le_rfl
    | succ m hm ih =>
      intro hmb
      obtain ⟨c, hc, hxc⟩ := ih (by omega)
      obtain ⟨d, hd, hxd⟩ := graded_const TT K m _ hxc (fun g => by
        rw [map_sub, AlgEquiv.commutes, sub_sub_sub_cancel_right]
        exact hFa hmb (hg g))
      refine ⟨c + d, ?_, ?_⟩
      · rw [map_add (f := _)]
        exact Submodule.add_mem _ hc (hFa hm hd)
      · rwa [map_add, ← sub_sub]
  exact key b hab le_rfl

end GlobalTheory.FilInv
end

