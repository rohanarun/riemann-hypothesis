module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0238

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.CharpolyConjGlAlt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial _root_.GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.GalN.V

private theorem charpoly_conj_gl {k : Type} [Field k] {n : ℕ} (g a : GL (Fin n) k) :
    ((g * a * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly =
      (a : Matrix (Fin n) (Fin n) k).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.CharpolyRootPow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial _root_.GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.GalN.V

section

variable {F Ω K : Type} [Field F] [Field Ω] [Algebra F Ω] [Field K] [Algebra F K] [Algebra K Ω]
  [IsScalarTower F K Ω]

private def resK (K : Type) [Field K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
    (σ : G F Ω) : K →ₐ[F] Ω :=
  (σ : Ω →ₐ[F] Ω).comp (IsScalarTower.toAlgHom F K Ω)

private theorem resK_apply (σ : G F Ω) (x : K) : resK K σ x = σ (algebraMap K Ω x) := rfl

private theorem lift_of_fix (σ : G F Ω) (h : ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x) :
    ∃ τ : G K Ω, (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω) τ = σ := by
  exact ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃+* Ω)) h, by ext x; rfl⟩

private theorem lift_of_res {σ τ : G F Ω} (h : resK K σ = resK K τ) :
    ∃ u : G K Ω, (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω) u = σ⁻¹ * τ := by
  apply lift_of_fix
  intro x
  have e := congrArg (fun f => f x) h
  simp only [resK_apply] at e
  rw [AlgEquiv.mul_apply, ← e]
  simp

private theorem exists_pow_lift [Finite (K →ₐ[F] Ω)] (s : G F Ω) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ u : G K Ω,
      (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω) u = s ^ m := by
  obtain ⟨a, b, hne, hab⟩ := Finite.exists_ne_map_eq_of_infinite (fun m : ℕ => resK K (s ^ m))
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨u, hu⟩ := lift_of_res (K := K) hab
    refine ⟨b - a, by omega, u, ?_⟩
    rw [hu, inv_mul_eq_iff_eq_mul, ← pow_add, Nat.add_sub_cancel' hlt.le]
  · obtain ⟨u, hu⟩ := lift_of_res (K := K) hab.symm
    refine ⟨a - b, by omega, u, ?_⟩
    rw [hu, inv_mul_eq_iff_eq_mul, ← pow_add, Nat.add_sub_cancel' hlt.le]

end

section

variable {F Ω K : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [Field K] [NumberField K]
  [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]

private theorem isFrob_descend {A : ValuationSubring Ω} {q : ℕ} {u : G K Ω}
    (h : IsFrob A q ((AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω) u)) : IsFrob A q u :=
  ⟨h.1, h.2⟩

private theorem ine_descend {A : ValuationSubring Ω} {u : G K Ω}
    (h : (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω) u ∈ Ine (F := F) A) :
    u ∈ Ine (F := K) A :=
  ⟨h.1, h.2⟩

private theorem isFrob_pow {A : ValuationSubring Ω} {q : ℕ} {σ : G F Ω} (h : IsFrob A q σ) (k : ℕ) :
    IsFrob A (q ^ k) (σ ^ k) := by
  obtain ⟨hd, hf⟩ := h
  have hint : ∀ τ : G F Ω, τ ∈ ValuationSubring.decompositionSubgroup F A →
      ∀ y : Ω, A.valuation y ≤ 1 → A.valuation (τ y) ≤ 1 := by
    intro τ hτ y hy
    by_contra hc
    push_neg at hc
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hc
    have hprod : ∀ z : Ω, z ≠ 0 → A.valuation z * A.valuation z⁻¹ = 1 := fun z hz => by
      rw [← map_mul, mul_inv_cancel₀ hz, map_one]
    have h1 : A.valuation (τ y⁻¹) < 1 := by
      by_contra h'
      push_neg at h'
      have e := hprod (τ y) (by simpa using hy0)
      rw [← map_inv₀ τ] at e
      exact absurd e (ne_of_gt (one_lt_mul_of_lt_of_le hc h'))
    rw [valuation_apply_lt_one_iff (A := A) hτ] at h1
    have e := hprod y hy0
    exact absurd e (ne_of_lt (lt_of_le_of_lt (mul_le_of_le_one_left' hy) h1))
  refine ⟨pow_mem hd k, ?_⟩
  induction k with
  | zero =>
    intro x _
    simp
  | succ k ih =>
    intro x hx
    set y := (σ ^ k) x with hydef
    have hy : A.valuation y ≤ 1 := hint _ (pow_mem hd k) x hx
    have hz : A.valuation (x ^ q ^ k) ≤ 1 := by
      rw [map_pow]
      exact pow_le_one' hx _
    have e : (σ ^ (k + 1)) x - x ^ q ^ (k + 1) = (σ y - y ^ q) + (y ^ q - (x ^ q ^ k) ^ q) := by
      rw [show σ ^ (k + 1) = σ * σ ^ k from pow_succ' σ k, show q ^ (k + 1) = q ^ k * q from pow_succ q k,
        pow_mul, AlgEquiv.mul_apply]
      ring
    rw [e]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (hf y hy) ?_)
    rw [← geom_sum₂_mul, map_mul]
    have hs : A.valuation (∑ i ∈ Finset.range q, y ^ i * (x ^ q ^ k) ^ (q - 1 - i)) ≤ 1 := by
      apply Valuation.map_sum_le
      intro i _
      rw [map_mul, map_pow, map_pow]
      exact mul_le_one' (pow_le_one' hy _) (pow_le_one' hz _)
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hs) (ih x hx)

private theorem ine_finite [Finite (K →ₐ[F] Ω)] {l : ℕ} [Fact l.Prime] {n : ℕ}
    (r : G F Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω)
    (h : ((r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) ''
      (Ine (F := K) A : Set (G K Ω))).Finite) :
    (r '' (Ine (F := F) A : Set (G F Ω))).Finite := by
  classical
  let c : (K →ₐ[F] Ω) → GL (Fin n) (Qbar l) := fun φ =>
    if hφ : ∃ g ∈ Ine (F := F) A, resK K g = φ then r (Classical.choose hφ) else 1
  refine ((Set.finite_univ.prod h).image (fun p : (K →ₐ[F] Ω) × GL (Fin n) (Qbar l) => c p.1 * p.2)).subset ?_
  rintro _ ⟨σ, hσ, rfl⟩
  have hex : ∃ g ∈ Ine (F := F) A, resK K g = resK K σ := ⟨σ, hσ, rfl⟩
  obtain ⟨hg, hgres⟩ := Classical.choose_spec hex
  obtain ⟨u, hu⟩ := lift_of_res (K := K) hgres
  have huI : u ∈ Ine (F := K) A := ine_descend (by rw [hu]; exact mul_mem (inv_mem hg) hσ)
  refine ⟨(resK K σ, r (AlgEquiv.restrictScalarsHom F u)), ⟨Set.mem_univ _, u, huI, rfl⟩, ?_⟩
  show c (resK K σ) * r ((AlgEquiv.restrictScalarsHom F) u) = r σ
  simp only [c, dif_pos hex]
  rw [hu, map_mul, map_inv, mul_inv_cancel_left]

end

private theorem charpoly_root_pow {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) k) {N : ℕ} (hN : 0 < N) {α : k}
    (h : (M ^ N).charpoly.IsRoot α) : ∃ a, M.charpoly.IsRoot a ∧ a ^ N = α := by
  rw [← Matrix.mem_spectrum_iff_isRoot_charpoly, spectrum.map_pow_of_pos M hN] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a, Matrix.mem_spectrum_iff_isRoot_charpoly.1 ha, rfl⟩

private theorem noLink_pow {l : ℕ} [Fact l.Prime] {n : ℕ} {x : GL (Fin n) (Qbar l)} {Q : ℕ}
    (h : NoLink x Q) {N : ℕ} (hN : 0 < N) : NoLink (x ^ N) (Q ^ N) := by
  intro α β hα hβ k hk heq
  rw [Units.val_pow_eq_pow_val] at hα hβ
  obtain ⟨a, ha, rfl⟩ := charpoly_root_pow _ hN hα
  obtain ⟨b, hb, rfl⟩ := charpoly_root_pow _ hN hβ
  apply h a b ha hb (N * k) (Nat.mul_pos hN hk)
  rw [pow_mul, pow_mul, mul_pow]
  push_cast at heq
  exact heq

theorem UpperTheory.GalN.V.L.wup :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω], Unlinked r → Unlinked (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) := by
  intro F Ω _ _ _ _ _ l _ n r K _ _ _ _ _ hU
  intro w hl A hA hfin
  haveI : Finite (K →ₐ[F] Ω) := inferInstance
  set v := HeightOneSpectrum.under (𝓞 F) w with hvdef
  have hAv : IsPlaceOver A v := GlobalTheory.AboveL.SatBC.isPlaceOver_under hA
  have hlv : (l : 𝓞 F) ∉ v.asIdeal := by
    intro hm
    apply hl
    have hw : algebraMap (𝓞 F) (𝓞 K) (l : 𝓞 F) ∈ w.asIdeal := hm
    simpa using hw
  obtain ⟨s, j, hj, hfrob, hnl⟩ := hU v hlv A hAv (ine_finite r A hfin)
  obtain ⟨m, hm, u, hu⟩ := exists_pow_lift (K := K) s
  set f := w.asIdeal.inertiaDeg (𝓞 F) with hfdef
  have hnorm : normV w = normV v ^ f := GlobalTheory.AboveL.SatBC.normV_under_pow F K w
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hnorm
      unfold normV at hnorm
      haveI := w.isPrime
      obtain ⟨hs, _⟩ := Nat.card_eq_one_iff_unique.1 hnorm
      exact not_subsingleton _ hs
    · exact h0
  have e : normV w ^ (j * m) = (normV v ^ j) ^ (m * f) := by
    rw [hnorm, ← pow_mul, ← pow_mul]
    ring_nf
  refine ⟨u ^ f, j * m, Nat.mul_pos hj hm, ?_, ?_⟩
  · apply isFrob_descend (F := F)
    rw [map_pow, hu, ← pow_mul, e]
    exact isFrob_pow hfrob (m * f)
  · rw [MonoidHom.comp_apply, map_pow, hu, ← pow_mul, e, map_pow r]
    exact noLink_pow hnl (Nat.mul_pos hm hf)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.IsRootCharpolySmul
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial _root_.GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.GalN.V

private theorem isRoot_charpoly_smul' {k : Type} [Field k] {n : ℕ} (c : k) (hc : c ≠ 0)
    (M : Matrix (Fin n) (Fin n) k) (x : k) :
    (c • M).charpoly.IsRoot (c * x) ↔ M.charpoly.IsRoot x := by
  have h : Matrix.scalar (Fin n) (c * x) - c • M = c • (Matrix.scalar (Fin n) x - M) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij, mul_sub]
  rw [Polynomial.IsRoot.def, Polynomial.IsRoot.def, Matrix.eval_charpoly, Matrix.eval_charpoly, h,
    Matrix.det_smul]
  simp [hc]

private theorem finite_char_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (μ : G F Ω →* (Qbar l)ˣ) (hμ : Continuous μ)
    {w : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) : (μ '' (Ine (F := F) A : Set (G F Ω))).Finite := by
  obtain ⟨ι⟩ : Nonempty (Qbar l ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  let m : G F Ω →* GL (Fin 1) (Qbar l) := UpperTheory.V.Af.tw 1 μ
  have hval : ∀ s, (m s : Matrix (Fin 1) (Fin 1) (Qbar l)) = (μ s : Qbar l) • (1 : Matrix (Fin 1) (Fin 1) (Qbar l)) := by
    intro s
    simpa [m] using UpperTheory.V.Af.tw_val (1 : G F Ω →* GL (Fin 1) (Qbar l)) μ s
  have hc : Continuous fun g => (m g : Matrix (Fin 1) (Fin 1) (Qbar l)) := by
    simp only [hval]
    exact (Units.continuous_val.comp hμ).smul continuous_const
  have h0 : (GlobalTheory.WeilDeligne.wdOf h hl ι m).mono0 :=
    WD.mono0_of_lpDim_eq_one (by rw [lpDim_wdOf]; simp)
  have hfin := (weilDeligneParam_monodromy_eq_zero_iff hl ι hc).1 h0
  refine (hfin.image Matrix.GeneralLinearGroup.det).subset ?_
  rintro _ ⟨s, hs, rfl⟩
  refine ⟨m s, ⟨s, hs, rfl⟩, ?_⟩
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, hval]

theorem UpperTheory.GalN.V.L.wtw :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (μ : G F Ω →* (Qbar l)ˣ), Continuous μ → Unlinked r → Unlinked (UpperTheory.V.Af.tw r μ) := by
  intro F Ω _ _ _ _ _ l _ n r μ hμ hU w hl A hA hfin
  have hμf := finite_char_ine μ hμ hl hA
  have hr : (r '' (Ine (F := F) A : Set (G F Ω))).Finite := by
    refine (Set.Finite.image2
      (fun (c : (Qbar l)ˣ) (x : GL (Fin n) (Qbar l)) => Matrix.GeneralLinearGroup.scalar (Fin n) c⁻¹ * x)
      hμf hfin).subset ?_
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨μ s, ⟨s, hs, rfl⟩, UpperTheory.V.Af.tw r μ s, ⟨s, hs, rfl⟩, ?_⟩
    apply Units.ext
    have e := UpperTheory.V.Af.tw_val r μ s
    simp only [Units.val_mul, e]
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, smul_smul]
  obtain ⟨s, j, hj, hs, hn⟩ := hU w hl A hA hr
  refine ⟨s, j, hj, hs, ?_⟩
  intro α β hα hβ k hk e
  set c : Qbar l := (μ s : Qbar l) with hcdef
  have hc : c ≠ 0 := Units.ne_zero _
  rw [UpperTheory.V.Af.tw_val] at hα hβ
  have back : ∀ x : Qbar l, (c • (r s : Matrix (Fin n) (Fin n) (Qbar l))).charpoly.IsRoot x →
      (r s : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot (c⁻¹ * x) := by
    intro x hx
    refine (isRoot_charpoly_smul' c hc _ _).1 ?_
    rwa [mul_inv_cancel_left₀ hc]
  refine hn _ _ (back _ hα) (back _ hβ) k hk ?_
  rw [mul_pow, mul_left_comm, mul_pow, e, mul_pow]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Wdown
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial _root_.GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.GalN.V

private theorem val_le_one {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (A : ValuationSubring Ω) (x : 𝓞 K) : A.valuation (algebraMap K Ω (x : K)) ≤ 1 := by
  have hi : IsIntegral ℤ (algebraMap K Ω (x : K)) := (x.2 : IsIntegral ℤ (x : K)).map (IsScalarTower.toAlgHom ℤ K Ω)
  have hA : IsIntegral A (algebraMap K Ω (x : K)) := hi.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hA
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

private theorem exists_place {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω]
    [Algebra F Ω] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A w) :
    ∃ v : HeightOneSpectrum (𝓞 K), IsPlaceOver A v := by
  let I : Ideal (𝓞 K) :=
    { carrier := {x | A.valuation (algebraMap K Ω (x : K)) < 1}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        have e : algebraMap K Ω ((a + b : 𝓞 K) : K) = algebraMap K Ω (a : K) + algebraMap K Ω (b : K) := by
          simp
        rw [e]
        exact Valuation.map_add_lt _ ha hb
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have e : algebraMap K Ω ((c • a : 𝓞 K) : K) = algebraMap K Ω (c : K) * algebraMap K Ω (a : K) := by
          simp
        rw [e, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_le_one A c)) ha }
  have hmem : ∀ x : 𝓞 K, x ∈ I ↔ A.valuation (algebraMap K Ω (x : K)) < 1 := fun _ => Iff.rfl
  have hprime : I.IsPrime := by
    refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
    · have := (hmem 1).1 (h ▸ Submodule.mem_top)
      simp at this
    · rw [hmem] at hab
      by_contra hcon
      push_neg at hcon
      obtain ⟨h1, h2⟩ := hcon
      rw [hmem, not_lt] at h1 h2
      have e1 := le_antisymm (val_le_one A a) h1
      have e2 := le_antisymm (val_le_one A b) h2
      have e : algebraMap K Ω ((a * b : 𝓞 K) : K) = algebraMap K Ω (a : K) * algebraMap K Ω (b : K) := by
        simp
      rw [e, map_mul, e1, e2] at hab
      simp at hab
  have hne : I ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    intro hI
    have h1 : A.valuation (algebraMap F Ω (x : F)) < 1 := (hA x).2 hx
    have h2 : algebraMap (𝓞 F) (𝓞 K) x ∈ I := by
      rw [hmem]
      rw [IsScalarTower.algebraMap_apply F K Ω] at h1
      exact h1
    rw [hI, Ideal.mem_bot] at h2
    exact hx0 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by simpa using h2))
  exact ⟨⟨I, hprime, hne⟩, fun x => (hmem x).symm⟩
end

