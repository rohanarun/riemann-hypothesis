module

public import Mathlib
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0465
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0511
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0050
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0521
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinVerticalBound
section
noncomputable section

namespace GlobalTheory.CompanionTheory.EisHalf

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter _root_.Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem hgt_of_mem {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (ha : IsHgt K a) {k : G2 σ Y} (hk : k ∈ K) : a k = 1 := by
  have h1 : IsPar (1 : G2 σ Y) 1 := isPar_iff.2 ((Matrix.one_mul _).trans (Matrix.mul_one _).symm)
  have := ha.val 1 1 h1 k hk
  simpa using this

theorem hgt_mul {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (ha : IsHgt K a) {p : G2 σ Y} {t} (hp : IsPar p t) {k : G2 σ Y}
    (hk : k ∈ K) (u : G2 σ Y) : a (p * k * u) = a (p * k) * a (k * u) := by
  obtain ⟨q, v, hq, k', hk', e⟩ := ha.iwa (k * u)
  rw [mul_assoc, e, ← mul_assoc, ha.val _ _ (hp.mul hq) k' hk', ha.val p t hp k hk, ha.val q v hq k' hk', map_mul, map_mul,
    NNReal.coe_mul]

theorem exists_nhd_one {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (hK : IsCompact (K : Set (G2 σ Y))) (ac : Continuous a)
    (ha : IsHgt K a) (a0 : ∀ x, 0 < a x) :
    ∃ W : Set (G2 σ Y), IsOpen W ∧ (1 : G2 σ Y) ∈ W ∧ ∀ g, ∀ u ∈ W, a g / 2 ≤ a (g * u) ∧ a (g * u) ≤ 2 * a g := by
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have hn : IsOpen ((fun y : G2 σ Y × G2 σ Y => a (y.1 * y.2)) ⁻¹' Set.Ioo (1 / 2) 2) :=
    isOpen_Ioo.preimage (ac.comp continuous_mul)
  have hs : (K : Set (G2 σ Y)) ×ˢ ({1} : Set (G2 σ Y)) ⊆ (fun y : G2 σ Y × G2 σ Y => a (y.1 * y.2)) ⁻¹' Set.Ioo (1 / 2) 2 := by
    rintro ⟨k, u⟩ ⟨hk, hu⟩
    have hu' : u = 1 := hu
    subst hu'
    simp only [Set.mem_preimage, mul_one]
    rw [hgt_of_mem ha hk]
    norm_num
  obtain ⟨U, V, -, hV, hKU, h1V, hUV⟩ := generalized_tube_lemma hK isCompact_singleton hn hs
  refine ⟨V, hV, h1V rfl, fun g u hu => ?_⟩
  obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa g
  have h := hUV (show (k, u) ∈ U ×ˢ V from ⟨hKU hk, hu⟩)
  obtain ⟨h1, h2⟩ : 1 / 2 < a (k * u) ∧ a (k * u) < 2 := h
  rw [hgt_mul ha hp hk]
  have := a0 (p * k)
  constructor <;> nlinarith

theorem rpow_le_add {A r c c' : ℝ} (hA : 0 < A) (h1 : c ≤ r) (h2 : r ≤ c') : A ^ r ≤ A ^ c + A ^ c' := by
  have p := Real.rpow_pos_of_pos hA c
  have p' := Real.rpow_pos_of_pos hA c'
  rcases le_total A 1 with h | h
  · linarith [Real.rpow_le_rpow_of_exponent_ge hA h h1]
  · linarith [Real.rpow_le_rpow_of_exponent_le h h2]

theorem rpow_le_of_near {A B : ℝ} (hA : 0 < A) (h1 : A / 2 ≤ B) (h2 : B ≤ 2 * A) (e : ℝ) : B ^ e ≤ 2 ^ |e| * A ^ e := by
  have hB : 0 < B := by linarith
  rcases le_total 0 e with h | h
  · rw [abs_of_nonneg h, ← Real.mul_rpow (by norm_num) hA.le]
    exact Real.rpow_le_rpow hB.le h2 h
  · have k := Real.rpow_le_rpow_of_nonpos (half_pos hA) h1 h
    refine k.trans (le_of_eq ?_)
    rw [abs_of_nonpos h, div_eq_mul_inv, Real.mul_rpow hA.le (by norm_num), Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num),
      mul_comm]

theorem eis_half_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ t₀ : ℝ, ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), t₀ ≤ t → (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) → (∀ s : ℂ, t < s.re → (fun x => Ê s x) ∈ modFun σ Y) ∧ ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) ({s : ℂ | t < s.re} ×ˢ Set.univ) ∧ ∀ c c' : ℝ, t < c → ∃ (C : ℝ) (N : ℕ), ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ∀ x, ‖Ê s x‖ ≤ C * (ht2 x : ℝ) ^ N := by
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY b K a hb hK ha χ s₁ f hf
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨ac, a0⟩ := GlobalTheory.T.height_function_continuous_pos' F E σ B n Y r s hB hn hY b K a hb hK ha
  have kc := GlobalTheory.T.isCompact_standard_maximal F E σ B n Y r s hB hn hY b K a hb hK ha
  obtain ⟨C, hC⟩ := GlobalTheory.T.flat_section_growth_bound K a kc ha a0 χ s₁ f hf
  obtain ⟨σ₀, hG⟩ := GlobalTheory.T.eisenstein_series_convergent F E σ B n Y r s hB hn hY b K a hb hK ha
  obtain ⟨W, hW, h1W, hWa⟩ := exists_nhd_one kc ac ha a0
  refine ⟨σ₀ - n / 2, fun t Ê ht hE => ?_⟩
  have tb : ∀ (z : ℂ) (c c' : ℝ), c ≤ z.re → z.re ≤ c' → ∀ g,
      ‖flat a f s₁ z g‖ ≤ |C| * (a g ^ (c + (n : ℝ) / 2) + a g ^ (c' + (n : ℝ) / 2)) := fun z c c' h1 h2 g =>
    (hC z g).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_pos_of_pos (a0 g) _).le).trans
      (mul_le_mul_of_nonneg_left (rpow_le_add (a0 g) (by linarith) (by linarith)) (abs_nonneg C)))
  have gr : ∀ c c' : ℝ, t < c → ∃ (D : ℝ) (N : ℕ), ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ∀ x, ‖Ê s x‖ ≤ D * (ht2 x : ℝ) ^ N := by
    intro c c' hc
    have h1 : σ₀ < c + (n : ℝ) / 2 := by linarith
    have h2 : σ₀ < max c c' + (n : ℝ) / 2 := by linarith [le_max_left c c']
    obtain ⟨C₁, N₁, H₁⟩ := hG _ h1
    obtain ⟨C₂, N₂, H₂⟩ := hG _ h2
    refine ⟨|C| * (|C₁| + |C₂|), max N₁ N₂, fun z h1z h2z x => ?_⟩
    have hx : (1 : ℝ) ≤ ht2 x := one_le_heightGL F x.1
    have S := (H₁ x).1.add (H₂ x).1
    have hs := (hE z (by linarith) x).norm_le_of_bounded (S.mul_left |C|).hasSum
      (fun q => tb z c (max c c') h1z (h2z.trans (le_max_right c c')) _)
    refine hs.trans ?_
    rw [tsum_mul_left, (H₁ x).1.tsum_add (H₂ x).1, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
    have p1 : (ht2 x : ℝ) ^ N₁ ≤ (ht2 x : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ hx (le_max_left _ _)
    have p2 : (ht2 x : ℝ) ^ N₂ ≤ (ht2 x : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ hx (le_max_right _ _)
    have q0 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N₁ := pow_nonneg (by linarith) _
    have q1 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N₂ := pow_nonneg (by linarith) _
    rw [add_mul]
    exact add_le_add ((H₁ x).2.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) q0).trans
        (mul_le_mul_of_nonneg_left p1 (abs_nonneg _))))
      ((H₂ x).2.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) q1).trans (mul_le_mul_of_nonneg_left p2 (abs_nonneg _))))
  have ct : ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) ({s : ℂ | t < s.re} ×ˢ Set.univ) := by
    rintro ⟨z₀, x₀⟩ ⟨hz₀, -⟩
    have hz₁ : t < z₀.re := hz₀
    obtain ⟨c, hc1, hc2⟩ := exists_between hz₁
    obtain ⟨c', hc'⟩ := exists_gt z₀.re
    have h1 : σ₀ < c + (n : ℝ) / 2 := by linarith
    have h2 : σ₀ < c' + (n : ℝ) / 2 := by linarith
    obtain ⟨_, _, H₁⟩ := hG _ h1
    obtain ⟨_, _, H₂⟩ := hG _ h2
    let V : Set (G2 σ Y) := (fun x => x₀⁻¹ * x) ⁻¹' W
    have hV : IsOpen V := hW.preimage (continuous_const.mul continuous_id)
    let S : Set (ℂ × G2 σ Y) := {z : ℂ | c < z.re ∧ z.re < c'} ×ˢ V
    have hS : IsOpen S :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)).prod hV
    have mS : (z₀, x₀) ∈ S := ⟨⟨hc2, hc'⟩, by simpa [V] using h1W⟩
    have sumU : Summable fun q : Cos σ Y => |C| *
        (2 ^ |c + (n : ℝ) / 2| * a ((Quotient.out q).1 * x₀) ^ (c + (n : ℝ) / 2) +
          2 ^ |c' + (n : ℝ) / 2| * a ((Quotient.out q).1 * x₀) ^ (c' + (n : ℝ) / 2)) :=
      (((H₁ x₀).1.mul_left _).add ((H₂ x₀).1.mul_left _)).mul_left _
    have cts : ContinuousOn (fun y : ℂ × G2 σ Y => ∑' q : Cos σ Y, eisTerm (flat a f s₁ y.1) y.2 q) S := by
      refine continuousOn_tsum (fun q => Continuous.continuousOn ?_) sumU ?_
      · have cg : Continuous fun y : ℂ × G2 σ Y => (Quotient.out q).1 * y.2 := continuous_const.mul continuous_snd
        exact ((Complex.continuous_ofReal.comp (ac.comp cg)).cpow (continuous_fst.sub continuous_const)
          fun y => Complex.ofReal_mem_slitPlane.2 (a0 _)).mul (hf.cont.comp cg)
      · rintro q ⟨z, x⟩ ⟨⟨hz1, hz2⟩, hx⟩
        have hu := hWa ((Quotient.out q).1 * x₀) (x₀⁻¹ * x) hx
        rw [show (Quotient.out q).1 * x₀ * (x₀⁻¹ * x) = (Quotient.out q).1 * x by group] at hu
        exact (tb z c c' hz1.le hz2.le _).trans (mul_le_mul_of_nonneg_left (add_le_add
          (rpow_le_of_near (a0 _) hu.1 hu.2 _) (rpow_le_of_near (a0 _) hu.1 hu.2 _)) (abs_nonneg C))
    have ctE : ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) S :=
      cts.congr fun y hy => (hE y.1 (hc1.trans hy.1.1) y.2).tsum_eq.symm
    exact (ctE.continuousAt (hS.mem_nhds mS)).continuousWithinAt
  refine ⟨fun z hz => ?_, ct, gr⟩
  obtain ⟨D, N, hD⟩ := gr z.re z.re hz
  have cz : Continuous fun x => Ê z x :=
    ct.comp_continuous (Continuous.prodMk_right z) fun x => ⟨hz, trivial⟩
  have M1 : (1 : ℝ) ≤ max D 1 := le_max_right _ _
  have M0 : (0 : ℝ) < max D 1 := by linarith
  have Mc : ((max D 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 M0.ne'
  have e : (fun x => Ê z x) = ((max D 1 : ℝ) : ℂ) • ((((max D 1 : ℝ) : ℂ))⁻¹ • fun x => Ê z x) := by
    rw [smul_smul, mul_inv_cancel₀ Mc, one_smul]
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨cz.const_smul _, N, fun x => ?_⟩)
  have hx : (1 : ℝ) ≤ ht2 x := one_le_heightGL F x.1
  have q0 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N := pow_nonneg (by linarith) _
  rw [Pi.smul_apply, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg M0.le, inv_mul_le_iff₀ M0]
  exact (hD z le_rfl le_rfl x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) q0)

end GlobalTheory.CompanionTheory.EisHalf

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductLintegralLimit
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem isHermND_hypOne (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) :
    IsHermND σ (hypOne J) := by
  refine ⟨fun i j => ?_, fun h => ?_⟩
  · induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => change σ 0 = 0; simp
      | succ j =>
        induction j using Fin.cases with
        | zero => change σ 1 = 1; simp
        | succ j => change σ 0 = 0; simp
    | succ i =>
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => change σ 1 = 1; simp
        | succ j =>
          induction j using Fin.cases with
          | zero => change σ 0 = 0; simp
          | succ j => change σ 0 = 0; simp
      | succ i =>
        induction j using Fin.cases with
        | zero => change σ 0 = 0; simp
        | succ j =>
          induction j using Fin.cases with
          | zero => change σ 0 = 0; simp
          | succ j => exact hJ.1 i j
  · obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    have hrow : ∀ i, ∑ j, hypOne J i j * v j = 0 := fun i => congrFun hv0 i
    have h1 : v 1 = 0 := by
      have := hrow 0
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at this
      simpa [hypOne_zero_rest, hypOne_zero_zero, hypOne_zero_one] using this
    have h0 : v 0 = 0 := by
      have := hrow 1
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at this
      simpa [hypOne_one_rest, hypOne_one_zero, hypOne_one_one] using this
    have ht : J.mulVec (fun j : Fin M => v j.succ.succ) = 0 := by
      funext i
      have := hrow i.succ.succ
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at this
      simpa [Matrix.mulVec, dotProduct, hypOne_rest_rest, hypOne_rest_zero, hypOne_rest_one] using this
    have hz : (fun j : Fin M => v j.succ.succ) = 0 := by
      by_contra hne
      exact hJ.2 (Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hne, ht⟩)
    apply hv
    funext i
    induction i using Fin.cases with
    | zero => exact h0
    | succ i =>
      induction i using Fin.cases with
      | zero => exact h1
      | succ i => exact congrFun hz i

end Alg

theorem measurableSet_primV (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSet (primV σ J b v) := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  haveI : T2Space (Fv F v) := inferInstance
  obtain ⟨-, -, -, t2, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := t2
  obtain ⟨-, lc, sc, -, -, hact⟩ := GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hσ (M + 2) (hypOne J)
    (isHermND_hypOne σ J hJ) (Fv F v)
  haveI := lc
  haveI := sc
  haveI := GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_fv F E σ hσ 1 (M + 2) v
  have hc := (hact 1).1
  have hlat := (GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b 1 (M + 2)).2.2.2.1 v
  have hclopen : IsClopen (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)) :=
    ⟨hlat.1.isClosed, hlat.2⟩
  have hcl : IsClosed {g : HA (Fv F v) σ (hypOne J) | latStab σ (hypOne J) b v g} := by
    have hE : {g : HA (Fv F v) σ (hypOne J) | latStab σ (hypOne J) b v g} =
        ⋂ x : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E,
          {g | actW (Fv F v) σ (hypOne J) g x ∈ latV b v ↔ x ∈ latV b v} := by
      ext g
      simp [latStab]
    rw [hE]
    refine isClosed_iInter fun x => ?_
    have hcx : Continuous fun g : HA (Fv F v) σ (hypOne J) => actW (Fv F v) σ (hypOne J) g x :=
      hc.comp (continuous_id.prodMk continuous_const)
    have hp := hclopen.preimage hcx
    by_cases hx : x ∈ (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E))
    · have hs : {g : HA (Fv F v) σ (hypOne J) | actW (Fv F v) σ (hypOne J) g x ∈ latV b v ↔ x ∈ latV b v} =
          (fun g => actW (Fv F v) σ (hypOne J) g x) ⁻¹' latV b v := by
        ext g
        simp [hx]
      rw [hs]
      exact hp.1
    · have hs : {g : HA (Fv F v) σ (hypOne J) | actW (Fv F v) σ (hypOne J) g x ∈ latV b v ↔ x ∈ latV b v} =
          ((fun g => actW (Fv F v) σ (hypOne J) g x) ⁻¹' latV b v)ᶜ := by
        ext g
        simp [hx]
      rw [hs]
      exact hp.compl.1
  have hcont : Continuous fun g : HA (Fv F v) σ (hypOne J) => actW (Fv F v) σ (hypOne J) g (e0 _ M) :=
    hc.comp (continuous_id.prodMk continuous_const)
  have him : IsSigmaCompact (primV σ J b v) := by
    exact (isSigmaCompact_univ.of_isClosed_subset hcl (Set.subset_univ _)).image hcont
  obtain ⟨K, hK, hU⟩ := him
  rw [← hU]
  exact MeasurableSet.iUnion fun n => (hK n).measurableSet

theorem measurable_purePr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable Ψinf → (∀ v, Measurable (Ψ v)) → Measurable (purePr σ J b S Ψinf Ψ) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b S Ψinf Ψ hΨinf hΨ
  obtain ⟨hpi, hpf, hpv, -⟩ := GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b 1 (M + 2)
  haveI := GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_af F E σ hσ 1 (M + 2)
  haveI := GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_ainf F E σ hσ 1 (M + 2)
  haveI : ∀ v, BorelSpace (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) :=
    fun v => GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_fv F E σ hσ 1 (M + 2) v
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have hset : MeasurableSet {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E |
      ∀ v, v ∉ S → projV v (projFin y) ∈ primV σ J b v} := by
    have hE : {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E |
        ∀ v, v ∉ S → projV v (projFin y) ∈ primV σ J b v} =
        ⋂ v, ⋂ _ : v ∉ S, (fun y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E => projV v (projFin y)) ⁻¹'
          primV σ J b v := by
      ext y
      simp
    rw [hE]
    refine MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => ?_
    exact ((hpv v).comp hpf).measurable (measurableSet_primV F E σ hσ M J hJ d b v)
  unfold purePr
  refine Measurable.indicator ?_ hset
  refine (hΨinf.comp hpi.measurable).mul ?_
  refine Finset.measurable_prod _ fun v _ => ?_
  exact (hΨ v).comp ((hpv v).comp hpf).measurable

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMapLaw
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.Frob

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

def evalMap {π : Representation ℂ (GL (Fin (a + b)) k) V} {σ : Representation ℂ (GL (Fin a) k) W}
    {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ)) :
    V →ₗ[ℂ] TensorProduct ℂ W W' :=
  φ.toLinearMap ∘ₗ (twKer π (unipRad k (two (stdSum (rfl : a + b = a + b)))) 1).mkQ

theorem evalMap_law {π : Representation ℂ (GL (Fin (a + b)) k) V}
    {σ : Representation ℂ (GL (Fin a) k) W} {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ))
    (q : parab k (two (stdSum (rfl : a + b = a + b)))) (w : V) :
    evalMap φ (π q w) =
      (deltaHalf k (Two (Fin a) (Fin b)) (leviProj k _ q) : ℂ) •
        extTensor σ ρ ((leviTwo k (Fin a) (Fin b)).symm (leviProj k _ q)) (evalMap φ w) := by
  set xy := (leviTwo k (Fin a) (Fin b)).symm (leviProj k _ q) with hxy
  have hL : leviProj k (two (stdSum (rfl : a + b = a + b))) q = leviTwo k _ _ xy :=
    (MulEquiv.apply_symm_apply _ _).symm
  obtain ⟨u, hu, hpu⟩ := exists_levi_mul_unip k (two (stdSum (rfl : a + b = a + b))) q
  rw [hL] at hpu ⊢
  have hpu' : (q : GL (Fin (a + b)) k) =
      leviEmb k (two (stdSum (rfl : a + b = a + b))) (leviTwo k _ _ xy) * u := hpu
  have hmk : (Submodule.Quotient.mk (π u w) :
      Jacquet π (unipRad k (two (stdSum (rfl : a + b = a + b))))) = Submodule.Quotient.mk w := by
    rw [Submodule.Quotient.eq]
    refine Submodule.subset_span ⟨⟨u, hu⟩, w, ?_⟩
    simp
  have key : ∀ (M : Levi k (Two (Fin a) (Fin b))) (x : V),
      (Submodule.Quotient.mk (π (leviEmb k (two (stdSum (rfl : a + b = a + b))) M) x) :
        Jacquet π (unipRad k (two (stdSum (rfl : a + b = a + b))))) =
        (deltaHalf k (Two (Fin a) (Fin b)) M : ℂ) •
          jac (two (stdSum (rfl : a + b = a + b))) π M (Submodule.Quotient.mk x) := by
    intro M x
    rw [jac_mk, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  have hint := Representation.IntertwiningMap.isIntertwining _ _ φ xy
    (Submodule.Quotient.mk w : Jacquet π (unipRad k (two (stdSum (rfl : a + b = a + b)))))
  simp only [evalMap, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
  rw [hpu', map_mul, Module.End.mul_apply, key, hmk, map_smul]
  change _ • φ (jac₂ (stdSum (rfl : a + b = a + b)) π xy (Submodule.Quotient.mk w)) = _
  rw [hint]
  rfl

def frobMap {π : Representation ℂ (GL (Fin (a + b)) k) V} (hs : IsSmooth π)
    {σ : Representation ℂ (GL (Fin a) k) W} {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ)) :
    π.IntertwiningMap (prod₂ σ ρ) :=
  { toFun := fun v => ⟨⟨fun x => evalMap φ (π x v), fun q x => by
        show evalMap φ (π (q * x) v) = _
        rw [map_mul, Module.End.mul_apply]
        exact evalMap_law φ q (π x v)⟩,
      mem_smoothPart_of_nhds (Filter.mem_of_superset ((hs v).mem_nhds (by simp)) fun h hh => by
        have hh' : π h v = v := hh
        refine Subtype.ext (funext fun x => ?_)
        show evalMap φ (π (x * h) v) = evalMap φ (π x v)
        rw [map_mul, Module.End.mul_apply, hh'])⟩
    map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by
      show evalMap φ (π x (v + w)) = evalMap φ (π x v) + evalMap φ (π x w)
      rw [map_add (f := _), map_add (f := _)]))
    map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by
      show evalMap φ (π x (c • v)) = c • evalMap φ (π x v)
      rw [map_smul, map_smul]))
    isIntertwining' := fun h => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
      show evalMap φ (π x (π h v)) = evalMap φ (π (x * h) v)
      rw [map_mul, Module.End.mul_apply])) }

theorem frobMap_one {π : Representation ℂ (GL (Fin (a + b)) k) V} (hs : IsSmooth π)
    {σ : Representation ℂ (GL (Fin a) k) W} {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ)) (v : V) :
    (frobMap hs φ v).1.1 1 = φ (Submodule.Quotient.mk v) := by
  show evalMap φ (π 1 v) = _
  rw [map_one]
  rfl

theorem exists_injective_of_jac₂ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b : ℕ) (V W W' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (π : Representation ℂ (GL (Fin (a + b)) k) V) (σ : Representation ℂ (GL (Fin a) k) W)
    (ρ : Representation ℂ (GL (Fin b) k) W'), IsSmooth π → π.IsIrreducible →
    ∀ φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ), φ ≠ 0 →
      ∃ ψ : π.IntertwiningMap (prod₂ σ ρ), Function.Injective ψ := by
  intro k _ _ _ _ a b V W W' _ _ _ _ _ _ π σ ρ hs hπ φ hφ
  refine ⟨frobMap hs φ, ?_⟩
  haveI := hπ
  refine (Representation.IsIrreducible.injective_or_eq_zero (frobMap hs φ)).resolve_right fun h0 => hφ ?_
  ext v
  show φ (Submodule.Quotient.mk v) = 0
  rw [← frobMap_one hs φ v, h0]
  rfl

end GlobalTheory.CompanionTheory.Frob
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyOfSectionPlaces
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocHypSec

private theorem exists_heightOneSpectrum_under_maximalRealSubfield {E : Type} [Field E] [NumberField E] [IsCMField E]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) = v := by
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E))
    (Ideal.comap_bot_le_of_injective _ hinj)
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQ]
    exact Ideal.comap_bot_of_injective _ hinj
  exact ⟨⟨Q, hQp, hQne⟩, HeightOneSpectrum.ext hQ⟩

theorem eventually_cofinite_of_section :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → ∀ P : PlF E → Prop,
  (∀ᶠ w : {w : Pl E // w ∈ S} in cofinite, P (w.1.under (𝓞 (maximalRealSubfield E)))) → ∀ᶠ v in cofinite, P v := by
  intro E _ _ _ S hS P hP
  rw [Filter.eventually_cofinite] at hP ⊢
  refine (hP.image fun w : {w : Pl E // w ∈ S} => w.1.under (𝓞 (maximalRealSubfield E))).subset ?_
  intro v hv
  obtain ⟨w₀, hw₀⟩ := exists_heightOneSpectrum_under_maximalRealSubfield v
  obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w₀
  exact ⟨⟨u, huS⟩, show ¬P (u.under _) by rw [hu, hw₀]; exact hv, hu.trans hw₀⟩

end GlobalTheory.CompanionTheory.LocHypSec
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizableSchwartzOrbitalIntegral
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem pureN_isSchwartzBruhat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : (∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))), IsSchwartzArch φ → (∀ v, IsCompact (A v) ∧ IsOpen (A v)) → (∀ v, v ∉ S → A v = latV b v) → IsSchwartzBruhat (pureN φ A) := by
  intro F E _ _ _ _ _ σ _ M J _ n _ d b S φ A hφ hA hS
  have hc : IsCompact (boxFN A) := GlobalTheory.CompanionTheory.WhitFree.PureTuple.isCompact_boxF b S A (fun v => (hA v).1) hS
  have hcl : IsClosed (boxFN A) := GlobalTheory.CompanionTheory.WhitFree.PureTuple.isClosed_boxF b A fun v => (hA v).1
  have ho : IsOpen (boxFN A) := GlobalTheory.CompanionTheory.WhitFree.PureTuple.isOpen_boxF b S A (fun v => (hA v).2) hS
  refine isSchwartzBruhat_of_prod hφ (Φf := (boxFN A).indicator fun _ => (1 : ℂ)) ⟨?_, ?_⟩ fun _ => rfl
  · exact (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) ⟨hcl, ho⟩).isLocallyConstant
  · exact HasCompactSupport.intro' hc hcl fun Y hY => Set.indicator_of_notMem hY _

end GlobalTheory.CompanionTheory.SiegelND.Coef
end
end

