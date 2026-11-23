module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0113
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardFilterLowerHeckeRepsEqRelIndexPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0736

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BadPrimesSharp
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.BadPrimesS

open GlobalTheory.ColNorms.BadPrimes

theorem bad_primes_sharp : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → (∀ P ∈ rowSG Pr sel mu, P ∈ Pr.vGs) ∧ (∀ P ∈ Pr.vGs, ∃ i, P ∈ Pr.vG i ∧ Formalism.L2.Col.qOf P = Pr.g i ∧ ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal ∧ ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 ∧ ((Pr.g (1 - i) : ℕ) : 𝓞 X.E) ∉ P.asIdeal ∧ ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal ∧ Pr.piT u ∉ P.asIdeal) ∧ (∀ P ∈ Pr.vT u, ((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal) ∧ (∏ P : rowSG Pr sel mu, Formalism.L2.Col.qOf P.1) = (Pr.g 0 * Pr.g 1) ^ N.R.f ∧ Odd (Pr.T u) ∧ (∀ i, Odd (Pr.g i)) ∧ ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u ∧ (2 : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ h
  obtain ⟨⟨-, -, -, -, -, -, hX1, -, -, hPr, -, hc, -, -⟩, -, -, -, hmu, -⟩ := h
  subst hmu
  have hX := hX1.ok
  have h2 : 2 ∣ Pr.cond := by
    rw [hc, NumDatum.cond]
    exact N.H.toHostRaw.two_dvd_condN
  have hS : ∀ P, P ∈ Sall sel (1 : Tup X.F X.E X.K Sg) u ↔ P ∈ Pr.vT u ∨ P ∈ Pr.vGs := fun P => by
    rw [← rowSG_one sel Sg]
    exact Finset.mem_union
  refine ⟨fun P hP => rowSG_one sel Sg ▸ hP, fun P hP => ?_, fun P hP => T_mem hPr hP, ?_, odd_typePrime_of_two_dvd_cond hX hPr h2 u,
    odd_g hPr h2, fun P hP => ⟨fun h' => conjP_notMem hPr u ((hS _).1 hP) ((hS _).1 h'), ?_⟩⟩
  · obtain ⟨i, hi⟩ := exists_vG hP
    have hT : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun hT =>
      hPr.T_ne_g u i (eq_of_natCast_mem P (hPr.T_prime u) (hPr.g_prime i) hT (g_mem hPr hi))
    refine ⟨i, hi, hPr.vG_norm i P hi, g_mem hPr hi,
      (GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hPr i P hi).2, fun hg => ?_, hT,
      fun hπ => hT (hPr.piT_norm u ▸ Ideal.mul_mem_right _ _ hπ)⟩
    have := g_injective hPr (eq_of_natCast_mem P (hPr.g_prime _) (hPr.g_prime _) hg (g_mem hPr hi))
    fin_cases i <;> simp at this
  · rw [Finset.prod_coe_sort _ (fun P => Formalism.L2.Col.qOf P), rowSG_one, prod_qOf_vGs hPr,
      GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.card_eq_f N X pl.symm]
  · rcases (hS _).1 hP with h | h
    · exact two_notMem_vT hPr h2 h
    · obtain ⟨i, hi⟩ := exists_vG h
      intro hP2
      have := eq_of_natCast_mem P (hPr.g_prime i) Nat.prime_two (g_mem hPr hi) (by exact_mod_cast hP2)
      have ho := odd_g hPr h2 i
      rw [this] at ho
      exact absurd ho (by decide)

end GlobalTheory.Core.Ht2.BadPrimesS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmMultiplierIntegralSeriesAtInertPrimeProof
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda

theorem norm_eq_one_of_quad_root {l : ℕ} [Fact l.Prime] (x : ℂ_[l]) (N : ℕ) (hN : ¬ l ∣ N)
    (hx : x ^ 2 - x + (N : ℂ_[l]) = 0) : ‖x‖ = 1 := by
  have hNn : ‖(N : ℂ_[l])‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hN
  have hle : ∀ y : ℂ_[l], y ^ 2 - y + (N : ℂ_[l]) = 0 → ‖y‖ ≤ 1 := by
    intro y hy
    by_contra h
    push_neg at h
    have h1 : y ^ 2 = y - N := by linear_combination hy
    have h2 : ‖y - (N : ℂ_[l])‖ ≤ max ‖y‖ ‖(N : ℂ_[l])‖ := by
      rw [sub_eq_add_neg, ← norm_neg (N : ℂ_[l])]
      exact IsUltrametricDist.norm_add_le_max _ _
    rw [hNn, max_eq_left h.le] at h2
    have h3 : ‖y‖ ^ 2 ≤ ‖y‖ := by rw [← norm_pow, h1]; exact h2
    nlinarith
  have h1 := hle x hx
  have h2 := hle (1 - x) (by linear_combination hx)
  have hprod : x * (1 - x) = N := by linear_combination -hx
  have h4 : ‖x‖ * ‖1 - x‖ = 1 := by rw [← norm_mul, hprod, hNn]
  refine le_antisymm h1 ?_
  calc (1 : ℝ) = ‖x‖ * ‖1 - x‖ := h4.symm
    _ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg x)
    _ = ‖x‖ := mul_one _

theorem endOmega_holds : EndOmega := by
  intro d L hd hL l _ hl5 hld hsq ι g2 g3 hG n
  obtain ⟨-, -, h2, h3, hΔ, lam, hlam, rfl, rfl⟩ := hG
  have hc0 : ι.symm lam ≠ 0 := by simpa using hlam
  obtain ⟨L', -, hg2, hg3, -, hCM⟩ := _root_.GlobalTheory.homotheticLattice L (ι.symm lam) hc0
  have hιc : ι (ι.symm lam) = lam := ι.apply_symm_apply lam
  have e2 : ι L'.g₂ = lam ^ 4 * ι L.g₂ := by rw [hg2, map_mul, map_pow, hιc]
  have e3 : ι L'.g₃ = lam ^ 6 * ι L.g₃ := by rw [hg3, map_mul, map_pow, hιc]
  have hL' : HasCMBy d L' := hCM d hL
  have hq := _root_.GlobalTheory.omegaK_quadratic d hd
  set N := (d + 1) / 4 with hNdef
  have hN0 : 0 < N := by omega
  have hlN : ¬ l ∣ N := by
    intro h
    apply hsq
    refine ⟨1, ?_⟩
    have h4 : 4 * N = d + 1 := by omega
    have h5 : ((4 * N : ℕ) : ZMod l) = 0 := by
      rw [Nat.cast_mul, (ZMod.natCast_eq_zero_iff N l).mpr h, mul_zero]
    rw [h4] at h5
    push_cast at h5
    linear_combination h5
  have hιβ : ‖ι (omegaK d)‖ = 1 := by
    apply norm_eq_one_of_quad_root _ N hlN
    have := congrArg ι hq
    simpa using this
  have hNz : ∀ z, omegaK d * z ∈ L'.lattice → (N : ℂ) * z ∈ L'.lattice := by
    intro z hz
    have hz2 : omegaK d * (omegaK d * z) ∈ L'.lattice := hL' _ hz
    have e : (N : ℂ) * z = omegaK d * z - omegaK d * (omegaK d * z) := by linear_combination z * hq
    rw [e]
    exact sub_mem hz hz2
  have key := _root_.GlobalTheory.Honda.mulBy_coefLe_of_kernel_prime_to L' l hl5 ι (by rw [e2]; exact h2) (by rw [e3]; exact h3)
    (by rw [e2, e3]; exact hΔ) (omegaK d) N hL' hιβ hN0 hlN hNz
  rw [e2, e3] at key
  rw [Formalism.L2.Th1.A.uSerEq ℂ_[l]]
  exact key n

end GlobalTheory.Honda
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsUnramifiedHeightFunctionLowerBlock
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ParHecke

theorem isHgt_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (H : GL (A ⊕ D) k → ℝ), IsHgt ϖ H → IsHgt ϖ (fun m : GL D k => H (emb₂ k (Equiv.refl (A ⊕ D)) (1, m))) := by
  intro k _ _ _ _ A D _ _ _ _ ϖ H hH
  refine ⟨fun κ hκ g => ?_, fun e => ?_⟩
  · have hK : emb₂ k (Equiv.refl (A ⊕ D)) (1, κ) ∈ KO k (A ⊕ D) :=
      (mem_parahoric.1 (GlobalTheory.ChainStepSupp.emb₂_mem_parahoric (one_mem _) hκ)).1
    have e1 : emb₂ k (Equiv.refl (A ⊕ D)) (1, κ * g) =
        emb₂ k (Equiv.refl (A ⊕ D)) (1, κ) * emb₂ k (Equiv.refl (A ⊕ D)) (1, g) := by
      rw [← map_mul]; simp
    have e2 : emb₂ k (Equiv.refl (A ⊕ D)) (1, g * κ) =
        emb₂ k (Equiv.refl (A ⊕ D)) (1, g) * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ) := by
      rw [← map_mul]; simp
    exact ⟨by simp only [e1]; exact (hH.1 _ hK _).1, by simp only [e2]; exact (hH.1 _ hK _).2⟩
  · show H (emb₂ k (Equiv.refl (A ⊕ D)) (1, torusElt k D ϖ e)) = _
    rw [GlobalTheory.ChainStepSupp.emb₂_one_torusElt, mtor, hH.2]
    congr 2
    simp [sumAbs, Fintype.sum_sum_type]

end GlobalTheory.ParHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockCoefficientIsSphericalHeckeEigen
section
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
open Classical

namespace GlobalTheory.LowerHeckeEig

theorem esymm_map_mul_right' (t : ℂ) (M : Multiset ℂ) (j : ℕ) :
    (M.map fun b => b * t).esymm j = t ^ j * M.esymm j := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, ← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun s hs => ?_)
  have hc := (Multiset.mem_powersetCard.1 hs).2
  simp only [Function.comp, Multiset.prod_map_mul, Multiset.map_id', Multiset.map_const', Multiset.prod_replicate, hc]
  ring

theorem det_torus_indic {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : Type} [Fintype D] [DecidableEq D] (ϖ : kˣ) (s : Finset D) :
    GeneralLinearGroup.det (torusElt k D ϖ (indic s)) = ϖ ^ s.card := by
  ext
  rw [GeneralLinearGroup.val_det_apply, val_torusElt, det_diagonal, Units.val_pow_eq_pow_val]
  simp only [indic]
  simp only [apply_ite (fun n : ℤ => (ϖ : k) ^ n), zpow_one, zpow_zero]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

theorem genVal_shift (q a N : ℕ) (B : Multiset ℂˣ) (u : ℂˣ) (n : ℕ) :
    genVal q a N B n = genVal q 0 N (B.map (· * u⁻¹)) n * ((u : ℂ) ^ n * ((Real.sqrt q : ℝ) : ℂ) ^ (a * n)) := by
  have e : (B.map (· * u⁻¹)).map (fun b : ℂˣ => (b : ℂ)) =
      (B.map (fun b : ℂˣ => (b : ℂ))).map (fun z => z * ((u⁻¹ : ℂˣ) : ℂ)) := by
    simp [Multiset.map_map, Function.comp_def]
  simp only [genVal, e, esymm_map_mul_right', zero_mul, zero_add, pow_add, Units.val_inv_eq_inv_val, inv_pow]
  have := u.ne_zero
  field_simp

theorem realKey (a n : ℕ) (c q Hm Hmg : ℝ) (hc : 0 < c) (hq0 : 0 < q) (hq : c ^ 2 * Hmg = q ^ n * Hm)
    (h : a = 0 ∨ 0 < Hm) : (c * Real.sqrt Hmg) ^ a = (Real.sqrt q ^ n * Real.sqrt Hm) ^ a ∧ Real.sqrt Hmg ^ a ≠ 0 := by
  rcases h with h0 | hpos
  · simp [h0]
  · have hHmg : 0 < Hmg := by
      by_contra hle
      push_neg at hle
      have h3 : c ^ 2 * Hmg ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hle
      have h4 : 0 < q ^ n * Hm := mul_pos (pow_pos hq0 _) hpos
      linarith
    refine ⟨congrArg (· ^ a) ?_, pow_ne_zero _ (Real.sqrt_pos.2 hHmg).ne'⟩
    refine (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt hHmg.le, Real.sq_sqrt hpos.le, ← pow_mul, mul_comm n 2, pow_mul,
      Real.sq_sqrt hq0.le, hq]

theorem realNeg (n : ℕ) (c q Hm Hmg : ℝ) (hc : 0 < c) (hq0 : 0 ≤ q) (hq : c ^ 2 * Hmg = q ^ n * Hm)
    (h : Hm ≤ 0) : Hmg ≤ 0 := by
  by_contra hlt
  push_neg at hlt
  have h3 : 0 < c ^ 2 * Hmg := mul_pos (pow_pos hc 2) hlt
  have h4 : q ^ n * Hm ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hq0 _) h
  linarith

theorem alg1 (fmg P r ξm ξκ ξn ξκ' C : ℂ) (hr : r ≠ 0) (h1 : ξm ≠ 0) (h2 : ξκ ≠ 0) (h3 : ξn ≠ 0) (h4 : ξκ' ≠ 0)
    (hf : fmg = (ξm * (ξκ * (ξn * ξκ')))⁻¹ * P / r) :
    fmg * (ξn * ξm * (C * r)) = ξκ⁻¹ * (C * (ξκ'⁻¹ * P)) := by
  subst hf
  field_simp

theorem alg2 (S P lam0 ξn ξm Q Sg : ℂ) (h1 : ξn ≠ 0) (h2 : ξm ≠ 0) (h3 : Q ≠ 0) (h4 : Sg ≠ 0)
    (h : S * (ξn * ξm * (Q * Sg)) = lam0 * (ξn * Q) * P) : S = lam0 * (ξm⁻¹ * P / Sg) := by
  have hnq : ξn * Q ≠ 0 := mul_ne_zero h1 h3
  field_simp
  apply mul_left_cancel₀ hnq
  linear_combination h

theorem coeff_isEigen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V) (B : Multiset ℂˣ) (x : V) (ℓ : V →ₗ[ℂ] ℂ), IsGen π ξ ϖ B x → IsCoType π ξ ℓ → ∀ H : GL D k → ℝ, IsHgt ϖ H → ∀ f : GL D k → ℂ, (∀ m, f m = (((ξ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * ℓ (π (emb₂ k (Equiv.refl (A ⊕ D)) (1, m)) x) / ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A) → (∀ κ ∈ KO k D, ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) ∧ ∀ (s : Finset D) R, IsRepsK (torusElt k D ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (Fintype.card D) (B.map (· * (ξ ϖ)⁻¹)) s.card * f m := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ξ hξt hξu V _ _ π B x ℓ hgen hco H hH f hf
  have hbi : IsBiType ξ (fun h => ℓ (π h x)) := by
    intro j hj d hd g
    constructor
    · show ℓ (π (j * g) x) = _
      rw [map_mul, Module.End.mul_apply]
      exact hco j hj d hd _
    · show ℓ (π (g * j) x) = _
      rw [map_mul, Module.End.mul_apply, hgen.1 j hj d hd, map_smul, map_smul, smul_eq_mul]
  have hdet : ∀ κ : GL D k, ((GeneralLinearGroup.det κ : kˣ) : k) = (emb₂ k (Equiv.refl (A ⊕ D)) (1, κ)).1.toBlocks₂₂.det := by
    intro κ
    rw [val_emb_one, toBlocks_fromBlocks₂₂, GeneralLinearGroup.val_det_apply]
  have hφL : ∀ κ ∈ KO k D, ∀ m, ℓ (π (emb₂ k (Equiv.refl (A ⊕ D)) (1, κ * m)) x) =
      (ξ (GeneralLinearGroup.det κ) : ℂ) * ℓ (π (emb₂ k (Equiv.refl (A ⊕ D)) (1, m)) x) := by
    intro κ hκ m
    rw [← emb_mul_emb]
    exact (hbi _ (emb_mem hκ) _ (hdet κ) _).1
  have hφR : ∀ κ ∈ KO k D, ∀ m, ℓ (π (emb₂ k (Equiv.refl (A ⊕ D)) (1, m * κ)) x) =
      (ξ (GeneralLinearGroup.det κ) : ℂ) * ℓ (π (emb₂ k (Equiv.refl (A ⊕ D)) (1, m)) x) := by
    intro κ hκ m
    rw [← emb_mul_emb]
    exact (hbi _ (emb_mem hκ) _ (hdet κ) _).2
  refine ⟨fun κ hκ m => ⟨?_, ?_⟩, fun s R hR m => ?_⟩
  · rw [hf, hf, hφL κ hκ m, (hH.1 κ hκ m).1, map_mul, map_mul]
    have := (ξ (GeneralLinearGroup.det κ)).ne_zero
    push_cast
    field_simp
  · rw [hf, hf, hφR κ hκ m, (hH.1 κ hκ m).2, map_mul, map_mul]
    have := (ξ (GeneralLinearGroup.det κ)).ne_zero
    push_cast
    field_simp
  · set w := torusElt k D ϖ (indic s) with hw
    choose! κc hκc κ'c hκ'c hgκ using hR.1
    have hdec : ∀ g ∈ R, ∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * w * κ' :=
      fun g hg => ⟨_, hκc g hg, _, hκ'c g hg, hgκ g hg⟩
    choose! N hN using fun g hg => GlobalTheory.T.exists_finset_reps_maximalIdealMatrix_mod_mul k A D ϖ hϖ s g (hdec g hg)
    obtain ⟨R', hrep, hsum⟩ := _root_.GlobalTheory.LowerHecke.repsBuild k A D ϖ hϖ s R hR κc κ'c
      (fun g hg => ⟨hκc g hg, hκ'c g hg, hgκ g hg⟩) N hN
    have heig := hgen.2.2 s R' blockDet hrep
    set E := fun m : GL D k => emb₂ k (Equiv.refl (A ⊕ D)) (1, m) with hE
    set φ : GL (A ⊕ D) k → ℂ := fun h => ℓ (π h x) with hφ
    have hφR' : ∀ κ ∈ KO k D, ∀ m, φ (E (m * κ)) = (ξ (GeneralLinearGroup.det κ) : ℂ) * φ (E m) := hφR
    set c : GL D k → ℕ := fun g => (preLat m.1 ⊓ preLat (g⁻¹).1).relIndex (preLat m.1 ⊓ mLat k D) with hc
    set lamA := genVal (resCard k) (Fintype.card A) (Fintype.card D) B s.card with hlamA
    have e0 : ∀ J, ℓ (π (E m) (π J x)) = φ (E m * J) := fun J => by simp only [hφ, map_mul, Module.End.mul_apply]
    have h1 : lamA * φ (E m) = ∑ j ∈ R', (((ξ (blockDet j))⁻¹ : ℂˣ) : ℂ) * φ (E m * (j * mtor ϖ (indic s))) := by
      have := congrArg (fun v => ℓ (π (E m) v)) heig
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul] at this
      simp only [← e0]
      exact this
    have hterm : ∀ g ∈ R, ∑ ν ∈ N g, (((ξ (blockDet (lowU ν * E (κc g))))⁻¹ : ℂˣ) : ℂ) *
        φ (E m * (lowU ν * E (κc g) * mtor ϖ (indic s))) =
        (((ξ (GeneralLinearGroup.det (κc g)))⁻¹ : ℂˣ) : ℂ) * ((c g : ℂ) ^ Fintype.card A *
          ((ξ (GeneralLinearGroup.det (κ'c g)⁻¹) : ℂ) * φ (E (m * g)))) := by
      intro g hg
      have hy : m * κc g * w = m * g * (κ'c g)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        calc m * κc g * w * κ'c g = m * (κc g * w * κ'c g) := by group
          _ = m * g := by rw [← hgκ g hg]
      have hcnt := (_root_.GlobalTheory.LowerHeckeCount.card_filter_eq k A D ϖ hϖ s m g (m * κc g * w) (hdec g hg) ⟨_, inv_mem (hκ'c g hg), hy⟩ (N g)
        (hN g hg)).1
      have e1 : ∀ ν : Matrix D A k, E m * (lowU ν * E (κc g) * mtor ϖ (indic s)) = lowU (m.1 * ν) * E (m * κc g * w) := by
        intro ν
        simp only [hE]
        rw [mtor_eq, ← mul_assoc, ← mul_assoc, emb_mul_lowU, mul_assoc (lowU _), emb_mul_emb, mul_assoc (lowU _),
          emb_mul_emb]
      have hb : ∀ (ν : Matrix D A k) (κ : GL D k), blockDet (lowU ν * E κ) = GeneralLinearGroup.det κ :=
        fun ν κ => blockDet_lowU_emb ν κ
      simp only [hb, e1]
      have hs : ∀ (ν : Matrix D A k) (y : GL D k), φ (lowU ν * E y) = if ∃ ν₁ ν₂ : Matrix D A k, (∀ i a, valuation k (ν₁ i a) < 1) ∧
          (∀ i a, valuation k (ν₂ i a) < 1) ∧ ν = ν₁ + y.1 * ν₂ then φ (E y) else 0 :=
        fun ν y => _root_.GlobalTheory.LowerHeckeSupp.biType_lowU_emb k A D ξ hξt hξu φ hbi ν y
      simp only [hs, mul_ite, mul_zero]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hcnt]
      rw [hy, hφR' _ (inv_mem (hκ'c g hg))]
      simp only [hc]
      push_cast
      ring
    have hf' : ∀ m, f m = (((ξ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * φ (E m) / ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A := hf
    have h2 : lamA * φ (E m) = ∑ g ∈ R, (((ξ (GeneralLinearGroup.det (κc g)))⁻¹ : ℂˣ) : ℂ) * ((c g : ℂ) ^ Fintype.card A *
          ((ξ (GeneralLinearGroup.det (κ'c g)⁻¹) : ℂ) * φ (E (m * g)))) :=
      h1.trans ((hsum _).trans (Finset.sum_congr rfl hterm))
    have hqc : ∀ g ∈ R, ((c g : ℕ) : ℝ) ^ 2 * H (m * g) = (resCard k : ℝ) ^ s.card * H m := fun g hg =>
      GlobalTheory.T.unramifiedHeight_lattice_index_identity k D ϖ hϖ H hH m g s (hdec g hg) (mLat k D) (preLat m.1) (preLat (g⁻¹).1) (fun _ => Iff.rfl)
        (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    have hcpos : ∀ g ∈ R, (0 : ℝ) < c g := by
      intro g hg
      have hy : m * κc g * w = m * g * (κ'c g)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        calc m * κc g * w * κ'c g = m * (κc g * w * κ'c g) := by group
          _ = m * g := by rw [← hgκ g hg]
      exact_mod_cast (_root_.GlobalTheory.LowerHeckeCount.card_filter_eq k A D ϖ hϖ s m g (m * κc g * w) (hdec g hg) ⟨_, inv_mem (hκ'c g hg), hy⟩ (N g) (hN g hg)).2
    have hdg : ∀ g ∈ R, (ξ (GeneralLinearGroup.det (m * g)) : ℂ) = ξ (GeneralLinearGroup.det m) *
        (ξ (GeneralLinearGroup.det (κc g)) * ((ξ ϖ : ℂ) ^ s.card * ξ (GeneralLinearGroup.det (κ'c g)))) := by
      intro g hg
      conv_lhs => rw [hgκ g hg]
      simp only [hw, map_mul, det_torus_indic, map_pow, Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    have hlam := genVal_shift (resCard k) (Fintype.card A) (Fintype.card D) B (ξ ϖ) s.card
    have hq0' : (0 : ℝ) ≤ resCard k := Nat.cast_nonneg _
    by_cases hcase : Fintype.card A = 0 ∨ 0 < H m
    · have hq0 : (0 : ℝ) < resCard k := by
        have : 0 < resCard k := Nat.card_pos
        exact_mod_cast this
      have hσ : ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A ≠ 0 := by
        rcases hcase with h0 | hpos
        · simp [h0]
        · exact pow_ne_zero _ (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hpos).ne')
      have hQ : ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (Fintype.card A * s.card) ≠ 0 :=
        pow_ne_zero _ (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hq0).ne')
      have hgU : ∀ g ∈ R, f (m * g) * ((ξ ϖ : ℂ) ^ s.card * ξ (GeneralLinearGroup.det m) *
          (((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (Fintype.card A * s.card) * ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A)) =
          (((ξ (GeneralLinearGroup.det (κc g)))⁻¹ : ℂˣ) : ℂ) *
          ((c g : ℂ) ^ Fintype.card A * ((ξ (GeneralLinearGroup.det (κ'c g)⁻¹) : ℂ) * φ (E (m * g)))) := by
        intro g hg
        obtain ⟨h6, h7⟩ := realKey (Fintype.card A) s.card (c g) (resCard k) (H m) (H (m * g)) (hcpos g hg) hq0
          (hqc g hg) hcase
        have h8 : ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (Fintype.card A * s.card) * ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A =
            (c g : ℂ) ^ Fintype.card A * ((Real.sqrt (H (m * g)) : ℝ) : ℂ) ^ Fintype.card A := by
          have h9 : Real.sqrt (resCard k) ^ (Fintype.card A * s.card) * Real.sqrt (H m) ^ Fintype.card A =
              (c g : ℝ) ^ Fintype.card A * Real.sqrt (H (m * g)) ^ Fintype.card A := by
            rw [← mul_pow, h6, mul_pow, ← pow_mul, mul_comm s.card]
          exact_mod_cast h9
        have h10 : ((Real.sqrt (H (m * g)) : ℝ) : ℂ) ^ Fintype.card A ≠ 0 := by exact_mod_cast h7
        rw [h8]
        simp only [map_inv, Units.val_inv_eq_inv_val]
        refine alg1 _ _ _ _ _ _ _ _ h10 (ξ _).ne_zero (ξ _).ne_zero (pow_ne_zero _ (ξ ϖ).ne_zero) (ξ _).ne_zero ?_
        rw [hf' (m * g), Units.val_inv_eq_inv_val, hdg g hg]
      have hS := Finset.sum_mul R (fun g => f (m * g)) ((ξ ϖ : ℂ) ^ s.card * ξ (GeneralLinearGroup.det m) *
          (((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (Fintype.card A * s.card) * ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A))
      rw [Finset.sum_congr rfl hgU, ← h2, hlamA, hlam] at hS
      rw [hf' m, Units.val_inv_eq_inv_val]
      exact alg2 _ _ _ _ _ _ _ (pow_ne_zero _ (ξ ϖ).ne_zero) (ξ _).ne_zero hQ hσ (by rw [hS])
    · push_neg at hcase
      obtain ⟨ha, hle⟩ := hcase
      have hz : ∀ m', H m' ≤ 0 → f m' = 0 := by
        intro m' h
        rw [hf' m', Real.sqrt_eq_zero'.2 h, Complex.ofReal_zero, zero_pow ha, div_zero]
      rw [hz m hle, mul_zero]
      exact Finset.sum_eq_zero fun g hg => hz _ (realNeg s.card (c g) (resCard k) (H m) (H (m * g)) (hcpos g hg) hq0'
        (hqc g hg) hle)

end GlobalTheory.LowerHeckeEig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricHeckeGenericEigenvalueMapMul
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ParHecke

theorem esymm_map_mul_const (s : Multiset ℂ) (c : ℂ) (n : ℕ) :
    (s.map (· * c)).esymm n = c ^ n * s.esymm n := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, Multiset.sum_map_mul_left.symm]
  congr 1
  refine Multiset.map_congr rfl fun t ht => ?_
  have hc : t.card = n := (Multiset.mem_powersetCard.1 ht).2
  simp only [Function.comp_apply]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hc, mul_comm, Multiset.map_id']

theorem genVal_map_mul (q r N n : ℕ) (B : Multiset ℂˣ) (c : ℂˣ) :
    genVal q r N (B.map (· * c)) n = (c : ℂ) ^ n * genVal q r N B n := by
  unfold genVal
  have e : ((B.map (· * c)).map fun b : ℂˣ => (b : ℂ)) = (B.map fun b : ℂˣ => (b : ℂ)).map (· * (c : ℂ)) := by
    simp [Multiset.map_map, Function.comp_def]
  rw [e, esymm_map_mul_const]
  ring

end GlobalTheory.ParHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeightsRows
section
namespace GlobalTheory.Core.Ht2.StepRowsS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem weights_rows : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i < N.R.m → (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (W.lamTrue u i τ) (W.nuW u (i + 1) τ) (W.lamTrue u (i + 1) τ)) ∧ ∀ (z : RPl N.R) (l : Fin (N.R.N i)), (((W.nuW u (i + 1) (pl z)).w l : ℤ) : ℚ) = N.nu δ (i + 1) z l := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hyp i hi
  obtain ⟨-, hW, -, -, -, -, -, -, hS⟩ := hyp
  refine ⟨fun τ => StepRows.stepWeights W u hi τ fun l => ?_, fun z l => StepRows.nuW_eq_nu N W pl u δ hW hi z l⟩
  obtain ⟨z, rfl⟩ := pl.surjective τ
  have h1 := StepRows.nuW_eq_nu N W pl u δ hW hi z l
  have h2 := (hS.2.2.2.2.1 (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩) z l.1 l.2).1
  rw [← h1] at h2
  exact_mod_cast h2

end GlobalTheory.Core.Ht2.StepRowsS
end

