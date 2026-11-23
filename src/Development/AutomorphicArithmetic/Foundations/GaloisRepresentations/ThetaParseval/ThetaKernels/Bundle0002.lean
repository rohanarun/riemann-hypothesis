module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformArchimedeanCm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.EisensteinGrowthForms.GrowForms
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContDiffThetaTrRealFK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open scoped Classical ContDiff
noncomputable section
namespace GlobalTheory.ThetaSmoothF
set_option maxHeartbeats 2000000 in
theorem contDiff_thetaTr_realF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WOF F E nS nT), Continuous L →
            (∀ t, (L t).map (finPartF F E) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (w + L t) := by
  intro F E _ _ _ _ _ σ B0' hgood hψ nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ JA JB ξ0 hJA hJB κ _ co hrat Φ hΦ k L hLc hLf w0
  set ψ := B0'.ψ
  obtain ⟨P, Q, hPQ⟩ := darboux_real_coordsF (F := F) (E := E) nS nT κ co.e k L hLc hLf
  obtain ⟨Λ, hΛ⟩ := psiInf_eq_exp_linearF _ ψ hψ
  have hψ1 : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have hΛre : ∀ m, (Λ m).re = 0 := by
    intro m
    have h1 := hψ1 (pairA _ ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m) 0)
    have h2 := hΛ ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m)
    unfold psiInf at h2
    rw [h2, RingEquiv.apply_symm_apply, Complex.norm_exp] at h1
    exact Real.exp_eq_one_iff _ |>.mp h1
  suffices key : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ w,
      Summable (fun x : κ → F => co.rho ψ w Φ (fun i => algebraMap F (AF F) (x i))) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ Φ (w + L t) from
    (key Φ hΦ w0).2
  have rho_add : ∀ w (Φ₁ Φ₂ : (κ → AF F) → ℂ), co.rho ψ w (Φ₁ + Φ₂) = co.rho ψ w Φ₁ + co.rho ψ w Φ₂ := by
    intro w Φ₁ Φ₂; funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, mul_add]
  have rho_smul : ∀ w (c : ℂ) (Φ₁ : (κ → AF F) → ℂ), co.rho ψ w (c • Φ₁) = c • co.rho ψ w Φ₁ := by
    intro w c Φ₁; funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]; ring
  have rho_zero : ∀ w, co.rho ψ w (0 : (κ → AF F) → ℂ) = 0 := by
    intro w; funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    intro w
    obtain ⟨M, hM⟩ := _root_.GlobalTheory.LatSumSB.summable_sb_mul_decay F κ g hg (fun i => ((co.e w).1 i).2)
    let eM := InfiniteAdeleRing.ringEquiv_mixedSpace F
    let yv : (κ → F) → (κ → mixedEmbedding.mixedSpace F) := fun x i => mixedEmbedding F (x i)
    let ah : κ → mixedEmbedding.mixedSpace F := fun i => eM ((co.e w).1 i).1
    let bh : κ → mixedEmbedding.mixedSpace F := fun i => eM ((co.e w).2 i).1
    let c2 : mixedEmbedding.mixedSpace F := eM (⅟(2 : AF F)).1
    let B0 : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin k → ℝ) →ₗ[ℝ] ℂ :=
      LinearMap.mk₂ ℝ (fun y t => Λ (∑ i, y i * Q t i))
        (fun y₁ y₂ t => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)])
        (fun r y t => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul])
        (fun y t₁ t₂ => by simp only [map_add (f := _), Pi.add_apply, mul_add, Finset.sum_add_distrib])
        (fun r y t => by simp only [map_smul, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum])
    let B : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℂ :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.toContinuousLinearMap : ((Fin k → ℝ) →ₗ[ℝ] ℂ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ B0)
    have hB : ∀ y t, B y t = Λ (∑ i, y i * Q t i) := fun y t => rfl
    let hfun : (Fin k → ℝ) → ℂ := fun t => Λ (c2 * ∑ i, (ah i * Q t i + P t i * bh i + P t i * Q t i))
    have hPi : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin k → ℝ => P t i :=
      fun i => ((ContinuousLinearMap.proj i).comp P).contDiff
    have hQi : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin k → ℝ => Q t i :=
      fun i => ((ContinuousLinearMap.proj i).comp Q).contDiff
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) hfun :=
      Λ.contDiff.comp (contDiff_const.mul (ContDiff.sum fun i _ =>
        ((contDiff_const.mul (hQi i)).add ((hPi i).mul contDiff_const)).add ((hPi i).mul (hQi i))))
    have hre : ∀ y t, (B y t + hfun t).re = 0 := by
      intro y t; rw [hB, ← map_add (f := _)]; exact hΛre _
    let K : (κ → F) → ℂ := fun x =>
      ψ ((fun i => algebraMap F (AF F) (x i)) ⬝ᵥ (co.e w).2 + ⅟2 * ((co.e w).1 ⬝ᵥ (co.e w).2)) *
        g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) + ((co.e w).1 i).2)
    let G : (κ → F) → (Fin k → ℝ) → ℂ := fun x t => Complex.exp (B (yv x) t + hfun t) * f (yv x + ah + P t)
    let term : (κ → F) → (Fin k → ℝ) → ℂ := fun x t => K x * G x t
    have hid : ∀ x t, co.rho ψ (w + L t) (GlobalTheory.WeilM.pureA F f g)
        (fun i => algebraMap F (AF F) (x i)) = term x t := by
      intro x t
      have he : co.e (w + L t) = ((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0,
          (co.e w).2 + fun i => pairA F (eM.symm (Q t i)) 0) := by
        rw [map_add (f := _), hPQ t]; rfl
      have hy : ∀ i, eM (algebraMap F (AF F) (x i)).1 = yv x i := by
        intro i; simp only [yv, eM]; rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]; rfl
      have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
          (((fun i => algebraMap F (AF F) (x i)) +
            ((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0)) i).1) = yv x + ah + P t := by
        funext i
        change eM ((algebraMap F (AF F) (x i)).1 + (((co.e w).1 i).1 + eM.symm (P t i))) = _
        rw [map_add (f := _), map_add (f := _), RingEquiv.apply_symm_apply, hy i, ← add_assoc]
        rfl
      have h2 : (fun i => (((fun i => algebraMap F (AF F) (x i)) +
            ((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0)) i).2) =
          fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) + ((co.e w).1 i).2 := by
        funext i
        change (algebraMap F (AF F) (x i)).2 + (((co.e w).1 i).2 + 0) = _
        rw [add_zero]
        rfl
      have hL : co.rho ψ (w + L t) (GlobalTheory.WeilM.pureA F f g) (fun i => algebraMap F (AF F) (x i)) =
          ψ ((fun i => algebraMap F (AF F) (x i)) ⬝ᵥ ((co.e w).2 + fun i => pairA F (eM.symm (Q t i)) 0) +
            ⅟2 * (((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0) ⬝ᵥ
              ((co.e w).2 + fun i => pairA F (eM.symm (Q t i)) 0))) *
          (f (yv x + ah + P t) * g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) +
            ((co.e w).1 i).2)) := by
        rw [← h1, ← h2]
        show GlobalTheory.WeilM.schr ψ (co.e (w + L t)) _ _ = _
        rw [he]
        rfl
      rw [hL]
      let φ : AF F →+* mixedEmbedding.mixedSpace F := eM.toRingHom.comp (fstA F).toRingHom
      let φf : AF F →+* FiniteAdeleRing (𝓞 F) F := (sndA F).toRingHom
      have hφx : ∀ i, φ (algebraMap F (AF F) (x i)) = yv x i := hy
      have hφP : ∀ i, φ (pairA F (eM.symm (P t i)) 0) = P t i := fun i => eM.apply_symm_apply _
      have hφQ : ∀ i, φ (pairA F (eM.symm (Q t i)) 0) = Q t i := fun i => eM.apply_symm_apply _
      have hφa : ∀ i, φ ((co.e w).1 i) = ah i := fun i => rfl
      have hφb : ∀ i, φ ((co.e w).2 i) = bh i := fun i => rfl
      have hφ2 : φ ⅟2 = c2 := rfl
      have hφdef : ∀ z : AF F, eM z.1 = φ z := fun _ => rfl
      have hφfdef : ∀ z : AF F, z.2 = φf z := fun _ => rfl
      have hφpair : ∀ n, φ (pairA F (eM.symm n) 0) = n := fun n => eM.apply_symm_apply _
      have hφfpair : ∀ n, φf (pairA F (eM.symm n) 0) = 0 := fun n => rfl
      have hφfP : ∀ i, φf (pairA F (eM.symm (P t i)) 0) = 0 := fun i => rfl
      have hφfQ : ∀ i, φf (pairA F (eM.symm (Q t i)) 0) = 0 := fun i => rfl
      set X := (fun i => algebraMap F (AF F) (x i)) ⬝ᵥ (co.e w).2 + ⅟2 * ((co.e w).1 ⬝ᵥ (co.e w).2)
        with hX
      set m := ∑ i, yv x i * Q t i + c2 * ∑ i, (ah i * Q t i + P t i * bh i + P t i * Q t i) with hm
      have hsplit : (fun i => algebraMap F (AF F) (x i)) ⬝ᵥ
            ((co.e w).2 + fun i => pairA F (eM.symm (Q t i)) 0) +
          ⅟2 * (((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0) ⬝ᵥ
            ((co.e w).2 + fun i => pairA F (eM.symm (Q t i)) 0)) = X + pairA F (eM.symm m) 0 := by
        have hY : (fun i => algebraMap F (AF F) (x i)) ⬝ᵥ (fun i => pairA F (eM.symm (Q t i)) 0) +
            ⅟2 * ((co.e w).1 ⬝ᵥ (fun i => pairA F (eM.symm (Q t i)) 0) +
              (fun i => pairA F (eM.symm (P t i)) 0) ⬝ᵥ (co.e w).2 +
              (fun i => pairA F (eM.symm (P t i)) 0) ⬝ᵥ (fun i => pairA F (eM.symm (Q t i)) 0)) =
            pairA F (eM.symm m) 0 := by
          refine Prod.ext ?_ ?_
          · apply eM.injective
            rw [hφdef, hφdef, hφpair, hm]
            set_option synthInstance.maxHeartbeats 100000 in
              simp only [dotProduct, map_add (f := _), map_mul, map_sum, hφx, hφP, hφQ, hφa, hφb, hφ2, Finset.sum_add_distrib]
          · rw [hφfdef, hφfdef, hφfpair]
            set_option synthInstance.maxHeartbeats 100000 in
              simp only [dotProduct, map_add (f := _), map_mul, map_sum, hφfP, hφfQ, mul_zero, zero_mul, Finset.sum_const_zero,
              add_zero]
        rw [← hY, hX]
        simp only [dotProduct_add, add_dotProduct]
        ring
      have hψY : ψ (pairA F (eM.symm m) 0) = Complex.exp (B (yv x) t + hfun t) := by
        change psiInf F ψ (eM.symm m) = _
        rw [hΛ, show InfiniteAdeleRing.ringEquiv_mixedSpace F = eM from rfl, RingEquiv.apply_symm_apply, hm,
          map_add]
        rfl
      rw [hsplit, AddChar.map_add_eq_mul, hψY]
      simp only [term, K, G]
      ring
    have hK : ∀ x, ‖K x‖ =
        ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) + ((co.e w).1 i).2)‖ := by
      intro x; simp only [K, norm_mul, hψ1, one_mul]
    have hG : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G x) := fun x =>
      (Complex.contDiff_exp.comp ((B (yv x)).contDiff.add hsm)).mul
        ((f.smooth ⊤).comp (contDiff_const.add P.contDiff))
    have hsmooth : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (term x) := fun x => contDiff_const.mul (hG x)
    have hbd : ∀ (n : ℕ) (R : ℝ), ∃ u : (κ → F) → ℝ, Summable u ∧
        ∀ x t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (term x) t‖ ≤ u x := by
      intro n R
      obtain ⟨C, hC⟩ := GlobalTheory.ThetaSmooth.norm_iteratedFDeriv_exp_mul_schwartz_le f B hfun hsm hre ah P n M R
      refine ⟨fun x => C * (‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) +
        ((co.e w).1 i).2)‖ * ((1 + ‖yv x + 0‖) ^ M)⁻¹), (hM 0).mul_left C, fun x t ht => ?_⟩
      have e : term x = K x • G x := rfl
      rw [e, iteratedFDeriv_const_smul_apply ((hG x).contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul, hK]
      have h1 := hC (yv x) t ht
      calc _ ≤ ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) +
            ((co.e w).1 i).2)‖ * (C * ((1 + ‖yv x‖) ^ M)⁻¹) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = _ := by simp only [add_zero]; ring
    refine ⟨?_, ?_⟩
    · obtain ⟨u, hu, hu'⟩ := hbd 0 0
      refine Summable.of_norm_bounded hu fun x => ?_
      have h1 := hu' x 0 (by simp)
      rw [norm_iteratedFDeriv_zero, ← hid x 0] at h1
      simpa using h1
    · have e : (fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ (GlobalTheory.WeilM.pureA F f g) (w + L t)) =
          fun t => ∑' x, term x t := funext fun t => tsum_congr fun x => hid x t
      rw [e]
      exact GlobalTheory.T.contDiff_tsum_of_summable_iteratedFDeriv_bounds term hsmooth hbd
  | zero =>
    intro w
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, rho_zero, Pi.zero_apply]
    exact ⟨summable_zero, by simpa [GlobalTheory.WeilM.thetaSum] using contDiff_const⟩
  | add Φ₁ Φ₂ _ _ h1 h2 =>
    intro w
    refine ⟨by rw [rho_add]; exact (h1 w).1.add (h2 w).1, ?_⟩
    have e : (fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ (Φ₁ + Φ₂) (w + L t)) =
        fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ Φ₁ (w + L t) +
          GlobalTheory.WeilSchrodinger.thetaTr F co ψ Φ₂ (w + L t) := by
      funext t
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, rho_add, Pi.add_apply]
      exact (h1 (w + L t)).1.tsum_add (h2 (w + L t)).1
    rw [e]; exact (h1 w).2.add (h2 w).2
  | smul c Φ₁ _ h1 =>
    intro w
    refine ⟨by rw [rho_smul]; exact (h1 w).1.const_smul c, ?_⟩
    have e : (fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ (c • Φ₁) (w + L t)) =
        fun t => c * GlobalTheory.WeilSchrodinger.thetaTr F co ψ Φ₁ (w + L t) := by
      funext t
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, rho_smul, Pi.smul_apply, smul_eq_mul]
      exact tsum_mul_left
    rw [e]; exact contDiff_const.mul (h1 w).2
end GlobalTheory.ThetaSmoothF
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousThetaTrFK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
namespace GlobalTheory.ThetaTrContF
theorem continuous_thetaTrF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, Continuous (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B _ hψ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ _ _ κ _ co _ Φ hΦ
  haveI : IsModuleTopology (AF F) (Matrix (Fin nT) (Fin nS) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
  have hc : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  exact (GlobalTheory.ThetaTrCont.schA_cont F B.ψ hψ.1.1 hψ.1.2.1 hΦ).2.comp hc
end GlobalTheory.ThetaTrContF
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DerivHeisQuasiK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
noncomputable section
namespace GlobalTheory.ThetaDerivQuasi
open Formalism.IndefR.DatumF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end GlobalTheory.ThetaDerivQuasi
theorem GlobalTheory.ThetaDerivQuasi.deriv_heis_quasi_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : Formalism.IndefR.DatumF.WOF F E nS nT),
      deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (Formalism.IndefR.DatumF.ratWF γ + w)) 0 = B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) * deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ _ f hf L _ _ γ w
  have key : ∀ t : ℝ, Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (Formalism.IndefR.DatumF.ratWF γ + w) =
      B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) *
        Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f w := by
    intro t
    simp only [Formalism.IndefR.DatumF.heisOF]
    rw [add_assoc, hf.quasi γ (w + L t), GlobalTheory.ThetaDerivQuasi.symplOHF_add_left',
      GlobalTheory.ThetaDerivQuasi.symplOHF_add_right', neg_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    have h1 : B.ψ (Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) (L t)) *
        B.ψ (-Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) (L t)) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    linear_combination (B.ψ (Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ w (L t)) *
      B.ψ (-Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w) * f (w + L t)) * h1
  simp_rw [key]
  exact congrFun (deriv_const_mul_field' _) 0
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DictXOfK
section
set_option synthInstance.maxHeartbeats 200000

section
set_option linter.unusedSectionVars false
noncomputable section
namespace PositivityTheory.KCo
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype κ] {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {ψ : AddChar (AF F) ℂ}
variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
def DictX_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (B : Base F E)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) (χX χW : Chr F E), _root_.UpperTheory.TP.W.GoodK σ B → (∃ r s, X.IsHerm σ B r s) →
    (∃ r s, W.IsSkew σ B r s) → M.IsWeil B.ψ χX χW om → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∃ ι, M.IsLinBar B.ψ t 1 1 ι) ∧
      (∀ g₀ : GL (Fin n) (Fv F v), ∃ g ∈ UAt σ X (evFin F v), (mat g).map (piW t) = g₀) ∧
      (∀ h₀ : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), (mat h).map (piW t) = h₀) ∧
      ∀ ι, M.IsLinBar B.ψ t 1 1 ι →
        (∀ g ∈ UAt σ X (evFin F v), ∀ g₀ : GL (Fin n) (Fv F v), (mat g).map (piW t) = g₀ →
          Reads v ι (om (g, 1)) (omB (chrW χW t) (chrW χX t) g₀ 1)) ∧
        ∀ h ∈ UAt σ W (evFin F v), ∀ h₀ : GL (Fin d) (Fv F v), (mat h).map (piW t) = h₀ →
          Reads v ι (om (1, h)) (omB (chrW χW t) (chrW χX t) 1 h₀)
theorem dictX_of_k (hM : ModelEx) (hC : Cyc) (hA : AdSt) (hS : SecSt) (hU : ActsUniq) : _root_.PositivityTheory.KCo.DictX_k := by
  intro F E _ _ _ _ _ σ n d B X W M om χX χW hB ⟨_, _, hX⟩ ⟨_, _, hW⟩ hom v t
  obtain ⟨⟨sec, h⟩, -⟩ := hS F E σ hB.cm v t
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have uu : ∀ {m : ℕ} {J : Matrix (Fin m) (Fin m) E}, IsUnit J.det → IsUnit ((incM F J).map (piW t)) := fun {m J} hJ => by
    rw [incM_map h]
    exact ((Matrix.isUnit_iff_isUnit_det J).2 hJ).map (t : E →+* Fv F v).mapMatrix
  have hG : Grams σ t (incM F X.J) (incM F W.J) := by
    refine ⟨uu (GlobalTheory.CompanionTheory.Ar.RT.isUnit_det_of_cartan (F := F) X.J (B.emb w).1 1 (X.θ w) (by rw [one_smul]; exact hX.cartan w)),
      uu (GlobalTheory.CompanionTheory.Ar.RT.isUnit_det_of_cartan (F := F) W.J (B.emb w).1 Complex.I (W.θ w) (hW.cartan w)), 1, one_mul _,
      Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩
    · rw [incM_map' h, incM_map h, one_smul, hX.herm]; rfl
    · rw [incM_map' h, incM_map h, neg_smul, one_smul, hW.skew, map_neg]; rfl
  obtain ⟨ι₀, hι₀⟩ := exists_lm hM hA hB.std h hG M.co
  obtain ⟨hR, ⟨d', hd', hL⟩, -⟩ := hom
  obtain ⟨ε, -, hε, hε'⟩ := hG.sym
  refine ⟨⟨_, linBar_of_lm hA hU h hG hι₀⟩, fun g₀ => h.exists_ug hε hG.uA g₀, fun g₀ => h.exists_ug hε' hG.uB g₀, fun ι hι => ?_⟩
  have lm := lm_of_linBar hA hB.std h hG hι
  refine ⟨fun g hg g₀ e φ hφ => ?_, fun g hg g₀ e φ hφ => ?_⟩
  · obtain ⟨φ₁, h1, h2, h3⟩ := acts_formula hM hC hA hB.std h hG.swap (lm.swap hd') hL.isWeilB g hg g₀ e φ hφ
    refine ⟨φ₁, h1, h2, funext fun Y => ?_⟩
    have := congrFun h3 (ofM Yᵀ)
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Pi.smul_apply, rmL_apply, swH_apply, toM_ofM, smul_eq_mul] at this
    simp only [omB, gdet, map_one, Units.val_one, mul_one, apow_one, Matrix.mul_one]
    refine this.trans (congrArg _ (congrArg _ ?_))
    rw [← transpose_transpose (g₀.1ᵀ * Y), transpose_mul, transpose_transpose]
    rfl
  · obtain ⟨φ₁, h1, h2, h3⟩ := acts_formula hM hC hA hB.std h hG lm hR.isWeilB g hg g₀ e φ hφ
    refine ⟨φ₁, h1, h2, funext fun Y => ?_⟩
    have := congrFun h3 (ofM Y)
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Pi.smul_apply, rmL_apply, toM_ofM, smul_eq_mul] at this
    simp only [omB, gdet, map_one, Units.val_one, mul_one, one_mul, apow_one, transpose_one, Matrix.one_mul]
    exact this
end PositivityTheory.KCo
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DifferentiableAtHeisOFLineK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
noncomputable section
namespace GlobalTheory.HeisLineDiffF
open Formalism.IndefR.DatumF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
end GlobalTheory.HeisLineDiffF
open Formalism.IndefR.DatumF in
theorem GlobalTheory.HeisLineDiffF.differentiableAt_heisOF_line_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, DifferentiableAt ℝ (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f w) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ hψ f hf L hL hL0 w
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.HeisLineDiffF.exists_log hψ
  let φ : ℝ →+ ℂ :=
    { toFun := fun t => lam (symplOHF σ JS JT ξ₀ w (L t))
      map_zero' := by rw [map_zero L, GlobalTheory.HeisLineDiffF.symplOHF_zero_right, map_zero]
      map_add' := fun x y => by rw [map_add L, GlobalTheory.HeisLineDiffF.symplOHF_add_right, map_add (f := _)] }
  have hφ : Continuous φ := hl.comp (GlobalTheory.HeisLineDiffF.continuous_symplOHF σ JS JT ξ₀ w hL)
  let L' : (Fin 1 → ℝ) →+ WOF F E nS nT := L.comp (Pi.evalAddMonoidHom (fun _ : Fin 1 => ℝ) 0)
  have hL' : Continuous L' := hL.comp (continuous_apply 0)
  have hsm := hf.smooth 1 L' hL' (fun x => hL0 (x 0)) w
  have hg : ContDiff ℝ ∞ fun t : ℝ => f (w + L' (fun _ => t)) :=
    hsm.comp (contDiff_pi.2 fun _ => contDiff_id)
  have e : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f w) =
      fun t : ℝ => Complex.exp (φ t) * f (w + L' (fun _ => t)) := by
    funext t
    rw [heisOF, hlam _ (GlobalTheory.HeisLineDiffF.sndA_symplOHF σ JS JT ξ₀ w (L t) (hL0 t))]
    rfl
  rw [e]
  have hd1 : DifferentiableAt ℝ (fun t : ℝ => Complex.exp (φ t)) 0 :=
    ((φ.toRealLinearMap hφ).differentiableAt).cexp
  exact hd1.mul ((hg.differentiable (by simp)) 0)
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisHalfKAlt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace SiegelEisensteinSeries
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
def EisHalf_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ c : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ (t : ℝ) (v : ℂ → modFun σ Y), (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) ((v s).1 x)) ∧
        WHolo (growForms σ Y) v {s | t < s.re}
end SiegelEisensteinSeries
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisLeftRatK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.CompanionTheory.EisRat
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter _root_.Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
end GlobalTheory.CompanionTheory.EisRat
namespace GlobalTheory.CompanionTheory.EisRat
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter _root_.Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
theorem eis_left_rat_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → IsHecke F E χ → ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) → ∀ s : ℂ, t < s.re → ∀ γ ∈ rat2 σ Y, ∀ x, Ê s (γ * x) = Ê s x := by
  intro F E _ _ _ _ _ σ B n Y r s _ _ _ b K a _ _ hK χ s₁ f hf hχ t Ê hs s' hs' γ hγ x
  exact (law_flat hK hf s').eis_rat hχ (hs s' hs') hγ x
end GlobalTheory.CompanionTheory.EisRat
end
end
end

