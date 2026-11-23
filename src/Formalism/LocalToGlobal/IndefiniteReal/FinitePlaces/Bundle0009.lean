module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FourVac

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FrameInt
section
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))

theorem frMapO_add (x y : WO S T) : frMapO S T βS βT (x + y) = frMapO S T βS βT x + frMapO S T βS βT y := by
  unfold frMapO
  rw [Matrix.map_add (toEAf D) (fun a b => (toEAf D).map_add a b), Matrix.mul_add, Matrix.add_mul]

theorem frMapO_zero : frMapO S T βS βT 0 = 0 := by
  unfold frMapO
  rw [Matrix.map_zero (toEAf D) (toEAf D).map_zero, Matrix.mul_zero, Matrix.zero_mul]

theorem frMapO_nsmul (k : ℕ) (x : WO S T) : frMapO S T βS βT (k • x) = k • frMapO S T βS βT x := by
  induction k with
  | zero => rw [zero_smul, zero_smul, frMapO_zero]
  | succ n ih => rw [succ_nsmul, succ_nsmul, frMapO_add, ih]

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemUniq
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def cF (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₐ[D.host.F] Af D.host.F ⊗[D.host.F] D.host.E :=
  Algebra.TensorProduct.map (AlgHom.id D.host.F (Af D.host.F)) D.sp.cm.sig

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a w =>
    show (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig)
      ((Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig) (a ⊗ₜ[D.host.F] w)) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    show a ⊗ₜ[D.host.F] star (star w) = _
    rw [star_star]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem finPart_cA (z : AE D) : finPart D (cA D z) = cF D (finPart D z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a w => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem cF_int {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) : cF D z ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a, ha, starO y, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem cF_cF (z : Af D.host.F ⊗[D.host.F] D.host.E) : cF D (cF D z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a w =>
    show a ⊗ₜ[D.host.F] star (star w) = _
    rw [star_star]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem intAE_mul {z z' : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) (hz' : z' ∈ intAE D) :
    z * z' ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, rfl⟩ := hx
    induction hz' using AddSubgroup.closure_induction with
    | mem x' hx' =>
      obtain ⟨a', ha', y', rfl⟩ := hx'
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact AddSubgroup.subset_closure ⟨a * a', intAf_mul ha ha', y * y', by push_cast; rfl⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx


set_option maxHeartbeats 800000 in
theorem idem_class (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ¬ Lev.IsConjPl (D := D) P P)
    (e₀ : AE D) (ι : D.host.E →ₐ[D.host.F] (belowPl P).adicCompletion D.host.F)
    (hs₀ : e₀ + cA D e₀ = phiE (belowPl P) 1)
    (hz : ∀ z : AE D, z * e₀ = e₀ * phiE (belowPl P) (compV (belowPl P) ι (finPart D z)))
    (hκ : compV (belowPl P) ι (finPart D e₀) = 1) (he₀ : e₀ * e₀ = e₀) (hc₀ : e₀ * cA D e₀ = 0)
    (e : AE D) (h1 : e * e = e) (h2 : e * cA D e = 0) (h3 : e + cA D e = phiE (belowPl P) 1) :
    e = e₀ ∨ e = cA D e₀ := by
  have hκφ : compV (belowPl P) ι (finPart D (phiE (belowPl P) 1)) = 1 := compV_phiE (belowPl P) ι 1
  have hsum : compV (belowPl P) ι (finPart D e) + compV (belowPl P) ι (finPart D (cA D e)) = 1 := by
    rw [← map_add (f := _), ← map_add (f := _), h3, hκφ]
  have hidem : compV (belowPl P) ι (finPart D e) * compV (belowPl P) ι (finPart D e) =
      compV (belowPl P) ι (finPart D e) := by rw [← map_mul, ← map_mul, h1]
  have heps : e * phiE (belowPl P) 1 = e := by rw [← h3, mul_add, h1, h2, add_zero]
  have heps₀ : e₀ * phiE (belowPl P) 1 = e₀ := by rw [← hs₀, mul_add, he₀, hc₀, add_zero]
  have hceps₀ : cA D e₀ * phiE (belowPl P) 1 = cA D e₀ := by
    have := congrArg (cA D) heps₀; rwa [map_mul, cA_phiE] at this
  have hA := hz e
  have hB : e * cA D e₀ = cA D e₀ * phiE (belowPl P) (compV (belowPl P) ι (finPart D (cA D e))) := by
    have := congrArg (cA D) (hz (cA D e))
    rwa [map_mul, map_mul, cA_cA, cA_phiE] at this
  have hdec : e = e₀ * phiE (belowPl P) (compV (belowPl P) ι (finPart D e)) +
      cA D e₀ * phiE (belowPl P) (compV (belowPl P) ι (finPart D (cA D e))) := by
    linear_combination hA + hB - e * hs₀ - heps
  have hq : compV (belowPl P) ι (finPart D e) * (compV (belowPl P) ι (finPart D e) - 1) = 0 := by
    linear_combination hidem
  rcases mul_eq_zero.1 hq with h0 | h1''
  · right
    have hc1 : compV (belowPl P) ι (finPart D (cA D e)) = 1 := by rw [h0, zero_add] at hsum; exact hsum
    rw [hdec, h0, hc1, phiE_zero, mul_zero, zero_add, hceps₀]
  · left
    have h1' : compV (belowPl P) ι (finPart D e) = 1 := by linear_combination h1''
    have hc0 : compV (belowPl P) ι (finPart D (cA D e)) = 0 := by rw [h1'] at hsum; linear_combination hsum
    rw [hdec, h1', hc0, phiE_zero, mul_zero, add_zero, heps₀]

theorem sglV_orth {F : Type} [Field F] [NumberField F] {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) :
    sglV v (1 : v.adicCompletion F) * sglV w 1 = 0 := by
  apply af_ext; intro u
  rw [map_mul, map_zero]
  by_cases hu : u = v
  · subst hu; rw [sglV_ne w _ h, mul_zero]
  · rw [sglV_ne v _ hu, zero_mul]

theorem phiE_orth {v w : HeightOneSpectrum (𝓞 D.host.F)} (h : v ≠ w) : phiE (D := D) v 1 * phiE w 1 = 0 := by
  unfold phiE
  rw [← map_mul]
  have : sA v 1 * sA w 1 = 0 := Prod.ext (by show (0 : Ainf D.host.F) * 0 = 0; rw [mul_zero]) (sglV_orth h)
  rw [this, map_zero]

theorem placeIdem_eq {w : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D w ε) : ε = sA w 1 := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  have : α = sglV w 1 := by
    apply af_ext; intro u
    by_cases hu : u = w
    · subst hu; rw [h1, sglV_same]
    · rw [h0 u hu, sglV_ne w _ hu]
  rw [this]; rfl

theorem below_of_idemAt {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D} (he : Formalism.L2.NTheta.IsIdemAt e P) :
    e + cA D e = phiE (belowPl P) 1 := by
  obtain ⟨⟨h1, h2, w, ε, hpl, hs⟩, hcl⟩ := he
  rw [placeIdem_eq hpl] at hs
  change e + cA D e = phiE w 1 at hs
  by_cases hw : w = belowPl P
  · rw [← hw]; exact hs
  exfalso
  have heps : e * phiE w 1 = e := by rw [← hs, mul_add, h1, h2, add_zero]
  have hint : finPart D e ∈ intAE D := by
    have h := hcl 1 one_ne_zero
    have h1P : (1 : 𝓞 D.host.E) ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    have := not_not.1 (mt h.2 h1P)
    rwa [show ((1 : 𝓞 D.host.E) : D.host.E)⁻¹ = 1 by simp, map_one, mul_one] at this
  have hne : ¬ (belowPl P).asIdeal ≤ w.asIdeal := by
    intro hle
    apply hw
    exact (HeightOneSpectrum.ext ((belowPl P).isMaximal.eq_of_le w.isPrime.ne_top hle)).symm
  obtain ⟨x, hxv, hxw⟩ := Set.not_subset.1 hne
  have hx0 : x ≠ 0 := fun h => hxw (h ▸ zero_mem _)
  have hy : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ P.asIdeal := hxv
  have hy0 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]; exact hx0
  have hnot := (hcl _ hy0).1 hy
  apply hnot
  have hxF : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E)⁻¹ =
      algebraMap D.host.F D.host.E ((x : D.host.F)⁻¹) := by rw [algebraMap_O, map_inv₀]
  have hv1 : Valued.v (((x : D.host.F) : w.adicCompletion D.host.F)) = 1 :=
    le_antisymm (val_coe_le_one w x) (not_lt.1 fun h => hxw ((val_coe_lt_one_iff w x).1 h))
  obtain ⟨c, hc⟩ : ∃ c : w.adicCompletion D.host.F, c = algebraMap D.host.F (w.adicCompletion D.host.F) ((x : D.host.F)⁻¹) * 1 :=
    ⟨_, rfl⟩
  have hc1 : Valued.v c ≤ 1 := by
    rw [hc, mul_one, map_inv₀, algebraMap_adic_eq, map_inv₀, hv1, inv_one]
  rw [hxF, incA_alg, ← heps, mul_assoc, mul_comm (phiE w 1), phiE_smul, ← hc, map_mul, finPart_phiE]
  exact intAE_mul hint (AddSubgroup.subset_closure ⟨sglV w c, sglV_int w ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ w).2 hc1), 1, by simp⟩)

theorem cA_mul_incA (z : AE D) (x : D.host.E) : cA D (z * incA D x) = cA D z * incA D (star x) := by
  rw [map_mul, cA_incA]

theorem conj_of_cA {P Q : HeightOneSpectrum (𝓞 D.host.E)} {e e' : AE D} (he : Formalism.L2.NTheta.IsIdemAt e P)
    (he' : Formalism.L2.NTheta.IsIdemAt e' Q) (hc : e' = cA D e) : Lev.IsConjPl (D := D) P Q := by
  intro x hx
  refine ⟨starO x, ?_, rfl⟩
  by_cases hx0 : x = 0
  · subst hx0
    have : starO (0 : 𝓞 D.host.E) = 0 := FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E (by
      show star ((0 : 𝓞 D.host.E) : D.host.E) = _; simp)
    rw [this]; exact zero_mem _
  have hs0 : starO x ≠ 0 := by
    intro h; apply hx0
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    have : star ((x : 𝓞 D.host.E) : D.host.E) = 0 := congrArg (fun y : 𝓞 D.host.E => (y : D.host.E)) h
    simpa using this
  rw [he'.2 _ hs0, hc]
  intro hmem
  apply (he.2 x hx0).1 hx
  have : finPart D (cA D e * incA D ((starO x : D.host.E)⁻¹)) = cF D (finPart D (e * incA D ((x : D.host.E)⁻¹))) := by
    rw [← finPart_cA, cA_mul_incA, coe_starO, star_inv₀]
  rw [this] at hmem
  have := cF_int hmem
  rwa [cF_cF] at this

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InvForm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

theorem exists_invForm (e₁ : AE D) (he : e₁ * cA D e₁ = 0) (Λ : AddSubgroup (WO S T))
    (hLL : ∀ x ∈ Λ, IsHalf e₁ x → ∀ y ∈ Λ, IsHalf (cA D e₁) y → ψ (symplO S T x y) = 1)
    (hdY : ∀ y, IsHalf (cA D e₁) y → (∀ x ∈ Λ, IsHalf e₁ x → ψ (symplO S T x y) = 1) → y ∈ Λ)
    (hfX : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ Λ, IsHalf e₁ u →
      ∃ r ∈ R, ∃ v ∈ Λ, IsHalf e₁ v ∧ u = r + k • v)
    (hfY : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ Λ, IsHalf (cA D e₁) u →
      ∃ r ∈ R, ∃ v ∈ Λ, IsHalf (cA D e₁) v ∧ u = r + k • v)
    (hoY : ∀ y, IsHalf (cA D e₁) y → ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ)
    (hlev : ∀ f, IsThetaFunO ψ S T f → ∃ k : ℕ, 0 < k ∧
      ∀ u ∈ Λ, (IsHalf e₁ u ∨ IsHalf (cA D e₁) u) → heisO ψ S T (k • u) f = f)
    {w : WO S T → ℂ} (hw : IsThetaFunO ψ S T w) (hwX : ∀ u ∈ Λ, IsHalf e₁ u → heisO ψ S T u w = w)
    (hwY : ∀ u ∈ Λ, IsHalf (cA D e₁) u → heisO ψ S T u w = w) (hw0 : w ≠ 0) :
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, (∀ i j, cA D e₁ * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f →
        ℓ (heisO ψ S T u f) = ℓ f) ∧ ℓ w ≠ 0 := by
  have mi := fun {x : WO S T} {H K : AddSubgroup (WO S T)} (h : x ∈ H ⊓ K) => AddSubgroup.mem_inf.1 h
  let N : Submodule ℂ (WO S T → ℂ) := Submodule.span ℂ
    {v | ∃ u ∈ halfSub S T (cA D e₁), ∃ G ∈ {f : WO S T → ℂ | IsThetaFunO ψ S T f}, v = heisL ψ S T u G - G}
  have hwN : w ∉ N := by
    intro hmem
    refine hw0 (Four.vac_eq_zero_of_mem_span (ρ := heisL ψ S T) (χ := fun t y => ψ (symplO S T t y))
      (L := Λ) (X := halfSub S T e₁) (Y := halfSub S T (cA D e₁))
      (fun y hy y' hy' => heisL_add_half ψ S T (cA_half_orth he) hy hy')
      (fun x _ y _ => heisL_comm ψ S T x y)
      (fun t t' y => by simp only [symplO_add_left, AddChar.map_add_eq_mul])
      (fun t y y' => by simp only [symplO_add_right, AddChar.map_add_eq_mul])
      (fun t y => psi_ne_zero ψ _)
      (fun x hx y hy => hLL x (mi hx).1 (mi hx).2 y (mi hy).1 (mi hy).2)
      (fun y hy h => hdY y hy fun x hx hxe => h x (AddSubgroup.mem_inf.2 ⟨hx, hxe⟩))
      (fun k hk => by
        obtain ⟨R, hR⟩ := hfX k hk
        exact finite_qt_of S T R fun u hu => by
          obtain ⟨r, hr, v, hv, hve, huv⟩ := hR u (mi hu).1 (mi hu).2
          exact ⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩)
      (fun k hk => by
        obtain ⟨R, hR⟩ := hfY k hk
        exact finite_qt_of S T R fun u hu => by
          obtain ⟨r, hr, v, hv, hve, huv⟩ := hR u (mi hu).1 (mi hu).2
          exact ⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩)
      (fun k hk t h => nsmul_eq_zero_WO S T hk h)
      (fun y hy => hoY y hy) {f | IsThetaFunO ψ S T f}
      (fun G hG => by
        obtain ⟨k, hk, hGk⟩ := hlev G hG
        exact ⟨k, hk, fun u hu => hGk u (mi hu).1 (Or.inl (mi hu).2),
          fun u hu => hGk u (mi hu).1 (Or.inr (mi hu).2)⟩)
      (fun u hu => hwX u (mi hu).1 (mi hu).2) (fun u hu => hwY u (mi hu).1 (mi hu).2) hmem)
  obtain ⟨ℓ, hℓw, hℓN⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hwN inferInstance
  refine ⟨ℓ, fun u hu f hf => ?_, hℓw⟩
  have hmem : heisL ψ S T u f - f ∈ N := Submodule.subset_span ⟨u, hu, f, hf, rfl⟩
  have h0 : ℓ (heisL ψ S T u f - f) = 0 := by
    have : ℓ (heisL ψ S T u f - f) ∈ N.map ℓ := Submodule.mem_map_of_mem hmem
    rw [hℓN] at this
    exact (Submodule.mem_bot ℂ).1 this
  rw [map_sub, sub_eq_zero] at h0
  exact h0

end Formalism.IndefR.Fin

end
end

