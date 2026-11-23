module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0087
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdempotentFiniteRankAdjointCuspidal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0128
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
section
namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain _root_.Formalism.L2.Col Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem absNorm_eq_of_split_factor (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hv : DegOne v)
    {P P' : HeightOneSpectrum (𝓞 E)} (hne : P ≠ P')
    (hm : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = P.asIdeal * P'.asIdeal) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  obtain ⟨hq, hq2⟩ := hv
  constructor
  · have hr : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
      rw [← h2]
      exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm
    have h1 := Ideal.absNorm_algebraMap (𝓞 F) (𝓞 E) v.asIdeal
    rw [hm, hr, map_mul] at h1
    have hP : Ideal.absNorm P.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact P.isPrime.ne_top
    have hP' : Ideal.absNorm P'.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact P'.isPrime.ne_top
    obtain ⟨k, hk, e⟩ := (Nat.dvd_prime_pow hq).1 (Dvd.intro _ h1)
    interval_cases k
    · exact absurd (by simpa using e) hP
    · simpa using e
    · rw [e] at h1
      exact absurd ((Nat.mul_eq_left (pow_pos hq.pos 2).ne').1 h1) hP'
  · intro hmem
    obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)} := by
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact Ideal.absNorm_mem _
    have h3 := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 E))) hI
    rw [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.map_mul, hm, mul_assoc] at h3
    have h4 : P.asIdeal * P.asIdeal ∣ P.asIdeal * (P'.asIdeal * I.map (algebraMap (𝓞 F) (𝓞 E))) := by
      rw [← h3, ← sq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hmem
    have h5 := (mul_dvd_mul_iff_left P.ne_bot).1 h4
    rcases P.prime.dvd_or_dvd h5 with h6 | h6
    · rw [Ideal.dvd_iff_le] at h6
      exact hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top h6).symm)
    · rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at h6
      have h7 : v.asIdeal ≤ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) := by
        rw [← Ideal.map_le_iff_le_comap, hm]
        exact (Ideal.mul_le_inf).trans inf_le_left
      rw [← v.isMaximal.eq_of_le (Ideal.comap_ne_top _ P.isPrime.ne_top) h7] at h6
      apply hq2
      rw [← Ideal.span_singleton_le_iff_mem, hI, sq]
      exact Ideal.mul_mono_right h6

theorem absNorm_eq_of_splitAt (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v)
    (hv : DegOne v) {Q : HeightOneSpectrum (𝓞 E)} (hQ : Q.asIdeal.under (𝓞 F) = v.asIdeal) :
    Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal ∧ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 := by
  obtain ⟨P, P', hne, hm⟩ := hs
  have h1 : P.asIdeal * P'.asIdeal ≤ Q.asIdeal := by
    rw [← hm, Ideal.map_le_iff_le_comap, ← hQ]
  rcases Q.isPrime.mul_le.1 h1 with h | h
  · obtain rfl : P = Q := HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h)
    exact absNorm_eq_of_split_factor h2 hv hne hm
  · obtain rfl : P' = Q := HeightOneSpectrum.ext (P'.isMaximal.eq_of_le Q.isPrime.ne_top h)
    exact absNorm_eq_of_split_factor h2 hv hne.symm (hm.trans (mul_comm _ _))


omit [NumberField E] [Field E] [Algebra F E] in
theorem plc_eq_absNorm {v : HeightOneSpectrum (𝓞 F)} (hq : (Ideal.absNorm v.asIdeal).Prime) :
    Formalism.EigenvalueLevelCeiling.plc v = Ideal.absNorm v.asIdeal := by
  have h6 : ringChar (𝓞 F ⧸ v.asIdeal) ∣ Ideal.absNorm v.asIdeal := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  have := v.isPrime
  rcases (Nat.dvd_prime hq).1 h6 with h7 | h7
  · exact absurd h7 CharP.ringChar_ne_one
  · exact h7

end Split

theorem degOneUnram_of_mem_vG {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (i : Fin 2)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vG i) : DegOneUnram P := by
  have hcc : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  have hE : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, ← hX.card_Tau, mul_comm]
    rfl
  have hn : qOf P = Pr.g i := hPr.vG_norm i P hP
  refine ⟨hn ▸ hPr.g_prime i, ?_⟩
  rw [hn]
  refine GlobalTheory.SplitUnram.natCast_notMem_sq X.E X.conjO (X.conjO (Pr.piG i)) (Pr.g i) hcc (hPr.g_prime i) ?_ ?_ ?_
    (hPr.vG_norm i) P hP
  · rw [hcc, mul_comm]; exact hPr.piG_norm i
  · rw [hcc]; exact (hPr.piG_cop i).symm
  · rw [hE, ← hPr.vG_card i]; rfl

theorem levelPrimes : LevelPrimes := by
  classical
  intro X Pr sel S mu hX hPr hsel P
  by_cases hP : P.1 ∈ Pr.vGs
  · refine ⟨?_, fun h => absurd hP h⟩
    rcases Finset.mem_union.1 hP with h | h
    exacts [degOneUnram_of_mem_vG hX hPr 0 h, degOneUnram_of_mem_vG hX hPr 1 h]
  · rcases Finset.mem_union.1 P.2 with h1 | h1
    · exact absurd h1 hP
    unfold QE at h1
    split_ifs at h1 with h2
    · obtain ⟨v0, hv0, e⟩ := Finset.mem_image.1 h1
      have hv1 : v0 ∈ Qprime (mu : Chr X.F X.E X.K) := by simpa using hv0
      have hgood : GoodPl X.E S v0 := by
        by_contra hn
        have h4 := (Subgroup.mem_inf.1 mu.2).2
        exact hv1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v0) hn)
      obtain ⟨h3, h4⟩ := absNorm_eq_of_splitAt hX.rankE hgood.1 hgood.2.1 (Q := P.1) (e ▸ hsel v0)
      have h5 : qOf P.1 = Ideal.absNorm v0.asIdeal := h3
      refine ⟨⟨h5 ▸ hgood.2.1.1, h5 ▸ h4⟩, fun _ => ?_⟩
      rw [h5, ← plc_eq_absNorm hgood.2.1.1]
      exact hgood.2.2
    · simp at h1

end GlobalTheory.ColPeriod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AfIsoEqZeroIff
section
open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AfeLocTr

open HeightOneSpectrum

def IsIntAd {E : Type} [Field E] [NumberField E] (z : FiniteAdeleRing (𝓞 E) E) : Prop :=
  ∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (z Q) ≤ 1

theorem eq_zero_of_le_exp {x : WithZero (Multiplicative ℤ)} (h : ∀ n : ℕ, x ≤ WithZero.exp (-(n : ℤ))) : x = 0 := by
  by_contra hx
  have e := WithZero.exp_log hx
  set n : ℕ := (-WithZero.log x + 1).toNat
  have h1 := h n
  rw [← e, WithZero.exp_le_exp] at h1
  have h2 := Int.self_le_toNat (-WithZero.log x + 1)
  omega

theorem exists_gen {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    ∃ h : ℕ, 0 < h ∧ ∃ α : 𝓞 E, Ideal.span {α} = P.asIdeal ^ h := by
  have hP : P.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero P.ne_bot
  set h := Fintype.card (ClassGroup (𝓞 E))
  have hPh : P.asIdeal ^ h ∈ nonZeroDivisors (Ideal (𝓞 E)) := pow_mem hP h
  have h1 : ClassGroup.mk0 ⟨P.asIdeal ^ h, hPh⟩ = 1 := by
    have e : (⟨P.asIdeal ^ h, hPh⟩ : nonZeroDivisors (Ideal (𝓞 E))) = ⟨P.asIdeal, hP⟩ ^ h := Subtype.ext (by simp)
    rw [e, map_pow, pow_card_eq_one]
  haveI := (ClassGroup.mk0_eq_one_iff hPh).1 h1
  exact ⟨h, Fintype.card_pos, _, Ideal.span_singleton_generator _⟩

theorem comp_eq_zero_iff {E : Type} [Field E] [NumberField E] (z : FiniteAdeleRing (𝓞 E) E) (hz : IsIntAd z)
    (P : HeightOneSpectrum (𝓞 E)) :
    z P = 0 ↔ ∀ n : ℕ, ∃ π : 𝓞 E, π ≠ 0 ∧ π ∈ P.asIdeal ^ n ∧
      IsIntAd (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E π)⁻¹ * z) := by
  constructor
  · intro h0 n
    obtain ⟨h, hh, α, hα⟩ := exists_gen P
    have hα0 : α ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at hα
      exact pow_ne_zero _ P.ne_bot hα.symm
    have hαP : α ∈ P.asIdeal := Ideal.pow_le_self hh.ne' (hα ▸ Ideal.mem_span_singleton_self α)
    refine ⟨α ^ n, pow_ne_zero _ hα0, Ideal.pow_mem_pow hαP n, fun Q => ?_⟩
    show Valued.v (((algebraMap (𝓞 E) E (α ^ n))⁻¹ : E) * z Q) ≤ 1
    by_cases hQ : Q = P
    · subst hQ
      rw [h0, mul_zero, map_zero]
      exact zero_le'
    · have hαQ : α ∉ Q.asIdeal := by
        intro hm
        have h2 : P.asIdeal ^ h ≤ Q.asIdeal := by rw [← hα, Ideal.span_singleton_le_iff_mem]; exact hm
        exact hQ (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top (Q.isPrime.le_of_pow_le h2)).symm)
      have hv : Q.valuation E (algebraMap (𝓞 E) E (α ^ n)) = 1 :=
        (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) Q).2 fun hm => hαQ (Q.isPrime.mem_of_pow_mem n hm)
      rw [map_mul, valuedAdicCompletion_eq_valuation', map_inv₀, hv, inv_one, one_mul]
      exact hz Q
  · intro h
    refine (Valued.v.zero_iff).1 (eq_zero_of_le_exp fun n => ?_)
    obtain ⟨π, hπ0, hπn, hint⟩ := h n
    have h1 : Valued.v (((algebraMap (𝓞 E) E π)⁻¹ : E) * z P) ≤ 1 := hint P
    rw [map_mul, valuedAdicCompletion_eq_valuation', map_inv₀, valuation_of_algebraMap] at h1
    have hv0 : P.intValuation π ≠ 0 := P.intValuation_ne_zero π hπ0
    have h2 : Valued.v (z P) ≤ P.intValuation π := by
      calc Valued.v (z P) = P.intValuation π * ((P.intValuation π)⁻¹ * Valued.v (z P)) := by
            rw [← mul_assoc, mul_inv_cancel₀ hv0, one_mul]
        _ ≤ P.intValuation π * 1 := by gcongr
        _ = P.intValuation π := mul_one _
    exact h2.trans ((P.intValuation_le_pow_iff_mem π n).2 hπn)

end GlobalTheory.AfeLocTr

namespace GlobalTheory.AfeLocTr

open HeightOneSpectrum

theorem transport_zero {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (s : E ≃+* E')
    (Φ : FiniteAdeleRing (𝓞 E) E ≃+* FiniteAdeleRing (𝓞 E') E')
    (hΦ : ∀ x : E, Φ (algebraMap E _ x) = algebraMap E' _ (s x)) (hI : ∀ z, IsIntAd (Φ z) ↔ IsIntAd z)
    (P : HeightOneSpectrum (𝓞 E)) (Q : HeightOneSpectrum (𝓞 E'))
    (hPQ : ∀ a ∈ P.asIdeal, RingOfIntegers.mapRingEquiv s a ∈ Q.asIdeal)
    (z : FiniteAdeleRing (𝓞 E) E) (hz : IsIntAd z) (h0 : z P = 0) : Φ z Q = 0 := by
  rw [comp_eq_zero_iff z hz] at h0
  rw [comp_eq_zero_iff (Φ z) ((hI z).2 hz)]
  intro n
  obtain ⟨π, hπ0, hπn, hint⟩ := h0 n
  set f := RingOfIntegers.mapRingEquiv s
  refine ⟨f π, (map_ne_zero_iff _ f.injective).2 hπ0, ?_, ?_⟩
  · have h1 : Ideal.map f P.asIdeal ≤ Q.asIdeal := Ideal.map_le_iff_le_comap.2 hPQ
    have h2 : f π ∈ Ideal.map f (P.asIdeal ^ n) := Ideal.mem_map_of_mem _ hπn
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono h1 n h2
  · have e : algebraMap (𝓞 E') E' (f π) = s (algebraMap (𝓞 E) E π) := RingOfIntegers.mapRingEquiv_apply s π
    have e2 : algebraMap E' (FiniteAdeleRing (𝓞 E') E') (algebraMap (𝓞 E') E' (f π))⁻¹ * Φ z =
        Φ (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E π)⁻¹ * z) := by
      rw [map_mul, hΦ, map_inv₀ s, e]
    rw [e2]
    exact (hI _).2 hint

theorem afIso_eq_zero_iff : ∀ (F E F' E' : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E'] (s : E ≃+* E') (φ : AfE F E ≃+* AfE F' E'), (∀ x : E, φ (x ⊗ₜ[F] 1) = s x ⊗ₜ[F'] 1) → (∀ y, φ y ∈ RInt F' E' ↔ y ∈ RInt F E) → ∀ y ∈ RInt F E, ∀ P : HeightOneSpectrum (𝓞 E), (GlobalTheory.Mem.Col2.afIso F' E' (φ y) (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s) P) = 0 ↔ GlobalTheory.Mem.Col2.afIso F E y P = 0) := by
  intro F E F' E' _ _ _ _ _ _ _ _ _ _ s φ hφ hR y hy P
  set ι := GlobalTheory.Mem.Col2.afIso F E
  set ι' := GlobalTheory.Mem.Col2.afIso F' E'
  set Φ : FiniteAdeleRing (𝓞 E) E ≃+* FiniteAdeleRing (𝓞 E') E' := ι.symm.trans (φ.trans ι')
  have hΦa : ∀ w, Φ w = ι' (φ (ι.symm w)) := fun _ => rfl
  have hΦ : ∀ x : E, Φ (algebraMap E _ x) = algebraMap E' _ (s x) := fun x => by
    rw [hΦa, ← GlobalTheory.Mem.Col2.afIso_tmul_one F E x, RingEquiv.symm_apply_apply, hφ, GlobalTheory.Mem.Col2.afIso_tmul_one]
  have hI : ∀ w, IsIntAd (Φ w) ↔ IsIntAd w := fun w => by
    unfold IsIntAd
    rw [hΦa, ← GlobalTheory.Mem.Col2.mem_rInt_iff, hR, GlobalTheory.Mem.Col2.mem_rInt_iff, RingEquiv.apply_symm_apply]
  have hΦy : Φ (ι y) = ι' (φ y) := by rw [hΦa, RingEquiv.symm_apply_apply]
  have hz : IsIntAd (ι y) := (GlobalTheory.Mem.Col2.mem_rInt_iff F E y).1 hy
  set Q := HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s) P
  have hQ : ∀ b : 𝓞 E', b ∈ Q.asIdeal ↔ (RingOfIntegers.mapRingEquiv s).symm b ∈ P.asIdeal := fun b => Iff.rfl
  rw [← hΦy]
  constructor
  · intro h0
    have hΦ' : ∀ x : E', Φ.symm (algebraMap E' _ x) = algebraMap E _ (s.symm x) := fun x => by
      rw [RingEquiv.symm_apply_eq, hΦ, RingEquiv.apply_symm_apply]
    have hI' : ∀ w, IsIntAd (Φ.symm w) ↔ IsIntAd w := fun w => by
      rw [← hI, RingEquiv.apply_symm_apply]
    have hQP : ∀ a ∈ Q.asIdeal, RingOfIntegers.mapRingEquiv s.symm a ∈ P.asIdeal := fun a ha => by
      have e : RingOfIntegers.mapRingEquiv s.symm a = (RingOfIntegers.mapRingEquiv s).symm a := rfl
      rw [e]
      exact (hQ a).1 ha
    have := transport_zero s.symm Φ.symm hΦ' hI' Q P hQP (Φ (ι y)) ((hI _).2 hz) h0
    rwa [RingEquiv.symm_apply_apply] at this
  · intro h0
    refine transport_zero s Φ hΦ hI P Q (fun a ha => ?_) (ι y) hz h0
    rw [hQ, RingEquiv.symm_apply_apply]
    exact ha

end GlobalTheory.AfeLocTr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjOpInvolutive
section
noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CsdBack

theorem invTOp_involutive {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} :
    Function.Involutive (invTOp : Op E a → Op E a) := by
  intro o
  cases o with
  | fin k => simp only [invTOp]; congr 1
  | cpt k => simp only [invTOp]; congr 1; ext i j; simp [barK, Matrix.star_apply]
  | lie X =>
    simp only [invTOp]; congr 1
    funext i j
    exact neg_neg (X i j)

theorem conjOp_involutive {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ} :
    Function.Involutive (conjOp : Op L a → Op L a) := by
  intro o
  cases o with
  | fin k => simp only [conjOp]; congr 1; ext i j; simp [GlobalTheory.ThetaPull.cFin_cFin]
  | cpt k => simp only [conjOp]; congr 1; ext i j; simp [barK, Matrix.star_apply]
  | lie X => simp only [conjOp]; congr 1; ext i j; simp

theorem isCsd_of_paired : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (a : ℕ) (π : CuspSub L a), Paired π π invTOp → DualIsConj π → π.IsCsd := by
  intro hP L _ _ _ a π h1 h2
  obtain ⟨B₁, l1, r1, f1, c1, x1⟩ := h1
  obtain ⟨B₂, l2, r2, f2, c2, x2⟩ := h2
  obtain ⟨P, hP0, hPP, hfin, hadj⟩ := _root_.GlobalTheory.IdemAdj.exists_idem_adj hP L a π
  obtain ⟨P₁, e1⟩ := hadj invTOp (Or.inl rfl) B₁ l1 r1 f1 c1 x1
  obtain ⟨P₂, e2⟩ := hadj conjOp (Or.inr rfl) B₂ l2 r2 f2 c2 x2
  obtain ⟨v, hv⟩ : ∃ v, P v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP0 (LinearMap.ext h)
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual ℂ π.V, g (P v) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ (P v)).1 h)
  have hf : (g ∘ₗ P) ∘ₗ P = g ∘ₗ P := by rw [LinearMap.comp_assoc, hPP]
  obtain ⟨ψ₁, hψ₁⟩ := GlobalTheory.T.exists_representing_of_comp_idempotent_of_nondegenerate B₁ l1 r1 P P₁ hPP hfin e1 (g ∘ₗ P) hf
  obtain ⟨ψ₂, hψ₂⟩ := GlobalTheory.T.exists_representing_of_comp_idempotent_of_nondegenerate B₂ l2 r2 P P₂ hPP hfin e2 (g ∘ₗ P) hf
  have hne : ψ₁ ≠ 0 := by
    rintro rfl
    apply hg
    have := hψ₁ v
    simp only [map_zero, LinearMap.comp_apply] at this
    exact this.symm
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.ContraPair.iso_of_common_functional L a π invTOp conjOp invTOp_involutive conjOp_involutive B₁ B₂ l1 r1 f1 c1 x1
    l2 r2 f2 c2 x2 ψ₁ ψ₂ hne (fun φ => (hψ₁ φ).trans (hψ₂ φ).symm)
  exact GlobalTheory.T.isConjSelfDual_of_invTranspose_iso_cmConj L a π S hS

end GlobalTheory.CsdBack

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdjoinSplitHeckeGeneratorsDualsSpherical
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitGen

theorem top_step : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), conjPl P ≠ P → ∀ d : List ℤ, IsLab V P d → (∀ x ∈ d, 0 ≤ x) → (∃ x ∈ d, 0 < x) → ∃ m : ℕ, 0 < m ∧ ∃ c : List ℤ →₀ ℂ, (∀ d' ∈ c.support, (∀ x ∈ d', 0 ≤ x) ∧ d'.sum = d.sum ∧ (d'.map fun x => x ^ 2).sum < (d.map fun x => x ^ 2).sum) ∧ ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (d.map fun x => if 0 < x then x - 1 else x) 1) (opOf π P (Finsupp.single (dualLab (splitLab V.rank (d.filter fun x => 0 < x).length)) 1) u) = (m : ℂ) • opOf π P (Finsupp.single d 1) u + opOf π P c u := _root_.GlobalTheory.SplitTopStep.top_step

theorem central_shift : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), conjPl P ≠ P → ∀ (d : List ℤ) (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (splitLab V.rank V.rank) 1) (opOf π P (Finsupp.single d 1) u) = opOf π P (Finsupp.single (d.map fun x => x - 1) 1) u := _root_.GlobalTheory.CentralShift.central_shift

section Gen

variable {D : D7} (V : HSp D) (P : Pl D.host.E) {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M)

def gens : Set (Module.End ℂ M) :=
  {x | ∃ k, k ≤ V.rank ∧ (x = opOf π P (Finsupp.single (splitLab V.rank k) 1) ∨
    x = opOf π P (Finsupp.single (dualLab (splitLab V.rank k)) 1))}

def Good (c : List ℤ →₀ ℂ) : Prop :=
  ∃ a ∈ Algebra.adjoin ℂ (gens V P π), ∀ u : M, (∀ k ∈ hyp V P, π k u = u) → a u = opOf π P c u

variable {V P π}

theorem opOf_eq_sum (c : List ℤ →₀ ℂ) (u : M) :
    opOf π P c u = ∑ d ∈ c.support, c d • opOf π P (Finsupp.single d 1) u := by
  rw [opOf, Finsupp.sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [LinearMap.smul_apply, GlobalTheory.SphLabelOps.opOf_single, LinearMap.sum_apply]

theorem good_of_support {c : List ℤ →₀ ℂ} (h : ∀ d ∈ c.support, Good V P π (Finsupp.single d 1)) :
    Good V P π c := by
  classical
  choose a ha he using h
  refine ⟨∑ d ∈ c.support.attach, c d • a d.1 d.2, Subalgebra.sum_mem _ fun d _ => Subalgebra.smul_mem _ (ha _ _) _,
    fun u hu => ?_⟩
  rw [opOf_eq_sum, LinearMap.sum_apply, ← Finset.sum_attach c.support]
  exact Finset.sum_congr rfl fun d _ => by rw [LinearMap.smul_apply, he _ _ u hu]

theorem good_gen {x : Module.End ℂ M} (hx : x ∈ gens V P π) : x ∈ Algebra.adjoin ℂ (gens V P π) :=
  Algebra.subset_adjoin hx

theorem good_nonlab {d : List ℤ} (h : ¬ IsLab V P d) : Good V P π (Finsupp.single d 1) := by
  refine ⟨0, Subalgebra.zero_mem _, fun u _ => ?_⟩
  rw [GlobalTheory.SphLabelOps.opOf_single, Hk3.rep, dite_eq_right h, Finset.sum_empty, LinearMap.zero_apply]

theorem fixed_opOf (c : List ℤ →₀ ℂ) {u : M} (hu : ∀ k ∈ hyp V P, π k u = u) : ∀ k ∈ hyp V P, π k (opOf π P c u) = opOf π P c u :=
  (GlobalTheory.SphLabelOps.label_operators V P).2.1 c M π u hu

theorem good_nonneg (hP : conjPl P ≠ P) : ∀ s q : ℕ, ∀ d : List ℤ, (∀ x ∈ d, 0 ≤ x) → d.sum = (s : ℤ) →
    (d.map fun x => x ^ 2).sum = (q : ℤ) → Good V P π (Finsupp.single d 1) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ihs =>
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ihq =>
  intro d hd hs hq
  by_cases hl : IsLab V P d
  swap
  · exact good_nonlab hl
  by_cases hpos : ∃ x ∈ d, 0 < x
  · obtain ⟨m, hm, c, hc, hrel⟩ := top_step V P hP d hl hd hpos
    set d1 := d.map fun x => if 0 < x then x - 1 else x with hd1
    have hd1n : ∀ x ∈ d1, 0 ≤ x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      have := hd y hy
      split_ifs <;> omega
    have hlt : d1.sum < d.sum := by
      have := List.sum_lt_sum (l := d) (fun x => if 0 < x then x - 1 else x) id
        (fun x _ => by simp only [id]; split_ifs <;> omega)
        (by obtain ⟨x, hx, hx0⟩ := hpos; exact ⟨x, hx, by simp only [id]; rw [if_pos hx0]; omega⟩)
      simpa using this
    have hs1 : 0 ≤ d1.sum := List.sum_nonneg hd1n
    have hq1 : 0 ≤ (d1.map fun x => x ^ 2).sum := List.sum_nonneg fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      positivity
    have g1 : Good V P π (Finsupp.single d1 1) :=
      ihs d1.sum.toNat (by omega) _ d1 hd1n (by omega) (Int.toNat_of_nonneg hq1).symm
    have gc : Good V P π c := good_of_support fun d' hd' => by
      obtain ⟨h1, h2, h3⟩ := hc d' hd'
      have h4 : 0 ≤ (d'.map fun x => x ^ 2).sum := List.sum_nonneg fun x hx => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
        positivity
      exact ihq _ (by omega) d' h1 (by omega) (Int.toNat_of_nonneg h4).symm
    obtain ⟨a1, ha1, e1⟩ := g1
    obtain ⟨ac, hac, ec⟩ := gc
    set k := (d.filter fun x => 0 < x).length
    have hk : k ≤ V.rank := by
      have := ((_root_.GlobalTheory.LabChar.labels_char V P d).1 hl).1
      rw [← this]
      exact List.length_filter_le _ _
    refine ⟨(m : ℂ)⁻¹ • (a1 * opOf π P (Finsupp.single (dualLab (splitLab V.rank k)) 1) - ac),
      Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.mul_mem _ ha1 (good_gen ⟨k, hk, Or.inr rfl⟩)) hac) _,
      fun u hu => ?_⟩
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, e1 _ (fixed_opOf _ hu), hrel M π u hu,
      ec u hu, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hm', one_smul]
  · push_neg at hpos
    have h0 : d = splitLab V.rank 0 := by
      have hlen := ((_root_.GlobalTheory.LabChar.labels_char V P d).1 hl).1
      rw [splitLab, Nat.sub_zero, List.replicate_zero, List.append_nil, ← hlen]
      exact List.eq_replicate_iff.2 ⟨rfl, fun x hx => le_antisymm (hpos x hx) (hd x hx)⟩
    refine ⟨_, good_gen ⟨0, Nat.zero_le _, Or.inl rfl⟩, fun u _ => by rw [h0]⟩

theorem shift (hP : conjPl P ≠ P) (u : M) (hu : ∀ k ∈ hyp V P, π k u = u) :
    ∀ (j : ℕ) (d : List ℤ), ((opOf π P (Finsupp.single (splitLab V.rank V.rank) 1)) ^ j)
      (opOf π P (Finsupp.single (d.map fun x => x + (j : ℤ)) 1) u) = opOf π P (Finsupp.single d 1) u := by
  intro j
  induction j with
  | zero => intro d; simp
  | succ j ih =>
    intro d
    rw [pow_succ, Module.End.mul_apply, central_shift V P hP _ M π u hu, List.map_map, ← ih d]
    congr 4
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp_apply, Nat.cast_succ]
    ring

end Gen

theorem gen_split : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), conjPl P ≠ P → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (d : List ℤ), ∃ a ∈ Algebra.adjoin ℂ {x : Module.End ℂ M | ∃ k, k ≤ V.rank ∧ (x = opOf π P (Finsupp.single (splitLab V.rank k) 1) ∨ x = opOf π P (Finsupp.single (dualLab (splitLab V.rank k)) 1))}, ∀ u : M, (∀ k ∈ hyp V P, π k u = u) → a u = opOf π P (Finsupp.single d 1) u := by
  intro D V P hP M _ _ π d
  set t : ℕ := (d.map fun x => (-x).toNat).sum
  have ht : ∀ x ∈ d.map (fun x => x + (t : ℤ)), 0 ≤ x := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun x : ℤ => (-x).toNat) hx)
    omega
  have hs : 0 ≤ (d.map fun x => x + (t : ℤ)).sum := List.sum_nonneg ht
  have hq : 0 ≤ ((d.map fun x => x + (t : ℤ)).map fun x => x ^ 2).sum := List.sum_nonneg fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    positivity
  obtain ⟨a, ha, he⟩ := good_nonneg (V := V) (P := P) (π := π) hP _ _ _ ht (Int.toNat_of_nonneg hs).symm
    (Int.toNat_of_nonneg hq).symm
  refine ⟨(opOf π P (Finsupp.single (splitLab V.rank V.rank) 1)) ^ t * a,
    Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (good_gen ⟨V.rank, le_rfl, Or.inl rfl⟩) _) ha, fun u hu => ?_⟩
  rw [Module.End.mul_apply, he u hu, shift hP u hu]

end GlobalTheory.SplitGen
end

