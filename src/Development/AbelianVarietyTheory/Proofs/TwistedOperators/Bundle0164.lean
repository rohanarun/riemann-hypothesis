module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersRamificationLevelPlaces
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelRamif

variable {D : D7}

theorem not_two_primes (PP : Pl D.host.E) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h1 : (p : 𝓞 D.host.E) ∈ PP.asIdeal) (h2 : (q : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  have hc : IsCoprime (p : 𝓞 D.host.E) (q : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem natCast_mem_conj {PP PP' : Pl D.host.E} (h : Formalism.IndefR.Lev.IsConjPl PP PP') {n : ℕ}
    (hn : (n : 𝓞 D.host.E) ∈ PP.asIdeal) : (n : 𝓞 D.host.E) ∈ PP'.asIdeal := by
  obtain ⟨c', hc', e⟩ := h _ hn
  have e2 : c' = (n : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    have e3 : (((n : 𝓞 D.host.E)) : D.host.E) = (n : D.host.E) := map_natCast (algebraMap (𝓞 D.host.E) D.host.E) n
    rw [e, e3, star_natCast]
  rwa [e2] at hc'

theorem exists_prime_mem {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) {PP : Pl D.host.E}
    (h : PP ∈ Q) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ∀ i, q ≠ D.host.g i := by
  obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := hQ PP h
  refine ⟨q, hq, ?_, hne⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hc, ← nsmul_one]
  exact card_nsmul_eq_zero'

theorem typePrime_mem {P : Formalism.L2.Host.PiBar D.host} {k : Fin 2} {PP : Pl D.host.E} (h : P.Div k PP) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  have h1 := P.pb_over k
  have h2 : PP.under (𝓞 D.host.K) = P.pb k := h
  rw [← h2] at h1
  have h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h1
  rwa [map_natCast] at h3

theorem isConjPl_of_eq {w w' : Pl D.host.E}
    (h : w'.asIdeal = Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) w.asIdeal) : Formalism.IndefR.Lev.IsConjPl w' w := by
  intro c hc
  rw [h, Formalism.L2.Col.mem_conjIdeal] at hc
  exact ⟨_, hc, rfl⟩

theorem ramif_at_levels : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ (t : T0) (j : Fin D.R.m), Disjoint L.Pg (L.Q t) ∧ (∀ PP ∈ L.Q t, (L.C.mu0 j).UnrAt PP) ∧ (∀ PP ∈ L.Pg, (L.xiH t).UnrAt PP) ∧ ∀ PP', PP' ∉ L.Pg → (∀ PP ∈ L.Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → (L.C.mu0 j).UnrAt PP' := by
  classical
  intro D T0 L μ0 hL t j
  have hoff : ∀ (k : Fin 2) (PP : Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal →
      PP ∉ L.Q t ∧ ¬ ∃ PP' ∈ L.Q t, Formalism.IndefR.Lev.IsConjPl PP' PP := by
    intro k PP hk
    refine ⟨fun hQ => ?_, fun ⟨PP', hQ, hc⟩ => ?_⟩
    · obtain ⟨q, hq, hm, hne⟩ := exists_prime_mem (hL.Q_pl t) hQ
      exact not_two_primes PP hq (D.host.g_prime k) (hne k) hm hk
    · obtain ⟨q, hq, hm, hne⟩ := exists_prime_mem (hL.Q_pl t) hQ
      exact not_two_primes PP hq (D.host.g_prime k) (hne k) (natCast_mem_conj hc hm) hk
  have hPg : ∀ PP ∈ L.Pg, PP ∉ L.Q t ∧ ¬ ∃ PP' ∈ L.Q t, Formalism.IndefR.Lev.IsConjPl PP' PP := by
    intro PP h
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
    exact hoff k PP (typePrime_mem hk)
  have hM := L.C.isMu0 j
  refine ⟨Finset.disjoint_left.2 fun PP h => (hPg PP h).1, fun PP hQ => ?_, fun PP h => ?_, fun PP h1 h2 => ?_⟩
  · exact hM.unr PP fun k hk => (hoff k PP hk).1 hQ
  · by_contra hn
    rcases (hL.Q_ram t PP).1 hn with h' | h'
    · exact (hPg PP h).1 h'
    · exact (hPg PP h).2 h'
  · refine hM.unr PP fun k hk => ?_
    rcases GlobalTheory.ConjOverQuad.div_or_conj_div D L.C.P k PP hk with h | ⟨PP', h, hc⟩
    · exact h1 ((hL.Pg PP).2 ⟨k, h⟩)
    · exact h2 PP' ((hL.Pg PP').2 ⟨k, h⟩) (isConjPl_of_eq hc)

end GlobalTheory.LevelRamif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory
namespace LevelPlaces
open _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory GlobalTheory.SplitOffPlaces

theorem under_eq_of_isConjPl {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
  refine HeightOneSpectrum.ext ((P.under (𝓞 D.host.F)).isMaximal.eq_of_le (P'.under (𝓞 D.host.F)).isPrime.ne_top
    fun a ha => ?_)
  obtain ⟨c', h1, h2⟩ := h (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ha
  have hfix : star (algebraMap D.host.F D.host.E (a : D.host.F)) = algebraMap D.host.F D.host.E (a : D.host.F) :=
    (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = c' := RingOfIntegers.ext (h2.trans hfix).symm
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P'.asIdeal
  rwa [e]

theorem natCast_mem_of_isConjPl {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P')
    {n : ℕ} (hn : (n : 𝓞 D.host.E) ∈ P.asIdeal) : (n : 𝓞 D.host.E) ∈ P'.asIdeal := by
  obtain ⟨c', h1, h2⟩ := h _ hn
  have e : (n : 𝓞 D.host.E) = c' := RingOfIntegers.ext (by
    rw [h2]
    change (n : D.host.E) = star (n : D.host.E)
    rw [star_natCast])
  rwa [e]

theorem isConjPl_conjSpec {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.IndefR.Lev.IsConjPl P (conjSpec P) :=
  fun c hc => ⟨cO D.host.E c, by
    change cO D.host.E (cO D.host.E c) ∈ P.asIdeal
    rwa [cO_cO], rfl⟩

theorem not_mem_of_prime {A : Type} [CommRing A] {I : Ideal A} (hI : I ≠ ⊤) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : q ≠ p) (h : (q : A) ∈ I) : (p : A) ∉ I := by
  intro h'
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hne)
  apply hI
  rw [Ideal.eq_top_iff_one]
  have e : (1 : A) = a * (q : A) + b * (p : A) := by
    exact_mod_cast congrArg (Int.cast : ℤ → A) hab.symm
  rw [e]
  exact add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ h')

theorem div_or_div_conj {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : Pb.Div k P ∨ Pb.Div k (conjSpec P) := by
  by_contra hc
  have h1 : Pb.pb k ≠ P.under (𝓞 D.host.K) := fun e => hc (Or.inl e.symm)
  have h2 : Pb.pb k ≠ (conjSpec P).under (𝓞 D.host.K) := fun e => hc (Or.inr e.symm)
  obtain ⟨x, hx, hx1, hx2⟩ := exists_mem_not_mem h1 h2
  obtain ⟨x', n, hx', hn⟩ := exists_norm D x
  have hnP : (n : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro h
    have e : (n : 𝓞 D.host.E) = algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x * cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x) := by
      rw [← hx', ← map_mul, hn, map_intCast]
    rw [e] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact hx1 h
    · exact hx2 h
  have hnb : (n : 𝓞 D.host.K) ∈ (Pb.pb k).asIdeal := hn ▸ Ideal.mul_mem_right _ _ hx
  have hp : Prime (D.host.g k : ℤ) := Nat.prime_iff_prime_int.1 (D.host.g_prime k)
  by_cases hd : (D.host.g k : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hd
    apply hnP
    push_cast
    exact Ideal.mul_mem_right _ _ hk
  · obtain ⟨a, b, hab⟩ := (hp.irreducible.coprime_iff_not_dvd).2 hd
    apply (Pb.pb k).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 D.host.K) = a * ((D.host.g k : ℕ) : 𝓞 D.host.K) + b * n := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.K) hab.symm
    rw [e]
    exact add_mem (Ideal.mul_mem_left _ _ (Pb.pb_over k)) (Ideal.mul_mem_left _ _ hnb)

theorem mem_of_div {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (P : HeightOneSpectrum (𝓞 D.host.E))
    (h : Pb.Div k P) : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  have h1 := Pb.pb_over k
  rw [← (show P.under (𝓞 D.host.K) = Pb.pb k from h)] at h1
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal := h1
  rwa [map_natCast] at h2

theorem not_mem_of_twist {D : D7} {Q : Finset (Pl D.host.E)} (hQ : Formalism.IndefR.Lev.IsTwistPlaces D.host.g Q)
    {P : Pl D.host.E} (hP : P ∈ Q) (k : Fin 2) : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hQ P hP
  refine not_mem_of_prime P.isPrime.ne_top (D.host.g_prime k) hq (hne k) ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hcard, ← nsmul_one]
  exact card_nsmul_eq_zero' (G := 𝓞 D.host.E ⧸ P.asIdeal)

end LevelPlaces


open LevelPlaces SplitOffPlaces in
theorem levCh_unramified_places : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ t : T0, Disjoint L.Pg (L.Q t) ∧ (∀ PP ∈ L.Pg, (L.xiH t).UnrAt PP) ∧ (∀ PP ∈ L.Q t, ∀ j, (L.C.mu0 j).UnrAt PP) ∧ ∀ P : Pl D.host.E, (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ P.under (𝓞 D.host.F)) → (L.xiH t).UnrAt P ∧ ∀ j, (L.C.mu0 j).UnrAt P := by
  intro D T0 L μ0 hL t
  have hPg : ∀ PP ∈ L.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP h => by
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
    exact ⟨k, mem_of_div _ k PP hk⟩
  have hQ : ∀ PP ∈ L.Q t, ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP h k =>
    not_mem_of_twist (hL.Q_pl t) h k
  refine ⟨Finset.disjoint_left.2 fun PP h h' => ?_, fun PP h => ?_, fun PP h j => ?_, fun P hP => ⟨?_, fun j => ?_⟩⟩
  · obtain ⟨k, hk⟩ := hPg PP h
    exact hQ PP h' k hk
  · obtain ⟨k, hk⟩ := hPg PP h
    by_contra hc
    rcases (hL.Q_ram t PP).1 hc with h' | ⟨PP', h', hc'⟩
    · exact hQ PP h' k hk
    · obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t PP' h'
      have hq' : (q : 𝓞 D.host.E) ∈ PP'.asIdeal := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hcard, ← nsmul_one]
        exact card_nsmul_eq_zero' (G := 𝓞 D.host.E ⧸ PP'.asIdeal)
      exact not_mem_of_prime PP.isPrime.ne_top (D.host.g_prime k) hq (hne k) (natCast_mem_of_isConjPl hc' hq') hk
  · exact (L.C.isMu0 j).unr PP fun k => hQ PP h k
  · by_contra hc
    rcases (hL.Q_ram t P).1 hc with h' | ⟨PP', h', hc'⟩
    · exact hP P (Or.inr h') rfl
    · exact hP PP' (Or.inr h') (under_eq_of_isConjPl hc')
  · refine (L.C.isMu0 j).unr P fun k hk => ?_
    rcases div_or_div_conj L.C.P k P hk with h | h
    · exact hP P (Or.inl ((hL.Pg P).2 ⟨k, h⟩)) rfl
    · exact hP _ (Or.inl ((hL.Pg _).2 ⟨k, h⟩)) (under_eq_of_isConjPl (isConjPl_conjSpec P)).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocKIntMem
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.TwistValues

section General

variable {L : Type} [Field L] [NumberField L]

theorem locK_int_mem (χ : HChar L) (Λ : Subgroup ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 L))) (ht : ∀ v, χ.TameAt v)
    (hi : ∀ k, χ.inf k = 1) (hu : ∀ v, v ∉ S → χ.UnrAt v) (hv : ∀ v, v ∉ S → χ.val v ∈ Λ)
    {P : HeightOneSpectrum (𝓞 L)} (hP : P ∈ S) (b : 𝓞 L) (k : Lˣ) (hk : (k : L) = b) : χ.locK P k ∈ Λ := by
  classical
  have hb : b ≠ 0 := by
    rintro rfl
    exact k.ne_zero hk
  have h0 : P.intValuation b ≠ 0 := P.intValuation_ne_zero b hb
  obtain ⟨n, hn⟩ : ∃ n : ℕ, P.intValuation b = WithZero.exp (-(n : ℤ)) := by
    have h1 := P.intValuation_le_one b
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    refine ⟨(-WithZero.log (P.intValuation b)).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) (fun _ => n + 1)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => if v.1 = P then b else 1)
  have h1 : P.intValuation (a - b) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
    have h1 := ha P hP
    rw [if_pos rfl] at h1
    exact (P.intValuation_le_pow_iff_mem _ _).2 h1
  have h2 : P.intValuation a = P.intValuation b := by
    refine Valuation.map_eq_of_sub_lt _ (h1.trans_lt ?_)
    rw [hn, WithZero.exp_lt_exp]
    push_cast
    omega
  have ha0 : (a : L) ≠ 0 := by
    intro h
    have h3 : a = 0 := by exact_mod_cast h
    rw [h3, map_zero] at h2
    exact h0 h2.symm
  have hmem : χ.locK P (Units.mk0 _ ha0) ∈ Λ := by
    have h := TypeValues.productRule χ S hu (Units.mk0 _ ha0)
    rw [hi, one_mul, Finset.prod_eq_single_of_mem P hP (fun v hvS hvP => TypeValues.locK_eq_one (ht v) _ a rfl (by
      have h1 := ha v hvS
      rw [if_neg hvP] at h1
      exact Ideal.pow_le_self (Nat.succ_ne_zero n) h1))] at h
    rw [eq_inv_of_mul_eq_one_left h]
    refine Λ.inv_mem (finprod_induction (· ∈ Λ) Λ.one_mem (fun _ _ => Λ.mul_mem) fun v => ?_)
    exact finprod_induction (· ∈ Λ) Λ.one_mem (fun _ _ => Λ.mul_mem) fun hvS => Λ.zpow_mem (hv v hvS) _
  have hval : ∀ z : L, Valued.v (algebraMap L (P.adicCompletion L) z) = P.valuation L z :=
    fun z => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P z
  have hint : ∀ z : 𝓞 L, P.valuation L (z : L) = P.intValuation z := fun z => P.valuation_of_algebraMap z
  have h4 : χ.locK P (Units.mk0 _ ha0 * k⁻¹) = 1 := by
    have e : ((atFin P (Units.mk0 _ ha0 * k⁻¹) : (P.adicCompletion L)ˣ) : P.adicCompletion L) =
        algebraMap L (P.adicCompletion L) ((a : L) * (b : L)⁻¹) := by
      rw [← hk, ← Units.val_inv_eq_inv_val]
      rfl
    refine ht P _ ?_ ?_
    · unfold IsUnitAt
      rw [e, hval, map_mul, map_inv₀, hint, hint, h2, mul_inv_cancel₀ h0]
    · have e' : (a : L) * (b : L)⁻¹ - 1 = ((a - b : 𝓞 L) : L) * (b : L)⁻¹ := by
        have : (b : L) ≠ 0 := hk ▸ k.ne_zero
        push_cast
        field_simp
      rw [e, ← map_one (algebraMap L (P.adicCompletion L)), ← map_sub, hval, e', map_mul, map_inv₀, hint, hint, hn]
      refine (mul_le_mul_left h1 _).trans (le_of_eq ?_)
      rw [← WithZero.exp_neg, ← WithZero.exp_add]
      congr 1
      push_cast
      ring
  rw [map_mul, map_inv, mul_inv_eq_one] at h4
  exact h4 ▸ hmem

theorem locK_mem (χ : HChar L) (Λ : Subgroup ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 L))) (ht : ∀ v, χ.TameAt v)
    (hi : ∀ k, χ.inf k = 1) (hu : ∀ v, v ∉ S → χ.UnrAt v) (hv : ∀ v, v ∉ S → χ.val v ∈ Λ)
    (P : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : χ.locK P k ∈ Λ := by
  by_cases hP : P ∈ S
  · obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (k : L)
    have hb0 : (b : L) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hb
    have h1 := locK_int_mem χ Λ S ht hi hu hv hP b (Units.mk0 _ hb0) rfl
    have h2 := locK_int_mem χ Λ S ht hi hu hv hP a (k * Units.mk0 _ hb0) (by
      rw [Units.val_mul, ← e]
      exact div_mul_cancel₀ _ hb0)
    rw [map_mul] at h2
    exact (mul_mem_cancel_right h1).1 h2
  · have h : χ.locK P k = χ.val P ^ ordF P k := GlobalTheory.Mem.Chr.CharModel.locK_unr (F := L) ⟨χ.1, χ.2⟩ (hu P hP) k
    rw [h]
    exact Λ.zpow_mem (hv P hP) _

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
  _root_.Formalism.L2.Col GlobalTheory.RationalValues
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem char_mem {D : D7} (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (h : ChrEq c χ) {n : ℕ} (hn : 0 < n)
    (ho : χ.OrderDvd n) (M : Subfield ℂ) (hM : ∀ P k, ((χ.locK P k : ℂˣ) : ℂ) ∈ M) (x : (AE D)ˣ) : ((c x : Circle) : ℂ) ∈ M := by
  have h1 : ∀ x, c x ^ n = 1 := HeckeFinTrivial.eq_one_of_trivial_on_finite D (c ^ n) ⟨h.1.1.pow n, fun x => by
    rw [MonoidHom.pow_apply, h.1.2, one_pow]⟩ (CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n ho)
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  obtain ⟨y, hy⟩ := IdeleDiv.exists_pow_eq_of_finPart_eq_one D n hn (a x) (ha x).2
  rw [hab x, map_mul, ← hy, map_pow, h1, one_mul]
  obtain ⟨j, j1, j2, j3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := CharLocProd.char_eq_prod_locK D j j1 j2 (PlaceIdem.exists_isPlIdem D j j1 j2 j3) c χ h
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom (b x))
  rw [hprod (b x) (hb x).1 S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS']
  exact prod_mem fun P _ => hM P _

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem xiH_locK_mem (hL : R.toLevCh.Is A.μ0) (hon : R.fam_pl_onto) (hmu : R.fam_muVal)
    (hok : ∀ t P, P ∈ A.ok t ↔ Bridge.SplitOff (R.pl P) ((R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E))))
    (i : Fin D.R.m) (t : T0) (PP : Pl D.host.E) (k : D.host.Eˣ) :
    (((R.xiH t).locK PP k : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
  classical
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  let T : Finset (Pl D.host.E) := R.Sb ∪ R.Q t ∪ R.Q A.μ0
  have hQ : ∀ v ∈ R.Q t, v ∈ T := fun v hv => Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  have hu : ∀ v, v ∉ T ∪ T.image conjPrime₂ → (R.xiH t).UnrAt v := fun v hv => by
    by_contra hn
    rcases (hL.Q_ram t v).1 hn with h | ⟨w, hw, h⟩
    · exact hv (Finset.mem_union_left _ (hQ v h))
    · refine hv (Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, hQ w hw, ?_⟩))
      have h1 : w = conjPrime₂ v := HeightOneSpectrum.ext (w.isMaximal.eq_of_le (conjPrime₂ v).isPrime.ne_top fun c hc => by
        obtain ⟨c', hc', e⟩ := h c hc
        rw [mem_conjP, show cO D.host.E c = c' from RingOfIntegers.ext e.symm]
        exact hc')
      rw [h1, conjP_conjP]
  have hv : ∀ v, v ∉ T ∪ T.image conjPrime₂ → (R.xiH t).val v ∈ unitsIn D.what₂.embLL.fieldRange := fun v hv => by
    by_cases hc : conjPrime₂ v = v
    · have h1 : (((R.xiH t).val v : ℂˣ) : ℂ) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, TypeValues.val_sq_eq_one D.sp.cm (hL.xi_triv t) (hu v hv) hc, Units.val_one]
      show (((R.xiH t).val v : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange
      rcases sq_eq_one_iff.1 h1 with h2 | h2
      · rw [h2]; exact one_mem _
      · rw [h2]; exact neg_mem (one_mem _)
    · have hs : ∀ S : Set (Pl D.host.E), (∀ w ∈ S, w ∈ T) → Bridge.SplitOff v S := fun S hS =>
        ⟨fun h => hc (HeightOneSpectrum.ext ((conjIdeal_asIdeal v).symm.trans h)),
          fun h => hv (Finset.mem_union_left _ (hS v h)), fun w hw h => hv (Finset.mem_union_right _ (Finset.mem_image.2
            ⟨w, hS w hw, by rw [show w = conjPrime₂ v from HeightOneSpectrum.ext (h.trans (conjIdeal_asIdeal v)), conjP_conjP]⟩))⟩
      have hS : ∀ w ∈ R.Sb, w ∈ T := fun w hw => Finset.mem_union_left _ (Finset.mem_union_left _ hw)
      obtain ⟨P, rfl⟩ := hon v (hs _ hS)
      have h1 : (R.C.mu0 i * R.xiH t).val (R.pl P) ∈ unitsIn D.what₂.embLL.fieldRange :=
        ⟨_, hmu i t P ((hok t P).2 (hs _ fun w hw => hw.elim (hS w) (hQ w)))⟩
      have h2 : (R.C.mu0 i * R.xiH A.μ0).val (R.pl P) ∈ unitsIn D.what₂.embLL.fieldRange :=
        ⟨_, hmu i A.μ0 P ((hok A.μ0 P).2 (hs _ fun w hw => hw.elim (hS w) fun h => Finset.mem_union_right _ h))⟩
      rw [hL.xi_base, mul_one] at h2
      rw [HChar.val_mul] at h1
      exact (mul_mem_cancel_left h2).1 h1
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  exact locK_mem (R.xiH t) _ (T ∪ T.image conjPrime₂) (hL.xi_tame t) (TypeValues.inf_eq_one _ hn ho) hu hv PP k

theorem xiVal : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → GlobalTheory.TwistField.XiVal R := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hF t x
  obtain ⟨_, _, _, hT⟩ := hF.tie
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  exact char_mem _ _ (hL.xi t) hn ho _
    (xiH_locK_mem R hL hF.pl_onto hF.muVal hT.ok ⟨0, lt_of_lt_of_le two_pos D.R.two_le_m⟩ t) x

end GlobalTheory.TwistValues
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapMulMtEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicModulus.RowMat

theorem map_coord_eq {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (f : V → V) (hf : Measurable f)
    (hfH : ∀ μ : Measure V, μ.IsAddHaarMeasure → μ.map f = μ) (ρ : ℕ)
    [inst : MeasurableSpace (Fin ρ → V)] [hB : BorelSpace (Fin ρ → V)]
    (lam : Measure (Fin ρ → V)) [hlam : lam.IsAddHaarMeasure] :
    lam.map (fun b i => f (b i)) = lam := by
  have e : inst = MeasurableSpace.pi :=
    hB.measurable_eq.trans (@BorelSpace.measurable_eq (Fin ρ → V) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst e
  have hp : MeasurePreserving f (Measure.addHaar : Measure V) Measure.addHaar :=
    ⟨hf, hfH _ inferInstance⟩
  have hpi := measurePreserving_pi (fun _ : Fin ρ => (Measure.addHaar : Measure V))
    (fun _ => Measure.addHaar) (fun _ => hp)
  rw [Measure.isAddLeftInvariant_eq_smul lam (Measure.pi fun _ : Fin ρ => (Measure.addHaar : Measure V)),
    Measure.map_smul _ hpi.measurable.aemeasurable]
  congr 1
  exact (measurePreserving_pi (fun _ : Fin ρ => (Measure.addHaar : Measure V))
    (fun _ => Measure.addHaar) (fun _ => hp)).map_eq

theorem map_mul_mt_eq : ∀ (D : D7) (S₀ : HSp D) (ρ : ℕ) (lam : Measure (Mx D ρ S₀.rank)),
    lam.IsAddHaarMeasure → ∀ h : GA D S₀,
      lam.map (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h) = lam := by
  intro D S₀ ρ lam hlam h
  have h1 : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  have h2 : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1
  have h3 : LocallyCompactSpace (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.1
  have h4 : SecondCountableTopology (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.2.1
  have h5 : BorelSpace (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.2.2
  have hcm := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  have hrow := GlobalTheory.AdelicModulus.Row.map_vecMul_unitary _ _ D.sp.cm.sig hcm.1 S₀.rank S₀.gram
    (hcm.2 S₀) h
  have e : (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h) =
      fun b i => Matrix.vecMul (b i) (mt S₀ h) := by
    funext b i j
    rfl
  rw [e]
  have hm : Measurable (fun x : Fin S₀.rank → AE D => Matrix.vecMul x (mt S₀ h)) :=
    (Continuous.matrix_vecMul continuous_id continuous_const).measurable
  exact map_coord_eq (V := Fin S₀.rank → AE D) (f := fun x => Matrix.vecMul x (mt S₀ h)) (hf := hm)
    (hfH := fun μ hμ => hrow μ hμ) (ρ := ρ) (inst := measMx ρ S₀.rank)
    (hB := @BorelSpace.mk _ _ (measMx ρ S₀.rank) rfl) (lam := lam) (hlam := hlam)

end GlobalTheory.AdelicModulus.RowMat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemUnder

theorem under_eq_of_isIdemAt : ∀ (D : D7) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), Formalism.L2.NTheta.IsIdemAt e PP → IsPlaceIdem D v ε → e + cA D e = algebraMap (AF D.host.F) (AE D) ε → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v := by
  intro D e PP v ε he hv hsum

  obtain ⟨hee, hec, -⟩ := he.1
  have hfix : e * algebraMap (AF D.host.F) (AE D) ε = e := by
    rw [← hsum, mul_add, hee, hec, add_zero]

  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hone : Φ e PP = 1 := (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ he).2.1
  by_contra hne
  have hzero := (GlobalTheory.IdemSupport.place_comp hΦ hv).2.2 PP hne
  have hcomp := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) e (algebraMap (AF D.host.F) (AE D) ε) PP
  rw [hfix, hzero, mul_zero, hone] at hcomp
  exact one_ne_zero hcomp

end GlobalTheory.IdemUnder
end

