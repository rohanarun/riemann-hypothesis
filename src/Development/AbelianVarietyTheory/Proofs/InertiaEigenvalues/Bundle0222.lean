module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionLatticeGradedOfLevelLe
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaActionSubMemSpanPowSucc
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

namespace GlobalTheory.GamFilt

theorem sub_mem_pow_succ {A : Type*} [CommRing A] (f : A →+* A) (I : Ideal A)
    (h0 : ∀ a, f a - a ∈ I) (h1 : ∀ a ∈ I, f a - a ∈ I ^ 2) :
    ∀ k : ℕ, ∀ a ∈ I ^ k, f a - a ∈ I ^ (k + 1) := by
  intro k
  induction k with
  | zero => intro a _; simpa using h0 a
  | succ k ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      have hfy : f y ∈ I := by
        have := I.add_mem (h0 y) hy
        simpa using this
      have e : f (x * y) - x * y = (f x - x) * f y + x * (f y - y) := by
        rw [map_mul]; ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ]
        exact Ideal.mul_mem_mul (ih x hx) hfy
      · rw [show k + 1 + 1 = k + 2 from rfl, pow_add]
        exact Ideal.mul_mem_mul hx (h1 y hy)
    · intro x y hx hy
      have e : f (x + y) - (x + y) = (f x - x) + (f y - y) := by
        rw [map_add (f := _)]; ring
      rw [e]
      exact Ideal.add_mem _ hx hy

theorem sub_mem_pow_succ_pair {A : Type*} [CommRing A] (f : A →+* A) (p t : A)
    (h0 : ∀ a, f a - a ∈ Ideal.span {p, t}) (hp : f p = p)
    (ht : f t - t ∈ Ideal.span {p, t} ^ 2) :
    ∀ k : ℕ, ∀ a ∈ Ideal.span {p, t} ^ k, f a - a ∈ Ideal.span {p, t} ^ (k + 1) := by
  refine sub_mem_pow_succ f _ h0 ?_
  intro y hy
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hy
  have e : f (a * p + b * t) - (a * p + b * t) =
      (f a - a) * p + (f b - b) * t + f b * (f t - t) := by
    rw [map_add (f := _), map_mul, map_mul, hp]; ring
  rw [e]
  have hpm : p ∈ Ideal.span {p, t} := Ideal.subset_span (by simp)
  have htm : t ∈ Ideal.span {p, t} := Ideal.subset_span (by simp)
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) (Ideal.mul_mem_left _ _ ht)
  · rw [pow_two]; exact Ideal.mul_mem_mul (h0 a) hpm
  · rw [pow_two]; exact Ideal.mul_mem_mul (h0 b) htm

theorem X_dvd_sub {O : Type*} [CommRing O] (g : PowerSeries O →ₐ[O] PowerSeries O)
    (hg : PowerSeries.constantCoeff (g PowerSeries.X) = 0) (a : PowerSeries O) :
    PowerSeries.X ∣ g a - a := by
  have h1 : PowerSeries.X ∣ a - PowerSeries.C (PowerSeries.constantCoeff a) := by
    rw [PowerSeries.X_dvd_iff]; simp
  obtain ⟨b, hb⟩ := h1
  have ha : a = algebraMap O (PowerSeries O) (PowerSeries.constantCoeff a) + PowerSeries.X * b := by
    rw [← hb, PowerSeries.algebraMap_apply]; simp
  rw [PowerSeries.X_dvd_iff, ha, map_add (f := _), AlgHom.commutes, map_mul]
  simp [hg]

theorem exists_X_sub {O : Type*} [CommRing O] (F : PowerSeries O) (p : ℕ) (c : O)
    (h0 : PowerSeries.constantCoeff F = 0) (h1 : PowerSeries.coeff 1 F = 1 + p * c) :
    ∃ h : PowerSeries O, F - PowerSeries.X =
      PowerSeries.X * ((p : PowerSeries O) * PowerSeries.C c + PowerSeries.X * h) := by
  have : PowerSeries.X ^ 2 ∣ F - PowerSeries.X - PowerSeries.X * (PowerSeries.C ((p : O) * c)) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simp [h0]
    · rw [map_sub, map_sub, h1, PowerSeries.coeff_succ_X_mul]
      simp
  obtain ⟨h, hh⟩ := this
  refine ⟨h, ?_⟩
  rw [map_mul, map_natCast] at hh
  linear_combination hh

theorem letγ_sub_mem {O : Type} [CommRing O] {n : ℕ} (g : PowerSeries O →ₐ[O] PowerSeries O) (p : ℕ)
    (c : O) (h0 : PowerSeries.constantCoeff (g PowerSeries.X) = 0)
    (h1 : PowerSeries.coeff 1 (g PowerSeries.X) = 1 + p * c) :
    ∀ k : ℕ, ∀ a ∈ (Ideal.span {((p : ℕ) : LetA O n), letπ}) ^ k,
      letγ g a - a ∈ (Ideal.span {((p : ℕ) : LetA O n), letπ}) ^ (k + 1) := by
  have hpm : ((p : ℕ) : LetA O n) ∈ Ideal.span {((p : ℕ) : LetA O n), letπ} :=
    Ideal.subset_span (by simp)
  have htm : (letπ : LetA O n) ∈ Ideal.span {((p : ℕ) : LetA O n), letπ} :=
    Ideal.subset_span (by simp)
  refine sub_mem_pow_succ_pair (letγ g : LetA O n →ₐ[O] LetA O n).toRingHom _ _ ?_ (map_natCast _ _) ?_
  · intro a
    choose b hb using fun i => X_dvd_sub g h0 (a i)
    have e : (letγ g : LetA O n →ₐ[O] LetA O n).toRingHom a - a = letπ * b := funext hb
    rw [e]
    exact Ideal.mul_mem_right _ _ htm
  · obtain ⟨h, hh⟩ := exists_X_sub _ p c h0 h1
    have e : (letγ g : LetA O n →ₐ[O] LetA O n).toRingHom letπ - letπ =
        letπ * (((p : ℕ) : LetA O n) * (fun _ => PowerSeries.C c) + letπ * (fun _ => h)) :=
      funext fun _ => hh
    rw [e, pow_two]
    exact Ideal.mul_mem_mul htm (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hpm)
      (Ideal.mul_mem_right _ _ htm))

theorem exists_eq_one_add {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (u : ↥(OL LL))
    (hu : (1 : WithTop ℚ) ≤ P.v LL (algebraMap ↥(OL LL) ↥LL.1 u - 1)) :
    ∃ c : ↥(OL LL), u = 1 + (l : ↥(OL LL)) * c := by
  have hl : (l : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  set y : ↥LL.1 := (algebraMap ↥(OL LL) ↥LL.1 u - 1) / (l : ↥LL.1) with hy
  have e : algebraMap ↥(OL LL) ↥LL.1 u - 1 = (l : ↥LL.1) * y := by
    rw [hy]; field_simp
  rw [e, AddValuation.map_mul, P.v_l] at hu
  have h0 : 0 ≤ P.v LL y := by
    have : (1 : WithTop ℚ) + 0 ≤ 1 + P.v LL y := by simpa using hu
    exact (WithTop.add_le_add_iff_left WithTop.one_ne_top).1 this
  refine ⟨⟨y, (P.v_O LL y).1 h0⟩, Subtype.ext ?_⟩
  have : (u : ↥LL.1) - 1 = (l : ↥LL.1) * y := e
  push_cast
  linear_combination this

theorem gamma_sub_mem_pow_succ :
    ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime]
      (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    ∀ g ∈ ((HW l).W K s LL h).GKs, ∀ (k : ℕ),
    ∀ a ∈ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), letπ}) ^ k,
      ((HW l).W K s LL h).γA (((HW l).W K s LL h).resΓ g) a - a ∈
        (Ideal.span {((l : ℕ) : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), letπ}) ^ (k + 1) := by
  intro D HW l _ K s LL h
  let W := (HW l).W K s LL h
  intro g hg
  have h1 := (W.GKs_def g).1 hg
  rw [← W.χΓ_res g] at h1
  have hs : (1 : WithTop ℚ) ≤ (W.s : WithTop ℚ) := by exact_mod_cast W.s_pos
  obtain ⟨c, hc⟩ := exists_eq_one_add (D.loc l) LL _ (hs.trans h1)
  exact letγ_sub_mem (W.γ₀ (W.resΓ g)) l c (W.γ₀_X _).1 ((W.γ₀_X _).2.trans hc)

end GlobalTheory.GamFilt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisExtra
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.LocIota

theorem ιB_algebraMap_Kur {l : ℕ} [Fact l.Prime] (P : LocPrime l) (c : ↥(MaximalUnramifiedExtension l)) :
    P.ιB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l) := by
  have hint : IsIntegral ℚ_[l] (c : Om l) := Algebra.IsIntegral.isIntegral _
  obtain ⟨K, hc⟩ : ∃ K : FinExt l, (c : Om l) ∈ K0 K :=
    ⟨⟨IntermediateField.adjoin ℚ_[l] {(c : Om l)},
      IntermediateField.adjoin.finiteDimensional hint⟩,
      IntermediateField.mem_adjoin_simple_self ℚ_[l] (c : Om l), c.2⟩
  have h := (P.PD K).ι.commutes (⟨c, hc⟩ : ↥(K0 K))
  rw [P.PD_ι] at h
  exact h

end GlobalTheory.LocIota
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisMore
section
namespace GlobalTheory.NonzeroScalarLattice

theorem exists_ne_zero_smul_mem {G : Type} [Group G] {LL : Type} [Field LL] {O : Type}
    [CommRing O] [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] {ρ : Representation LL G V} [IsDomain O] [IsFractionRing O LL]
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (w : V) :
    ∃ (b : O), b ≠ (0 : O) ∧ b • w ∈ Formalism.WeaklyAdmissibleFiltrations.Lattice.T L := by
  have hw : w ∈ Submodule.span LL (L.T : Set V) := by
    rw [L.span]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.T.smul_mem _ hax
    · rw [mul_smul]; exact L.T.smul_mem _ hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := O) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap O LL q ≠ 0 := by
      intro h
      exact hq0 (IsFractionRing.injective O LL (by rw [h, map_zero]))
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have h1 : q • ((algebraMap O LL p / algebraMap O LL q) • x) = p • x := by
      rw [← algebraMap_smul LL q, smul_smul, mul_div_cancel₀ _ hq1, algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact L.T.smul_mem _ hax

end GlobalTheory.NonzeroScalarLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAcrisLogOneAddAddOfMul
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LogU

theorem defect_mem {R : Type} [CommRing R] (S : Subring R) (a b : R)
    (ha : ∀ i : ℕ, ∃ g ∈ S, ((i.factorial : ℕ) : R) * g = a ^ i)
    (hb : ∀ j : ℕ, ∃ g ∈ S, ((j.factorial : ℕ) : R) * g = b ^ j) (n : ℕ) :
    ∃ e ∈ S, truncLogF n (a + b + a * b) - truncLogF n a - truncLogF n b =
      ((n.factorial * ((n - 1) / 2).factorial : ℕ) : R) * e := by
  choose A hAS hA using ha
  choose B hBS hB using hb
  have hD : ∀ d : Fin 2 →₀ ℕ, ∃ D : ℤ, (((d 0).factorial * (d 1).factorial : ℕ) : ℤ) *
      AddMonoidAlgebra.coeff (logDefect n) d = ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) * D := by
    intro d
    have hd : Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) = d := by
      ext x; fin_cases x <;> simp
    by_cases h : d 0 + d 1 < n
    · have := GlobalTheory.T.coeff_logDefect_eq_zero_of_add_lt n (d 0) (d 1) h
      rw [hd] at this
      exact ⟨0, by rw [this]; simp⟩
    · obtain ⟨D, hD⟩ := _root_.GlobalTheory.LogUIntg.logDefect_coeff_dvd n (d 0) (d 1) (by omega)
      rw [hd] at hD
      exact ⟨D, hD⟩
  choose D hD using hD
  refine ⟨∑ d ∈ (logDefect n).support, (D d : R) * (A (d 0) * B (d 1)),
    Subring.sum_mem _ fun d _ => Subring.mul_mem _ (intCast_mem S _)
      (Subring.mul_mem _ (hAS _) (hBS _)), ?_⟩
  rw [← aeval_logDefect, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hc := congrArg (Int.cast : ℤ → R) (hD d)
  push_cast at hc
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, eq_intCast]
  rw [← hA, ← hB]
  push_cast
  linear_combination (A (d 0) * B (d 1)) * hc

theorem isLogJ_add : ∀ (l : ℕ) [Fact l.Prime] (a b : Per.Ainf l) (y y' : Per.Acris l), GlobalTheory.LogU.InJ a →
    GlobalTheory.LogU.InJ b → GlobalTheory.LogU.IsLogJ a y → GlobalTheory.LogU.IsLogJ b y' → GlobalTheory.LogU.IsLogJ (a + b + a * b) (y + y') := by
  intro l _ a b y y' ha hb hy hy' r
  have hl : l.Prime := Fact.out
  obtain ⟨N1, hN1⟩ := hy r
  obtain ⟨N2, hN2⟩ := hy' r
  refine ⟨max (max N1 N2) (2 * l ^ r + 1), fun n hn => ?_⟩
  obtain ⟨sa, hsa, za, hza⟩ := hN1 n (le_of_max_le_left (le_of_max_le_left hn))
  obtain ⟨sb, hsb, zb, hzb⟩ := hN2 n (le_of_max_le_right (le_of_max_le_left hn))
  have hn' : 2 * l ^ r + 1 ≤ n := le_of_max_le_right hn
  have hA : ∀ i : ℕ, ∃ g ∈ (Per.Acris0 l).toSubring, ((i.factorial : ℕ) : Per.AinfP l) * g =
      algebraMap (Per.Ainf l) (Per.AinfP l) a ^ i := fun i => by
    obtain ⟨g, hg⟩ := exists_divPow ha i
    exact ⟨g, g.2, hg⟩
  have hB : ∀ i : ℕ, ∃ g ∈ (Per.Acris0 l).toSubring, ((i.factorial : ℕ) : Per.AinfP l) * g =
      algebraMap (Per.Ainf l) (Per.AinfP l) b ^ i := fun i => by
    obtain ⟨g, hg⟩ := exists_divPow hb i
    exact ⟨g, g.2, hg⟩
  obtain ⟨e, he, hE⟩ := defect_mem _ _ _ hA hB n
  have hdvd : l ^ r ∣ ((n - 1) / 2).factorial := by
    refine Nat.dvd_factorial (pow_pos hl.pos r) ?_
    generalize l ^ r = L at hn' ⊢
    omega
  obtain ⟨q, hq⟩ := hdvd
  let E : Per.Acris0 l := ⟨e, he⟩
  refine ⟨sa + sb + ((l ^ r * q : ℕ) : Per.Acris0 l) * E, ?_,
    za + zb - (q : Per.Acris l) * algebraMap (Per.Acris0 l) (Per.Acris l) E, ?_⟩
  · rw [hq] at hE
    simp only [truncLogF] at hE
    have hEe : ((E : Per.Acris0 l) : Per.AinfP l) = e := rfl
    have hc : (((sa + sb + ((l ^ r * q : ℕ) : Per.Acris0 l) * E : Per.Acris0 l)) : Per.AinfP l) =
        (sa : Per.AinfP l) + (sb : Per.AinfP l) + ((l ^ r * q : ℕ) : Per.AinfP l) * e := by
      simp [hEe]
    rw [hc]
    simp only [map_add (f := _), map_mul]
    push_cast at hE ⊢
    linear_combination hsa + hsb - hE
  · set_option synthInstance.maxHeartbeats 200000 in
    simp only [map_add (f := algebraMap (Per.Acris0 l) (Per.Acris l)), map_mul, map_natCast]
    push_cast
    linear_combination hza + hzb

end GlobalTheory.LogU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeKurOfNorm
section
namespace GlobalTheory.UnramValue

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct IsLocalRing Polynomial

theorem exists_pow_card_eq {S : Type*} [CommRing S] [IsLocalRing S]
    [IsAdicComplete (maximalIdeal S) S] [Fintype (ResidueField S)] (x : S) :
    ∃ t : S, t ^ Fintype.card (ResidueField S) = t ∧ t - x ∈ maximalIdeal S := by
  have h1 : 1 < Fintype.card (ResidueField S) := Fintype.one_lt_card
  have hm : (X ^ Fintype.card (ResidueField S) - X : S[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1)
  obtain ⟨t, ht, htx⟩ := (IsAdicComplete.henselianRing S (maximalIdeal S)).is_henselian _ hm x
    (by
      rw [← residue_eq_zero_iff]
      simp [FiniteField.pow_card])
    (by
      change IsUnit (residue S _)
      rw [derivative_sub, derivative_X_pow]
      simp)
  refine ⟨t, ?_, htx⟩
  simpa [sub_eq_zero] using ht

variable {l : ℕ} [Fact l.Prime]

theorem norm_natCast_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap', Padic.norm_p]

theorem integral_mem (L : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] L]
    (h : ∀ x ∈ L, x ≠ 0 → ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k) (x : integralClosure ℤ_[l] L) :
    ((x : L) : Om l) ∈ MaximalUnramifiedExtension l := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : L) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have : IsLocalRing (integralClosure ℤ_[l] L) :=
    (GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt l L).toIsLocalRing
  have hmax : ∀ y : integralClosure ℤ_[l] L,
      y ∈ maximalIdeal (integralClosure ℤ_[l] L) ↔ ‖((y : L) : Om l)‖ < 1 := fun y => by
    rw [GlobalTheory.DiscEval.mem_maximalIdeal_iff_norm, GlobalTheory.DiscEval.intEmb_apply,
      GlobalTheory.DiscEval.fieldEmb_apply, PadicComplex.norm_extends]
  have hint : ∀ y : L, y ∈ integralClosure ℤ_[l] L ↔ ‖(y : Om l)‖ ≤ 1 := fun y => by
    rw [GlobalTheory.DiscEval.mem_integralClosure_iff_norm, GlobalTheory.DiscEval.fieldEmb_apply,
      PadicComplex.norm_extends]
  let N : Submodule ℤ_[l] (integralClosure ℤ_[l] L) :=
    { carrier := {y | ((y : L) : Om l) ∈ MaximalUnramifiedExtension l}
      add_mem' := fun ha hb => (MaximalUnramifiedExtension l).add_mem ha hb
      zero_mem' := (MaximalUnramifiedExtension l).zero_mem
      smul_mem' := fun c y hy => (MaximalUnramifiedExtension l).smul_mem (x := (c : ℚ_[l])) hy }
  have := GlobalTheory.DiscEval.isAdicComplete_integralClosure L
  have := GlobalTheory.DiscEval.finite_residueField_integralClosure L
  let _ := Fintype.ofFinite (ResidueField (integralClosure ℤ_[l] L))
  have hle : (⊤ : Submodule ℤ_[l] (integralClosure ℤ_[l] L)) ≤ N := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal ℤ_[l])
      Module.Finite.fg_top (maximalIdeal_le_jacobson _) fun y _ => ?_
    obtain ⟨t, ht, hty⟩ := exists_pow_card_eq y
    have htN : t ∈ N := by
      change ((t : L) : Om l) ∈ MaximalUnramifiedExtension l
      by_cases h0 : ((t : L) : Om l) = 0
      · rw [h0]; exact zero_mem _
      have h1 : 1 < Fintype.card (ResidueField (integralClosure ℤ_[l] L)) := Fintype.one_lt_card
      refine IntermediateField.subset_adjoin _ _
        ⟨Fintype.card (ResidueField (integralClosure ℤ_[l] L)) - 1, by omega, ?_, ?_⟩
      · rintro ⟨c, hc⟩
        have h2 : (l : ResidueField (integralClosure ℤ_[l] L)) = 0 := by
          rw [← map_natCast (residue _), residue_eq_zero_iff, hmax]
          push_cast
          rw [norm_natCast_l]
          exact inv_lt_one_of_one_lt₀ hl1
        have h3 := congrArg (Nat.cast : ℕ → ResidueField (integralClosure ℤ_[l] L)) hc
        rw [Nat.cast_sub h1.le] at h3
        simp [h2] at h3
      · have h2 := congrArg (fun z : integralClosure ℤ_[l] L => ((z : L) : Om l)) ht
        push_cast at h2
        apply mul_right_cancel₀ h0
        rw [← pow_succ, Nat.sub_add_cancel h1.le, h2, one_mul]
    have hd : ((t - y : integralClosure ℤ_[l] L) : L) / l ∈ integralClosure ℤ_[l] L := by
      rw [hint]
      rw [hmax] at hty
      generalize ((t - y : integralClosure ℤ_[l] L) : L) = z at hty
      push_cast
      by_cases h0 : (z : Om l) = 0
      · simp [h0]
      obtain ⟨k, hk⟩ := h _ z.2 h0
      rw [hk, zpow_lt_one_iff_right₀ hl1] at hty
      rw [norm_div, hk, norm_natCast_l, div_inv_eq_mul, ← zpow_add_one₀ (by positivity)]
      exact zpow_le_one_of_nonpos₀ hl1.le (by omega)
    have he : y = t - (l : ℤ_[l]) • (⟨_, hd⟩ : integralClosure ℤ_[l] L) := by
      apply Subtype.ext
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
      push_cast
      field_simp
      ring
    rw [he]
    refine sub_mem (Submodule.mem_sup_left htN) (Submodule.mem_sup_right
      (Submodule.smul_mem_smul ?_ Submodule.mem_top))
    exact PadicInt.irreducible_p.not_isUnit
  exact hle Submodule.mem_top

theorem le_Kur_of_norm : ∀ (l : ℕ) [Fact l.Prime] (M : FinExt l),
    (∀ x ∈ M.1, x ≠ 0 → ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k) → M.1 ≤ MaximalUnramifiedExtension l := by
  intro l _ M h x hx
  obtain ⟨L, hL⟩ := M
  obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := integralClosure ℤ_[l] L) (⟨x, hx⟩ : L)
  have h1 : x = ((a : L) : Om l) / ((b : L) : Om l) := (congrArg Subtype.val hab).symm
  rw [h1]
  exact div_mem (integral_mem L h a) (integral_mem L h b)

end GlobalTheory.UnramValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodCyclotomicCharReducesModPrimePow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CycLevel

theorem toZModPow_eq_of_norm_sub_le {l : ℕ} [Fact l.Prime] (u : ℤ_[l]) (a : ℕ) (r : ℕ)
    (h : ‖(u : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(r : ℤ))) :
    (PadicInt.toZModPow r u : ZMod (l ^ r)) = (a : ZMod (l ^ r)) := by
  have h1 : ‖u - (a : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by
    rw [PadicInt.norm_def]; push_cast; exact h
  have h2 := (PadicInt.norm_le_pow_iff_mem_span_pow (u - (a : ℤ_[l])) r).mp h1
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h2
  exact h2

theorem chi_reduces (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (r : ℕ) (g : ↥(GK K)) :
    ∃ u : ℤ_[l], (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = (u : ℚ_[l]) ∧
      (PadicInt.toZModPow r u : ZMod (l ^ r)) =
        ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) := by
  obtain ⟨ζ, hζ1, hζ⟩ := GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr K.1
    (IntermediateField.fixingSubgroupEquiv K.1 g) r
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc (g : GQ l) r ζ hζ1
  have key := hζ a hga
  have hr : (l : ℝ) ^ (-(r : ℤ)) ≤ 1 := by
    apply zpow_le_one_of_nonpos₀
    · exact_mod_cast (Fact.out : l.Prime).one_lt.le
    · simp
  have hnorm : ‖((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
    have e : ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) =
        (((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) + (a : ℚ_[l]) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha.trans hr) ?_)
    have := PadicInt.norm_le_one (a : ℤ_[l])
    rwa [PadicInt.norm_def, PadicInt.coe_natCast] at this
  let u : ℤ_[l] := ⟨_, hnorm⟩
  have hu : (u : ℚ_[l]) = ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) := rfl
  have ha' : ‖(u : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by rw [hu]; exact ha
  refine ⟨u, (P.PD_χ K g).trans hu.symm, ?_⟩
  rw [toZModPow_eq_of_norm_sub_le u a r ha', key]
  rfl

end GlobalTheory.CycLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionLatticeGradedOfLevelLeStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachExpansionLattice_graded_of_level_le : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ s) = 1 → Full (Di (HW l) h T i) (Lat C h T i ζ) → Graded (Lat C h T i ζ) := by
  first | exact @GlobalTheory.NL.GradedLat.graded_of_level_le | exact GlobalTheory.NL.GradedLat.graded_of_level_le | (intros; apply GlobalTheory.NL.GradedLat.graded_of_level_le <;> assumption)
end

