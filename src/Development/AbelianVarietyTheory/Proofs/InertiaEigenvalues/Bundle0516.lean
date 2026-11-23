module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0253
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitBreuilKisinBasisInvariantEtale
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.LimBasis

variable {l : ℕ} [hl : Fact l.Prime]

theorem sep (z : WCb l) (h : ∀ n, (l : WCb l) ^ n ∣ z) : z = 0 := by
  ext m
  obtain ⟨y, hy⟩ := h (m + 1)
  rw [hy, mul_comm, WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self m)]
  simp

def Cg {ι κ : Type} (n : ℕ) (M : Matrix ι κ (WCb l)) : Prop := ∃ Y : Matrix ι κ (WCb l), M = ((l : WCb l) ^ n) • Y

section Cg

variable {ι κ μ : Type} {n : ℕ}

theorem cg_of {M : Matrix ι κ (WCb l)} (h : ∀ i j, (l : WCb l) ^ n ∣ M i j) : Cg n M :=
  ⟨Matrix.of fun i j => Classical.choose (h i j), by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    exact Classical.choose_spec (h i j)⟩

theorem Cg.dvd {M : Matrix ι κ (WCb l)} (h : Cg n M) (i : ι) (j : κ) : (l : WCb l) ^ n ∣ M i j := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨Y i j, by simp⟩

theorem Cg.add {M M' : Matrix ι κ (WCb l)} (h : Cg n M) (h' : Cg n M') : Cg n (M + M') := by
  obtain ⟨Y, rfl⟩ := h
  obtain ⟨Y', rfl⟩ := h'
  exact ⟨Y + Y', (smul_add _ _ _).symm⟩

theorem Cg.neg {M : Matrix ι κ (WCb l)} (h : Cg n M) : Cg n (-M) := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨-Y, (smul_neg _ _).symm⟩

theorem Cg.sub {M M' : Matrix ι κ (WCb l)} (h : Cg n M) (h' : Cg n M') : Cg n (M - M') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

theorem Cg.mul_left [Fintype κ] {M : Matrix κ μ (WCb l)} (P : Matrix ι κ (WCb l)) (h : Cg n M) : Cg n (P * M) := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨P * Y, Matrix.mul_smul _ _ _⟩

theorem Cg.mul_right [Fintype κ] {M : Matrix ι κ (WCb l)} (P : Matrix κ μ (WCb l)) (h : Cg n M) : Cg n (M * P) := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨Y * P, Matrix.smul_mul _ _ _⟩

theorem Cg.map (f : WCb l →+* WCb l) {M : Matrix ι κ (WCb l)} (h : Cg n M) : Cg n (M.map f) := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨Y.map f, Matrix.ext fun i j => by simp⟩

theorem Cg.eq_zero {M : Matrix ι κ (WCb l)} (h : ∀ n, Cg n M) : M = 0 := by
  refine Matrix.ext fun i j => ?_
  exact sep _ fun n => (h n).dvd i j

end Cg

variable {K : FinExt l} (bk : BK K)

def InOE {ι κ : Type} (M : Matrix ι κ (WCb l)) : Prop := ∀ i j, M i j ∈ bk.OE

variable {bk}

theorem InOE.mul {ι κ μ : Type} [Fintype κ] {M : Matrix ι κ (WCb l)} {M' : Matrix κ μ (WCb l)} (h : InOE bk M)
    (h' : InOE bk M') : InOE bk (M * M') := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (h i k) (h' k j)

theorem InOE.smul {ι κ : Type} {c : WCb l} (hc : c ∈ bk.OE) {M : Matrix ι κ (WCb l)} (h : InOE bk M) :
    InOE bk (c • M) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact Subring.mul_mem _ hc (h i j)

variable (bk)

theorem evW_mem (s : bk.S) : bk.evW s ∈ bk.OE := fun _ => ⟨0, s, 0, by simp⟩

theorem inOE_evW {ι κ : Type} (M : Matrix ι κ bk.S) : InOE bk (M.map bk.evW) := fun i j => evW_mem bk (M i j)

theorem mem_of_approx {x : WCb l} (h : ∀ n, ∃ w ∈ bk.OE, (l : WCb l) ^ n ∣ x - w) : x ∈ bk.OE := by
  intro n
  obtain ⟨w, hw, c, hc⟩ := h n
  obtain ⟨m, s, y, hy⟩ := hw n
  exact ⟨m, s, y + bk.evW X ^ m * c, by linear_combination bk.evW X ^ m * hc + hy⟩

theorem inOE_of_approx {ι κ : Type} {A : Matrix ι κ (WCb l)}
    (h : ∀ n, ∃ M : Matrix ι κ (WCb l), InOE bk M ∧ Cg n (A - M)) : InOE bk A := fun i j =>
  mem_of_approx bk fun n => by
    obtain ⟨M, hM, hc⟩ := h n
    exact ⟨M i j, hM i j, by simpa [Matrix.sub_apply] using hc.dvd i j⟩

theorem E_not_dvd : ¬ (l : bk.S) ∣ bk.E := by
  rintro ⟨s, hs⟩
  have h := congrArg (PowerSeries.coeff bk.Ep.natDegree) hs
  rw [BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree] at h
  have h2 : (1 : Wq l bk.a) = (PowerSeries.coeff bk.Ep.natDegree s) * (l : Wq l bk.a) := by
    rw [h, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, mul_comm]
  have h3 := congrArg (fun w : Wq l bk.a => w.coeff 0) h2
  simp only [WittVector.one_coeff_zero, WittVector.mul_charP_coeff_zero] at h3
  exact one_ne_zero h3

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)), IsUnit T0 → (∀ n, ∃ (R : Matrix (Fin d) (Fin (tw.d' n)) (WCb l)) (R' : Matrix (Fin (tw.d' n)) (Fin d) (WCb l)), (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (R * R' - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j)) → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g).val * T0.map (galW l (g : GQ l)) = T0) ∧ ∃ A0 A0' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A0 i j ∈ bk.OE) ∧ (∀ i j, A0' i j ∈ bk.OE) ∧ T0.map (frobW l) = T0 * A0 ∧ A0 * A0' = 1 := by
  intro l _ K bk τ _ d N ρ tw F T0 hT0 hR
  obtain ⟨-, -, hunit, -, -, hfix, hfrob⟩ := GlobalTheory.OEDvr.main l K bk
  obtain ⟨e, he, heE⟩ := hunit bk.E (E_not_dvd bk)
  have key : ∀ n, ∃ (R : Matrix (Fin d) (Fin (tw.d' n)) (WCb l)) (R' : Matrix (Fin (tw.d' n)) (Fin d) (WCb l)),
      InOE bk R ∧ InOE bk R' ∧ Cg n (zW (tw.Pi n) * (F n).T - T0 * R) ∧
      Cg n (T0 - zW (tw.Pi n) * (F n).T * R') := fun n => by
    obtain ⟨R, R', h1, h2, h3, h4⟩ := hR n
    refine ⟨R, R', h1, h2, cg_of h3, ?_⟩
    have e1 : T0 - zW (tw.Pi n) * (F n).T * R' =
        -(T0 * (R * R' - 1)) - (zW (tw.Pi n) * (F n).T - T0 * R) * R' := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]; abel
    rw [e1]
    exact ((cg_of h4).mul_left T0).neg.sub ((cg_of h3).mul_right R')
  have hdet : IsUnit T0.det := (Matrix.isUnit_iff_isUnit_det T0).1 hT0
  refine ⟨fun g hg => ?_, ?_⟩
  · let σ : WCb l →+* WCb l := (galW l (g : GQ l)).toRingEquiv.toRingHom
    have hσz : ∀ {m m' : Type} (M : Matrix m m' ℤ_[l]), (zW M).map σ = zW M := fun M =>
      Matrix.ext fun i j => (galW l (g : GQ l)).commutes (M i j)
    change zW (ρ g).val * T0.map σ = T0
    refine sub_eq_zero.1 (Cg.eq_zero fun n => ?_)
    obtain ⟨R, R', -, hR', -, h2⟩ := key n
    have hR'σ : R'.map σ = R' := Matrix.ext fun i j => hfix g hg _ (hR' i j)
    have hT' : zW (tw.ρ' n g).val * (F n).T.map σ = (F n).T := (F n).fix g hg
    have hequi : Cg n (zW (ρ g).val * zW (tw.Pi n) - zW (tw.Pi n) * zW (tw.ρ' n g).val) := by
      have e2 : zW (ρ g).val * zW (tw.Pi n) - zW (tw.Pi n) * zW (tw.ρ' n g).val =
          -zW (tw.Pi n * (tw.ρ' n g).val - (ρ g).val * tw.Pi n) := by
        simp only [zW, Matrix.map_sub _ (map_sub (algebraMap ℤ_[l] (WCb l))), Matrix.map_mul, neg_sub]
      rw [e2]
      refine (cg_of fun i j => ?_).neg
      have := map_dvd (algebraMap ℤ_[l] (WCb l)) ((tw.onto n).equi g i j)
      rwa [map_pow, map_natCast] at this
    have h3 : Cg n (T0.map σ - zW (tw.Pi n) * (F n).T.map σ * R') := by
      have := h2.map σ
      rwa [Matrix.map_sub _ (map_sub σ), Matrix.map_mul, Matrix.map_mul, hσz, hR'σ] at this
    have e3 : zW (ρ g).val * T0.map σ - T0 = zW (ρ g).val * (T0.map σ - zW (tw.Pi n) * (F n).T.map σ * R') +
        (zW (ρ g).val * zW (tw.Pi n) - zW (tw.Pi n) * zW (tw.ρ' n g).val) * (F n).T.map σ * R' -
        (T0 - zW (tw.Pi n) * (zW (tw.ρ' n g).val * (F n).T.map σ) * R') := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]; abel
    rw [e3, hT']
    exact ((h3.mul_left _).add ((hequi.mul_right _).mul_right _)).sub h2
  · let f : WCb l →+* WCb l := (frobW l).toRingHom
    change ∃ A0 A0' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A0 i j ∈ bk.OE) ∧ (∀ i j, A0' i j ∈ bk.OE) ∧
      T0.map f = T0 * A0 ∧ A0 * A0' = 1
    have hfz : ∀ {m m' : Type} (M : Matrix m m' ℤ_[l]), (zW M).map f = zW M := fun M =>
      Matrix.ext fun i j => (frobW l).commutes (M i j)
    have hfOE : ∀ {m m' : Type} {M : Matrix m m' (WCb l)}, InOE bk M → InOE bk (M.map f) :=
      fun h i j => hfrob _ (h i j)
    have hTf : IsUnit (T0.map f) := hT0.map f.mapMatrix
    have hdetf : IsUnit (T0.map f).det := (Matrix.isUnit_iff_isUnit_det _).1 hTf
    have heN : bk.evW bk.E ^ N * e ^ N = 1 := by rw [← mul_pow, heE, one_pow]
    have hφ : ∀ n, (F n).T.map f = (F n).T * (e ^ N • (F n).A.map bk.evW) := fun n => by
      have h := (F n).φ
      rw [Matrix.mul_smul, ← h, smul_smul, mul_comm (e ^ N), heN, one_smul]
      rfl
    have hφ' : ∀ n, (F n).T = (F n).T.map f * (e ^ N • (F n).A'.map bk.evW) := fun n => by
      have hA : (F n).A.map bk.evW * (F n).A'.map bk.evW =
          (bk.evW bk.E ^ (2 * N)) • (1 : Matrix (Fin (tw.d' n)) (Fin (tw.d' n)) (WCb l)) := by
        rw [← Matrix.map_mul, (F n).A_mul]
        refine Matrix.ext fun i j => ?_
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      have hs : e ^ N * (e ^ N * bk.evW bk.E ^ (2 * N)) = 1 := by
        linear_combination (bk.evW bk.E ^ N * e ^ N + 1) * heN
      rw [hφ n, Matrix.mul_assoc]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hA, Matrix.mul_one]
      rw [hs, one_smul]
    refine ⟨T0⁻¹ * T0.map f, (T0.map f)⁻¹ * T0, ?_, ?_, ?_, ?_⟩
    · refine inOE_of_approx bk fun n => ?_
      obtain ⟨R, R', hR, hR', h1, h2⟩ := key n
      refine ⟨R * (e ^ N • (F n).A.map bk.evW) * R'.map f,
        (hR.mul ((inOE_evW bk _).smul (pow_mem he N))).mul (hfOE hR'), ?_⟩
      have i4 : T0.map f - T0 * (R * (e ^ N • (F n).A.map bk.evW) * R'.map f) =
          (T0 - zW (tw.Pi n) * (F n).T * R').map f +
            (zW (tw.Pi n) * (F n).T - T0 * R) * (e ^ N • (F n).A.map bk.evW) * R'.map f := by
        rw [Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, hfz, hφ n]
        simp only [Matrix.sub_mul, Matrix.mul_assoc]; abel
      have e4 : T0⁻¹ * T0.map f - R * (e ^ N • (F n).A.map bk.evW) * R'.map f =
          T0⁻¹ * (T0.map f - T0 * (R * (e ^ N • (F n).A.map bk.evW) * R'.map f)) := by
        rw [Matrix.mul_sub, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]
      rw [e4, i4]
      exact ((h2.map f).add ((h1.mul_right _).mul_right _)).mul_left _
    · refine inOE_of_approx bk fun n => ?_
      obtain ⟨R, R', hR, hR', h1, h2⟩ := key n
      refine ⟨R.map f * (e ^ N • (F n).A'.map bk.evW) * R',
        ((hfOE hR).mul ((inOE_evW bk _).smul (pow_mem he N))).mul hR', ?_⟩
      have e6 : zW (tw.Pi n) * ((F n).T.map f * ((e ^ N • (F n).A'.map bk.evW) * R')) =
          zW (tw.Pi n) * ((F n).T * R') := by
        rw [← Matrix.mul_assoc ((F n).T.map f), ← hφ' n]
      have i5 : T0 - T0.map f * (R.map f * (e ^ N • (F n).A'.map bk.evW) * R') =
          (T0 - zW (tw.Pi n) * (F n).T * R') +
            (zW (tw.Pi n) * (F n).T - T0 * R).map f * (e ^ N • (F n).A'.map bk.evW) * R' := by
        rw [Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, hfz]
        simp only [Matrix.sub_mul, Matrix.mul_assoc, e6]; abel
      have e5 : (T0.map f)⁻¹ * T0 - R.map f * (e ^ N • (F n).A'.map bk.evW) * R' =
          (T0.map f)⁻¹ * (T0 - T0.map f * (R.map f * (e ^ N • (F n).A'.map bk.evW) * R')) := by
        rw [Matrix.mul_sub, Matrix.nonsing_inv_mul_cancel_left _ _ hdetf]
      rw [e5, i5]
      exact (h2.add (((h1.map f).mul_right _).mul_right _)).mul_left _
    · exact (Matrix.mul_nonsing_inv_cancel_left T0 _ hdet).symm
    · rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdetf, Matrix.nonsing_inv_mul _ hdet]

end GlobalTheory.LimBasis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMulVec
section
noncomputable section

namespace GlobalTheory.Pass.LocDirect

open _root_.Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem isTopRing : IsTopologicalRing (Br.LL D.nbr i w hw) :=
  (goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL).2.2.2.1

def ModuleGaloisRepresentation {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  haveI := isTopRing i w hw
  GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) (Br.loc D.nbr i w hw M)
    (GlobalTheory.PotDual.continuous_loc D i w hw M hM)

abbrev fam (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    Br.G D.nbr i w hw →* Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw) :=
  Br.loc D.nbr i w hw (rTwO D.nd i r x)

def toLLv {a n : ℕ} (y : Fin a → Fin n → KK D.nd i) : Fin a → Fin n → Br.LL D.nbr i w hw :=
  fun j m => Br.toLLK (D.nbr i w hw) (y j m)

theorem loc_mulVec {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (v : Fin k → KK D.nd i) :
    (Br.loc D.nbr i w hw M g).mulVec (fun m => Br.toLLK (D.nbr i w hw) (v m)) =
      fun m => Br.toLLK (D.nbr i w hw)
        ((mapM (toK D.nd i) M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)).mulVec v m) := by
  funext m
  rw [RingHom.map_mulVec]
  congr 1
  ext a b
  simp only [Br.loc, Br.locM, Br.locO, mapM, MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, toK]
  exact congrArg Subtype.val (Br.toLLK_alg (D.nbr i w hw) _).symm

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

def XV {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) :
    Submodule (Br.LL D.nbr i w hw) (Fin a → Fin D.R.nV → Br.LL D.nbr i w hw) :=
  Submodule.span _ (toLLv i w hw '' (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)))

theorem XV_stable {a : ℕ} (x : Fin a → D.nd.X i) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
      (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
    (g : Br.G D.nbr i w hw) :
    ∀ u ∈ XV i w hw Y, sumRho (fun j : Fin a => fam i w hw r (x j)) id g u ∈ XV i w hw Y := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, rfl⟩ := hu
    refine Submodule.subset_span ⟨_, hst ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) y hy, ?_⟩
    funext j
    rw [sumRho_apply]
    exact (loc_mulVec i w hw _ g (y j)).symm
  | zero => simp
  | add u v _ _ hu hv => rw [map_add (f := _)]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ c hu

def Xgrep {a : ℕ} (x : Fin a → D.nd.X i)
    (hc : ∀ j, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r (x j)) g)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
      (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  haveI := isTopRing i w hw
  GRep.sub (GRep.sum (Qp := ℚ_[D.nd.l i]) (O := Br.OLL D.nbr i w hw) (fun j : Fin a => fam i w hw r (x j))
    (fun j v => (hc j).matrix_mulVec continuous_const) id) (XV i w hw Y) (XV_stable i w hw r x Y hst)

def pushSet {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) {a : ℕ} (x : Fin a → D.nd.X i)
    (E : Fin a → Fin D.R.nV → KK D.nd i) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
      (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
    (hE : ∀ γ : GE D.nd,
      (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y) :
    Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) :=
  {c | ∃ φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k,
      (∀ (γ : GE D.nd) (y : ↥Y), φ ⟨_, hst γ y.1 y.2⟩ = WKG M γ (φ y)) ∧
      c = fun g => Br.phi (D.nbr i w hw) k
        (φ ⟨_, hE ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)⟩)}

theorem mem_cutCoc (Xs : Set (D.nd.X i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (c : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) :
    c ∈ cutCoc i w hw r Xs M ↔ ∃ (a : ℕ) (x : Fin a → D.nd.X i) (_ : ∀ j, x j ∈ Xs) (E : Fin a → Fin D.R.nV → KK D.nd i)
      (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (_ : Y.FG)
      (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
        (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
      (hE : ∀ γ : GE D.nd,
        (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y),
      c ∈ pushSet i w hw r M x E Y hst hE := Iff.rfl
end GlobalTheory.Pass.LocDirect
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTatePeriodConjRatioUnramified
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon


set_option maxHeartbeats 1000000 in
theorem lt_period_conj_ratio : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (s : ℕ), 0 < s → ∀ (x : P.R.B), IsUnit x → P.φB^[s] x = (l : P.R.B) * x → P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → (∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1) → ∀ g : GQ l, ∃ a : ↥(MaximalUnramifiedExtension l), fr l s a = a ∧ P.actQ g x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B a * x := by
  intro l _ P AI T s hs x hx hφ h1 h2 hj g
  obtain ⟨-, -, hsh, hinv, -, -, -, htz, tadd, t0, -⟩ := _root_.GlobalTheory.PMon.bdR_tied l P AI T
  have iter_mul : ∀ (m : ℕ) (a b : P.R.B), P.φB^[m] (a * b) = P.φB^[m] a * P.φB^[m] b := by
    intro m a b
    induction m generalizing a b with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, map_mul]
  have iter_one : ∀ m : ℕ, P.φB^[m] (1 : P.R.B) = 1 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, map_one]
  have iter_act : ∀ (m : ℕ) (b : P.R.B), P.φB^[m] (P.actQ g b) = P.actQ g (P.φB^[m] b) := by
    intro m b
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, phiB_actQ]
  have ev_mul : ∀ (m : ℕ) (a b : P.R.B), ev P m (a * b) = ev P m a * ev P m b := by
    intro m a b
    rw [← evHom_apply, map_mul, evHom_apply, evHom_apply]
  obtain ⟨w, hw⟩ : ∃ w : P.R.B, x * w = 1 := ⟨_, hx.mul_val_inv⟩
  set y := P.actQ g x * w with hy
  have hyx : y * x = P.actQ g x := by rw [hy, mul_assoc, mul_comm w x, hw, mul_one]

  have hfix : P.φB^[s] y = y := by
    have e1 : P.φB^[s] x * P.φB^[s] w = 1 := by rw [← iter_mul, hw, iter_one]
    rw [hφ] at e1
    rw [hy, iter_mul, iter_act, hφ, map_mul, map_natCast]
    calc (l : P.R.B) * P.actQ g x * P.φB^[s] w = P.actQ g x * (((l : P.R.B) * x * P.φB^[s] w) * w) := by
          linear_combination (-(l : P.R.B) * P.actQ g x * P.φB^[s] w) * hw
      _ = P.actQ g x * w := by rw [e1, one_mul]

  have key : ∀ (k : ℤ) (e u v z : P.R.BdR), e = tz P k * u → u * v = 1 → u ∈ Fil P 0 → v ∈ Fil P 0 →
      z * e = P.actQdR g e → z ∈ Fil P 0 := by
    intro k e u v z he huv hu hv hz
    have hk : tz P k * tz P (-k) = 1 := by rw [← tadd, add_neg_cancel, t0]
    have hz' : z * e = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) * tz P k * P.actQdR g u := by
      rw [hz, he, map_mul, htz]
    have hzz : z = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) * P.actQdR g u * v := by
      linear_combination (-z + algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) * P.actQdR g u * v) * hk
        - z * tz P k * tz P (-k) * huv - tz P (-k) * v * z * he + tz P (-k) * v * hz'
    rw [hzz]
    exact Fil_mul_right (Fil_mul_left (q_mem_Fil P _) (Fil_act g hu)) hv
  have hev : ∀ j, ev P j y * ev P j x = P.actQdR g (ev P j x) := by
    intro j
    rw [← ev_mul, hyx, ev_act]
  have hfil : ∀ j < s, ev P j y ∈ Fil P 0 := by
    intro j hjs
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · have hu0 : tz P (-1) * P.ιB x ∈ Fil P 0 := by
        have := (hsh 1 (-1) (P.ιB x)).1 h1
        rwa [show (1 : ℤ) + -1 = 0 by norm_num] at this
      have hu1 : tz P (-1) * P.ιB x ∉ Fil P 1 := by
        intro h
        apply h2
        exact (hsh 2 (-1) (P.ιB x)).2 (by rw [show (2 : ℤ) + -1 = 1 by norm_num]; exact h)
      obtain ⟨v, hv, huv⟩ := hinv _ hu0 hu1
      refine key 1 (ev P 0 x) _ v _ ?_ huv hu0 hv (hev 0)
      change P.ιB x = tz P 1 * (tz P (-1) * P.ιB x)
      rw [← mul_assoc, ← tadd, show (1 : ℤ) + -1 = 0 by norm_num, t0, one_mul]
    · obtain ⟨e0, e1⟩ := hj j hpos hjs
      obtain ⟨v, hv, huv⟩ := hinv _ e0 e1
      exact key 0 (ev P j x) (ev P j x) v _ (by rw [t0, one_mul]) huv e0 hv (hev j)
  obtain ⟨a, ha, hya⟩ := _root_.GlobalTheory.PMon.unr_of_iterate_fixed l P AI T s hs y hfix hfil
  exact ⟨a, ha, by rw [← hyx, hya]⟩

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBlochKatoQuotientPowIffReductionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_blochKato_quotient_pow_iff_reduction : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ HfQ (P.PD K) LA _ hI ↔ ∃ a : ↥(latticeCocycles LA), (a : ↥(GK K) → A.V) ∈ finiteCocycles (P.PD K) A.ρ ∧ c = redT LA _ a := by
  first | exact @GlobalTheory.BKTorsionRed.mem_HfQ_iff_red | exact GlobalTheory.BKTorsionRed.mem_HfQ_iff_red | (intros; apply GlobalTheory.BKTorsionRed.mem_HfQ_iff_red <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulActBSubMem
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

theorem muPow_smul_actB_sub_mem : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (ε : OCb l), IsEps ε → ∀ (k : ℕ) (v : TW (OB l O) T) (z : TW (OA l O) T), toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • v = TWincl (toB l O) T z → ∃ z' : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • (actB (sQ l) T g v - v) = TWincl (toB l O) T z' := by
  intro l _ O K _ _ _ _ _ _ _ _ _ T g ε hε k v z hv
  obtain ⟨δ, hδ, -⟩ := hε.2
  obtain ⟨-, -, -, -, -, hgal, -⟩ := (_root_.GlobalTheory.MuOfEps.main l).2 ε δ hε hδ
  obtain ⟨u, hu⟩ := hgal (sQ l g)
  have hB : ∀ x : OA l O, toB l O (galOA O (sQ l g) x) = galOB O (sQ l g) (toB l O x) := fun x => by
    simp only [toB, AlgHom.comp_apply, galOB_toOB, galOCr_toOCr]
  have hμ : galOA O (sQ l g) ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) =
      ((1 : O) ⊗ₜ[ℤ_[l]] (u : Ainf l)) ^ k * ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) := by
    rw [map_pow, galOA_tmul, hu, ← mul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hinv : ((1 : O) ⊗ₜ[ℤ_[l]] ((u⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ k * ((1 : O) ⊗ₜ[ℤ_[l]] (u : Ainf l)) ^ k = 1 := by
    rw [← mul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, ← Algebra.TensorProduct.one_def, one_pow]
  set m := toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) with hm
  set w := TWact (galOA O (sQ l g)) T g z with hw
  have h1 : actB (sQ l) T g (m • v) = TWincl (toB l O) T w := by
    rw [hv]
    exact (GlobalTheory.Cyc.Decomp.TWincl_act (toB l O) (galOA O (sQ l g)) (galOB O (sQ l g)) hB T g z).symm
  have h2 : actB (sQ l) T g (m • v) =
      toB l O (((1 : O) ⊗ₜ[ℤ_[l]] (u : Ainf l)) ^ k) • (m • actB (sQ l) T g v) := by
    rw [actB, GlobalTheory.Cyc.Decomp.TWact_smul, hm, ← hB, hμ, map_mul, mul_smul]
  have h3 : m • actB (sQ l) T g v =
      TWincl (toB l O) T ((((1 : O) ⊗ₜ[ℤ_[l]] ((u⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ k) • w) := by
    rw [GlobalTheory.Cyc.Decomp.TWincl_smul, ← h1, h2, smul_smul, ← map_mul, hinv, map_one, one_smul]
  refine ⟨(((1 : O) ⊗ₜ[ℤ_[l]] ((u⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ k) • w - z, ?_⟩
  rw [smul_sub, h3, hv, map_sub]

end GlobalTheory.BKGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TaylorShiftFrobeniusMemDividedTwoVariableGeneratStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylorShift_frobenius_mem_dividedTwoVariableGeneratorSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ x : (Wq l a)⟦X⟧, shP a sh (inclS t K (frobS l a x)) ∈ PPSet t K e ∧ ∃ B ∈ PPSet t K e, shP a sh (inclS t K (frobS l a x)) - constP a K (inclS t K (frobS l a x)) = (l : ZMod a → K⟦X⟧⟦X⟧) * B := by
  first | exact @GlobalTheory.CrysPrism.ShMem.shP_frob_mem | exact GlobalTheory.CrysPrism.ShMem.shP_frob_mem | (intros; apply GlobalTheory.CrysPrism.ShMem.shP_frob_mem <;> assumption)
end

