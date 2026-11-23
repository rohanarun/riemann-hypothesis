module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.Columns.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LiesOverSpanOfNatCastMemHeightOne
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0068
public import Formalism.GradedWeylDivisibility.FinalC
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOneDetIdealTransportedLattice
section
open NumberField IsDedekindDomain nonZeroDivisors

noncomputable section

namespace GlobalTheory.CharValCompare

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.IndefiniteRowSideFullHecke

section Pull

variable {E E' : Type} [Field E] [Field E'] (e : E ≃+* E')

theorem map_osmul (c : 𝓞 E) (a : E) : e (c • a) = RingOfIntegers.mapRingEquiv e c • e a := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

def pull (I : Submodule (𝓞 E') E') : Submodule (𝓞 E) E where
  carrier := {x | e x ∈ I}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    show e (a + b) ∈ I
    rw [e.map_add]
    exact I.add_mem ha hb
  smul_mem' := fun c a ha => by
    show e (c • a) ∈ I
    rw [map_osmul]
    exact I.smul_mem _ ha

theorem mem_pull (I : Submodule (𝓞 E') E') (x : E) : x ∈ pull e I ↔ e x ∈ I := Iff.rfl

theorem pull_one : pull e 1 = 1 := by
  ext x
  rw [mem_pull, Submodule.mem_one, Submodule.mem_one]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨RingOfIntegers.mapRingEquiv e.symm r, by rw [← e.symm_apply_apply x, ← hr]; rfl⟩
  · rintro ⟨r, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv e r, rfl⟩

theorem pull_norm (c : E → E) (c' : E' → E') (h : ∀ x, e (c x) = c' (e x)) {I : Submodule (𝓞 E') E'}
    (hI : ∃ J : Submodule (𝓞 E') E', (∀ x, x ∈ J ↔ c' x ∈ I) ∧ I * J = 1) :
    ∃ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ c x ∈ pull e I) ∧ pull e I * J = 1 := by
  obtain ⟨J, hJ, hIJ⟩ := hI
  refine ⟨pull e J, fun x => by rw [mem_pull, mem_pull, hJ, h], le_antisymm ?_ ?_⟩
  · rw [Submodule.mul_le]
    intro x hx y hy
    rw [← pull_one e, mem_pull, map_mul, ← hIJ]
    exact Submodule.mul_mem_mul hx hy
  · rw [Submodule.one_le]
    have h1 : ∀ z ∈ I * J, e.symm z ∈ pull e I * pull e J := by
      intro z hz
      refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) fun a b ha hb => ?_
      · rw [map_mul]
        exact Submodule.mul_mem_mul (by simpa [mem_pull] using ha) (by simpa [mem_pull] using hb)
      · rw [e.symm.map_add]
        exact add_mem ha hb
    simpa using h1 1 (hIJ ▸ Submodule.mem_one.2 ⟨1, map_one _⟩)

end Pull

section Vp

variable {E : Type} [Field E] [NumberField E] [StarRing E]


end Vp

section Val

variable {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)



end Val

section Chi

variable {D : D7} {X : Fields} (s : Seam D X) {χ : TaylorLogMetric.IdE D → ℂ}

theorem mem_lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (y : Fin n → D.host.E) :
    y ∈ s.lat N ↔ (fun i => s.iE.symm (y i)) ∈ N := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      simpa using hx
    | zero =>
      convert N.zero_mem using 1
      funext i
      exact map_zero _
    | add a b _ _ ha hb =>
      convert N.add_mem ha hb using 1
      funext i
      exact map_add _ _ _
    | smul c a _ ha =>
      convert N.smul_mem (RingOfIntegers.mapRingEquiv s.iE.symm c) ha using 1
      funext i
      exact map_osmul s.iE.symm c (a i)
  · intro hy
    exact Submodule.subset_span ⟨_, hy, funext fun i => s.iE.apply_symm_apply _⟩

theorem detId_lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N) = pull s.iE.symm (detI N) := by
  apply le_antisymm
  · rw [TaylorLogMetric.detId, Submodule.span_le]
    rintro _ ⟨A, hA, rfl⟩
    refine Submodule.subset_span ⟨A.map s.iE.symm, fun v hv => ?_, (s.iE.symm : D.host.E →+* X.E).map_det A⟩
    have h1 := (mem_lat s N _).1 (hA (fun i => s.iE (v i)) fun i _ => by
      have := hv i (Set.mem_univ _)
      rw [← pull_one s.iE] at this
      exact this)
    convert h1 using 1
    funext i
    simp [Matrix.mulVec, dotProduct]
  · have : detI N ≤ pull s.iE (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) := by
      rw [detI, Submodule.span_le]
      rintro _ ⟨A, hA, rfl⟩
      refine Submodule.subset_span ⟨A.map s.iE, fun v hv => (mem_lat s N _).2 ?_, (s.iE : X.E →+* D.host.E).map_det A⟩
      have h1 := hA (fun i => s.iE.symm (v i)) fun i _ => by
        have := hv i (Set.mem_univ _)
        rw [← pull_one s.iE.symm] at this
        exact this
      convert h1 using 1
      funext i
      simp [Matrix.mulVec, dotProduct]
    intro y hy
    simpa [mem_pull] using this hy

variable {s}

theorem normOne_idealPreimageUnderRingEquiv (hs : s.Ok) {I : Submodule (𝓞 X.E) X.E} (h : NormOne I) : TaylorLogMetric.N1 D (pull s.iE.symm I) :=
  pull_norm s.iE.symm D.host.conj star (fun x => by rw [RingEquiv.symm_apply_eq, hs.2, s.iE.apply_symm_apply]) h

theorem normOne_detIdeal_transportedLattice (hs : s.Ok) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) := by
  rw [detId_lat]
  exact normOne_idealPreimageUnderRingEquiv hs (normOne_detI hN)

end Chi

section Parts

variable {D : D7} {Z : Dat} {s : Seam D Z.X} {χ : TaylorLogMetric.IdE D → ℂ}
  {sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)} {S : Set ℕ}
  {mu : Tup Z.X.F Z.X.E Z.X.K S} {cst : LocCst Z.X (rowSG Z.Pr sel mu)}

theorem T_mem (hZ : Z.Ok) {u : Z.Pr.Word} {P : HeightOneSpectrum (𝓞 Z.X.E)} (hP : P ∈ Z.Pr.vT u) :
    ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∈ P.asIdeal := by
  rw [← hZ.primes.piT_norm u]
  exact Ideal.mul_mem_right _ _ (decoFin_mem_of_mem_divs hP)

end Parts

end GlobalTheory.CharValCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RenameMemDualWeyl
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

noncomputable section

namespace GlobalTheory.SubstMem

open Formalism.GradedWeylDivisibility

variable {K : Type} [Field K]


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
theorem _root_.GlobalTheory.SubstMem.rename_mem_dualWeyl {a b : ℕ} (hab : a ≤ b) (ν : Fin a → ℕ) (ν' : Fin b → ℕ)
    (h1 : ∀ i, ν' (Fin.castLE hab i) = ν i) (h2 : ∀ j : Fin b, a ≤ (j : ℕ) → ν' j = 0)
    (f : MvPolynomial (Fin a × Fin a) K) (hf : f ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl K a a ν) :
    rename (Prod.map (Fin.castLE hab) (Fin.castLE hab)) f ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl K b b ν' := by
  rw [_root_.Formalism.GradedWeylDivisibility.mem_dualWeyl_iff] at hf ⊢
  obtain ⟨hhom, hinv⟩ := hf
  refine ⟨?_, ?_⟩
  · intro d hd
    have hinj : Function.Injective (Prod.map (Fin.castLE hab) (Fin.castLE hab)) :=
      (Fin.castLE_injective hab).prodMap (Fin.castLE_injective hab)
    have hmem : d ∈ (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab)) f).support :=
      mem_support_iff.2 hd
    rw [support_rename_of_injective hinj, Finset.mem_image] at hmem
    obtain ⟨d0, hd0, rfl⟩ := hmem
    have h0 := hhom (mem_support_iff.1 hd0)
    rw [Finsupp.weight_apply] at h0
    rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul])]
    funext k
    by_cases hk : (k : ℕ) < a
    · have hk' : k = Fin.castLE hab ⟨k, hk⟩ := Fin.ext rfl
      rw [hk', h1, ← h0]
      simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp [_root_.Formalism.GradedWeylDivisibility.colW, Pi.single_apply]
      simp only [Fin.ext_iff, Fin.coe_castLE]
    · rw [h2 k (not_lt.1 hk)]
      simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_eq_zero fun v _ => ?_
      have hne : Fin.castLE hab v.2 ≠ k := by
        intro h; apply hk; rw [← h]; simp
      simp [_root_.Formalism.GradedWeylDivisibility.colW, Pi.single_apply, Ne.symm hne]
  · intro l j hlj
    by_cases hj : (j : ℕ) < a
    · have hl : (l : ℕ) < a := lt_trans hlj hj
      obtain ⟨l', rfl⟩ : ∃ l' : Fin a, Fin.castLE hab l' = l := ⟨⟨l, hl⟩, Fin.ext rfl⟩
      obtain ⟨j', rfl⟩ : ∃ j' : Fin a, Fin.castLE hab j' = j := ⟨⟨j, hj⟩, Fin.ext rfl⟩
      have key : (_root_.Formalism.GradedWeylDivisibility.colAddGen K (Fin.castLE hab l') (Fin.castLE hab j')).comp
          (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab))) =
          (rename (Option.map (Prod.map (Fin.castLE hab) (Fin.castLE hab)))).comp
            (_root_.Formalism.GradedWeylDivisibility.colAddGen K (r := a) l' j') := by
        apply MvPolynomial.algHom_ext
        rintro ⟨v1, v2⟩
        by_cases hv : v2 = j'
        · subst hv
          simp only [AlgHom.comp_apply, rename_X, _root_.Formalism.GradedWeylDivisibility.colAddGen, aeval_X, Prod.map_snd, Prod.map_fst,
            if_pos rfl]
          simp only [ite_true, if_true, map_add (f := _), map_mul, rename_X]
          rfl
        · have hv' : Fin.castLE hab v2 ≠ Fin.castLE hab j' :=
            fun h => hv (Fin.castLE_injective hab h)
          simp only [AlgHom.comp_apply, rename_X, _root_.Formalism.GradedWeylDivisibility.colAddGen, aeval_X, Prod.map_snd, Prod.map_fst,
            if_neg hv, if_neg hv']
          rfl
      have e := DFunLike.congr_fun key f
      simp only [AlgHom.comp_apply] at e
      rw [e, hinv l' j' (show l' < j' from hlj), rename_rename, rename_rename]
      rfl
    · have key : (_root_.Formalism.GradedWeylDivisibility.colAddGen K l j).comp (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab))) =
          (rename some).comp (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab))) := by
        apply MvPolynomial.algHom_ext
        intro v
        have hne : Fin.castLE hab v.2 ≠ j := by
          intro h; apply hj; rw [← h]; exact v.2.isLt
        simp only [AlgHom.comp_apply, rename_X, _root_.Formalism.GradedWeylDivisibility.colAddGen, aeval_X, Prod.map_snd, if_neg hne]
      exact DFunLike.congr_fun key f


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
theorem _root_.GlobalTheory.SubstMem.det_pow_mem (a m : ℕ) :
    _root_.Formalism.GradedWeylDivisibility.initMinor K (id : Fin a → Fin a) le_rfl ^ m ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl K a a (fun _ => m) := by
  refine _root_.Formalism.GradedWeylDivisibility.dualWeyl_of_eq (_root_.Formalism.GradedWeylDivisibility.dualWeyl_pow (_root_.Formalism.GradedWeylDivisibility.initMinor_mem (R := K) (id : Fin a → Fin a) le_rfl) m) ?_
  funext i
  simp [_root_.Formalism.GradedWeylDivisibility.initW]

def padRows {a b : ℕ} (A : Matrix (Fin a) (Fin b) K) : Matrix (Fin b) (Fin b) K :=
  fun α β => if h : (α : ℕ) < a then A ⟨α, h⟩ β else 0

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
theorem _root_.GlobalTheory.SubstMem.substAdj_blockEmb {ι : Type} {a b : ℕ} (hab : a ≤ b)
    (ap : ι → Matrix (Fin a) (Fin b) K) (τ : ι) (f : MvPolynomial (Fin a × Fin a) K) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.substAdj hab ap (_root_.Formalism.GradedWeylDivisibility.blockEmb K τ f) =
      _root_.Formalism.GradedWeylDivisibility.blockEmb K τ (_root_.Formalism.GradedWeylDivisibility.rowAct K (_root_.GlobalTheory.SubstMem.padRows (ap τ))
        (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab)) f)) := by
  have key : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.substAdj hab ap).comp (_root_.Formalism.GradedWeylDivisibility.blockEmb K τ) = (_root_.Formalism.GradedWeylDivisibility.blockEmb K τ).comp
      ((_root_.Formalism.GradedWeylDivisibility.rowAct K (_root_.GlobalTheory.SubstMem.padRows (ap τ))).comp
        (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab)))) := by
    apply MvPolynomial.algHom_ext
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.substAdj, _root_.Formalism.GradedWeylDivisibility.blockEmb, _root_.Formalism.GradedWeylDivisibility.rowAct, _root_.GlobalTheory.SubstMem.padRows, map_sum]
  exact DFunLike.congr_fun key f

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem DomWeight_detShift_eq_w_last {N : ℕ} (l : _root_.Formalism.BasicNotions.DomWeight N) (h : 0 < N) :
    l.detShift = l.w ⟨N - 1, by omega⟩ := by
  unfold _root_.Formalism.BasicNotions.DomWeight.detShift
  rw [dite_eq_left h]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem DomWeight_detShift_le_w {N : ℕ} (l : _root_.Formalism.BasicNotions.DomWeight N) (i : Fin N) : l.detShift ≤ l.w i := by
  rw [DomWeight_detShift_eq_w_last l (Fin.pos i)]
  exact l.anti (Fin.le_def.2 (by simp; omega))

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem isWeightedHomogeneous_colW_rowAct_of_isWeightedHomogeneous {R : Type} [CommRing R] {r n : ℕ}
    (g : Matrix (Fin r) (Fin r) R) {f : MvPolynomial (Fin r × Fin n) R} {ν : Fin n → ℕ}
    (hf : IsWeightedHomogeneous (_root_.Formalism.GradedWeylDivisibility.colW r n) f ν) :
    IsWeightedHomogeneous (_root_.Formalism.GradedWeylDivisibility.colW r n) (_root_.Formalism.GradedWeylDivisibility.rowAct R g f) ν := by
  rw [← mem_weightedHomogeneousSubmodule]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← support_sum_monomial_coeff f, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [mem_weightedHomogeneousSubmodule, ← hf (mem_support_iff.1 hd)]
  have e : _root_.Formalism.GradedWeylDivisibility.rowAct R g (monomial d (AddMonoidAlgebra.coeff f d)) =
      C (AddMonoidAlgebra.coeff f d) * d.prod (fun v k => (_root_.Formalism.GradedWeylDivisibility.rowAct R g (X v)) ^ k) := by
    simp only [_root_.Formalism.GradedWeylDivisibility.rowAct, aeval_monomial, aeval_X, algebraMap_eq]
  rw [e, Finsupp.weight_apply, ← zero_add (d.sum fun i c => c • _root_.Formalism.GradedWeylDivisibility.colW r n i)]
  exact (isWeightedHomogeneous_C _ _).mul
    (IsWeightedHomogeneous.prod _ _ _ fun v _ => (_root_.Formalism.GradedWeylDivisibility.rowAct_X_isWH g v).pow (d v))

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem rowAct_mem_dualWeyl_of_mem_dualWeyl {R : Type} [CommRing R] {r n : ℕ}
    (g : Matrix (Fin r) (Fin r) R) {ν : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) R}
    (hf : f ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl R r n ν) : _root_.Formalism.GradedWeylDivisibility.rowAct R g f ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl R r n ν := by
  rw [_root_.Formalism.GradedWeylDivisibility.mem_dualWeyl_iff] at hf ⊢
  refine ⟨isWeightedHomogeneous_colW_rowAct_of_isWeightedHomogeneous g hf.1, fun l j hlj => ?_⟩
  rw [_root_.Formalism.GradedWeylDivisibility.colAddGen_rowAct, hf.2 l j hlj, ← _root_.Formalism.GradedWeylDivisibility.rename_rowAct]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem frDet_eq_blockEmb_initMinor_id {K : Type} [Field K] {ι : Type} (a : ℕ) (τ : ι) :
    _root_.Formalism.L2.Ker.frDet K a τ = _root_.Formalism.GradedWeylDivisibility.blockEmb K τ (_root_.Formalism.GradedWeylDivisibility.initMinor K (id : Fin a → Fin a) le_rfl) := by
  simp only [_root_.Formalism.L2.Ker.frDet, _root_.Formalism.GradedWeylDivisibility.initMinor, AlgHom.map_det]
  congr 1
  ext p q
  simp [_root_.Formalism.GradedWeylDivisibility.blockEmb]


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
theorem _root_.GlobalTheory.SubstMem.substAdj_sharp_mem : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι]
    (a b : ℕ) (hab : a < b) (lam : ι → _root_.Formalism.BasicNotions.DomWeight a) (lam' : ι → _root_.Formalism.BasicNotions.DomWeight b) (s s' : ι → ℤ)
    (n : ι → ℕ), _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.WtCompat hab lam lam' s s' n →
    ∀ (ap : ι → Matrix (Fin a) (Fin b) K), ∀ P ∈ _root_.Formalism.L2.DIV.VV K lam,
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.substAdj hab.le ap (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.sharp n P) ∈ _root_.Formalism.L2.DIV.VV K lam' := by
  intro K _ ι _ a b hab lam lam' s s' n hc ap P hP
  obtain ⟨hc1, hc2, hc3⟩ := hc
  have hd' : ∀ τ, (lam' τ).detShift = -s τ := fun τ => by
    rw [DomWeight_detShift_eq_w_last _ (by omega)]
    exact hc2 τ _ (by simp; omega)
  have hw1 : ∀ τ i, (lam' τ).natW (Fin.castLE hab.le i) = (lam τ).natW i + n τ := by
    intro τ i
    have e1 := hc1 τ i
    have e2 := hc3 τ
    have e3 := DomWeight_detShift_le_w (lam τ) i
    have e4 := hd' τ
    simp only [_root_.Formalism.BasicNotions.DomWeight.natW]
    omega
  have hw2 : ∀ τ (j : Fin b), a ≤ (j : ℕ) → (lam' τ).natW j = 0 := by
    intro τ j hj
    have e1 := hc2 τ j hj
    have e4 := hd' τ
    simp only [_root_.Formalism.BasicNotions.DomWeight.natW]
    omega
  have hsharp : ∀ Q : _root_.Formalism.L2.DIV.Pol K ι a, _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.sharp n Q = Q * ∏ τ, _root_.Formalism.L2.Ker.frDet K a τ ^ n τ :=
    fun Q => rfl
  unfold _root_.Formalism.L2.DIV.VV _root_.Formalism.GradedWeylDivisibility.tensorLat at hP ⊢
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    rw [hsharp, ← Finset.prod_mul_distrib, map_prod]
    refine Submodule.subset_span ⟨fun τ => _root_.Formalism.GradedWeylDivisibility.rowAct K (_root_.GlobalTheory.SubstMem.padRows (ap τ))
      (rename (Prod.map (Fin.castLE hab.le) (Fin.castLE hab.le))
        (F τ * _root_.Formalism.GradedWeylDivisibility.initMinor K (id : Fin a → Fin a) le_rfl ^ n τ)), fun τ => ?_, ?_⟩
    · refine rowAct_mem_dualWeyl_of_mem_dualWeyl _ ?_
      refine _root_.GlobalTheory.SubstMem.rename_mem_dualWeyl hab.le ((lam τ).natW + fun _ => n τ) _
        (fun i => by simp [hw1]) (hw2 τ) _ ?_
      exact _root_.Formalism.GradedWeylDivisibility.dualWeyl_mul (hF τ) (_root_.GlobalTheory.SubstMem.det_pow_mem a (n τ))
    · refine Finset.prod_congr rfl fun τ _ => ?_
      rw [frDet_eq_blockEmb_initMinor_id, ← map_pow, ← map_mul, _root_.GlobalTheory.SubstMem.substAdj_blockEmb]
  | zero => simp [hsharp]
  | add x y _ _ hx hy =>
    rw [hsharp, add_mul, map_add (f := _)]
    exact add_mem (by rw [← hsharp]; exact hx) (by rw [← hsharp]; exact hy)
  | smul c x _ hx =>
    rw [hsharp, smul_mul_assoc, map_smul]
    exact Submodule.smul_mem _ c (by rw [← hsharp]; exact hx)

end GlobalTheory.SubstMem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowCloudUnitLower
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem cloudUnit_poly_bounds (x c F K cD k m N f L : ℝ) (hx : 1 ≤ x) (hc : 1 ≤ c) (hcx : c ≤ x) (hF : 1 ≤ F)
    (hK : 1 ≤ K) (hcD : 5 * c + F * c + 406 * K + 412 ≤ cD)
    (hk0 : 0 ≤ k) (hk : k ≤ x ^ (5 : ℝ)) (hm0 : 0 ≤ m) (hm : m ≤ x) (hN0 : 0 ≤ N) (hN : N ≤ x ^ (402 : ℝ))
    (hf0 : 0 ≤ f) (hf : f ≤ x ^ (3 : ℝ)) (hL0 : 0 ≤ L) (hL : L ≤ x) :
    (k ^ c * (c * m) ^ 3 / (6 * x ^ (-F)) ^ c ≤ x ^ cD ∧ c * m * N ≤ x ^ cD ∧
      k ^ c * (c * m ^ 4 * L) ^ 4 ≤ x ^ cD ∧ N * m ^ 10 ≤ x ^ cD) ∧ (N * f * L) ^ K ≤ x ^ cD := by
  have hx0 : 0 < x := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hFc : 0 ≤ F * c := by positivity
  have mono : ∀ a : ℝ, a ≤ 5 * c + F * c + 406 * K + 412 → x ^ a ≤ x ^ cD := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hx (ha.trans hcD)
  have hkc : k ^ c ≤ x ^ (5 * c) := by
    rw [Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow hk0 hk hc0
  have hnat : ∀ n : ℕ, x ^ n = x ^ (n : ℝ) := fun n => (Real.rpow_natCast x n).symm
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have h1 : (c * m) ^ 3 ≤ x ^ (6 : ℝ) := by
      calc (c * m) ^ 3 ≤ (x * x) ^ 3 := by gcongr
        _ = x ^ (6 : ℕ) := by ring
        _ = x ^ (6 : ℝ) := by rw [hnat]; norm_num
    have hp : 0 < x ^ (-F) := Real.rpow_pos_of_pos hx0 _
    have h2 : x ^ (-(F * c)) ≤ (6 * x ^ (-F)) ^ c := by
      rw [← neg_mul, Real.rpow_mul hx0.le]
      exact Real.rpow_le_rpow hp.le (by linarith) hc0
    have hq : 0 < x ^ (-(F * c)) := Real.rpow_pos_of_pos hx0 _
    calc k ^ c * (c * m) ^ 3 / (6 * x ^ (-F)) ^ c ≤ x ^ (5 * c) * x ^ (6 : ℝ) / x ^ (-(F * c)) := by gcongr
      _ = x ^ (5 * c + 6 + F * c) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_sub hx0]; congr 1; ring
      _ ≤ x ^ cD := mono _ (by linarith)
  · calc c * m * N ≤ x * x * x ^ (402 : ℝ) := by gcongr
      _ = x ^ (2 : ℕ) * x ^ (402 : ℝ) := by ring
      _ = x ^ (404 : ℝ) := by rw [hnat, ← Real.rpow_add hx0]; norm_num
      _ ≤ x ^ cD := mono _ (by linarith)
  · calc k ^ c * (c * m ^ 4 * L) ^ 4 ≤ x ^ (5 * c) * (x * x ^ 4 * x) ^ 4 := by gcongr
      _ = x ^ (5 * c) * x ^ (24 : ℕ) := by ring
      _ = x ^ (5 * c + 24) := by rw [hnat, ← Real.rpow_add hx0]; norm_num
      _ ≤ x ^ cD := mono _ (by linarith)
  · calc N * m ^ 10 ≤ x ^ (402 : ℝ) * x ^ 10 := by gcongr
      _ = x ^ (412 : ℝ) := by rw [hnat, ← Real.rpow_add hx0]; norm_num
      _ ≤ x ^ cD := mono _ (by linarith)
  · have h1 : N * f * L ≤ x ^ (406 : ℝ) := by
      calc N * f * L ≤ x ^ (402 : ℝ) * x ^ (3 : ℝ) * x := by gcongr
        _ = x ^ (406 : ℝ) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add_one hx0.ne']; norm_num
    calc (N * f * L) ^ K ≤ (x ^ (406 : ℝ)) ^ K := Real.rpow_le_rpow (by positivity) h1 (by linarith)
      _ = x ^ (406 * K) := by rw [← Real.rpow_mul hx0.le]
      _ ≤ x ^ cD := mono _ (by linarith)

theorem szRow_cloudUnit_lower : SzRow (fun C D L => ((D.R.k : ℝ) ^ C.P.CDel * (C.P.CDel * D.R.m) ^ 3 / D.div.etaF ^ C.P.CDel ≤ (D.s.Del : ℝ) ∧ C.P.CDel * D.R.m * D.R.N D.R.m ≤ (D.s.Del : ℝ) ∧ (D.R.k : ℝ) ^ C.P.CDel * (C.P.CDel * (D.R.m : ℝ) ^ 4 * L.sc.L) ^ 4 ≤ (D.s.Del : ℝ) ∧ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ (D.s.Del : ℝ)) ∧ (((D.R.N D.R.m : ℝ) * D.R.f * L.sc.L) ^ C.P.CCount ≤ (D.s.Del : ℝ))) := by
  intro eps h0 h1 C hC
  obtain ⟨x0, hx0⟩ := _root_.GlobalTheory.EX.rank_basic_bounds eps h0 h1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hmid, hlast⟩ := hC
  have hF : 1 ≤ C.P.CF := hmid _ (by simp [FC.cMid])
  have hc : 1 ≤ C.P.CDel := hlast _ (by simp [FC.cLast])
  have hK : 1 ≤ C.P.CCount := hlast _ (by simp [FC.cLast])
  refine ⟨5 * C.P.CDel + C.P.CF * C.P.CDel + 406 * C.P.CCount + 412, fun cD hcD => ⟨0, fun ch _ =>
    ⟨max x0 C.P.CDel, fun D L he hx V => ?_⟩⟩⟩
  have hxc : C.P.CDel ≤ L.sc.x := (le_max_right _ _).trans hx
  obtain ⟨hf, hm, hr, hkr, -, hL, hL1, -, -, -, -, -, -, -, hN, -, -⟩ :=
    hx0 L.sc D.R he ((le_max_left _ _).trans hx) V.ranks
  have hk : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := le_trans (by exact_mod_cast hkr) hr
  have hDel : L.sc.x ^ cD ≤ (D.s.Del : ℝ) := by
    rw [V.Del_eq, Rat.cast_natCast]
    exact Nat.le_ceil _
  obtain ⟨⟨a1, a2, a3, a4⟩, a5⟩ := cloudUnit_poly_bounds L.sc.x C.P.CDel C.P.CF C.P.CCount cD D.R.k D.R.m
    (D.R.N D.R.m) D.R.f L.sc.L (hc.trans hxc) hc hxc hF hK hcD (Nat.cast_nonneg _) hk (Nat.cast_nonneg _) hm
    (Nat.cast_nonneg _) hN (Nat.cast_nonneg _) hf (by linarith) hL
  rw [← V.etaF_eq] at a1
  exact ⟨⟨a1.trans hDel, a2.trans hDel, a3.trans hDel, a4.trans hDel⟩, a5.trans hDel⟩

end GlobalTheory.EX
end

