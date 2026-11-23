module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0405
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableExpCocycleCoboundaryModFil
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0407
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledProductSpanLatticeEntriesAndSpanStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledProductSpanLattice_entries_and_span : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (L : Fin m → FinExt l) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ), (∀ k g i j, ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ (L k).1) → (∀ k, ∀ x ∈ t k, ∀ i j, x i j ∈ (L k).1) → (∀ k (x : Matrix (Fin a) (Fin a) (Om l)), (∀ i j, x i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l)))) → (∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∀ k i j, x k i j ∈ (L k).1) ∧ ∀ x : Fin m → Matrix (Fin a) (Fin a) (Om l), (∀ k i j, x k i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (GlobalTheory.TraceConjugationCover.latT ρs t M : Set (Fin m → Matrix (Fin a) (Fin a) (Om l))) := by
  first | (exact @GlobalTheory.TraceConjugationCover.latT_entries_and_span) | (exact GlobalTheory.TraceConjugationCover.latT_entries_and_span) | (intros; apply GlobalTheory.TraceConjugationCover.latT_entries_and_span  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledProductSpanLatticeExistsPadicBasisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledProductSpanLattice_exists_padic_basis : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ), (∀ k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t k, zOm l (c' y) • y = 1) → (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → ∃ (d' : ℕ) (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)), LinearIndependent ℚ_[l] bb ∧ (∀ s, bb s ∈ GlobalTheory.TraceConjugationCover.latT ρs t M) ∧ ∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s := by
  first | (exact @GlobalTheory.TraceConjugationCover.latT_basis) | (exact GlobalTheory.TraceConjugationCover.latT_basis) | (intros; apply GlobalTheory.TraceConjugationCover.latT_basis  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledProductSpanLatticeStableGaloisRepTupleStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledProductSpanLattice_stable_galoisRepTuple : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ), (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → (∀ g, ∀ x ∈ GlobalTheory.TraceConjugationCover.latL t M, GlobalTheory.TraceConjugationCover.tup ρs g * x ∈ GlobalTheory.TraceConjugationCover.latL t M) ∧ ∀ g, ∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, GlobalTheory.TraceConjugationCover.tup ρs g * x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M := by
  first | (exact @GlobalTheory.TraceConjugationCover.stabE) | (exact GlobalTheory.TraceConjugationCover.stabE) | (intros; apply GlobalTheory.TraceConjugationCover.stabE  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SecondClosedOfFirstClosed
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.BlockJumpsCompare

section Continuity

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [IsTopologicalRing O] {X : Type} [TopologicalSpace X]

theorem continuous_of_mul (had : IsAdic (IsLocalRing.maximalIdeal O)) {d : O} (hd : d ≠ 0) {f : X → O}
    (h : Continuous fun x => d * f x) : Continuous f := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hp
  have hm : ∀ (n : ℕ) (y : O), y ∈ (IsLocalRing.maximalIdeal O) ^ n ↔ p ^ n ∣ y := by
    intro n y
    rw [hp.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rw [continuous_iff_continuousAt]
  intro x₀
  have h0 : Filter.Tendsto (fun x => (u : O) * p ^ k * (f x - f x₀)) (nhds x₀) (nhds 0) := by
    have := (h.sub (continuous_const (y := (u : O) * p ^ k * f x₀))).tendsto x₀
    simpa [mul_sub, Pi.sub_def] using this
  have h1 : Filter.Tendsto (fun x => f x - f x₀) (nhds x₀) (nhds 0) := by
    rw [had.hasBasis_nhds_zero.tendsto_right_iff] at h0 ⊢
    intro n _
    filter_upwards [h0 (k + n) trivial] with x hx
    have hx' := (hm _ _).1 hx
    refine (hm _ _).2 ?_
    rw [pow_add, mul_assoc, Units.dvd_mul_left] at hx'
    exact (mul_dvd_mul_iff_left (pow_ne_zero k hp.ne_zero)).1 hx'
  simpa [ContinuousAt] using h1.add_const (f x₀)

theorem continuous_of_comb (had : IsAdic (IsLocalRing.maximalIdeal O)) {ι : Type} [Fintype ι]
    (c : ι → FractionRing O) {h : ι → X → O} (hh : ∀ j, Continuous (h j)) {f : X → O}
    (hf : ∀ x, algebraMap O (FractionRing O) (f x) =
      ∑ j, c j * algebraMap O (FractionRing O) (h j x)) : Continuous f := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) c
  choose a ha using hd
  refine continuous_of_mul had (nonZeroDivisors.ne_zero d.2) ?_
  have : (fun x => (d : O) * f x) = fun x => ∑ j, a j * h j x := by
    funext x
    apply IsFractionRing.injective O (FractionRing O)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_sum, hf, ha, Finset.mul_sum, Algebra.smul_def, mul_assoc]
  rw [this]
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (hh j)

theorem continuous_of_splitsAs (had : IsAdic (IsLocalRing.maximalIdeal O)) {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] {n r t : ℕ} {M : Γ →* Matrix (Fin n) (Fin n) O}
    {P : Γ →* Matrix (Fin r) (Fin r) O} {χ : Fin t → Γ → FractionRing O}
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps.SplitsAs (mapM (algebraMap O (FractionRing O)) M)
      (mapM (algebraMap O (FractionRing O)) P) χ)
    (hM : Continuous fun g => M g) : Continuous fun g => P g := by
  obtain ⟨e, he⟩ := hs
  refine continuous_matrix fun a b => ?_
  set u : Fin n → FractionRing O := e.symm (Pi.single b 1, 0) with hu
  refine continuous_of_comb had
    (fun jk : Fin n × Fin n => (e (Pi.single jk.1 1)).1 a * u jk.2)
    (h := fun jk g => M g jk.1 jk.2) (fun jk => hM.matrix_elem jk.1 jk.2) fun g => ?_
  have h1 := congrFun (congrArg Prod.fst (he g u)) a
  have h2 : ∀ v : Fin n → FractionRing O, (e v).1 a = ∑ j, (e (Pi.single j 1)).1 a * v j := by
    intro v
    conv_lhs => rw [pi_eq_sum_univ' v]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Prod.fst_sum, Finset.sum_apply, mul_comm]
  rw [h2] at h1
  simp only [hu, LinearEquiv.apply_symm_apply, Matrix.mulVec_single_one] at h1
  rw [← hu] at h1
  rw [Fintype.sum_prod_type]
  refine Eq.trans ?_ (h1.symm.trans ?_)
  · rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change _ * (algebraMap O (FractionRing O) (M g j k) * u k) = _
    ring

end Continuity

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))

theorem blockSum_iff (π : N.X i) :
    GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum N i r ρ π ↔ GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps.BlockSplit N i r ρ π := Iff.rfl

theorem continuous_rho (π : N.X i) (hr : IsHeckeGalois N i π (r π))
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum N i r ρ π) :
    Continuous (fun g => ((ρ π g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))) :=
  continuous_of_splitsAs (M := rO N i r π) (P := rhoO N i ρ π) (N.O_adic i)
    ((blockSum_iff N i r ρ π).1 hs) hr.1

end Glob

end GlobalTheory.BlockJumpsCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeOfConjDualCharpoly
section
noncomputable section

namespace GlobalTheory.LatticeSelfDual

open GlobalTheory.TripleGal _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.AntiRamConj

theorem trace_eq_of_charpoly_eq' {K : Type} [CommRing K] [Nontrivial K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K}
    (h : A.charpoly = B.charpoly) : A.trace = B.trace := by
  rcases n with _ | n
  · simp [Matrix.trace]
  · rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, h]

def conjC (D : D7) : Gen.GE D.nd →* Gen.GE D.nd where
  toFun := conjAut D.ntw.cc (fun x => ⟨_, cc_symm_algebraMap_host D x⟩)
  map_one' := by ext x; simp [conjAut_apply]
  map_mul' g h := by ext x; simp [conjAut_apply]

theorem conjC_apply (D : D7) (g : Gen.GE D.nd) (x : D.nd.Om) :
    conjC D g x = D.ntw.cc (g (D.ntw.cc.symm x)) := rfl

section
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem tmat_one (i : X.Tw) (s : X.Sig i) : Tmat i s 1 = 1 := by
  rw [← Tgl_coe, map_one, Units.val_one]

theorem tmat_mul (i : X.Tw) (s : X.Sig i) (g h : Gen.GE N) : Tmat i s (g * h) = Tmat i s g * Tmat i s h := by
  rw [← Tgl_coe, ← Tgl_coe, ← Tgl_coe, map_mul, Units.val_mul]

def twistHom (i : X.Tw) (s : X.Sig i) : Gen.GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) where
  toFun g := (((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g
  map_one' := by simp [tmat_one]
  map_mul' g h := by
    rw [tmat_mul, map_mul, Units.val_mul, mul_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

def dualHom (i : X.Tw) (s : X.Sig i) : Gen.GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) where
  toFun g := Tdual i s g
  map_one' := by simp [Tdual, tmat_one]
  map_mul' g h := by
    simp only [Tdual]
    rw [tmat_mul, map_mul, Units.val_mul, Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]

theorem span_twist (i : X.Tw) (s : X.Sig i)
    (h : Submodule.span (IsLocalRing.ResidueField (X.O0 i)) (Set.range (rbar X i s)) = ⊤) :
    Submodule.span (IsLocalRing.ResidueField (X.O0 i))
      (Set.range fun g => (twistHom i s g).map (IsLocalRing.residue (X.O0 i))) = ⊤ := by
  rw [eq_top_iff, ← h, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  let u : (X.O0 i)ˣ := (eps0 X i g ^ D.R.t * (chiS i s g)⁻¹)⁻¹
  have e : rbar X i s g = IsLocalRing.residue (X.O0 i) (u : X.O0 i) •
      (twistHom i s g).map (IsLocalRing.residue (X.O0 i)) := by
    have e2 : ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) =
        (u : X.O0 i) • twistHom i s g := by
      show _ = (u : X.O0 i) • ((((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g)
      rw [Tmat, smul_smul, smul_smul, mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, one_smul]
    rw [rbar, e2]
    ext a b
    simp
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

end

theorem selfDual_of_charDual : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), ValuationStabilityAtRing D.ntw i s → CharDual i s → SelfDual i s := by
  intro D i s h2 hc
  have : CharZero (FractionRing (D.ntw.O0 i)) := charZero_of_injective_ringHom (D.ntw.emb0 i).injective
  have : CharZero (D.ntw.O0 i) :=
    ((algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))).charZero_iff (IsFractionRing.injective _ _)).2 inferInstance
  obtain ⟨U, hU⟩ := GlobalTheory.TraceConj.exists_gl_conj_of_trace_eq (D.ntw.O0 i) (Gen.GE D.nd) D.R.r (twistHom i s).toHomUnits
    ((dualHom i s).comp (conjC D)).toHomUnits (span_twist i s h2.1)
    (fun g => trace_eq_of_charpoly_eq' (hc g (conjC D g) (conjC_apply D g)))
  refine ⟨U, fun g g' hg => ?_⟩
  obtain rfl : g' = conjC D g := by ext x; rw [hg, conjC_apply]
  have := congrArg Units.val (eq_mul_inv_of_mul_eq (hU g))
  rw [Units.val_mul, Units.val_mul] at this
  exact this

end GlobalTheory.LatticeSelfDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearProjectiveModuleCompose
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.BCCancel

variable {R S T X Y : Type} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T]
  [IsScalarTower R S T] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]

theorem cancel_comm (f : X →ₗ[R] Y) (z : T ⊗[S] (S ⊗[R] X)) :
    AlgebraTensorModule.cancelBaseChange R S T T Y ((f.baseChange S).lTensor T z) =
      f.baseChange T (AlgebraTensorModule.cancelBaseChange R S T T X z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s x => simp [LinearMap.baseChange_tmul]
    | add a b ha hb => simp only [TensorProduct.tmul_add, map_add (f := _), ha, hb]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem bij_up (f : X →ₗ[R] Y) (hf : Function.Bijective (f.baseChange S)) :
    Function.Bijective (f.baseChange T) := by
  have hl : Function.Bijective ((f.baseChange S).lTensor T) := by
    exact (LinearEquiv.lTensor T (LinearEquiv.ofBijective _ hf)).bijective
  have hfun : ⇑(f.baseChange T) = AlgebraTensorModule.cancelBaseChange R S T T Y ∘
      (f.baseChange S).lTensor T ∘ (AlgebraTensorModule.cancelBaseChange R S T T X).symm := by
    funext z
    simp only [Function.comp_apply, cancel_comm, LinearEquiv.apply_symm_apply]
  rw [hfun]
  exact (AlgebraTensorModule.cancelBaseChange R S T T Y).bijective.comp
    (hl.comp (AlgebraTensorModule.cancelBaseChange R S T T X).symm.bijective)

theorem bij_down [Module.FaithfullyFlat S T] (f : X →ₗ[R] Y) (hf : Function.Bijective (f.baseChange T)) :
    Function.Bijective (f.baseChange S) := by
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective S T]
  have hfun : ⇑((f.baseChange S).lTensor T) = (AlgebraTensorModule.cancelBaseChange R S T T Y).symm ∘
      f.baseChange T ∘ AlgebraTensorModule.cancelBaseChange R S T T X := by
    funext z
    simp only [Function.comp_apply, ← cancel_comm, LinearEquiv.symm_apply_apply]
  rw [hfun]
  exact (AlgebraTensorModule.cancelBaseChange R S T T Y).symm.bijective.comp
    (hf.comp (AlgebraTensorModule.cancelBaseChange R S T T X).bijective)

end GlobalTheory.BSP.BCCancel

namespace GlobalTheory.BSP.BCCancel

theorem bij_lin {A B C N N' N'' : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    [Module B N'] [IsScalarTower A B N'] [AddCommGroup N''] [Module A N''] [Module B N''] [Module C N'']
    [IsScalarTower B C N''] [IsScalarTower A B N''] [IsScalarTower A C N'']
    (u : N →ₗ[A] N') (v : N' →ₗ[B] N'') (hv : IsBaseChange C v)
    (hw : IsBaseChange C ((v.restrictScalars A).comp u)) :
    Function.Bijective ((u.liftBaseChange B).baseChange C) := by
  set L := u.liftBaseChange B
  have h0 := TensorProduct.isBaseChange A N B
  have hc : IsBaseChange C ((v ∘ₗ L : B ⊗[A] N →ₗ[B] N'').restrictScalars A ∘ₗ TensorProduct.mk A B N 1) := by
    convert hw using 1
    ext x
    simp [L, LinearMap.liftBaseChange_tmul]
  have h1 : IsBaseChange C (v ∘ₗ L) := IsBaseChange.of_comp h0 hc
  have hfun : ⇑(L.baseChange C) = hv.equiv.symm ∘ h1.equiv := by
    funext z
    simp only [Function.comp_apply]
    rw [LinearEquiv.eq_symm_apply]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c p => simp [IsBaseChange.equiv_tmul, LinearMap.baseChange_tmul]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [hfun]
  exact hv.equiv.symm.bijective.comp h1.equiv.bijective

end GlobalTheory.BSP.BCCancel

namespace GlobalTheory.BSP

theorem semiBC_of_cover : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (h : Hom B C), Cover h →
    ∀ (A : Type) [CommRing A] (k : A →+* B.A) (N : Type) [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Module.Projective A N] (N' : Type) [AddCommGroup N'] [Module B.A N'] [Module.Finite B.A N']
    [Module.Projective B.A N'] (N'' : Type) [AddCommGroup N''] [Module C.A N''] (u : N →ₛₗ[k] N')
    (v : N' →ₛₗ[h.f] N'') (w : N →ₛₗ[h.f.comp k] N''), (∀ x, w x = v (u x)) → SemiBC v → SemiBC w →
    SemiBC u := by
  intro l _ R _ B C h hc A _ k N _ _ _ _ N' _ _ _ _ N'' _ _ u v w hw hv hwb
  letI : Algebra A B.A := k.toAlgebra
  letI : Algebra B.A C.A := h.f.toAlgebra
  letI : Algebra A C.A := (h.f.comp k).toAlgebra
  haveI : IsScalarTower A B.A C.A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module A N' := Module.compHom N' k
  haveI : IsScalarTower A B.A N' := ⟨fun a b x => mul_smul (k a) b x⟩
  letI : Module B.A N'' := Module.compHom N'' h.f
  letI : Module A N'' := Module.compHom N'' (h.f.comp k)
  haveI : IsScalarTower B.A C.A N'' := ⟨fun a b x => mul_smul (h.f a) b x⟩
  haveI : IsScalarTower A C.A N'' := ⟨fun a b x => mul_smul (h.f (k a)) b x⟩
  haveI : IsScalarTower A B.A N'' := ⟨fun a b x => by
    show h.f (k a * b) • x = h.f (k a) • (h.f b • x)
    rw [map_mul, mul_smul]⟩
  let u' : N →ₗ[A] N' := { toFun := u, map_add' := u.map_add, map_smul' := fun a x => u.map_smulₛₗ a x }
  let v' : N' →ₗ[B.A] N'' := { toFun := v, map_add' := v.map_add, map_smul' := fun a x => v.map_smulₛₗ a x }
  let w' : N →ₗ[A] N'' := { toFun := w, map_add' := w.map_add, map_smul' := fun a x => w.map_smulₛₗ a x }
  have hv' : IsBaseChange C.A v' := (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange B.A C.A N' N'' v v' fun _ => rfl).1 hv
  have hw' : IsBaseChange C.A ((v'.restrictScalars A).comp u') := by
    have := (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange A C.A N N'' w w' fun _ => rfl).1 hwb
    convert this using 1
    ext x
    exact (hw x).symm
  set L := u'.liftBaseChange B.A
  have hC : Function.Bijective (L.baseChange C.A) := BCCancel.bij_lin u' v' hv' hw'
  letI : Algebra (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := (qmap h 1).toAlgebra
  haveI : IsScalarTower B.A (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.FaithfullyFlat (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := hc.ff 1
  have hQ : Function.Bijective (L.baseChange (C.A ⧸ adI C ^ 1)) := BCCancel.bij_up (S := C.A) L hC
  have hB : Function.Bijective (L.baseChange (B.A ⧸ adI B ^ 1)) :=
    BCCancel.bij_down (T := C.A ⧸ adI C ^ 1) L hQ
  haveI : IsAdicComplete (adI B) B.A := B.complete
  have hJ : adI B ^ 1 ≤ Ideal.jacobson ⊥ := (pow_one (adI B)).le.trans (IsAdicComplete.le_jacobson_bot (adI B))
  have hL : Function.Bijective L := _root_.GlobalTheory.BSP.bijective_of_bijective_baseChange_quotient B.A (adI B ^ 1) hJ (B.A ⊗[A] N) N' L hB
  have hu' : IsBaseChange B.A u' :=
    IsBaseChange.of_equiv (LinearEquiv.ofBijective L hL) fun x => by
      simp [L, LinearMap.liftBaseChange_tmul]
  exact (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange A B.A N N' u u' fun _ => rfl).2 hu'

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableExpCocycleCoboundaryModFilStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_exp_cocycle_coboundary_mod_fil : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d k k₀ : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), (∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l k₀ k i‖ ≤ 1) → Mn ^ d = 0 → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) - (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) ∈ Per.FilP l m) → ∀ m : ℕ, ∃ (kk : ℕ) (Λ : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, bk.E ∣ (Λ - (l : bk.S) ^ kk • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) ∧ ∀ (g : ↥(GK K)) i j, C.j ((GlobalTheory.SstPer.kap C bk k₀ k Mn (c g) * (Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l)) - (l : Per.Acris l) ^ k₀ • Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l m := by
  first | (exact @GlobalTheory.SstPer.Cob.cocycle_cob) | (exact GlobalTheory.SstPer.Cob.cocycle_cob) | (intros; apply GlobalTheory.SstPer.Cob.cocycle_cob  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableInvariantBdRPlusBasisApproxStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_invariant_bdRPlus_basis_approx : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)) (k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), Mn ^ d = 0 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U * ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * (Per.zB l (c g) * C.tB) ^ i) • (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)) ^ i) → ∀ lam : Per.BdRp l, (∀ g : ↥(GK K), Per.σDp (g : GQ l) lam = lam + aDp l (Per.zA l (c g)) * C.j C.t) → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * lam ∈ Per.FilP l m) → ∃ Λ₀ : Matrix (Fin d) (Fin d) (Per.BdRp l), (∀ g : ↥(GK K), (ρ g).map (Per.zD l) * (U.map C.ι * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))).map (Per.σD (g : GQ l)) = U.map C.ι * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))) ∧ ∀ m : ℕ, ∃ (k : ℕ) (Λ Λ' : Matrix (Fin d) (Fin d) (bk.S)), Λ * Λ' = (l : bk.S) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ ∀ i j, (Λ.map ((aDp l).comp bk.ev) - (l : Per.BdRp l) ^ k • Λ₀) i j ∈ Per.FilP l m := by
  first | (exact @GlobalTheory.SstPer.SFil.invariant_basis_approx) | (exact GlobalTheory.SstPer.SFil.invariant_basis_approx) | (intros; apply GlobalTheory.SstPer.SFil.invariant_basis_approx  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodsOverAcrisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_periods_over_Acris : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)), U * U' = 1 → ∀ (c₁ : ℕ) (F : Matrix (Fin d) (Fin d) (Wq l bk.a)), (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) → ∀ (k k₀ : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), (∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l k₀ k i‖ ≤ 1) → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U * ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * (Per.zB l (c g) * C.tB) ^ i) • (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)) ^ i) → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (X X' : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, (U.map C.ι * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j ∈ Per.FilD l N) → (∀ i j, (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U'.map C.ι) i j ∈ Per.FilD l N) → ∃ Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l), Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), (C.t ^ N * (l : Per.Acris l) ^ k₀) • ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • (Z * GlobalTheory.SstPer.kap C bk k₀ k Mn (c g))) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) := by
  first | (exact @GlobalTheory.CrisPeriods.periods_over_Acris_sst) | (exact GlobalTheory.CrisPeriods.periods_over_Acris_sst) | (intros; apply GlobalTheory.CrisPeriods.periods_over_Acris_sst  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanMapRepEqTop
section
namespace GlobalTheory.SpanMapTop

theorem map_mem_span {Γ A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
    (f : Γ → Matrix (Fin r) (Fin r) A) (M : Matrix (Fin r) (Fin r) A)
    (hM : M ∈ Submodule.span A (Set.range f)) :
    M.map (algebraMap A B) ∈
      Submodule.span B (Set.range fun g => (f g).map (algebraMap A B)) := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact Submodule.subset_span ⟨g, rfl⟩
  | zero =>
    have : (0 : Matrix (Fin r) (Fin r) A).map (algebraMap A B) = 0 := by
      ext i j; simp
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (x + y).map (algebraMap A B) = x.map (algebraMap A B) + y.map (algebraMap A B) := by
      ext i j; simp
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have : (a • x).map (algebraMap A B) = (algebraMap A B a) • x.map (algebraMap A B) := by
      ext i j; simp
    rw [this]; exact Submodule.smul_mem _ _ hx

theorem span_map_eq_top {Γ A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
    (f : Γ → Matrix (Fin r) (Fin r) A) (h : Submodule.span A (Set.range f) = ⊤) :
    Submodule.span B (Set.range fun g => (f g).map (algebraMap A B)) = ⊤ := by
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have h1 := map_mem_span (B := B) f (Matrix.single i j 1) (h ▸ Submodule.mem_top)
  have h2 : Matrix.single i j (M i j) =
      M i j • (Matrix.single i j (1 : A)).map (algebraMap A B) := by
    ext a b
    simp only [Matrix.single, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  rw [h2]
  exact Submodule.smul_mem _ _ h1

theorem span_mapRep_eq_top {Γ A : Type} [Group Γ] [CommRing A] {r : ℕ} {B : Type} [CommRing B]
    [Algebra A B] {ρ : Γ →* GL (Fin r) A}
    (h : Submodule.span A (Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat ρ)) = ⊤) :
    Submodule.span B
      (Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (Formalism.MainNotions.N.mapRep (algebraMap A B) ρ))) = ⊤ :=
  span_map_eq_top (B := B) (fun g => GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat ρ g) h

end GlobalTheory.SpanMapTop
end

