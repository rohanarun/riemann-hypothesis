module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0715
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDerivativeInducedTensorForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0654
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0710
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0688
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0712
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DegreeOnePrimeCMFieldOverSplitMaxRealSubfield
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open _root_.GlobalTheory

namespace GlobalTheory.SplitDegOne

theorem exists_unique_other {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ℕ) (a : ι)
    (hpos : ∀ i, 1 ≤ g i) (hsum : ∑ i, g i = 2) (ha : g a = 1) :
    ∃ b, b ≠ a ∧ g b = 1 ∧ ∀ c, c = a ∨ c = b := by
  have h1 : ∑ i ∈ Finset.univ.erase a, g i = 1 := by
    have := Finset.add_sum_erase Finset.univ g (Finset.mem_univ a)
    omega
  have hcard : (Finset.univ.erase a).card ≤ 1 := by
    have := Finset.card_nsmul_le_sum (Finset.univ.erase a) g 1 (fun i _ => hpos i)
    rw [smul_eq_mul, mul_one] at this
    exact this.trans h1.le
  have hne : (Finset.univ.erase a).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at h1
    omega
  obtain ⟨b, hb⟩ := Finset.card_eq_one.1 (le_antisymm hcard hne.card_pos)
  have hbm : b ∈ Finset.univ.erase a := hb ▸ Finset.mem_singleton_self b
  refine ⟨b, Finset.ne_of_mem_erase hbm, by rw [hb, Finset.sum_singleton] at h1; exact h1, fun c => ?_⟩
  by_cases hc : c = a
  · exact Or.inl hc
  · right
    have : c ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hc, Finset.mem_univ c⟩
    rw [hb] at this
    exact Finset.mem_singleton.1 this

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)),
    w.asIdeal.inertiaDeg ℤ = 1 → w.asIdeal.ramificationIdx ℤ = 1 →
    Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E))) ∧
    (Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) (w.under (𝓞 (maximalRealSubfield E)))).card = 2 ∧
    ∀ w' ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) (w.under (𝓞 (maximalRealSubfield E))),
      Ideal.absNorm w'.asIdeal = Ideal.absNorm w.asIdeal ∧
        w'.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
  intro E _ _ _ w hf he
  classical
  let v := w.under (𝓞 (maximalRealSubfield E))
  have hwv : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hv0 : v.asIdeal ≠ ⊥ := v.ne_bot
  have hfw : w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield E)) = 1 := by
    have := Ideal.inertiaDeg_tower (R := ℤ) v.asIdeal w.asIdeal
    rw [hf] at this
    exact (mul_eq_one.1 this.symm).2
  have hew : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
    have := Ideal.ramificationIdx_tower (R := ℤ) v.asIdeal w.asIdeal
    rw [he] at this
    exact (mul_eq_one.1 this.symm).2
  have h2 : Module.finrank (𝓞 (maximalRealSubfield E)) (𝓞 E) = 2 := by
    rw [← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]
    exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 (maximalRealSubfield E))
      (maximalRealSubfield E) (𝓞 E) E).symm
  let _ : Fintype (v.asIdeal.primesOver (𝓞 E)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)
  rw [h2] at hsum
  let a : v.asIdeal.primesOver (𝓞 E) := ⟨w.asIdeal, w.isPrime, hwv⟩
  obtain ⟨b, hba, hb1, hall⟩ := exists_unique_other (fun q : v.asIdeal.primesOver (𝓞 E) =>
      q.1.ramificationIdx (𝓞 (maximalRealSubfield E)) * q.1.inertiaDeg (𝓞 (maximalRealSubfield E))) a
    (fun q => by
      have : q.1.IsPrime := q.2.1
      exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Ideal.ramificationIdx_pos (R := _) q.1).ne'
        (Ideal.inertiaDeg_pos q.1 _).ne'))
    hsum (by simp only [a, hew, hfw, mul_one])
  have hbl : b.1.LiesOver v.asIdeal := b.2.2
  let B : HeightOneSpectrum (𝓞 E) := ⟨b.1, b.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot hv0 b.1⟩
  have hB : B.under (𝓞 (maximalRealSubfield E)) = v :=
    HeightOneSpectrum.ext (Ideal.over_def b.1 v.asIdeal).symm
  have hwB : w ≠ B := fun h => hba (Subtype.ext (congrArg HeightOneSpectrum.asIdeal h).symm)

  have hmem : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 (maximalRealSubfield E)) = v → u = w ∨ u = B := by
    intro u hu
    have hul : u.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hu]; rfl⟩
    rcases hall ⟨u.asIdeal, u.isPrime, hul⟩ with h | h
    · exact Or.inl (HeightOneSpectrum.ext (congrArg Subtype.val h))
    · exact Or.inr (HeightOneSpectrum.ext (congrArg Subtype.val h))
  have hB1 := mul_eq_one.1 hb1
  have hnorm : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 (maximalRealSubfield E)) = v →
      Ideal.absNorm u.asIdeal = Ideal.absNorm v.asIdeal ∧ u.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
    intro u hu
    have hul : u.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hu]; rfl⟩
    have hf1 : u.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield E)) = 1 ∧
        u.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
      rcases hmem u hu with rfl | rfl
      · exact ⟨hfw, hew⟩
      · exact ⟨hB1.2, hB1.1⟩
    refine ⟨?_, hf1.2⟩
    rw [← Ideal.absNorm_pow_inertiaDeg v.asIdeal u.asIdeal, hf1.1, pow_one]
  refine ⟨GlobalTheory.LFun.isSplit_iff.2 ⟨w, B, hwB, rfl, hB⟩, ?_, fun u hu => ?_⟩
  · rw [Finset.card_eq_two]
    refine ⟨w, B, hwB, Finset.ext fun u => ?_⟩
    rw [GlobalTheory.LFun.mem_aboveF, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hmem u, by rintro (rfl | rfl); exacts [rfl, hB]⟩
  · have hu' := GlobalTheory.LFun.mem_aboveF.1 hu
    exact ⟨(hnorm u hu').1.trans (hnorm w rfl).1.symm, (hnorm u hu').2⟩

end GlobalTheory.SplitDegOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfIsLocCompGL
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open scoped ContDiff

namespace GlobalTheory.DiscSMO

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a c N : ℕ} {n : Fin c → ℕ}
  {π π' : ∀ i, CuspSub E (n i)}


def prodForm (φ : ∀ i, (π i).V) : (∀ i, GA E (n i)) → ℂ := fun m => ∏ i, (φ i).1.1 (m i)

structure IsTensorOf (T : ∀ i, (π i).V →ₗ[ℂ] (π' i).V) (Θ : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)) : Prop where
  comm : ∀ i o φ, T i ((π i).op o φ) = (π' i).op o (T i φ)
  prod : ∀ φ, Θ (prodForm φ) = prodForm fun i => T i (φ i)

namespace IsTensorOf

variable {T : ∀ i, (π i).V →ₗ[ℂ] (π' i).V} {Θ : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)}

end IsTensorOf

variable {h : ∑ i, n i = N}




namespace IsTensorOf

variable {T : ∀ i, (π i).V →ₗ[ℂ] (π' i).V} {Θ : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)}

end IsTensorOf

theorem mem_Sm_of_one {f : GA E a → ℂ} (hf : ∀ g, ContDiffAt ℝ ∞ (chart f g) (oneL E a)) : f ∈ Sm E a := by
  rintro g x ⟨y, hy⟩
  obtain rfl : x = toL y.val := hy.symm
  have e : chart f g = chart f (g * infGL E a y) ∘ lmul (toL (y⁻¹).val) := by
    rw [← chart_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have e1 : lmul (toL (y⁻¹).val) (toL y.val) = oneL E a := y.inv_mul
  rw [e]
  refine (ContDiffAt.comp _ ?_ (lmul (toL (y⁻¹).val)).contDiff.contDiffAt).contDiffWithinAt
  rw [e1]
  exact hf _

theorem contDiffAt_chart_mul {f : GA E a → ℂ} {g : GA E a} {y : GL (Fin a) (Cinf E)}
    (hf : ContDiffAt ℝ ∞ (chart (fun x => f (x * infGL E a y)) g) (oneL E a)) :
    ContDiffAt ℝ ∞ (chart f (g * infGL E a y)) (oneL E a) := by
  have e : chart f g = chart (fun x => f (x * infGL E a y)) g ∘ rmul (toL (y⁻¹).val) := by
    rw [← chart_rt_inf]
    simp only [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  have e1 : rmul (toL (y⁻¹).val) (toL y.val) = oneL E a := y.mul_inv
  have e2 : lmul (toL y.val) (oneL E a) = toL y.val := mul_one y.val
  rw [chart_mul, e]
  refine ContDiffAt.comp _ ?_ (lmul (toL y.val)).contDiff.contDiffAt
  rw [e2]
  refine ContDiffAt.comp _ ?_ (rmul (toL (y⁻¹).val)).contDiff.contDiffAt
  rw [e1]
  exact hf


namespace IsTensorOf

variable {T : ∀ i, (π i).V →ₗ[ℂ] (π' i).V} {Θ : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)}


end IsTensorOf


end GlobalTheory.DiscSMO

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdelicExtensionOfAlgebraicWeightDefiniteUn
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix Pointwise

namespace GlobalTheory.WeightRealExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem dense_rat_fin : Dense ((ratU E n : Set (UA E n)) * (finU (E := E) (n := n) : Set (UA E n))) := by
  intro g
  obtain ⟨k, hk, x, hx, rfl⟩ := GlobalTheory.DefU.exists_finU_mul_infU E n g
  rw [GlobalTheory.DefU.fin_mul_inf hk hx]
  have hc : Continuous (· * k : UA E n → UA E n) := continuous_mul_const k
  refine closure_mono ?_
    (image_closure_subset_closure_image hc ⟨x, GlobalTheory.DefiniteDense.mem_closure_rat_fin x hx, rfl⟩)
  rintro _ ⟨_, ⟨γ, hγ, k', hk', rfl⟩, rfl⟩
  exact ⟨γ, hγ, k' * k, (finU (E := E) (n := n)).mul_mem hk' hk, (mul_assoc _ _ _).symm⟩

theorem mem_rationalGL_of_unitaryGroupGram_unitGram (γ : UA E n) (γ₀ : GL (Fin n) E) (h : γ.1 = ratGL E n γ₀) : γ₀ ∈ GQ0 E n := by
  have h0 : Formalism.UG.cT (conjAd E) (γ.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * γ.1 = 1 := γ.2
  rw [mul_one, h] at h0
  have e : Formalism.UG.cT (conjAd E) ((γ₀ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) =
      (conjT (IsCMField.complexConj E : E →+* E) (γ₀ : Matrix (Fin n) (Fin n) E)).map (algebraMap E (Ad E)) := by
    ext i j
    simp [Formalism.UG.cT, conjT, conjAd_algebraMap]
  change Formalism.UG.cT (conjAd E) ((γ₀ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) *
      (γ₀ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E)) = 1 at h0
  rw [e, ← Matrix.map_mul, ← Matrix.map_one (algebraMap E (Ad E)) (map_zero _) (map_one _)] at h0
  have h1 := Matrix.map_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 E) E) h0
  exact mul_eq_one_comm.1 h1

def ratPt : GQ0 E n →* GQ E n where
  toFun γ := ⟨⟨GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E) γ.1, by
      have h0 : (γ.1 : Matrix (Fin n) (Fin n) E) * conjT (IsCMField.complexConj E : E →+* E) γ.1 = 1 := γ.2
      have e : conjT (conjAL E) ((γ.1 : Matrix (Fin n) (Fin n) E).map
          (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E)) =
          (conjT (IsCMField.complexConj E : E →+* E) (γ.1 : Matrix (Fin n) (Fin n) E)).map
            (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E) := by
        ext i j
        simp [conjT, conjAL]
      change (γ.1 : Matrix (Fin n) (Fin n) E).map (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E) *
        conjT (conjAL E) ((γ.1 : Matrix (Fin n) (Fin n) E).map
          (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E)) = 1
      rw [e, ← Matrix.map_mul, h0, Matrix.map_one _ (map_zero _) (map_one _)]⟩,
    Subgroup.mem_subgroupOf.2 ⟨γ.1, γ.2, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' x y := Subtype.ext (Subtype.ext (map_mul _ _ _))

def polyMat {ι : Type} (P : ι → ι → MvPolynomial ((E →+* ℂ) × Fin n × Fin n) ℂ) (g : UA E n) : Matrix ι ι ℂ :=
  fun i j => MvPolynomial.eval (fun p => coord p.1 ((cInf g : Matrix (Fin n) (Fin n) (Cinf E)) p.2.1 p.2.2)) (P i j)

theorem polyMat_congr {ι : Type} (P : ι → ι → MvPolynomial ((E →+* ℂ) × Fin n × Fin n) ℂ) {g h : UA E n}
    (e : cInf g = cInf h) : polyMat P g = polyMat P h := by
  unfold polyMat
  rw [e]

theorem polyMat_rat {ι : Type} (P : ι → ι → MvPolynomial ((E →+* ℂ) × Fin n × Fin n) ℂ) (γ : UA E n)
    (γ₀ : GL (Fin n) E) (h : γ.1 = ratGL E n γ₀) :
    polyMat P γ = fun i j =>
      MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix (Fin n) (Fin n) E) p.2.1 p.2.2)) (P i j) := by
  funext i j
  unfold polyMat
  congr 2
  funext p
  rw [← coord_algebraMap p.1]
  congr 1
  change pInf E ((γ.1 : Matrix (Fin n) (Fin n) (Ad E)) p.2.1 p.2.2) = _
  rw [h]
  rfl


omit [NumberField E] [IsCMField E] in
theorem continuous_coord' (τ : E →+* ℂ) : Continuous (coord τ) := by
  unfold coord
  split_ifs
  · exact continuous_apply _
  · exact Complex.continuous_conj.comp (continuous_apply _)

theorem continuous_pInf' : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_polyMat {ι : Type} (P : ι → ι → MvPolynomial ((E →+* ℂ) × Fin n × Fin n) ℂ) :
    Continuous (polyMat P) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (MvPolynomial.continuous_eval (P i j)).comp (continuous_pi fun p => ?_)
  refine (continuous_coord' p.1).comp (continuous_pInf'.comp
    (f := fun g : UA E n => (g.1 : Matrix (Fin n) (Fin n) (Ad E)) p.2.1 p.2.2) ?_)
  exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _

theorem exists_unitaryRationalMatrix_of_mem_definiteUnitaryRational {γ : UA E n} (hγ : γ ∈ ratU E n) : ∃ γ₀ : GQ0 E n, γ.1 = ratGL E n γ₀.1 := by
  obtain ⟨γ₀, hγ₀⟩ := Subgroup.mem_subgroupOf.1 hγ
  exact ⟨⟨γ₀, mem_rationalGL_of_unitaryGroupGram_unitGram γ γ₀ hγ₀.symm⟩, hγ₀.symm⟩

theorem mul_of_dense {G M : Type} [Mul G] [TopologicalSpace G] [ContinuousMul G] [Mul M] [TopologicalSpace M]
    [ContinuousMul M] [T2Space M] {D : Set G} (hD : Dense D) (f : G → M) (hf : Continuous f)
    (h : ∀ x ∈ D, ∀ y ∈ D, f (x * y) = f x * f y) (x y : G) : f (x * y) = f x * f y := by
  have hcl : IsClosed {z : G × G | f (z.1 * z.2) = f z.1 * f z.2} :=
    isClosed_eq (hf.comp (continuous_fst.mul continuous_snd))
      ((hf.comp continuous_fst).mul (hf.comp continuous_snd))
  exact hcl.closure_subset_iff.2 (fun z (hz : z ∈ D ×ˢ D) => h z.1 hz.1 z.2 hz.2) ((hD.prod hD) (x, y))

theorem mul_of_rat {M : Type} [Mul M] [TopologicalSpace M] [ContinuousMul M] [T2Space M] (f : UA E n → M)
    (hf : Continuous f) (hi : ∀ g h, cInf g = cInf h → f g = f h)
    (h : ∀ x ∈ ratU E n, ∀ y ∈ ratU E n, f (x * y) = f x * f y) : ∀ x y, f (x * y) = f x * f y := by
  refine mul_of_dense dense_rat_fin f hf fun x hx y hy => ?_
  obtain ⟨γ, hγ, k, hk, hx⟩ := Set.mem_mul.1 hx
  obtain ⟨δ, hδ, l, hl, hy⟩ := Set.mem_mul.1 hy
  have hk' : cInf k = 1 := hk
  have hl' : cInf l = 1 := hl
  have e1 : cInf x = cInf γ := by rw [← hx, map_mul, hk', mul_one]
  have e2 : cInf y = cInf δ := by rw [← hy, map_mul, hl', mul_one]
  rw [hi x γ e1, hi y δ e2, hi (x * y) (γ * δ) (by rw [map_mul, map_mul, e1, e2]), h γ hγ δ hδ]

theorem exists_extension : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n), ∃ R : UA L n →* Module.End ℂ a.W, (∀ k ∈ finU (E := L) (n := n), R k = 1) ∧ (∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ → (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → R γ = a.ρ γQ) ∧ ∀ (v : a.W) (μ : Module.Dual ℂ a.W), Continuous fun g : UA L n => μ (R g v) := by
  intro L _ _ _ n a
  obtain ⟨_, ι, _, _, b, P, hP⟩ := a.alg
  have hrat : ∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ →
      (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom →
      polyMat P γ = LinearMap.toMatrix b b (a.ρ γQ) := fun γ γQ γ₀ h1 h2 =>
    (polyMat_rat P γ γ₀ h1).trans (hP γQ γ₀ h2).symm
  have hrat' : ∀ (γ : UA L n) (γ₀ : GQ0 L n), γ.1 = ratGL L n γ₀.1 →
      polyMat P γ = LinearMap.toMatrix b b (a.ρ (ratPt (E := L) (n := n) γ₀)) := fun γ γ₀ h => hrat γ _ γ₀.1 h rfl
  have hone : polyMat P 1 = 1 := by
    rw [hrat' 1 1 (map_one (ratGL L n)).symm, map_one, map_one, LinearMap.toMatrix_one]
  have hmul : ∀ g h : UA L n, polyMat P (g * h) = polyMat P g * polyMat P h := by
    refine mul_of_rat (polyMat P) (continuous_polyMat P) (fun _ _ => polyMat_congr P) fun γ hγ δ hδ => ?_
    obtain ⟨γ₀, hγ₀⟩ := exists_unitaryRationalMatrix_of_mem_definiteUnitaryRational hγ
    obtain ⟨δ₀, hδ₀⟩ := exists_unitaryRationalMatrix_of_mem_definiteUnitaryRational hδ
    have e : (γ * δ).1 = ratGL L n (γ₀ * δ₀).1 := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, hγ₀, hδ₀]
    rw [hrat' γ γ₀ hγ₀, hrat' δ δ₀ hδ₀, hrat' (γ * δ) (γ₀ * δ₀) e, map_mul, map_mul, LinearMap.toMatrix_mul]
  refine ⟨⟨⟨fun g => Matrix.toLin b b (polyMat P g), ?_⟩, fun g h => ?_⟩, fun k hk => ?_, fun γ γQ γ₀ h1 h2 => ?_,
    fun v μ => ?_⟩
  · rw [hone, Matrix.toLin_one]
    rfl
  · change Matrix.toLin b b (polyMat P (g * h)) = _
    rw [hmul, Matrix.toLin_mul b b b]
    rfl
  · change Matrix.toLin b b (polyMat P k) = 1
    rw [polyMat_congr P (g := k) (h := 1) ((show cInf k = 1 from hk).trans (map_one _).symm), hone, Matrix.toLin_one]
    rfl
  · change Matrix.toLin b b (polyMat P γ) = _
    rw [hrat γ γQ γ₀ h1 h2, Matrix.toLin_toMatrix]
  · change Continuous fun g : UA L n => μ (Matrix.toLin b b (polyMat P g) v)
    have hc := continuous_polyMat P
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.toLin_apply, map_sum, map_smul, smul_eq_mul]
    refine continuous_finsetSum _ fun j _ => Continuous.mul ?_ continuous_const
    exact (continuous_apply j).comp (hc.matrix_mulVec continuous_const)

end GlobalTheory.WeightRealExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineCharJumpOne
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.LTChar

theorem exists_crystalline_char_jump_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ χ : ↥(GK K) →* (↥(OL LL))ˣ, Continuous (fun g => (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1)) ∧ IsCrys (P.PD K) (charRep ((Units.map (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom).comp χ)) ∧ ∀ τ b, multV (P.PD K) (charRep ((Units.map (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom).comp χ)) τ b = if b = (if τ = τ₀ then 1 else 0) then 1 else 0 := by
  intro l _ P AI hT K LL hA τ₀
  haveI := (P.PD K).finK₀
  have hn : 0 < finrank ℚ_[l] ↥(K0 K) := Module.finrank_pos
  obtain ⟨x, hxu, hxφ, hx1, hx2, hxj⟩ := _root_.GlobalTheory.LTPeriod.main l P AI hT K _ hn
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.ltChar_hom l P K x hxu (_root_.GlobalTheory.PeriodQuot.galois_periodRatio_mem_unramified l P AI hT K x hxu hxφ hx1 hx2 hxj)
  have hcont := _root_.GlobalTheory.LtCharCont.continuous_char_of_act l P AI hT K x hxu hx1 hx2 c hc
  obtain ⟨χ, hχc, hχ⟩ := _root_.GlobalTheory.ContCharUnitsOL.main l K LL τ₀ c hcont
  exact ⟨χ, hχc, _root_.GlobalTheory.HWL.charRep_crys_jump_one l P AI hT K LL hA τ₀ x hxu hxφ hx1 hx2 hxj c hc _ hχc hχ⟩

end GlobalTheory.LTChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisCharacterEqOneOfTrivialDegreeOneFrobenius
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open _root_.GlobalTheory

namespace GlobalTheory.FrobTrivChar

theorem eq_one_of_frob_trivial : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (φ : G E Ω →* (Qbar l)ˣ), Continuous φ →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 → w.asIdeal.ramificationIdx ℤ = 1 →
      ∀ (A : ValuationSubring Ω) (σ : G E Ω), IsPlaceOver (F := E) A w → IsFrob (F := E) A (normV w) σ → φ σ = 1) →
    φ = 1 := by
  classical
  intro E Ω _ _ _ _ _ l _ φ hφ hev
  have : IsGalois E Ω := {}
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.one_apply]
  by_contra hg
  have hV : IsOpen {x : G E Ω | φ x ≠ 1} := isOpen_ne_fun hφ continuous_const
  have hn : (fun u : G E Ω => u * g) ⁻¹' {x : G E Ω | φ x ≠ 1} ∈ nhds (1 : G E Ω) :=
    (hV.preimage (continuous_mul_const g)).mem_nhds (by simpa using hg)
  obtain ⟨L, hfd, hN, hL⟩ := (krullTopology_mem_nhds_one_iff_of_normal E Ω _).1 hn
  have hgal : IsGalois E L := {}
  have hS := Filter.eventually_cofinite.1 hev
  obtain ⟨v, hv, hf, he, B, hB, -, σ, hσ, hU⟩ := GlobalTheory.Published.cheb_holds E Ω L.fixingSubgroup
    L.fixingSubgroup_isOpen ((InfiniteGalois.normal_iff_isGalois L).2 hgal) g hS.toFinset
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  have h1 := hL hU
  simp only [Set.mem_preimage, Set.mem_setOf_eq, inv_mul_cancel_right] at h1
  exact h1 (hv hf he B σ hB hσ)

end GlobalTheory.FrobTrivChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasThetaAtOfThetaMod
section
noncomputable section

namespace GlobalTheory.RefPair

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain GlobalTheory.NPin GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def HasThetaAt (D : D7) {μt : D.what₂.Tup} {j : ℕ} (Mr : MtReal D μt j) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (X : RowMod D rep j) (μ η : HChar D.host.E) : Prop :=
  ∃ (Ω : Type) (_ : AddCommGroup Ω) (_ : Module ℂ Ω) (ω : GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ Ω)
    (Λ : Ω →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ) →ₗ[ℂ] ↥X.C →ₗ⋆[ℂ] ℂ) (φ₀ : Ω),
    (∀ h g φ (F F' : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ)) (y y' : ↥X.C),
      (F' : GAf D.host.E D.R.nV → Mr.wt.W) = NG.rt D.host.E D.R.nV h F → (y' : X.A) = X.ρ g y →
      Λ (ω (h, g) φ) F' y' = Λ φ F y) ∧
    (∀ x y (F : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ)), (F : GAf D.host.E D.R.nV → Mr.wt.W) = Mr.real x →
      inner ℂ y (D.what₂.thetaP μt j x) = Λ φ₀ F ⟨X.φ y, X.φ_mem y⟩) ∧
    ∀ (s : SplitPlace D.host.E) μw ηw, IsComp μ s.w μw → IsComp η s.w ηw →
      φ₀ ∈ ⨆ (ι : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] Ω)
        (_ : IsLinAt ω s μw ηw ι), LinearMap.range ι

end GlobalTheory.RefPair

end
end

