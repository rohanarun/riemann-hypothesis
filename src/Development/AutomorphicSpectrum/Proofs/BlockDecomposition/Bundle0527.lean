module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0509
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0511
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0510
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0494

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActWOneApply
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory _root_.Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

variable {F E : Type} [Field F] [Field E] [Algebra F E]

section Stab

variable (R : Type) [CommRing R] [Algebra F R]

theorem actW_mul_apply (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (g h : HA R σ J)
    (X : Fin n → Fin M → R ⊗[F] E) :
    actW R σ J (g * h) X = actW R σ J g (actW R σ J h X) := by
  funext a
  change ((HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
      (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E))) *ᵥ X a =
    (HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ
      ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ X a)
  rw [Matrix.mulVec_mulVec]

theorem actW_one_apply (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) : actW R σ J 1 X = X := by
  funext a
  change (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ X a = X a
  exact Matrix.one_mulVec _

def stabilizer₂ (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (HA R σ (hypOne J)) where
  carrier := {h | actW R σ (hypOne J) h (e0 _ M) = e0 _ M}
  one_mem' := actW_one_apply R σ (hypOne J) _
  mul_mem' := by
    intro g h hg hh
    change actW R σ (hypOne J) (g * h) (e0 _ M) = e0 _ M
    rw [actW_mul_apply, show actW R σ (hypOne J) h (e0 _ M) = e0 _ M from hh]
    exact hg
  inv_mem' := by
    intro g hg
    change actW R σ (hypOne J) g⁻¹ (e0 _ M) = e0 _ M
    have hg' : actW R σ (hypOne J) g (e0 _ M) = e0 _ M := hg
    conv_lhs => rw [← hg']
    rw [← actW_mul_apply, inv_mul_cancel, actW_one_apply]

def ratP (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (stabilizer₂ R σ J) :=
  Subgroup.comap (stabilizer₂ R σ J).subtype
    (show Subgroup (HA R σ (hypOne J)) from HFinIn R σ (hypOne J))

end Stab

def framesOne (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (n : ℕ) :
    Set (Fin (n + 1) → Fin (M + 2) → E) :=
  {X | X ∈ framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) ∧ X 0 = e0 E M 0}

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchLieDerivativeExistsStatement
section
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arch_lie_derivative_exists : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (hs : φ.1 ∈ AutomorphicForm.archSmooth E a), IsAutForm φ → (∀ [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)]
    (μ : MeasureTheory.Measure (AutomorphicForm.archGroup E a)) [μ.IsHaarMeasure]
    (k : ℕ) (J : Fin k → Fin (CuspidalSpectrum.archDim E a)),
    ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : AdelicGLn.AdelicGL E a,
      ((AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := E) (n := a) k J) (⟨φ.1, hs⟩ : ↥(AutomorphicForm.archSmooth E a)) :
        ↥(AutomorphicForm.archSmooth E a)) : AdelicGLn.AdelicGL E a → ℂ) g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂μ) := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv | exact GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv | (intros; apply GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanHermitianScalingByUnits
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.DiagScale

section Gen

theorem pi_map_scale_family {ι X : Type} [Fintype ι] [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (f : ι → X → X) (hf : ∀ i, Measurable (f i)) (c : ι → ℝ≥0) (h : ∀ i, μ.map (f i) = c i • μ) :
    (Measure.pi fun _ : ι => μ).map (fun x i => f i (x i)) =
      (∏ i, c i) • Measure.pi fun _ : ι => μ := by
  haveI : ∀ i, SigmaFinite (μ.map (f i)) := fun i => by rw [h i]; infer_instance
  rw [Measure.pi_map_pi (f := f) (fun i => (hf i).aemeasurable)]
  simp only [h]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib]
  push_cast
  rfl

theorem map_mul_scale {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [MeasurableSpace A] [BorelSpace A] (lam : Measure A) (u v : A) (c c' : ℝ≥0)
    (hu : lam.map (fun y => u * y) = c • lam) (hv : lam.map (fun y => v * y) = c' • lam) :
    lam.map (fun y => u * v * y) = (c * c') • lam := by
  have hm : ∀ x : A, Measurable (fun y : A => x * y) :=
    fun x => (continuous_const.mul continuous_id).measurable
  have e : (fun y => u * v * y) = (fun y => u * y) ∘ (fun y => v * y) := by
    funext y
    simp [mul_assoc]
  rw [e, ← Measure.map_map (hm u) (hm v), hv,
    Measure.map_smul c' (hm u).aemeasurable, hu, smul_smul, mul_comm]

def mulU (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [MeasurableSpace A] [BorelSpace A] (u : Aˣ) : A ≃ᵐ A :=
  { toEquiv := Units.mulLeft u
    measurable_toFun := (continuous_const.mul continuous_id).measurable
    measurable_invFun := (continuous_const.mul continuous_id).measurable }

theorem prod_pairs {n : ℕ} (c : Fin n → ℝ≥0) :
    (∏ i, c i * c i) * ∏ p : {p : Fin n × Fin n // p.1 < p.2}, (c p.1.1 * c p.1.2) ^ 2 =
      ∏ a, c a ^ (2 * n) := by
  classical
  set g : Fin n × Fin n → ℝ≥0 := fun x => c x.1 * c x.2 with hg
  have h1 : ∏ x : Fin n × Fin n, g x = (∏ a, c a) ^ (2 * n) := by
    rw [Fintype.prod_prod_type]
    simp only [hg, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_pow]
    ring
  have hU : ∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 < x.2), g x =
      ∏ p : {p : Fin n × Fin n // p.1 < p.2}, g p :=
    Finset.prod_subtype _ (by simp) _
  have hL : ∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.2 < x.1), g x =
      ∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 < x.2), g x :=
    Finset.prod_equiv (Equiv.prodComm _ _) (by simp) (by simp [hg, mul_comm])
  have hD : ∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 = x.2), g x =
      ∏ i, c i * c i := by
    symm
    refine Finset.prod_nbij' (fun i => (i, i)) Prod.fst (by simp) (by simp) (by simp) ?_ (by simp [hg])
    rintro ⟨a, b⟩ h
    simpa using (Finset.mem_filter.1 h).2
  have hS : ∏ x : Fin n × Fin n, g x =
      (∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 < x.2), g x) *
      ((∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 = x.2), g x) *
       (∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.2 < x.1), g x)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun x : Fin n × Fin n => x.1 < x.2) g]
    congr 1
    rw [← Finset.prod_filter_mul_prod_filter_not
      (Finset.univ.filter (fun x : Fin n × Fin n => ¬ x.1 < x.2)) (fun x => x.1 = x.2) g,
      Finset.filter_filter, Finset.filter_filter]
    congr 1
    · refine Finset.prod_congr (Finset.filter_congr fun x _ => ?_) fun _ _ => rfl
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨by simp [h], h⟩
    · refine Finset.prod_congr (Finset.filter_congr fun x _ => ?_) fun _ _ => rfl
      constructor
      · intro h
        exact lt_of_le_of_ne (not_lt.1 h.1) (fun e => h.2 e.symm)
      · intro h
        exact ⟨not_lt.2 h.le, h.ne'⟩
  have hP : ∏ p : {p : Fin n × Fin n // p.1 < p.2}, (c p.1.1 * c p.1.2) ^ 2 =
      (∏ p : {p : Fin n × Fin n // p.1 < p.2}, g p) ^ 2 := by
    rw [Finset.prod_pow]
  have hT : ∏ a, c a ^ (2 * n) = (∏ a, c a) ^ (2 * n) := Finset.prod_pow _ _ _
  rw [hT, ← h1, hS, hL, hD, hU, hP]
  ring

end Gen

section H
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

theorem coordHerm_map_diag (σ : E →ₐ[F] E) (hσ : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (lam : Measure R) [lam.IsAddHaarMeasure] {n : ℕ}
    (u : Fin n → Rˣ) (c : Fin n → ℝ≥0) (h : ∀ a, lam.map (fun y => (u a : R) * y) = c a • lam)
    (τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n → HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n) (hτm : Measurable τ)
    (hτ : ∀ S i j, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j =
      algebraMap R (R ⊗[F] E) (u i) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j *
        algebraMap R (R ⊗[F] E) (u j)) :
    (GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n).map τ =
      (∏ a, c a ^ (2 * n)) • GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  have hd : d = 2 := by
    rw [← h2, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  obtain ⟨hinv, δ, hδ, hσδ⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hσ
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  obtain ⟨hK, -, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ R 2 b lam ‹_›
  haveI := hK
  haveI := hH n
  have hhom := GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_isHomeomorph R hinv h2 hδ hσδ n t5 t6
  let φ := GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord R σ n
  let Q : Measure ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
    Measure.pi fun _ => GlobalTheory.CompanionTheory.SW.coordK R b lam
  let P := (Measure.pi fun _ : Fin n => lam).prod Q
  have hν : GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n = Measure.comap φ P := rfl
  have hcond : Function.Injective φ ∧ ∀ s, MeasurableSet s → NullMeasurableSet (φ '' s) P := by
    by_contra hc
    have h0 : GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n = 0 := by
      rw [hν, Measure.comap, dite_eq_right hc]
    have := isOpen_univ.measure_pos (GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n) Set.univ_nonempty
    simp [h0] at this
  let D1 : (Fin n → R) ≃ᵐ (Fin n → R) :=
    MeasurableEquiv.piCongrRight fun i => mulU R (u i * u i)
  let D2 : ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) ≃ᵐ
      ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
    MeasurableEquiv.piCongrRight fun p =>
      mulU (R ⊗[F] E) (Units.map (algebraMap R (R ⊗[F] E)).toMonoidHom (u p.1.1 * u p.1.2))
  have hsc : ∀ a a', lam.map (fun y => ((u a * u a' : Rˣ) : R) * y) = (c a * c a') • lam := by
    intro a a'
    rw [Units.val_mul]
    exact map_mul_scale lam _ _ _ _ (h a) (h a')
  have m1 : (Measure.pi fun _ : Fin n => lam).map D1 =
      (∏ i, c i * c i) • Measure.pi fun _ : Fin n => lam :=
    pi_map_scale_family lam (fun i y => ((u i * u i : Rˣ) : R) * y)
      (fun i => (continuous_const.mul continuous_id).measurable) _ (fun i => hsc i i)
  have m2 : Q.map D2 = (∏ p : {p : Fin n × Fin n // p.1 < p.2}, (c p.1.1 * c p.1.2) ^ 2) • Q :=
    pi_map_scale_family (GlobalTheory.CompanionTheory.SW.coordK R b lam)
      (fun (p : {p : Fin n × Fin n // p.1 < p.2}) y => algebraMap R (R ⊗[F] E) ((u p.1.1 * u p.1.2 : Rˣ) : R) * y)
      (fun p => (continuous_const.mul continuous_id).measurable) _
      (fun p => GlobalTheory.CompanionTheory.SW.Dil.coordK_map_unit R σ hσ b lam _ _ (hsc p.1.1 p.1.2))
  have hD : P.map (D1.prodCongr D2) = (∏ a, c a ^ (2 * n)) • P := by
    have e := Measure.map_prod_map (Measure.pi fun _ : Fin n => lam) Q D1.measurable D2.measurable
    rw [m1, m2, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, prod_pairs] at e
    exact e.symm
  rw [hν]
  refine GlobalTheory.CompanionTheory.SW.Dil.map_comap_scale φ P τ hτm (D1.prodCongr D2) _ hhom.surjective hcond.1 hcond.2 ?_ hD
  intro S
  refine Prod.ext ?_ ?_
  · funext i
    change algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i) =
      ((u i * u i : Rˣ) : R) * (algebraMap F R (1 / 2) *
        Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i))
    have e : algebraMap R (R ⊗[F] E) (u i) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i *
        algebraMap R (R ⊗[F] E) (u i) =
        ((u i * u i : Rˣ) : R) • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i := by
      rw [Algebra.smul_def, Units.val_mul, map_mul]
      ring
    rw [hτ, e, map_smul, smul_eq_mul]
    ring
  · funext p
    change (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) p.1.1 p.1.2 =
      algebraMap R (R ⊗[F] E) ((u p.1.1 * u p.1.2 : Rˣ) : R) *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) p.1.1 p.1.2
    rw [hτ, Units.val_mul, map_mul]
    ring

end H

theorem coordHerm_map_diag_ainf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ), IsHomeomorph e → ∀ t : Fin n → Ainf F, (∀ a, IsUnit (t a)) → ∀ τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n → HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n, Measurable τ → (∀ S i j, (τ S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j = algebraMap (Ainf F) (Ainf F ⊗[F] E) (t i) * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j * algebraMap (Ainf F) (Ainf F ⊗[F] E) (t j)) → (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n).map τ = (∏ a, ((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (2 * n)) • GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n := by
  intro F E _ _ _ _ _ σ hσ n d b lam hlam e he t ht τ hτm hτ
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  exact coordHerm_map_diag (Ainf F) σ hσ b lam (fun a => (ht a).unit)
    (fun a => (∏ w, ‖e (t a) w‖₊)⁻¹)
    (fun a => GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar F e he lam hlam (t a) (ht a)) τ hτm hτ

end GlobalTheory.CompanionTheory.SW.DiagScale
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMeasureScalingByUnits
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Dil

theorem pi_smul_nnreal {ι : Type} [Fintype ι] {X : ι → Type} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (c : ι → ℝ≥0) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  classical
  refine Measure.pi_eq (μ := fun i => c i • μ i) fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    Finset.prod_mul_distrib]
  norm_cast

theorem coordW_map_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ), IsHomeomorph e → ∀ t : Fin n → Ainf F, (∀ a, IsUnit (t a)) → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M).map (fun X a i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * X a i) = (∏ a, ((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (d * M)) • GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M := by
  intro F E _ _ _ _ _ σ hσ n M d b lam hlam e he t ht
  obtain ⟨j1, j2, j3, j4, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Ainf F) d b lam hlam
  haveI := hK
  have hfm : ∀ a, Measurable (fun y : Ainf F ⊗[F] E => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * y) :=
    fun a => (continuous_const.mul continuous_id).measurable
  have hrow : ∀ a, (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam).map
      (fun (x : Fin M → Ainf F ⊗[F] E) i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i) =
      (((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (d * M)) • Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam := by
    intro a
    obtain ⟨u, hu⟩ := ht a
    have h := GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar F e he lam hlam (t a) (ht a)
    rw [← hu] at h
    have hk := coordK_map_unit (Ainf F) σ hσ b lam u _ h
    rw [hu] at hk
    have hk1 := pi_map_scale (ι := Fin M) (GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) _ (hfm a) _ hk
    simp only [Fintype.card_fin, ← pow_mul] at hk1
    exact hk1
  have hrm : ∀ a, Measurable (fun (x : Fin M → Ainf F ⊗[F] E) i =>
      algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i) := fun a =>
    measurable_pi_iff.2 fun i => (hfm a).comp (measurable_pi_apply i)
  haveI : ∀ a, SigmaFinite ((Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam).map
      (fun (x : Fin M → Ainf F ⊗[F] E) i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i)) := fun a => by
    rw [hrow a]; infer_instance
  have hmap := Measure.pi_map_pi (μ := fun _ : Fin n => Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam)
    (f := fun a (x : Fin M → Ainf F ⊗[F] E) i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i) (fun a => (hrm a).aemeasurable)
  unfold GlobalTheory.CompanionTheory.SW.coordW
  refine hmap.trans ?_
  simp only [hrow]
  exact pi_smul_nnreal _ _

end GlobalTheory.CompanionTheory.SW.Dil
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanRankOneFreeOfPlaces
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.SW.BB

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0.FreeVec

open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.CoordCM

theorem real_indep {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (b : Module.Basis (Fin 2) F E) (τ : E →+* ℂ) (s t : ℝ)
    (hst : (s : ℂ) * τ (b 0) + (t : ℂ) * τ (b 1) = 0) : s = 0 ∧ t = 0 := by
  obtain ⟨θ₀, hθ₀⟩ := exists_moved h
  have hb0 : b 0 ≠ 0 := b.ne_zero 0
  obtain ⟨θ, hθ⟩ : ∃ θ : E, θ * b 0 = b 1 := ⟨b 1 / b 0, div_mul_cancel₀ _ hb0⟩
  have hmoved : σ θ ≠ θ := by
    intro hfix
    apply hθ₀
    obtain ⟨A, B, hAB⟩ : ∃ A B : F,
        θ₀ * b 0 = algebraMap F E A * b 0 + algebraMap F E B * b 1 :=
      ⟨_, _, by
        have := b.sum_repr (θ₀ * b 0)
        rw [Fin.sum_univ_two, Algebra.smul_def, Algebra.smul_def] at this
        exact this.symm⟩
    have h1 : θ₀ = algebraMap F E A + algebraMap F E B * θ := by
      apply mul_right_cancel₀ hb0
      rw [add_mul, mul_assoc, hθ]
      exact hAB
    rw [h1, map_add (f := _), map_mul, hfix, AlgHom.commutes, AlgHom.commutes]
  have him : (τ θ).im ≠ 0 := im_ne_zero h hmoved τ
  have hb1 : τ (b 1) = τ θ * τ (b 0) := by rw [← map_mul, hθ]
  have ht0 : τ (b 0) ≠ 0 := (map_ne_zero τ).2 hb0
  have h2 : (s : ℂ) + t * τ θ = 0 := by
    apply mul_right_cancel₀ ht0
    rw [zero_mul, add_mul, mul_assoc, ← hb1]
    exact hst
  have hi := congrArg Complex.im h2
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_add,
    zero_mul, add_zero, Complex.zero_im] at hi
  have ht : t = 0 := (mul_eq_zero.1 hi).resolve_right him
  subst ht
  refine ⟨?_, rfl⟩
  simpa using h2

theorem eq_coord {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    (b : Module.Basis (Fin 2) F E) (y : R ⊗[F] E) :
    y = (Algebra.TensorProduct.basis R b).repr y 0 ⊗ₜ[F] b 0 +
      (Algebra.TensorProduct.basis R b).repr y 1 ⊗ₜ[F] b 1 := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr y]
  rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
    TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  simp

theorem linearIndependent_of_xw_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ X : Fin 1 → Fin M → Ainf F ⊗[F] E, (∀ w, xw e b X w ≠ 0) → LinearIndependent (Ainf F ⊗[F] E) X := by
  intro F E _ _ _ _ _ σ h M d b ρ e hρ he hx X hX
  classical
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)
  obtain rfl : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [h.2.2.1] at this
    simpa using this.symm
  have hex : ∀ w : InfinitePlace F, ∃ t : E →+* ℂ, ∀ x, t (algebraMap F E x) = w.embedding x := by
    intro w
    letI : Algebra F ℂ := w.embedding.toAlgebra
    let t : E →ₐ[F] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    exact ⟨t, fun x => t.commutes x⟩
  choose τ hτ using hex
  obtain ⟨Θ, hΘ⟩ := exists_hom e τ (fun x w => by rw [hx, hρ, hτ])
  have key : ∀ (y : Ainf F ⊗[F] E) (w : InfinitePlace F), Θ y w = 0 →
      ∀ k, e ((Algebra.TensorProduct.basis (Ainf F) b).repr y k) w = 0 := by
    intro y w hy k
    have h1 : Θ y w = (e ((Algebra.TensorProduct.basis (Ainf F) b).repr y 0) w : ℂ) * τ w (b 0) +
        (e ((Algebra.TensorProduct.basis (Ainf F) b).repr y 1) w : ℂ) * τ w (b 1) := by
      conv_lhs => rw [eq_coord b y, map_add (f := _), Pi.add_apply, hΘ, hΘ]
    rw [hy] at h1
    obtain ⟨h0, h1'⟩ := real_indep h b (τ w) _ _ h1.symm
    fin_cases k
    · exact h0
    · exact h1'
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have hg' : ∀ j, g 0 * X 0 j = 0 := fun j => by simpa using congrFun hg j
  have hw : ∀ w, Θ (g 0) w = 0 := by
    intro w
    obtain ⟨⟨j, k⟩, hjk⟩ := Function.ne_iff.1 (hX w)
    have hne : Θ (X 0 j) w ≠ 0 := fun h0 => hjk (key _ _ h0 k)
    have h3 := congrFun (congrArg Θ (hg' j)) w
    rw [map_mul, Pi.mul_apply, map_zero] at h3
    exact (mul_eq_zero.1 h3).resolve_right hne
  refine (Algebra.TensorProduct.basis (Ainf F) b).ext_elem fun k => ?_
  rw [map_zero, Finsupp.zero_apply]
  apply e.injective
  rw [map_zero]
  funext w
  exact key _ _ (hw w) k

end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.FreeVec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockWeilActionThetaUnfoldingStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_weil_action_theta_unfolding : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (b : Matrix (Fin r) (Fin r) D.host.E), (b.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = b →
    ∀ (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsUnit a.det →
    ∀ (Φ : Mx D V.rank (r + s) → ℂ) (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) (v : Mx D V.rank ((r + s) + (r + s))),
    xPart v = -HMul.hMul (colJoin y₁ (0 : Mx D V.rank s)) (rat a) →
    yPart v = HMul.hMul (colJoin (-HMul.hMul y₁ (rat b)) y₂) (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹) →
    ∀ (p : Matrix (Fin V.rank) (Fin r) D.host.E) (q : Matrix (Fin V.rank) (Fin s) D.host.E),
      Heisenberg₂ ψ V v Φ (rat (colJoin p q * a)) = cellTerm ψ V b a Φ p q y₁ y₂ := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.Summand.summand | exact GlobalTheory.CompanionTheory.EisUnfold.Summand.summand | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.Summand.summand <;> assumption)
end
end

