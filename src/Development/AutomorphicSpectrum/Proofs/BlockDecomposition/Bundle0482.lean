module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.HermitianForms.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) (x : R ⊗[F] E) :
    sigR R' σ (Algebra.TensorProduct.map f (AlgHom.id F E) x) =
      Algebra.TensorProduct.map f (AlgHom.id F E) (sigR R σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def hermMap {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {n : ℕ} (S : HermR R σ n) : HermR R' σ n :=
  ⟨(S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map (Algebra.TensorProduct.map f (AlgHom.id F E)), by
    intro a b
    have h : sigR R σ ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) b a) = (S : Matrix _ _ _) a b := S.2 a b
    simp only [Matrix.map_apply]
    rw [sigR_map, h]⟩

theorem hermMap_sub {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {n : ℕ} (S T : HermR R σ n) :
    hermMap f σ (S - T) = hermMap f σ S - hermMap f σ T := by
  apply Subtype.ext
  funext a b
  simp [hermMap]

theorem hermMap_hermOf {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) :
    hermMap f σ (HeckeCharacterZeroLocus.SiegelWeilU.hermOf R σ T hT) = HeckeCharacterZeroLocus.SiegelWeilU.hermOf R' σ T hT := by
  apply Subtype.ext
  funext a b
  simp [hermMap, HeckeCharacterZeroLocus.SiegelWeilU.hermOf, HeckeCharacterZeroLocus.SiegelWeilU.inclR]

theorem sigR_hR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J y x) = hR R σ J x y := by
  have h2 : ∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR, hσ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h3 : ∀ i j, sigR R σ (JR R J i j) = JR R J j i := by
    intro i j
    simp [sigR, JR, inclR, hJ j i]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, map_sum, map_mul, h2, h3]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hermMap_hR {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → R ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (hR R σ J x y) =
      hR R' σ J (fun i => Algebra.TensorProduct.map f (AlgHom.id F E) (x i))
        (fun i => Algebra.TensorProduct.map f (AlgHom.id F E) (y i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, map_sum, map_mul, sigR_map]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [JR, inclR]

end Alg

section Cm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_invol {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2 τ, hCM.2.2.2 τ]
  simp

def gramH {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : HermR R σ n :=
  ⟨gramR R σ J X, fun a c => sigR_hR R σ (sig_invol hCM) hJ.1 (X a) (X c)⟩

theorem hermMap_gramH {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    hermMap f σ (gramH hCM hJ R X) =
      gramH hCM hJ R' (fun a i => Algebra.TensorProduct.map f (AlgHom.id F E) (X a i)) := by
  apply Subtype.ext
  funext a c
  exact hermMap_hR f σ J (X a) (X c)

end Cm

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def boxFN {M n : ℕ} (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)) :
    Set (Fin n → Fin M → Af F ⊗[F] E) :=
  {X | ∀ v, projV v X ∈ A v}

def pureN {M n : ℕ} (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (X : Fin n → Fin M → AF F ⊗[F] E) : ℂ :=
  φ (projInf X) * (boxFN A).indicator (fun _ => (1 : ℂ)) (projFin X)

def hermInf (σ : E →ₐ[F] E) {n : ℕ} (S : HermR (AF F) σ n) : HermR (Ainf F) σ n := hermMap (fstA F) σ S

def hermFin (σ : E →ₐ[F] E) {n : ℕ} (S : HermR (AF F) σ n) : HermR (Af F) σ n := hermMap (sndA F) σ S

def hermV (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (S : HermR (Af F) σ n) : HermR (Fv F v) σ n :=
  hermMap (evalV F v) σ S

def latH {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    Set (HermR (Fv F v) σ n) :=
  {S | (∀ i, algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
        ((S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i i) ∈ v.adicCompletionIntegers F) ∧
    ∀ i j, i < j → ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr
      ((S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i j) k ∈ v.adicCompletionIntegers F}

def intH {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Set (HermR (Af F) σ n) :=
  {y | ∀ v, v ∉ S → hermV σ v y ∈ latH σ b v n}

def boxH {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (HermR (Fv F v) σ n)) : Set (HermR (Af F) σ n) :=
  {y | (∀ v ∈ S, hermV σ v y ∈ U v) ∧ ∀ v, v ∉ S → hermV σ v y ∈ latH σ b v n}

def testH {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) {n : ℕ} (ρ : HermR (Ainf F) σ n → ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (HermR (Fv F v) σ n))
    (y : HermR (AF F) σ n) : ℂ :=
  (ρ (hermInf σ y) : ℂ) * (boxH σ b n S U).indicator (fun _ => (1 : ℂ)) (hermFin σ y)

def fouH (σ : E →ₐ[F] E) {n : ℕ} (ψ : AddChar (AF F) ℂ) (db : Measure (HermR (AF F) σ n))
    (τ : HermR (AF F) σ n → ℂ) (b : HermR (AF F) σ n) : ℂ :=
  ∫ y, τ y * ψ (pairHerm (AF F) σ n y b) ∂db

def chiT (σ : E →ₐ[F] E) {n : ℕ} (ψ : AddChar (AF F) ℂ) (T : Matrix (Fin n) (Fin n) E)
    (y : HermR (AF F) σ n) : ℂ :=
  ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
    (Matrix.trace (T.map (inclR (AF F)) * (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))))))

def coefSN {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (ψ : AddChar (AF F) ℂ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (T : Matrix (Fin n) (Fin n) E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ℂ :=
  ∫ y, (intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y) *
    (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * chiT σ ψ T y) ∂db

end Adelic

end GlobalTheory.CompanionTheory.SiegelND.Coef
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LaplacianMonicAnnihilatorMeasure
section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep.ConvLap

open Set Filter _root_.Topology MeasureTheory

section General

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} {h : IsExpLieAlgebra G 𝔤}

open IsExpLieAlgebra

theorem isSmoothFun_convDeriv {κ : G → ℂ}
    (hκ : h.IsSmoothFun κ) (X : 𝔤) :
    h.IsSmoothFun (h.convDeriv X κ) :=
  isSmoothFun_comp_inv (h := h) (κ := h.rightDeriv X fun z : G => κ z⁻¹)
    (h.isSmoothFun_rightDeriv (isSmoothFun_comp_inv hκ) X)

theorem rightDeriv_eq_integral_convDeriv_of_conv [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsHaarMeasure] {κ : G → ℂ}
    (hκ : h.IsSmoothFun κ) (hκc : HasCompactSupport κ)
    {f F : G → ℂ} (hfc : Continuous f) (hF : h.IsSmoothFun F)
    (hconv : ∀ x, F x = ∫ y, f (x * y) * κ y ∂μ) (X : 𝔤) (g : G) :
    h.rightDeriv X F g = ∫ y, f (g * y) * h.convDeriv X κ y ∂μ := by
  have hec : Continuous fun t : ℝ => h.expG (t • X) :=
    h.continuous_expG.comp (continuous_id.smul continuous_const)
  have hfg : Continuous fun y : G => f (g * y) := hfc.comp (continuous_const.mul continuous_id)
  have hκ'c : Continuous fun z : G => κ z⁻¹ := continuous_of_isSmoothFun (isSmoothFun_comp_inv hκ)
  have hDc := continuous_rightDeriv_comp_inv hκ X
  have hshift : ∀ t : ℝ, F (g * h.expG (t • X)) =
      ∫ y, f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹ ∂μ := by
    intro t
    rw [hconv (g * h.expG (t • X))]
    have := integral_mul_left_eq_self (μ := μ)
      (fun y => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹) (h.expG (t • X))
    rw [← this]
    congr 1
    funext y
    simp [mul_assoc, mul_inv_rev]
  have hderiv : ∀ (y : G) (t : ℝ), HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (s • X))⁻¹)
      (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) t := by
    intro y t
    have h1 := h.hasDerivAt_rightDeriv (isSmoothFun_comp_inv hκ) X (y⁻¹ * h.expG (t • X))
    have h1' : HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (t • X) * h.expG (s • X))⁻¹)
        (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) (t - t) := by
      rw [sub_self]; exact h1
    refine (h1'.comp_sub_const t t).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [mul_assoc, ← h.expG_add_smul, add_sub_cancel]
  set S : Set G := (fun p : ℝ × G => h.expG (p.1 • X) * p.2) ''
    (Metric.closedBall (0 : ℝ) 1 ×ˢ tsupport κ) with hSdef
  have hS : IsCompact S :=
    ((isCompact_closedBall 0 1).prod hκc).image
      ((hec.comp continuous_fst).mul continuous_snd)
  have hvanish : ∀ (y : G) (t : ℝ), t ∈ Metric.closedBall (0 : ℝ) 1 → y ∉ S →
      h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)) = 0 := by
    intro y t ht hy
    refine rightDeriv_comp_inv_eq_zero (fun hk => hy ⟨(t, (h.expG (t • X))⁻¹ * y), ⟨ht, ?_⟩, ?_⟩) X
    · simpa [mul_inv_rev] using hk
    · simp
  obtain ⟨M, hM⟩ := exists_bound_rightDeriv_comp_inv hκ hκc X
  have hbound : Integrable (S.indicator fun y => ‖f (g * y)‖ * M) μ := by
    refine IntegrableOn.integrable_indicator ?_ hS.measurableSet
    exact (hfg.norm.mul continuous_const).continuousOn.integrableOn_compact hS
  have hint0 : Integrable (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) μ := by
    have : (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) = fun y => f (g * y) * κ y := by
      funext y; simp
    rw [this]
    exact Continuous.integrable_of_hasCompactSupport (hfg.mul (continuous_of_isSmoothFun (f := κ) hκ))
      (hκc.mono' fun y hy => subset_tsupport κ (right_ne_zero_of_mul hy))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (t : ℝ) (y : G) => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹)
    (F' := fun (t : ℝ) (y : G) => f (g * y) *
      h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)))
    (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) 1)
    (bound := S.indicator fun y => ‖f (g * y)‖ * M)
    (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t =>
      (hfg.mul (hκ'c.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable) hint0
    (hfg.mul (hDc.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable
    (Eventually.of_forall fun y t ht => by
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      · rw [indicator_of_notMem hy, hvanish y t (Metric.ball_subset_closedBall ht) hy, mul_zero,
          norm_zero])
    hbound
    (Eventually.of_forall fun y t _ => (hderiv y t).const_mul (f (g * y)))
  have hd1 : HasDerivAt (fun t : ℝ => F (g * h.expG (t • X))) (h.rightDeriv X F g) 0 :=
    h.hasDerivAt_rightDeriv hF X g
  have hd2 := key.2.congr_of_eventuallyEq (Eventually.of_forall hshift)
  rw [hd1.unique hd2]
  congr 1
  funext y
  simp [convDeriv]

end General

section Adelic

open AutomorphicForm

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem uAction_ι_eq_integral_convDeriv [MeasurableSpace (archGroup K n)]
    [BorelSpace (archGroup K n)] {μ : MeasureTheory.Measure (archGroup K n)} [μ.IsHaarMeasure]
    (ψ u : archSmooth K n) {κ : archGroup K n → ℂ}
    (hκ : (isExpLieAlgebra K n).IsSmoothFun κ) (hκc : HasCompactSupport κ)
    (hu : ∀ g, (u : AdelicGLn.AdelicGL K n → ℂ) g =
      ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) * κ y ∂μ)
    (X : (isExpLieAlgebra K n).lieSubalgebra) (g : AdelicGLn.AdelicGL K n) :
    (uAction (UniversalEnvelopingAlgebra.ι ℝ X) u : AdelicGLn.AdelicGL K n → ℂ) g =
      ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) *
        (isExpLieAlgebra K n).convDeriv ((isExpLieAlgebra K n).ofLie X) κ y ∂μ := by
  rw [uAction_ι_apply]
  have hconv : ∀ x, archSlice (u : AdelicGLn.AdelicGL K n → ℂ) g x =
      ∫ y, archSlice (ψ : AdelicGLn.AdelicGL K n → ℂ) g (x * y) * κ y ∂μ := by
    intro x
    simp only [archSlice_apply, map_mul, ← mul_assoc]
    exact hu _
  rw [rightDeriv_eq_integral_convDeriv_of_conv hκ hκc
    (IsExpLieAlgebra.continuous_of_isSmoothFun (ψ.2 g)) (u.2 g) hconv]
  simp only [archSlice_apply, one_mul]

theorem exists_kernel_uAction_uJ [MeasurableSpace (archGroup K n)]
    [BorelSpace (archGroup K n)] (μ : MeasureTheory.Measure (archGroup K n)) [μ.IsHaarMeasure]
    (ψ : archSmooth K n) (k : ℕ) :
    ∀ (J : Fin k → Fin (CuspidalSpectrum.archDim K n)) (u : archSmooth K n)
      (κ : archGroup K n → ℂ), (isExpLieAlgebra K n).IsSmoothFun κ → HasCompactSupport κ →
      (∀ g, (u : AdelicGLn.AdelicGL K n → ℂ) g =
        ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) * κ y ∂μ) →
      ∃ D : archGroup K n → ℂ, (isExpLieAlgebra K n).IsSmoothFun D ∧ HasCompactSupport D ∧
        ∀ g : AdelicGLn.AdelicGL K n,
          ((uAction (CuspidalSpectrum.uJ (K := K) (n := n) k J) u :
            ↥(archSmooth K n)) : AdelicGLn.AdelicGL K n → ℂ) g =
            ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) * D y ∂μ := by
  induction k with
  | zero =>
    intro J u κ hκ hκc hu
    refine ⟨κ, hκ, hκc, fun g => ?_⟩
    simpa [CuspidalSpectrum.uJ] using hu g
  | succ k ih =>
    intro J u κ hκ hκc hu
    set X := CuspidalSpectrum.lieOf (CuspidalSpectrum.archBasis K n (J 0)) with hX
    obtain ⟨D, hD, hDc, hrep⟩ := ih (Fin.tail J)
      (uAction (UniversalEnvelopingAlgebra.ι ℝ X) u)
      ((isExpLieAlgebra K n).convDeriv ((isExpLieAlgebra K n).ofLie X) κ)
      (isSmoothFun_convDeriv hκ _) (IsExpLieAlgebra.hasCompactSupport_convDeriv hκc _)
      (fun g => uAction_ι_eq_integral_convDeriv ψ u hκ hκc hu X g)
    refine ⟨D, hD, hDc, fun g => ?_⟩
    rw [CuspidalSpectrum.uAction_uJ_succ]
    exact hrep g

theorem exists_conv_uJ_of_aeval_laplacian : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ψ : AutomorphicForm.archSmooth K n) (d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra K n).lieSubalgebra) (P : Polynomial ℂ),
    P.Monic → 0 < P.natDegree →
    (∀ g, Polynomial.aeval ((AutomorphicForm.isExpLieAlgebra K n).laplacian (F := ℂ) b) P
      (AutomorphicForm.sliceL g ψ) = 0) →
    ∀ [MeasurableSpace (AutomorphicForm.archGroup K n)] [BorelSpace (AutomorphicForm.archGroup K n)]
      (μ : MeasureTheory.Measure (AutomorphicForm.archGroup K n)) [μ.IsHaarMeasure]
      (k : ℕ) (J : Fin k → Fin (CuspidalSpectrum.archDim K n)),
      ∃ D : AutomorphicForm.archGroup K n → ℂ, Continuous D ∧ HasCompactSupport D ∧
        ∀ g : AdelicGLn.AdelicGL K n,
          ((AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := K) (n := n) k J) ψ :
            ↥(AutomorphicForm.archSmooth K n)) : AdelicGLn.AdelicGL K n → ℂ) g =
            ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * AutomorphicForm.infEmb K n y) * D y ∂μ := by
  intro K _ _ n ψ d b P hPm hPd hP _ _ μ _ k J
  obtain ⟨κ, hκs, hκc, -, hκ⟩ := (isExpLieAlgebra K n).exists_kernel_eq_conv_of_aeval_laplacian μ b P
    hPm hPd Filter.univ_mem
  have h1 : ∀ g, (ψ : AdelicGLn.AdelicGL K n → ℂ) g =
      ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) * κ y ∂μ := by
    intro g
    have := hκ (sliceL g ψ) (hP g) 1
    simpa [archSlice_apply] using this
  obtain ⟨D, hD, hDc, hrep⟩ := exists_kernel_uAction_uJ μ ψ k J ψ κ hκs hκc h1
  exact ⟨D, IsExpLieAlgebra.continuous_of_isSmoothFun hD, hDc, hrep⟩

end Adelic

end GlobalTheory.CompanionTheory.HCRep.ConvLap
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralTranslate
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E.E3 PositivityTheory.Rg.BcB

namespace GlobalTheory.CompanionTheory.CentRe

theorem no_growth (b I K : ℝ) (M : ℕ) (hb : 0 < b) (hI : 0 < I)
    (h : ∀ s : ℝ, 0 ≤ s → I * Real.exp (b * s) ≤ K * (1 + s) ^ M) : False := by
  set K' : ℝ := K / b ^ M / I * Real.exp b with hK'
  obtain ⟨x, hx1, hx2⟩ := (((Real.tendsto_exp_div_pow_atTop M).eventually_gt_atTop K').and
    (eventually_ge_atTop b)).exists
  have hx0 : 0 < x := lt_of_lt_of_le hb hx2
  have hs : 0 ≤ x / b - 1 := by
    rw [sub_nonneg, le_div_iff₀ hb]; linarith
  have hh := h _ hs
  rw [lt_div_iff₀ (pow_pos hx0 M)] at hx1
  have h1 : I * Real.exp (-b) * (K' * x ^ M) < I * Real.exp (-b) * Real.exp x :=
    mul_lt_mul_of_pos_left hx1 (mul_pos hI (Real.exp_pos _))
  have e1 : I * Real.exp (-b) * (K' * x ^ M) = K * (1 + (x / b - 1)) ^ M := by
    have hE := Real.exp_pos b
    rw [hK', Real.exp_neg, show 1 + (x / b - 1) = x / b by ring, div_pow]
    field_simp
  have e2 : I * Real.exp (-b) * Real.exp x = I * Real.exp (b * (x / b - 1)) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  rw [e1, e2] at h1
  exact absurd hh (not_le.2 h1)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem lintegral_translate [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure]
    (φ : GA E N → ℂ) (z : ℂ) (hz : ∀ (t : ℝ) g, φ (splitCentre E N t * g) = Complex.exp (z * t) * φ g)
    (t : ℝ) (Q : Set (GA E N)) :
    ∫⁻ g in (fun q => splitCentre E N t * q) '' Q, ‖φ g‖ₑ ^ 2 ∂μ =
      ENNReal.ofReal (Real.exp (2 * z.re * t)) * ∫⁻ g in Q, ‖φ g‖ₑ ^ 2 ∂μ := by
  rw [← (measurePreserving_mul_left μ (splitCentre E N t)).setLIntegral_comp_emb
    (measurableEmbedding_mulLeft _) (fun g => ‖φ g‖ₑ ^ 2) Q,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun g => ?_
  rw [hz, enorm_mul, mul_pow]
  congr 1
  rw [← ofReal_norm_eq_enorm, Complex.norm_exp, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 2
  simp
  ring

theorem centReGlue_holds : CentReGlue := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro hS hM E _ _ _ N φ z hφ hne hL hz
  letI : MeasurableSpace (GA E N) := borel _
  haveI : BorelSpace (GA E N) := ⟨rfl⟩
  obtain ⟨C, M, hC⟩ := hL Measure.haar inferInstance
  by_contra ha
  obtain ⟨x₀, hx₀⟩ : ∃ x, φ x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (funext hcon)
  obtain ⟨Q, hQ, hQn⟩ := exists_compact_mem_nhds x₀
  obtain ⟨n, hn⟩ := hM E N Q hQ
  obtain ⟨C₁, hC₁, hsz⟩ := hS E N {1} Q isCompact_singleton hQ
  set I : ENNReal := ∫⁻ g in Q, ‖φ g‖ₑ ^ 2 ∂(Measure.haar : Measure (GA E N)) with hI
  have key : ∀ t : ℝ, ENNReal.ofReal (Real.exp (2 * z.re * t)) * I ≤
      ENNReal.ofReal (C * n * (1 + C₁ * (1 + |t|)) ^ M) := by
    intro t
    rw [hI, ← lintegral_translate _ φ z hz t Q]
    refine hC _ (hQ.image (continuous_const.mul continuous_id)) n _ (by positivity) (hn _ ?_) ?_
    · exact fun g => GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t g
    · rintro _ ⟨q, hq, rfl⟩
      have h1 := hsz 1 rfl q hq (fun _ => t)
      rw [one_mul, PositivityTheory.Rg.Rs.JDict.tor_const] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hC₁)
      have : ‖(fun _ : Fin N => t)‖ ≤ |t| :=
        (pi_norm_le_iff_of_nonneg (abs_nonneg t)).2 fun _ => (Real.norm_eq_abs t).le
      linarith
  have hIpos : 0 < I := by
    rw [hI, setLIntegral_pos_iff (hφ.measurable.enorm.pow_const 2)]
    have hV : IsOpen (interior Q ∩ {x | φ x ≠ 0}) :=
      isOpen_interior.inter (isOpen_ne_fun hφ continuous_const)
    have hVne : (interior Q ∩ {x | φ x ≠ 0}).Nonempty :=
      ⟨x₀, mem_interior_iff_mem_nhds.2 hQn, hx₀⟩
    refine (hV.measure_pos _ hVne).trans_le (measure_mono ?_)
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, interior_subset hx1⟩
    simpa [Function.mem_support] using hx2
  have hItop : I ≠ ⊤ := by
    have h0 := key 0
    simp only [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul] at h0
    exact (h0.trans_lt ENNReal.ofReal_lt_top).ne
  have hI' : 0 < I.toReal := ENNReal.toReal_pos hIpos.ne' hItop
  have key' : ∀ t : ℝ, I.toReal * Real.exp (2 * z.re * t) ≤ C * n * (1 + C₁ * (1 + |t|)) ^ M := by
    intro t
    have h := key t
    rw [← ENNReal.ofReal_toReal hItop, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_le_ofReal_iff'] at h
    rcases h with h | h
    · rwa [mul_comm]
    · exact absurd h (not_le.2 (mul_pos (Real.exp_pos _) hI'))
  refine no_growth (2 * |z.re|) I.toReal (|C * n| * (1 + C₁) ^ M) M
    (by have := abs_pos.2 ha; positivity) hI' fun s hs => ?_
  have hsign : ∃ t : ℝ, 2 * z.re * t = 2 * |z.re| * s ∧ |t| = s := by
    rcases le_total 0 z.re with h | h
    · exact ⟨s, by rw [abs_of_nonneg h], abs_of_nonneg hs⟩
    · exact ⟨-s, by rw [abs_of_nonpos h]; ring, by rw [abs_neg, abs_of_nonneg hs]⟩
  obtain ⟨t, ht1, ht2⟩ := hsign
  have h := key' t
  rw [ht1, ht2] at h
  refine h.trans ?_
  have hb : 1 + C₁ * (1 + s) ≤ (1 + C₁) * (1 + s) := by nlinarith
  calc C * n * (1 + C₁ * (1 + s)) ^ M ≤ |C * n| * (1 + C₁ * (1 + s)) ^ M :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |C * n| * ((1 + C₁) * (1 + s)) ^ M :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb M) (abs_nonneg _)
    _ = |C * n| * (1 + C₁) ^ M * (1 + s) ^ M := by rw [mul_pow, mul_assoc]

end GlobalTheory.CompanionTheory.CentRe

end
end

