module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0501
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0497
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0045
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0507
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0478

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianArchimedeanComplexCoordinates
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def hermEquiv (σ : E →ₐ[F] E) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ))
    (hconj : ∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) (n : ℕ) :
    HermR (Ainf F) σ n ≃+ (InfinitePlace F → hermC n) where
  toFun b w := ⟨matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w, by
    refine mem_hermC.2 ?_
    ext a c
    simp only [Matrix.conjTranspose_apply, matC, RCLike.star_def]
    rw [← hconj, b.2 a c]⟩
  invFun G := ⟨fun a c => Θ.symm fun w => (G w : Matrix (Fin n) (Fin n) ℂ) a c, by
    intro a c
    apply Θ.injective
    funext w
    have h : (G w : Matrix (Fin n) (Fin n) ℂ).IsHermitian := mem_hermC.1 (G w).2
    rw [hconj]
    simp only [RingEquiv.apply_symm_apply]
    have := congrFun (congrFun h a) c
    simpa [Matrix.conjTranspose_apply] using this⟩
  left_inv b := by
    apply Subtype.ext
    ext a c
    simp [matC]
  right_inv G := by
    funext w
    apply Subtype.ext
    ext a c
    simp [matC]
  map_add' b b' := by
    funext w
    apply Subtype.ext
    ext a c
    simp [matC]

theorem continuous_hermEquiv (σ : E →ₐ[F] E) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ))
    (hconj : ∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) (hΘ : Continuous Θ) (n : ℕ) :
    Continuous (hermEquiv σ Θ hconj n) := by
  refine continuous_pi fun w => Continuous.subtype_mk ?_ _
  refine continuous_matrix fun a c => ?_
  have h1 : Continuous fun b : HermR (Ainf F) σ n =>
      (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) a c :=
    (continuous_id.matrix_elem a c).comp continuous_subtype_val
  exact (continuous_apply w).comp (hΘ.comp h1)

theorem continuous_hermEquiv_symm (σ : E →ₐ[F] E) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ))
    (hconj : ∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) (hΘ : Continuous Θ.symm) (n : ℕ) :
    Continuous (hermEquiv σ Θ hconj n).symm := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_matrix fun a c => ?_
  refine hΘ.comp (continuous_pi fun w => ?_)
  have h1 : Continuous fun b : hermC n => (b : Matrix (Fin n) (Fin n) ℂ) a c :=
    (continuous_id.matrix_elem a c).comp continuous_subtype_val
  exact h1.comp (continuous_apply w)

theorem continuous_symm (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (hΘ : IsHomeomorph Θ) :
    Continuous Θ.symm := by
  have e : (Θ.symm : (InfinitePlace F → ℂ) → Ainf F ⊗[F] E) = (hΘ.homeomorph Θ).symm := by
    funext y
    apply (hΘ.homeomorph Θ).injective
    rw [Homeomorph.apply_symm_apply]
    exact Θ.apply_symm_apply y
  rw [e]
  exact (hΘ.homeomorph Θ).symm.continuous

theorem topAddGroup_tens (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (hΘ : IsHomeomorph Θ) :
    IsTopologicalAddGroup (Ainf F ⊗[F] E) := by
  have c1 : Continuous Θ := hΘ.continuous
  have c2 : Continuous Θ.symm := continuous_symm Θ hΘ
  refine { continuous_add := ?_, continuous_neg := ?_ }
  · have : (fun p : (Ainf F ⊗[F] E) × (Ainf F ⊗[F] E) => p.1 + p.2) =
        fun p => Θ.symm (Θ p.1 + Θ p.2) := by
      funext p; simp
    rw [this]
    exact c2.comp ((c1.comp continuous_fst).add (c1.comp continuous_snd))
  · have : (fun x : Ainf F ⊗[F] E => -x) = fun x => Θ.symm (-Θ x) := by
      funext x; simp
    rw [this]
    exact c2.comp c1.neg

theorem exists_hermEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  ∀ n : ℕ, ∃ Ψ : HermR (Ainf F) σ n ≃+ (InfinitePlace F → hermC n),
    (∀ b w, ((Ψ b w : hermC n) : Matrix (Fin n) (Fin n) ℂ) = matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w) ∧
    ∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure →
      (ν.map Ψ).IsAddHaarMeasure ∧ ∀ G : (InfinitePlace F → hermC n) → ℂ, Integrable G (ν.map Ψ) → Integrable (fun b => G (Ψ b)) ν := by
  intro F E _ _ _ _ _ σ _ e τ Θ hc n
  obtain ⟨hΘ, hconj, -, -⟩ := hc
  have c1 : Continuous Θ := hΘ.continuous
  have c2 : Continuous Θ.symm := continuous_symm Θ hΘ
  haveI := topAddGroup_tens Θ hΘ
  haveI : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  have h1 := continuous_hermEquiv σ Θ hconj c1 n
  have h2 := continuous_hermEquiv_symm σ Θ hconj c2 n
  refine ⟨hermEquiv σ Θ hconj n, fun b w => rfl, fun ν hν => ⟨?_, fun G hG => ?_⟩⟩
  · exact AddEquiv.isAddHaarMeasure_map ν (hermEquiv σ Θ hconj n) h1 h2
  · exact hG.comp_measurable h1.measurable

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFiniteAdelesDenseRational
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua

theorem sig_sig_of_isCM {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2 τ, hCM.2.2.2 τ]
  simp

theorem sigR_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (t : R ⊗[F] E) :
    sigR R σ (sigR R σ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sigR_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (h : F) (t : R ⊗[F] E) :
    sigR R σ (h • t) = h • sigR R σ t :=
  map_smul (Algebra.TensorProduct.map (AlgHom.id F R) σ) h t

theorem inclR_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (h : F) (e : E) : inclR (F := F) R (h • e) = h • inclR (F := F) R e :=
  map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) h e

theorem sigR_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem denseRange_inclR (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] (hd : DenseRange (algebraMap F R)) :
    DenseRange (inclR R : E →+* R ⊗[F] E) := by
  haveI : Module.Finite F E :=
    Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let b := Module.finBasis F E
  have hφ := (_root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R).2.2.2.2.2.2.1 _ b
  let φ := hφ.homeomorph
  have hpi : DenseRange (Pi.map fun _ : Fin (Module.finrank F E) => (algebraMap F R)) :=
    DenseRange.piMap fun _ => hd
  have hc : DenseRange (φ.symm ∘ Pi.map fun _ : Fin (Module.finrank F E) => (algebraMap F R)) :=
    φ.symm.surjective.denseRange.comp hpi φ.symm.continuous
  refine hc.mono ?_
  rintro _ ⟨a, rfl⟩
  refine ⟨b.equivFun.symm a, ?_⟩
  apply φ.injective
  rw [Function.comp_apply, Homeomorph.apply_symm_apply]
  funext k
  show (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] (b.equivFun.symm a)) k = _
  simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.single_apply, apply_ite]

theorem hermE_dense_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ g : HermR (Af F) σ n, ∃ c : hermE σ n, g - hermIn (Af F) σ n c ∈ U := by
  intro F E _ _ _ _ _ σ hCM n U hU g
  obtain ⟨hlc, hsc, ht2, -, -, hden, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F
  obtain ⟨hTR, -, -, -, hsig, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Af F)
  have hincl := denseRange_inclR F E σ hCM (Af F) hden
  have hσ := sig_sig_of_isCM σ hCM

  have hmat : DenseRange (fun c : Matrix (Fin n) (Fin n) E => c.map (inclR (Af F))) :=
    DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hincl))

  let h : F := 1 / 2
  let Pm : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) → Matrix (Fin n) (Fin n) (Af F ⊗[F] E) :=
    fun m a b => h • (m a b + sigR (Af F) σ (m b a))
  have hPm : ∀ m, Pm m ∈ HermR (Af F) σ n := by
    intro m a b
    show sigR (Af F) σ (h • (m b a + sigR (Af F) σ (m a b))) = h • (m a b + sigR (Af F) σ (m b a))
    rw [sigR_smul, map_add (f := _), sigR_sigR _ _ hσ, add_comm]
  have hsmul : Continuous fun x : Af F ⊗[F] E => h • x := by
    simp_rw [Algebra.smul_def]
    exact continuous_const.mul continuous_id
  have hPc : Continuous Pm := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    exact hsmul.comp ((continuous_id.matrix_elem a b).add
      (hsig.comp (continuous_id.matrix_elem b a)))
  let P : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) → HermR (Af F) σ n := fun m => ⟨Pm m, hPm m⟩
  have hP : Continuous P := hPc.subtype_mk hPm
  have hW : IsOpen {m | g - P m ∈ U} :=
    hU.preimage (continuous_const.sub hP)
  have hg : P g.1 = g := by
    apply Subtype.ext
    ext a b
    show h • (g.1 a b + sigR (Af F) σ (g.1 b a)) = g.1 a b
    rw [g.2 a b, ← two_smul F, smul_smul]
    norm_num [h]
  have hne : ({m | g - P m ∈ U} : Set _).Nonempty := ⟨g.1, by simp [hg, U.zero_mem]⟩
  obtain ⟨c₀, hc₀⟩ := hmat.exists_mem_open hW hne
  let c : Matrix (Fin n) (Fin n) E := fun a b => h • (c₀ a b + σ (c₀ b a))
  have hc : c ∈ hermE σ n := by
    intro a b
    show σ (h • (c₀ b a + σ (c₀ a b))) = h • (c₀ a b + σ (c₀ b a))
    rw [Algebra.smul_def, map_mul, AlgHom.commutes, ← Algebra.smul_def, map_add (f := _), hσ, add_comm]
  refine ⟨⟨c, hc⟩, ?_⟩
  have hcP : hermIn (Af F) σ n ⟨c, hc⟩ = P (c₀.map (inclR (Af F))) := by
    apply Subtype.ext
    ext a b
    show inclR (Af F) (h • (c₀ a b + σ (c₀ b a))) =
      h • (inclR (Af F) (c₀ a b) + sigR (Af F) σ (inclR (Af F) (c₀ b a)))
    rw [inclR_smul, map_add (f := _), sigR_inclR]
  rw [hcP]
  exact hc₀

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianLatticeMemIffEntries
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.LatCmp

section Loc

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sum_coord {R : Type} [CommRing R] [Algebra F R] {d : ℕ} (b : Module.Basis (Fin d) F E) (x : R ⊗[F] E) :
    x = ∑ k, ((Algebra.TensorProduct.basis R b).repr x k) • ((1 : R) ⊗ₜ[F] b k) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr x]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply]

theorem coord_sig {R : Type} [CommRing R] [Algebra F R] {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E)
    (x : R ⊗[F] E) (l : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (sigR R σ x) l =
      ∑ k, (Algebra.TensorProduct.basis R b).repr x k *
        (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] σ (b k)) l := by
  have h : sigR R σ x =
      ∑ k, ((Algebra.TensorProduct.basis R b).repr x k) • ((1 : R) ⊗ₜ[F] σ (b k)) := by
    conv_lhs => rw [sum_coord (R := R) b x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp [sigR]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

variable [FiniteDimensional F E]

theorem trace_coord {R : Type} [CommRing R] [Algebra F R] {d : ℕ} (b : Module.Basis (Fin d) F E) (x : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) x =
      ∑ k, (Algebra.TensorProduct.basis R b).repr x k * algebraMap F R (Algebra.trace F E (b k)) := by
  conv_lhs => rw [sum_coord (R := R) b x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, GlobalTheory.LatVac.trace_tmul, one_mul, smul_eq_mul]

theorem trace_tmul_one {R : Type} [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (hσ : ∀ e, algebraMap F E (Algebra.trace F E e) = e + σ e) (x : R ⊗[F] E) :
    (Algebra.trace R (R ⊗[F] E) x) ⊗ₜ[F] (1 : E) = x + sigR R σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add (f := _), TensorProduct.add_tmul, hx, hy, map_add (f := _)]
    abel
  | tmul a e =>
    have h1 : (a * algebraMap F R (Algebra.trace F E e)) ⊗ₜ[F] (1 : E) =
        a ⊗ₜ[F] algebraMap F E (Algebra.trace F E e) := by
      rw [mul_comm, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    have h2 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [sigR]
    rw [GlobalTheory.LatVac.trace_tmul, h1, hσ, TensorProduct.tmul_add, h2]

theorem half_trace_tmul {R : Type} [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (hσ : ∀ e, algebraMap F E (Algebra.trace F E e) = e + σ e) (h2 : (2 : F) ≠ 0) (x : R ⊗[F] E)
    (hx : sigR R σ x = x) :
    (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) x) ⊗ₜ[F] (1 : E) = x := by
  rw [← Algebra.smul_def, ← TensorProduct.smul_tmul', trace_tmul_one σ hσ, hx, ← two_smul F x, smul_smul,
    one_div, inv_mul_cancel₀ h2, one_smul]

end Loc

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem latH_iff_at {d : ℕ} (σ : E →ₐ[F] E) (hσ : ∀ e, algebraMap F E (Algebra.trace F E e) = e + σ e)
    (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (n : ℕ)
    (h2 : (2 : F) ≠ 0)
    (hh : algebraMap F (Fv F v) (1 / 2) ∈ v.adicCompletionIntegers F)
    (h1 : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr ((1 : Fv F v) ⊗ₜ[F] (1 : E)) k ∈
      v.adicCompletionIntegers F)
    (hs : ∀ i k, (Algebra.TensorProduct.basis (Fv F v) b).repr ((1 : Fv F v) ⊗ₜ[F] σ (b i)) k ∈
      v.adicCompletionIntegers F)
    (ht : ∀ k, algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F)
    (Y : HermR (Fv F v) σ n) :
    Y ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n ↔
      (fun a i => (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) ∈
        (latV (M := n) (n := n) b v : Set (Fin n → Fin n → Fv F v ⊗[F] E)) := by
  constructor
  · rintro ⟨hd, ho⟩ a i k
    rcases lt_trichotomy a i with h | h | h
    · exact ho a i h k
    · subst h
      have e := half_trace_tmul (R := Fv F v) σ hσ h2 ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a) (Y.2 a a)
      have e2 : (Algebra.TensorProduct.basis (Fv F v) b).repr
          ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a) k =
          (algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
            ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a)) *
          (Algebra.TensorProduct.basis (Fv F v) b).repr ((1 : Fv F v) ⊗ₜ[F] (1 : E)) k := by
        conv_lhs => rw [← e]
        have e3 : (algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
            ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a)) ⊗ₜ[F] (1 : E) =
            (algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
            ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a)) • ((1 : Fv F v) ⊗ₜ[F] (1 : E)) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [e3, map_smul, Finsupp.smul_apply, smul_eq_mul]
      show (Algebra.TensorProduct.basis (Fv F v) b).repr
          ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a) k ∈ v.adicCompletionIntegers F
      rw [e2]
      exact mul_mem (hd a) (h1 k)
    · show (Algebra.TensorProduct.basis (Fv F v) b).repr
          ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) k ∈ v.adicCompletionIntegers F
      have e : sigR (Fv F v) σ ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i a) =
          (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i := Y.2 a i
      rw [← e, coord_sig]
      exact sum_mem fun l _ => mul_mem (ho i a h l) (hs l k)
  · intro h
    refine ⟨fun i => ?_, fun i j _ k => h i j k⟩
    rw [trace_coord b]
    exact mul_mem hh (sum_mem fun l _ => mul_mem (h i i l) (ht l))

end Place

theorem latH_iff_latV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite, ∀ Y : HermR (Fv F v) σ n, Y ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n ↔ (fun a i => (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) ∈ (latV (M := n) (n := n) b v : Set (Fin n → Fin n → Fv F v ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hCM n d b
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  obtain ⟨I1, I2⟩ := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ hCM d b
  have hT : ∀ k, ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F := by
    intro k
    by_cases h0 : Algebra.trace F E (b k) = 0
    · refine Filter.Eventually.of_forall fun v => ?_
      rw [h0, map_zero]
      exact zero_mem _
    · filter_upwards [I2 _ h0] with v hv
      exact hv.le
  filter_upwards [I2 (1 / 2) (by norm_num), I1 1, Filter.eventually_all.2 fun i => I1 (σ (b i)),
    Filter.eventually_all.2 hT] with v hh h1 hs ht Y
  exact latH_iff_at σ (GlobalTheory.CMTrace.trace_eq hCM) b v n two_ne_zero hh.le h1 hs ht Y

end GlobalTheory.CompanionTheory.SiegelND.Coef.LatCmp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory _root_.Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Free

def e0 (K : Type) [Zero K] [One K] (M : ℕ) : Fin 1 → Fin (M + 2) → K :=
  fun _ => Fin.cons 1 fun _ => 0

def consA {K : Type} [Zero K] [One K] {M n : ℕ} (a : Fin 1 → Fin n → K) (Y : Fin n → Fin M → K) :
    Fin (n + 1) → Fin (M + 2) → K :=
  Fin.cons (Fin.cons 1 fun _ => 0) fun j => Fin.cons (a 0 j) (Fin.cons 0 (Y j))

section PiLocalization₂

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]

def stageInt (σ : E →ₐ[F] E) {M n d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (lam : Measure R) (m' : Measure (Fin n → Fin M → R ⊗[F] E))
    (φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞) (g : HA R σ (hypOne J)) : ℝ≥0∞ :=
  ∫⁻ Y, ∫⁻ a, φ (actW R σ (hypOne J) g (consA a Y)) ∂(coordW R b lam 1 n) ∂m'

end PiLocalization₂

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def latStab (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (g : HA (Fv F v) σ J) : Prop :=
  ∀ x : Fin 1 → Fin M → Fv F v ⊗[F] E, actW (Fv F v) σ J g x ∈ latV b v ↔ x ∈ latV b v

def primV (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) :=
  {y | ∃ g : HA (Fv F v) σ (hypOne J), latStab σ (hypOne J) b v g ∧
    actW (Fv F v) σ (hypOne J) g (e0 _ M) = y}

def purePr (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞)
    (y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E) : ℝ≥0∞ :=
  {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E | ∀ v, v ∉ S → projV v (projFin y) ∈ primV σ J b v}.indicator
    (fun Y => Ψinf (projInf Y) * ∏ v ∈ S, Ψ v (projV v (projFin Y))) y

def ratA (n : ℕ) : AddSubgroup (Fin 1 → Fin n → AF F ⊗[F] E) where
  carrier := Set.range (ratTup (AF F) : (Fin 1 → Fin n → E) → Fin 1 → Fin n → AF F ⊗[F] E)
  zero_mem' := ⟨0, by funext a i; simp [ratTup]⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by funext a i; simp [ratTup]⟩
  neg_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by funext a i; simp [ratTup]⟩

def IsCovolOne {n : ℕ} (dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E)) : Prop :=
  dA.IsAddHaarMeasure ∧ ∃ D : Set (Fin 1 → Fin n → AF F ⊗[F] E),
    IsAddFundamentalDomain (ratA (F := F) (E := E) n) D dA ∧ dA D = 1

end Adelic

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryPointsHeightBoundFiniteStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor isTopologicalRing_tensor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_points_height_bound_finite : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E), IsUnit H.det → ∀ (Y : Set (unitaryPoints F E H 𝔸[F])) (ε : ℝ), 0 < ε → (∀ u ∈ Y, ∀ x : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F, x ≠ 0 → ε ≤ Reduction.height (trHom (ι := Fin n) (Module.finBasis F E) 𝔸[F] (u : GL (Fin n) (𝔸[F] ⊗[F] E))) x) → ∃ Ω : Set (unitaryPoints F E H 𝔸[F]), IsCompact Ω ∧ ∀ u ∈ Y, ∃ θ ∈ (unitaryDiagonal F H).range, θ⁻¹ * u ∈ Ω) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ t : ℝ, 0 < t → ∃ C₀ : Set (GAd σ J), IsCompact C₀ ∧ ∀ g : GAd σ J, (∀ v : Fin n → E, v ≠ 0 → t ≤ hgt σ J g v) → ∃ γ ∈ ratPts σ J, γ⁻¹ * g ∈ C₀ := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Mahler.exists_isCompact_of_le_hgt | exact GlobalTheory.CompanionTheory.RedCov.Mahler.exists_isCompact_of_le_hgt | (intros; apply GlobalTheory.CompanionTheory.RedCov.Mahler.exists_isCompact_of_le_hgt <;> assumption)
end

