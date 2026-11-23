module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0028
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0018
public import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0029
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0530
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0532
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.ExistsGlCol
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1787
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0035
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0019
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0036
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0034

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ArchimedeanChartGaussianNorm
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_chart_gaussian_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (hψ : IsCharAF F B.ψ) (f : BBF σ JS JT ξ₀ B.ψ), IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 →
        Sm (rhoVF σ JS JT ξ₀ B.ψ hψ ι) f := by
  first | exact @_root_.GlobalTheory.ThetaSmoothF.sm_of_thetaF_k | exact _root_.GlobalTheory.ThetaSmoothF.sm_of_thetaF_k | (intros; apply _root_.GlobalTheory.ThetaSmoothF.sm_of_thetaF_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BMatK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def eA_k : AE F E := (((R.ε : ℤ) : E) : E) |> inclR (F := F) (E := E) (AF F)
def elt_k (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) : d.G :=
  if h : ∃ x : d.G, inFrame d.b x = M then h.choose else 1
def uA_k (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := 1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)
def bMat_k (β : Matrix (Fin d.n) (Fin d.n) (AE F E)) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks 1 β 0 1
def sB_k (b : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ j, (Matrix.single L.i₀ (L.em j) (b j) + Matrix.single (L.em j) L.i₀ (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_k R * cA σ (b j))))
def aB_k (δ : E) (a : AF F) : Matrix (Fin d.n) (Fin d.n) (AE F E) := Matrix.single L.i₀ L.i₀ (a • inclR (F := F) (E := E) (AF F) δ)
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.CAInjectiveK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def Au_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)
theorem em_ne_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (j : Fin L.n) : L.em j ≠ L.i₀ := fun h => (L.rng (L.em j)).2 ⟨j, rfl⟩ h
theorem Au_mul_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u v : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L v = _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (u + v) := by
  have h0 : (∑ j, Matrix.single L.i₀ (L.em j) (u j)) * (∑ k, Matrix.single L.i₀ (L.em k) (v k)) = 0 := by
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun k _ => Matrix.single_mul_single_of_ne _ _ _ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.em_ne_k L j) _
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k, add_mul, mul_add, one_mul, mul_one, h0, add_zero, Pi.add_apply, Matrix.single_add,
    Finset.sum_add_distrib, add_assoc]
theorem Au_zero_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L 0 = 1 := by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k]
theorem cA_injective_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Function.Injective (cA σ) := by
  have : FiniteDimensional F E := Module.Finite.of_basis d.bs
  have hb : Function.Bijective σ := AlgHom.bijective σ
  exact (Algebra.TensorProduct.congr AlgEquiv.refl (AlgEquiv.ofBijective σ hb)).injective
theorem frame_blk_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {x : d.G} {A A' : Matrix (Fin d.n) (Fin d.n) (AE F E)}
    (h : inFrame d.b x = Matrix.fromBlocks A 0 0 A') : Aᵀ * A'.map (cA σ) = 1 := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have h2 := kunf.frame_eq hε x
  rw [h] at h2
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one,
    Matrix.map_zero _ (map_zero (cA σ))] at h2
  exact (Matrix.fromBlocks_inj.1 h2).2.1
theorem blk_unique_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {x y : d.G} {A A₁ A₂ : Matrix (Fin d.n) (Fin d.n) (AE F E)}
    (hx : inFrame d.b x = Matrix.fromBlocks A 0 0 A₁) (hy : inFrame d.b y = Matrix.fromBlocks A 0 0 A₂) : x = y := by
  have h1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.frame_blk_k d hx
  have h2 := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.frame_blk_k d hy
  have h1' : A₁.map (cA σ) * Aᵀ = 1 := mul_eq_one_comm.1 h1
  have e : A₁.map (cA σ) = A₂.map (cA σ) := by
    calc A₁.map (cA σ) = A₁.map (cA σ) * (Aᵀ * A₂.map (cA σ)) := by rw [h2, Matrix.mul_one]
      _ = A₂.map (cA σ) := by rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
  have e2 : A₁ = A₂ := Matrix.map_injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cA_injective_k d) e
  apply kunf.inFrame_injective d.b
  rw [hx, hy, e2]
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousThetaLiftOfDefinite
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open UpperTheory.TP
theorem UpperTheory.continuous_thetaLift_of_definite :
    _root_.UpperTheory.TP.Tools_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → Continuous (lift M om Φ φ) := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hp Φ hΦ φ hφ
  have cX : Cpt σ X.J := T.cpt F E σ B n X n 0 hp.base (Or.inl hp.herm) (by simp)
  have cW : Cpt σ W.J := T.cpt F E σ B d W d 0 hp.base (Or.inr hp.skew) (by simp)
  obtain ⟨t1, t2, -⟩ := (T.basic F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp).1 Φ hΦ
  obtain ⟨C, hC⟩ := cX.bdd₂ cW (f := fun x => theta om Φ x.1 x.2) t1 fun γ hγ δ hδ g g' => t2 γ hγ δ hδ g g'
  obtain ⟨C', hC'⟩ := cX.bdd hφ.1 hφ.2
  have hfin : M.μ M.dom < ⊤ := cX.fin _ _ hp.good.haar hp.good.dom
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  haveI := cW.sc
  haveI : FirstCountableTopology (UA σ W.J) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  have hs : Continuous fun g => star (φ g) := hφ.1.star
  unfold lift
  refine continuous_of_dominated (bound := fun _ => C * C') (fun h => ?_) (fun h => ?_) (integrable_const _) ?_
  · exact ((t1.comp (continuous_id.prodMk continuous_const)).mul hs).aestronglyMeasurable
  · refine Eventually.of_forall fun g => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (hC (g, h)) (hC' g) (norm_nonneg _) ((norm_nonneg _).trans (hC (g, h)))
  · refine Eventually.of_forall fun g => ?_
    exact (t1.comp (continuous_const.prodMk continuous_id)).mul continuous_const
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisHalfPlaneK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
namespace GlobalTheory.CompanionTheory.SiegelEis
theorem eis_half_plane_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ Ê : ℂ → G2 σ Y → ℂ, ∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧ ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re} := by
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY b K a hb hK hH χ s₁ f hf
  have hKc : IsCompact (K : Set (G2 σ Y)) := _root_.GlobalTheory.T.isCompact_standard_maximal_compact F E σ B n Y r s hB hn hY b K a hb hK hH
  obtain ⟨-, hpos⟩ := _root_.GlobalTheory.T.height_function_continuous_pos F E σ B n Y r s hB hn hY b K a hb hK hH
  obtain ⟨C, hC⟩ := GlobalTheory.T.flat_section_growth_bound K a hKc hH hpos χ s₁ f hf
  obtain ⟨σ₀, hσ⟩ := _root_.GlobalTheory.T.eisenstein_series_convergence_bound F E σ B n Y r s hB hn hY b K a hb hK hH
  have hsum : ∀ σ' : ℝ, σ₀ < σ' → ∀ x : G2 σ Y,
      Summable (fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ σ') := by
    intro σ' h x
    obtain ⟨_, _, h'⟩ := hσ σ' h
    exact (h' x).1
  have hterm : ∀ (z : ℂ) (x : G2 σ Y) (q : Cos σ Y),
      ‖eisTerm (flat a f s₁ z) x q‖ ≤ C * a ((Quotient.out q).1 * x) ^ (z.re + (n : ℝ) / 2) :=
    fun z x q => hC z _
  refine ⟨fun z x => ∑' q, eisTerm (flat a f s₁ z) x q, σ₀ - (n : ℝ) / 2, ?_, ?_⟩
  · intro z hz x
    have h1 : σ₀ < z.re + (n : ℝ) / 2 := by linarith
    exact (Summable.of_norm_bounded ((hsum _ h1 x).mul_left C) (hterm z x)).hasSum
  · intro x z hz
    have hz' : σ₀ - (n : ℝ) / 2 < z.re := hz
    obtain ⟨c, hc1, hc2⟩ := exists_between hz'
    set d : ℝ := z.re + 1 with hd
    have hopen : IsOpen {w : ℂ | c < w.re ∧ w.re < d} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hc3 : σ₀ < c + (n : ℝ) / 2 := by linarith
    have hd3 : σ₀ < d + (n : ℝ) / 2 := by linarith
    have hu : Summable (fun q : Cos σ Y => |C| * (a ((Quotient.out q).1 * x) ^ (c + (n : ℝ) / 2) +
        a ((Quotient.out q).1 * x) ^ (d + (n : ℝ) / 2))) :=
      ((hsum _ hc3 x).add (hsum _ hd3 x)).mul_left _
    have hdiff : ∀ q : Cos σ Y,
        DifferentiableOn ℂ (fun w : ℂ => eisTerm (flat a f s₁ w) x q) {w : ℂ | c < w.re ∧ w.re < d} :=
      fun q => (differentiable_cpow_term (hpos _) s₁ _).differentiableOn
    have hle : ∀ (q : Cos σ Y) (w : ℂ), w ∈ {w : ℂ | c < w.re ∧ w.re < d} →
        ‖eisTerm (flat a f s₁ w) x q‖ ≤ |C| * (a ((Quotient.out q).1 * x) ^ (c + (n : ℝ) / 2) +
          a ((Quotient.out q).1 * x) ^ (d + (n : ℝ) / 2)) := by
      intro q w hw
      have hA := hpos ((Quotient.out q).1 * x)
      have h2 := rpow_le_add_rpow (u := w.re + (n : ℝ) / 2) (c := c + (n : ℝ) / 2)
        (d := d + (n : ℝ) / 2) hA (by linarith [hw.1]) (by linarith [hw.2])
      have h3 := Real.rpow_nonneg hA.le (w.re + (n : ℝ) / 2)
      calc _ ≤ C * a ((Quotient.out q).1 * x) ^ (w.re + (n : ℝ) / 2) := hterm w x q
        _ ≤ |C| * a ((Quotient.out q).1 * x) ^ (w.re + (n : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) h3
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
    have hD := Complex.differentiableOn_tsum_of_summable_norm hu hdiff hopen hle
    have hmem : {w : ℂ | c < w.re ∧ w.re < d} ∈ 𝓝 z :=
      hopen.mem_nhds ⟨hc2, by rw [hd]; linarith⟩
    exact (hD.differentiableAt hmem).differentiableWithinAt
end GlobalTheory.CompanionTheory.SiegelEis
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisHalfPlaneKAlt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.CompanionTheory.EisHalf
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter _root_.Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem eis_half_plane_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ t₀ : ℝ, ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), t₀ ≤ t → (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) → (∀ s : ℂ, t < s.re → (fun x => Ê s x) ∈ modFun σ Y) ∧ ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) ({s : ℂ | t < s.re} ×ˢ Set.univ) ∧ ∀ c c' : ℝ, t < c → ∃ (C : ℝ) (N : ℕ), ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ∀ x, ‖Ê s x‖ ≤ C * (ht2 x : ℝ) ^ N := by
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY b K a hb hK ha χ s₁ f hf
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨ac, a0⟩ := _root_.GlobalTheory.T.height_function_continuous_pos F E σ B n Y r s hB hn hY b K a hb hK ha
  have kc := _root_.GlobalTheory.T.isCompact_standard_maximal_compact F E σ B n Y r s hB hn hY b K a hb hK ha
  obtain ⟨C, hC⟩ := GlobalTheory.T.flat_section_growth_bound K a kc ha a0 χ s₁ f hf
  obtain ⟨σ₀, hG⟩ := _root_.GlobalTheory.T.eisenstein_series_convergence_bound F E σ B n Y r s hB hn hY b K a hb hK ha
  obtain ⟨W, hW, h1W, hWa⟩ := exists_nhd_one kc ac ha a0
  refine ⟨σ₀ - n / 2, fun t Ê ht hE => ?_⟩
  have tb : ∀ (z : ℂ) (c c' : ℝ), c ≤ z.re → z.re ≤ c' → ∀ g,
      ‖flat a f s₁ z g‖ ≤ |C| * (a g ^ (c + (n : ℝ) / 2) + a g ^ (c' + (n : ℝ) / 2)) := fun z c c' h1 h2 g =>
    (hC z g).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_pos_of_pos (a0 g) _).le).trans
      (mul_le_mul_of_nonneg_left (rpow_le_add (a0 g) (by linarith) (by linarith)) (abs_nonneg C)))
  have gr : ∀ c c' : ℝ, t < c → ∃ (D : ℝ) (N : ℕ), ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ∀ x, ‖Ê s x‖ ≤ D * (ht2 x : ℝ) ^ N := by
    intro c c' hc
    have h1 : σ₀ < c + (n : ℝ) / 2 := by linarith
    have h2 : σ₀ < max c c' + (n : ℝ) / 2 := by linarith [le_max_left c c']
    obtain ⟨C₁, N₁, H₁⟩ := hG _ h1
    obtain ⟨C₂, N₂, H₂⟩ := hG _ h2
    refine ⟨|C| * (|C₁| + |C₂|), max N₁ N₂, fun z h1z h2z x => ?_⟩
    have hx : (1 : ℝ) ≤ ht2 x := one_le_heightGL F x.1
    have S := (H₁ x).1.add (H₂ x).1
    have hs := (hE z (by linarith) x).norm_le_of_bounded (S.mul_left |C|).hasSum
      (fun q => tb z c (max c c') h1z (h2z.trans (le_max_right c c')) _)
    refine hs.trans ?_
    rw [tsum_mul_left, (H₁ x).1.tsum_add (H₂ x).1, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
    have p1 : (ht2 x : ℝ) ^ N₁ ≤ (ht2 x : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ hx (le_max_left _ _)
    have p2 : (ht2 x : ℝ) ^ N₂ ≤ (ht2 x : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ hx (le_max_right _ _)
    have q0 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N₁ := pow_nonneg (by linarith) _
    have q1 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N₂ := pow_nonneg (by linarith) _
    rw [add_mul]
    exact add_le_add ((H₁ x).2.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) q0).trans
        (mul_le_mul_of_nonneg_left p1 (abs_nonneg _))))
      ((H₂ x).2.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) q1).trans (mul_le_mul_of_nonneg_left p2 (abs_nonneg _))))
  have ct : ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) ({s : ℂ | t < s.re} ×ˢ Set.univ) := by
    rintro ⟨z₀, x₀⟩ ⟨hz₀, -⟩
    have hz₁ : t < z₀.re := hz₀
    obtain ⟨c, hc1, hc2⟩ := exists_between hz₁
    obtain ⟨c', hc'⟩ := exists_gt z₀.re
    have h1 : σ₀ < c + (n : ℝ) / 2 := by linarith
    have h2 : σ₀ < c' + (n : ℝ) / 2 := by linarith
    obtain ⟨_, _, H₁⟩ := hG _ h1
    obtain ⟨_, _, H₂⟩ := hG _ h2
    let V : Set (G2 σ Y) := (fun x => x₀⁻¹ * x) ⁻¹' W
    have hV : IsOpen V := hW.preimage (continuous_const.mul continuous_id)
    let S : Set (ℂ × G2 σ Y) := {z : ℂ | c < z.re ∧ z.re < c'} ×ˢ V
    have hS : IsOpen S :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)).prod hV
    have mS : (z₀, x₀) ∈ S := ⟨⟨hc2, hc'⟩, by simpa [V] using h1W⟩
    have sumU : Summable fun q : Cos σ Y => |C| *
        (2 ^ |c + (n : ℝ) / 2| * a ((Quotient.out q).1 * x₀) ^ (c + (n : ℝ) / 2) +
          2 ^ |c' + (n : ℝ) / 2| * a ((Quotient.out q).1 * x₀) ^ (c' + (n : ℝ) / 2)) :=
      (((H₁ x₀).1.mul_left _).add ((H₂ x₀).1.mul_left _)).mul_left _
    have cts : ContinuousOn (fun y : ℂ × G2 σ Y => ∑' q : Cos σ Y, eisTerm (flat a f s₁ y.1) y.2 q) S := by
      refine continuousOn_tsum (fun q => Continuous.continuousOn ?_) sumU ?_
      · have cg : Continuous fun y : ℂ × G2 σ Y => (Quotient.out q).1 * y.2 := continuous_const.mul continuous_snd
        exact ((Complex.continuous_ofReal.comp (ac.comp cg)).cpow (continuous_fst.sub continuous_const)
          fun y => Complex.ofReal_mem_slitPlane.2 (a0 _)).mul (hf.cont.comp cg)
      · rintro q ⟨z, x⟩ ⟨⟨hz1, hz2⟩, hx⟩
        have hu := hWa ((Quotient.out q).1 * x₀) (x₀⁻¹ * x) hx
        rw [show (Quotient.out q).1 * x₀ * (x₀⁻¹ * x) = (Quotient.out q).1 * x by group] at hu
        exact (tb z c c' hz1.le hz2.le _).trans (mul_le_mul_of_nonneg_left (add_le_add
          (rpow_le_of_near (a0 _) hu.1 hu.2 _) (rpow_le_of_near (a0 _) hu.1 hu.2 _)) (abs_nonneg C))
    have ctE : ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) S :=
      cts.congr fun y hy => (hE y.1 (hc1.trans hy.1.1) y.2).tsum_eq.symm
    exact (ctE.continuousAt (hS.mem_nhds mS)).continuousWithinAt
  refine ⟨fun z hz => ?_, ct, gr⟩
  obtain ⟨D, N, hD⟩ := gr z.re z.re hz
  have cz : Continuous fun x => Ê z x :=
    ct.comp_continuous (Continuous.prodMk_right z) fun x => ⟨hz, trivial⟩
  have M1 : (1 : ℝ) ≤ max D 1 := le_max_right _ _
  have M0 : (0 : ℝ) < max D 1 := by linarith
  have Mc : ((max D 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 M0.ne'
  have e : (fun x => Ê z x) = ((max D 1 : ℝ) : ℂ) • ((((max D 1 : ℝ) : ℂ))⁻¹ • fun x => Ê z x) := by
    rw [smul_smul, mul_inv_cancel₀ Mc, one_smul]
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨cz.const_smul _, N, fun x => ?_⟩)
  have hx : (1 : ℝ) ≤ ht2 x := one_le_heightGL F x.1
  have q0 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N := pow_nonneg (by linarith) _
  rw [Pi.smul_apply, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg M0.le, inv_mul_le_iff₀ M0]
  exact (hD z le_rfl le_rfl x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) q0)
end GlobalTheory.CompanionTheory.EisHalf
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EpsEqK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp PositivityTheory.SiegelWeilFormula.kfour
namespace PositivityTheory.SiegelWeilFormula.Afc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem eps_eq_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {ε ε' : ℤˣ} (hε : FrameEq σ d.Y d.b ε) (hε' : FrameEq σ L.Y L.b ε') : ε = ε' := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  have hnL : 1 ≤ L.n := L.ok.hn
  have key : ∀ (s : ℤ), (∀ i j, σ (d.Y.J j i) = (s : E) * d.Y.J i j) → (∀ i j, σ (L.Y.J j i) = (s : E) * L.Y.J i j) →
      ε = ε' := fun s h1 h2 =>
    Units.ext ((eps_of_sign hσ d.ok.hn hε s h1).trans (eps_of_sign hσ hnL hε' s h2).symm)
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩ <;> rcases L.ok.sign with ⟨hA', hY'⟩ | ⟨hA', hY'⟩
  · exact key (-1) (fun i j => by rw [hY]; simp) (fun i j => by rw [hY']; simp)
  · exact (not_herm_skew d.ok.hm hA hA').elim
  · exact (not_herm_skew d.ok.hm hA' hA).elim
  · exact key 1 (fun i j => by rw [hY]; simp) (fun i j => by rw [hY']; simp)
end PositivityTheory.SiegelWeilFormula.Afc
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsInvFormSplitK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory
noncomputable section
namespace GlobalTheory.SplitInvFormF
theorem exists_invForm_split_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ → f₀ ≠ 0 →
        ∃ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
            ℓ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f ∧ ℓ f ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  obtain ⟨φ, hφ, hφ0, hd⟩ := _root_.GlobalTheory.T.exists_eigenvector_split_idempotent F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  obtain ⟨ℓ, h1, h2⟩ := GlobalTheory.HalfCoinv.exists_form (Y := conjHalf σ e nS nT) (ρ := heisL σ JS JT ξ₀ B.ψ)
    (B := commF σ JS JT ξ₀ B.ψ) (Θ := {g | IsThetaFunOF σ JS JT ξ₀ B.ψ g})
    (fun x hx x' hx' f => by
      show heisOF σ JS JT ξ₀ B.ψ x (heisOF σ JS JT ξ₀ B.ψ x' f) = heisOF σ JS JT ξ₀ B.ψ (x + x') f
      rw [heisOF_heisOF, symplOHF_half he hx hx', AddChar.map_zero_eq_one, one_smul])
    (fun f => heisOF_zero f) (fun u y f => heisOF_comm u y f)
    (fun u hu g hg => exists_nsmul_fix he hu hg) hφ0 hd
  exact ⟨ℓ, fun u hu f hf => h1 u hu f hf, φ, hφ, h2⟩
end GlobalTheory.SplitInvFormF
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GamQFEqOneIffK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
theorem beta_iota_right_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (x : WOF F E nS nT) (v : IxF F nS nT → ℂ) :
    B.ψ (symplOHF σ JS JT ξ₀ x (iotaVF ι v)) = Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (piWF θ x) v : ℝ)) :=
  _root_.PositivityTheory.ThKW.TauSpanIdentities.beta_iota_right_k C x v
theorem beta_iota_left_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (v : IxF F nS nT → ℂ) (x : WOF F E nS nT) :
    B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι v) x) = Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) v (piWF θ x) : ℝ)) :=
  _root_.PositivityTheory.ThKW.TauSpanIdentities.beta_iota_left_k C v x
theorem piWF_ratWF_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (y : Matrix (Fin nT) (Fin nS) E) :
    piWF θ (ratWF (F := F) y) = infRatF (tauB B) y :=
  _root_.PositivityTheory.ThKW.TauSpanIdentities.piWF_ratWF_k C y
theorem continuous_piWF_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) : Continuous (piWF (nS := nS) (nT := nT) θ) :=
  _root_.PositivityTheory.ThKW.TauSpanIdentities.continuous_piWF_k C
theorem piWF_actOF_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT) (x : WOF F E nS nT) :
    piWF θ (actOF σ JS JT g h x) = mMF σ JS JT θ (g, h) *ᵥ piWF θ x :=
  _root_.PositivityTheory.ThKW.TauSpanIdentities.piWF_actOF_k C g h x
theorem symplOF_actOF_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOF σ JS JT ξ₀ x y :=
  _root_.PositivityTheory.ThKW.TauSpanIdentities.symplOF_actOF_k C g h x y
theorem psi_rat_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    B.ψ (symplOHF σ JS JT ξ₀ (ratWF x) (ratWF y)) = 1 :=
  _root_.PositivityTheory.ThKW.TauSpanIdentities.psi_rat_k C x y
theorem gamQF_eq_one_iff_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    gamQF σ JS JT ξ₀ B.ψ x y = 1 ↔ ∃ z : ℤ, omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) x) (infRatF (tauB B) y) = z :=
  _root_.PositivityTheory.ThKW.TauSpanIdentities.gamQF_eq_one_iff_k C x y
theorem gamQF_eq_one_iff'_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    gamQF σ JS JT ξ₀ B.ψ x y = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT x y) = n :=
  _root_.PositivityTheory.ThKW.TauSpanIdentities.gamQF_eq_one_iff'_k C x y
theorem span_infRatF_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) :
    Submodule.span ℝ (Set.range (infRatF (nS := nS) (nT := nT) (tauB B))) = ⊤ :=
  _root_.PositivityTheory.ThKW.TauSpanIdentities.span_infRatF_k hB
end PositivityTheory.ThKW
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseHgt
section
set_option synthInstance.maxHeartbeats 200000

section
namespace GlobalTheory.ThK.Dbl
theorem hgtEx_k : _root_.GlobalTheory.ThK.Dbl.HgtEx_k := _root_.GlobalTheory.ThK.Dbl.hgtEx_of_k _root_.GlobalTheory.ThK.Dbl.stab2Cpt_k
end GlobalTheory.ThK.Dbl
end
end

