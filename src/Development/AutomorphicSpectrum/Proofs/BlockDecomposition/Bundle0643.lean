module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0024
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0633
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0634
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0758

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinGluing
section
open Filter Topology Set
open PositivityTheory.Rg.SwEis

namespace GlobalTheory.CompanionTheory.PolyDenominator

theorem exists_pow_mul (B : ℂ → ℂ) (hB : Differentiable ℂ B) (hz : ∃ z, B z ≠ 0) (a : ℂ) :
    ∃ (k : ℕ) (v : ℂ → ℂ), Differentiable ℂ v ∧ v a ≠ 0 ∧ ∀ z, B z = (z - a) ^ k * v z :=
  _root_.UpperTheory.Reformulated.B.GaloisBoundFirst.main B hB hz a

theorem finite_zeros (B : ℂ → ℂ) (hB : Differentiable ℂ B) (hz : ∃ z, B z ≠ 0) {Q : Set ℂ} (hQ : IsCompact Q) :
    {z | z ∈ Q ∧ B z = 0}.Finite := by
  obtain ⟨z₀, hz₀⟩ := hz
  have han : AnalyticOnNhd ℂ B univ := fun x _ => hB.analyticAt x
  by_contra hinf
  have hinf' : ({z | z ∈ Q ∧ B z = 0} : Set ℂ).Infinite := hinf
  obtain ⟨x, hxQ, hacc⟩ := hinf'.exists_accPt_of_subset_isCompact hQ (fun z hz => hz.1)
  have hfreq : ∃ᶠ z in 𝓝[≠] x, B z = 0 :=
    (accPt_iff_frequently_nhdsNE.1 hacc).mono fun z hz => hz.2
  exact hz₀ (han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (mem_univ x) hfreq (mem_univ z₀))

theorem factor_of_finset {Q : Set ℂ} (F : Finset ℂ) :
    ∀ B : ℂ → ℂ, Differentiable ℂ B → (∃ z, B z ≠ 0) → (∀ z ∈ Q, B z = 0 → z ∈ F) →
      ∃ (d : Polynomial ℂ) (u : ℂ → ℂ), d ≠ 0 ∧ Differentiable ℂ u ∧
        (∀ z, B z = d.eval z * u z) ∧ ∀ z ∈ Q, u z ≠ 0 := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro B hB _ hF
    refine ⟨1, B, one_ne_zero, hB, fun z => by simp, fun z hz h0 => ?_⟩
    simpa using hF z hz h0
  | insert a F _ ih =>
    intro B hB hz hF
    obtain ⟨k, v, hv, hva, hBv⟩ := exists_pow_mul B hB hz a
    obtain ⟨d, u, hd, hu, hvu, huQ⟩ := ih v hv ⟨a, hva⟩ (by
      intro z hzQ h0
      have hza : z ≠ a := fun h => hva (h ▸ h0)
      have hBz : B z = 0 := by rw [hBv, h0, mul_zero]
      exact (Finset.mem_insert.1 (hF z hzQ hBz)).resolve_left hza)
    refine ⟨(Polynomial.X - Polynomial.C a) ^ k * d, u,
      mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero a)) hd, hu, fun z => ?_, huQ⟩
    rw [hBv, hvu]
    simp [mul_assoc]

theorem exists_poly_factor (A : ℂ → ℂ) (hA : Differentiable ℂ A) (hz : ∃ z, A z ≠ 0) {Q : Set ℂ} (hQ : IsCompact Q) :
    ∃ (d : Polynomial ℂ) (u : ℂ → ℂ), d ≠ 0 ∧ Differentiable ℂ u ∧
      (∀ z, A z = d.eval z * u z) ∧ ∀ z ∈ Q, u z ≠ 0 :=
  factor_of_finset (finite_zeros A hA hz hQ).toFinset A hA hz fun z hzQ h0 => by simpa using And.intro hzQ h0

theorem glue : Glue := by
  classical
  intro X I _ T e H A R hA hAne hHd hHc hHe hed hec heT s₀
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = min s₀.re R - 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = s₀.im := ⟨_, rfl⟩
  have hQ : IsCompact (Icc a (R + 1) ×ℂ Icc (c - 1) (c + 1)) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨d, u, hd, hu, hAu, huQ⟩ := exists_poly_factor A hA hAne hQ
  let P : Set ℂ := {z | R < z.re}
  let W : Set ℂ := {z | a < z.re ∧ z.re < R + 1 ∧ c - 1 < z.im ∧ z.im < c + 1}
  let U : Set ℂ := P ∪ {z | a < z.re ∧ c - 1 < z.im ∧ z.im < c + 1}
  have hPo : IsOpen P := isOpen_lt continuous_const Complex.continuous_re
  have hWo : IsOpen W :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hUo : IsOpen U := hPo.union
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)))
  have hWQ : ∀ z ∈ W, u z ≠ 0 := fun z hz => huQ z (Complex.mem_reProdIm.2
    ⟨⟨hz.1.le, hz.2.1.le⟩, ⟨hz.2.2.1.le, hz.2.2.2.le⟩⟩)
  have hUPW : ∀ z ∈ U, z ∈ P ∨ z ∈ W := by
    rintro z (h | ⟨h1, h2, h3⟩)
    · exact Or.inl h
    · by_cases h : R < z.re
      · exact Or.inl h
      · exact Or.inr ⟨h1, by linarith [not_lt.1 h], h2, h3⟩
  let E : ℂ → X → ℂ := fun z x => if R < z.re then d.eval z * e z x else H z x / u z
  have hEP : ∀ z, R < z.re → ∀ x, E z x = d.eval z * e z x := fun z h x => by simp [E, h]
  have hEW : ∀ z ∈ W, ∀ x, E z x = H z x / u z := by
    intro z hz x
    by_cases h : R < z.re
    · have h0 := hWQ z hz
      rw [hEP z h, hHe z h, hAu z]
      field_simp
    · simp [E, h]
  have hHT : ∀ i x z, H z (T i x) = H z x := by
    intro i x z
    have h1 : AnalyticOnNhd ℂ (H · (T i x)) univ := fun w _ => (hHd (T i x)).analyticAt w
    have h2 : AnalyticOnNhd ℂ (H · x) univ := fun w _ => (hHd x).analyticAt w
    have hmem : ((R + 1 : ℝ) : ℂ) ∈ P := by simp [P]
    have h3 : (H · (T i x)) =ᶠ[𝓝 ((R + 1 : ℝ) : ℂ)] (H · x) := by
      filter_upwards [hPo.mem_nhds hmem] with w hw
      rw [hHe w hw, hHe w hw, heT]
    exact congrFun (h1.eq_of_eventuallyEq h2 h3) z
  refine ⟨U, d, E, hUo, ⟨⟨R, subset_union_left⟩, ?_⟩, ?_, hd, ?_, ?_, ?_, fun z hz x => hEP z hz x⟩
  · rintro s (h | ⟨h1, h2, h3⟩) t ht
    · left
      simp only [P, mem_setOf_eq, Complex.add_re, Complex.ofReal_re]
      exact lt_add_of_lt_of_nonneg h ht
    · right
      simp only [mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
      exact ⟨lt_add_of_lt_of_nonneg h1 ht, h2, h3⟩
  · by_cases h : R < s₀.re
    · exact Or.inl h
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · have := min_le_left s₀.re R
        rw [ha]; linarith
      · rw [hc]; linarith
      · rw [hc]; linarith
  · intro x z hz
    rcases hUPW z hz with h | h
    · have h1 : DifferentiableAt ℂ (fun w => d.eval w * e w x) z :=
        (d.differentiable z).mul ((hed x z h).differentiableAt (hPo.mem_nhds h))
      refine (h1.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hPo.mem_nhds h] with w hw using hEP w hw x
    · have h1 : DifferentiableAt ℂ (fun w => H w x / u w) z := (hHd x z).div (hu z) (hWQ z h)
      refine (h1.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hWo.mem_nhds h] with w hw using hEW w hw x
  · have hc1 : ContinuousOn (fun y : ℂ × X => d.eval y.1 * e y.1 y.2) (P ×ˢ univ) :=
      (d.continuous.comp continuous_fst).continuousOn.mul hec
    have hc2 : ContinuousOn (fun y : ℂ × X => H y.1 y.2 / u y.1) (W ×ˢ univ) :=
      hHc.continuousOn.div (hu.continuous.comp continuous_fst).continuousOn fun y hy => hWQ y.1 hy.1
    rintro ⟨z, x⟩ ⟨hz, -⟩
    rcases hUPW z hz with h | h
    · have ho : IsOpen (P ×ˢ (univ : Set X)) := hPo.prod isOpen_univ
      have hmem : (z, x) ∈ P ×ˢ (univ : Set X) := ⟨h, mem_univ x⟩
      have : ContinuousOn (fun y : ℂ × X => E y.1 y.2) (P ×ˢ univ) :=
        hc1.congr fun y hy => hEP y.1 hy.1 y.2
      exact (this.continuousAt (ho.mem_nhds hmem)).continuousWithinAt
    · have ho : IsOpen (W ×ˢ (univ : Set X)) := hWo.prod isOpen_univ
      have hmem : (z, x) ∈ W ×ˢ (univ : Set X) := ⟨h, mem_univ x⟩
      have : ContinuousOn (fun y : ℂ × X => E y.1 y.2) (W ×ˢ univ) :=
        hc2.congr fun y hy => hEW y.1 hy.1 y.2
      exact (this.continuousAt (ho.mem_nhds hmem)).continuousWithinAt
  · intro z hz i x
    rcases hUPW z hz with h | h
    · rw [hEP z h, hEP z h, heT]
    · rw [hEW z h, hEW z h, hHT]

end GlobalTheory.CompanionTheory.PolyDenominator
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenMulEqIdem
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.UnitNbhd

open PositivityTheory.RgEis (eSF)

section Gen

variable {R A : Type*} [CommRing R] [Nontrivial R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A]

theorem exists_mul_eq_norm (a : A) : ∃ c, a * c = algebraMap R A (Algebra.norm R a) := by
  classical
  let b := Module.Free.chooseBasis R A
  let M := Algebra.leftMulMatrix b a
  refine ⟨Matrix.toLin b b M.adjugate 1, ?_⟩
  have h1 : Algebra.norm R a = M.det := Algebra.norm_eq_matrix_det b a
  have h2 : Matrix.toLin b b M = LinearMap.mulLeft R a := by
    simp only [M, Algebra.leftMulMatrix_apply, Matrix.toLin_toMatrix]
    rfl
  have h3 : Matrix.toLin b b M (Matrix.toLin b b M.adjugate 1) = Matrix.toLin b b (M * M.adjugate) 1 := by
    rw [Matrix.toLin_mul b b b]; rfl
  have h4 : a * Matrix.toLin b b M.adjugate 1 = Matrix.toLin b b M (Matrix.toLin b b M.adjugate 1) := by
    rw [h2]; rfl
  rw [h4, h3, Matrix.mul_adjugate, h1, map_smul, Matrix.toLin_one, LinearMap.smul_apply, LinearMap.id_apply, Algebra.algebraMap_eq_smul_one]

theorem continuous_norm [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace A] [IsModuleTopology R A] :
    Continuous (fun a : A => Algebra.norm R a) := by
  classical
  let b := Module.Free.chooseBasis R A
  have h : (fun a : A => Algebra.norm R a) = fun a => (Algebra.leftMulMatrix b a).det := by
    funext a; exact Algebra.norm_eq_matrix_det b a
  rw [h]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  have : (fun a : A => Algebra.leftMulMatrix b a i j) = (b.coord i) ∘ₗ (LinearMap.mulRight R (b j)) := by
    funext a
    simp [Algebra.leftMulMatrix_eq_repr_mul]
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap _

end Gen

theorem exists_mul_eq_eSF {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : AF F)
    (h1 : ∀ w, evInf F w n ≠ 0) (h2 : ∀ v ∈ S, evFin F v n ≠ 0) : ∃ m : AF F, n * m = eSF S := by
  classical
  refine ⟨((fun w => (evInf F w n)⁻¹ : Ainf F), ∑ v ∈ S, singleFin v (evFin F v n)⁻¹), ?_⟩
  rw [GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.eSF_eq]
  refine Prod.ext ?_ (af_ext fun u => ?_)
  · funext w
    exact mul_inv_cancel₀ (h1 w)
  · change evalV F u (n.2 * ∑ v ∈ S, singleFin v (evFin F v n)⁻¹) = evalV F u (∑ v ∈ S, singleFin v 1)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.evalV_sum, map_sum]
    split_ifs with h
    · rw [Finset.sum_eq_single_of_mem u h (fun v _ hv => evalV_singleFin_ne (Ne.symm hv) _), evalV_singleFin_self]
      exact mul_inv_cancel₀ (h2 u h)
    · rw [Finset.sum_eq_zero, mul_zero]
      intro v hv
      exact evalV_singleFin_ne (by rintro rfl; exact h hv) _

theorem evInf_eSF {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (w : InfinitePlace F) :
    evInf F w (eSF S) = 1 := by
  rw [GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.eSF_eq]
  rfl

open Classical in
theorem evFin_eSF {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) : evFin F v (eSF S) = if v ∈ S then 1 else 0 := by
  rw [GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.eSF_eq]
  exact GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.evalV_sum S v

theorem compInf_eSF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (w : InfinitePlace F) :
    compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) (eSF S)) = 1 := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  change (Algebra.TensorProduct.map (evInf F w) (AlgHom.id F E)) _ = 1
  rw [Algebra.TensorProduct.map_tmul, show algebraMap (AF F) (AF F) (eSF S) = eSF S from rfl, evInf_eSF]
  simp [Algebra.TensorProduct.one_def]

open Classical in
theorem compFin_eSF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) :
    compFin F E v (algebraMap (AF F) (AF F ⊗[F] E) (eSF S)) = if v ∈ S then 1 else 0 := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  change (Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E)) _ = _
  rw [Algebra.TensorProduct.map_tmul, show algebraMap (AF F) (AF F) (eSF S) = eSF S from rfl, evFin_eSF]
  split_ifs <;> simp [Algebra.TensorProduct.one_def]

theorem eq_algebraMap_eSF
    (hc : ∀ (D : D7) (a : AE D), (∀ w, compInf D.host.F D.host.E w a = 0) → (∀ v, cv D v a = 0) → a = 0)
    (D : D7) (S : Finset (Pl D)) (e : AE D) (he : IsIdem S e) :
    e = algebraMap (AF D.host.F) (AE D) (eSF S) := by
  classical
  rw [← sub_eq_zero]
  refine hc D _ (fun w => ?_) (fun v => ?_)
  · rw [RingHom.map_sub, he.1 w, compInf_eSF, sub_self]
  · refine (RingHom.map_sub _ _ _).trans ?_
    rw [he.2 v]
    refine sub_eq_zero.2 ?_
    exact (compFin_eSF S v).symm

theorem exists_open_mul_eq_idem :
    (∀ (D : D7) (a : AE D), (∀ w, compInf D.host.F D.host.E w a = 0) → (∀ v, cv D v a = 0) → a = 0) →
    ∀ (D : D7) (S : Finset (Pl D)) (e : AE D), IsIdem S e → ∃ U : Set (AE D), IsOpen U ∧ 1 ∈ U ∧ ∀ x ∈ U, ∃ b, x * b = e := by
  intro hc D S e he
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have hn := continuous_norm (R := AF D.host.F) (A := AE D)
  have cI : ∀ w, Continuous (evInf D.host.F w) := fun w => (continuous_apply w).comp continuous_fst
  have cF : ∀ v, Continuous (evFin D.host.F v) := fun v => (RestrictedProduct.continuous_eval v).comp continuous_snd
  refine ⟨{a | (∀ w, evInf D.host.F w (Algebra.norm (AF D.host.F) a) ≠ 0) ∧
    ∀ v ∈ S, evFin D.host.F v (Algebra.norm (AF D.host.F) a) ≠ 0}, ?_, ?_, ?_⟩
  · have h : {a : AE D | (∀ w, evInf D.host.F w (Algebra.norm (AF D.host.F) a) ≠ 0) ∧
        ∀ v ∈ S, evFin D.host.F v (Algebra.norm (AF D.host.F) a) ≠ 0} =
        (⋂ w, {a : AE D | evInf D.host.F w (Algebra.norm (AF D.host.F) a) ≠ 0}) ∩
        ⋂ v ∈ S, {a : AE D | evFin D.host.F v (Algebra.norm (AF D.host.F) a) ≠ 0} := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [h]
    refine (isOpen_iInter_of_finite fun w => ?_).inter (isOpen_biInter_finset fun v _ => ?_)
    · exact isOpen_ne_fun ((cI w).comp hn) continuous_const
    · exact isOpen_ne_fun ((cF v).comp hn) continuous_const
  · simp only [Set.mem_setOf_eq, map_one]
    exact ⟨fun _ => one_ne_zero, fun _ _ => one_ne_zero⟩
  · rintro x ⟨h1, h2⟩
    obtain ⟨c, hxc⟩ := exists_mul_eq_norm (R := AF D.host.F) x
    obtain ⟨m, hm⟩ := exists_mul_eq_eSF S _ h1 h2
    refine ⟨c * algebraMap (AF D.host.F) (AE D) m, ?_⟩
    rw [← mul_assoc, hxc, ← map_mul, hm, eq_algebraMap_eSF hc D S e he]

end GlobalTheory.CompanionTheory.UnitNbhd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiCoefficientOfBound
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CfFJ

open _root_.Metric Set

variable {D : D7} {n ρ p : ℕ}

theorem conj_chz (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) :
    Continuous (fun z : hermA D ρ => conj (chz ψ b₀ z)) ∧ ∀ z : hermA D ρ, ‖conj (chz ψ b₀ z)‖ = 1 := by
  obtain ⟨hc, -⟩ := GlobalTheory.CompanionTheory.CoefWeight.continuous_norm_coefChar D ρ ψ hψ b₀
  have h1 : ∀ z : hermA D ρ, conj (chz ψ b₀ z) =
      ψ (-halfTr (Matrix.trace (HMul.hMul (b₀.1.map (incA D)) z.1 : Mx D ρ ρ))) := by
    intro z
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 _)]
    rfl
  refine ⟨by simpa only [h1] using hc, fun z => ?_⟩
  rw [RCLike.norm_conj]
  exact hψ.2.1 _

theorem cf_eq (d : Polynomial ℂ) (E : ℂ → G D n → ℂ) (s₀ : ℂ) (ε : ℝ) (k : ℕ) (g : G D n) :
    cf d E s₀ ε k g = ∮ w in C(s₀, ε),
      ((2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w)) * E w g := by
  have h : ∀ w : ℂ, ((2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w)) * E w g =
      (2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) * (E w g / d.eval w)) := fun w => by ring
  simp only [h, circleIntegral.integral_const_mul, cf]

theorem ker_eq (d : Polynomial ℂ) (F : ℂ → ℂ) (s₀ : ℂ) (ε : ℝ) (k : ℕ) :
    ∮ w in C(s₀, ε), ((2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w)) * F w =
      (2 * Real.pi * Complex.I)⁻¹ * ∮ w in C(s₀, ε), (w - s₀) ^ (k - 1) * (F w / d.eval w) := by
  have h : ∀ w : ℂ, ((2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w)) * F w =
      (2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) * (F w / d.eval w)) := fun w => by ring
  simp only [h, circleIntegral.integral_const_mul]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem cfFJ_of_pcBound : PcBound → CfFJ := by
  intro hPc D n H φ s₀ U d E σ hC ε hR
  obtain ⟨hε, hB, hroot⟩ := hR
  have hU := hC.isOpen
  have hS : sphere s₀ ε ⊆ U := sphere_subset_closedBall.trans hB
  have hsne : ∀ z ∈ sphere s₀ ε, z ≠ s₀ := by
    rintro z hz rfl
    simp [hε.ne] at hz
  set a : ℕ → ℂ → ℂ := fun k w => (2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w) with ha_def
  have ha : ∀ k, ContinuousOn (a k) (sphere s₀ ε) := fun k =>
    continuousOn_const.mul (((continuousOn_id.sub continuousOn_const).pow _).div
      d.continuous.continuousOn (fun z hz => hroot z (sphere_subset_closedBall hz) (hsne z hz)))
  have hcf : ∀ k g, cf d E s₀ ε k g = ∮ w in C(s₀, ε), a k w * E w g := fun k g => cf_eq d E s₀ ε k g
  refine ⟨fun k => ⟨?_, ?_⟩, ⟨d.rootMultiplicity s₀ + 1, fun k hk => funext fun g => ?_⟩, ?_⟩
  · have : cf d E s₀ ε k = fun g => ∮ w in C(s₀, ε), a k w * E w g := funext (hcf k)
    rw [this]
    exact circle_cont hC.cont hε.le hS (ha k)
  · intro γ hγ g
    rw [hcf, hcf]
    exact circleIntegral.integral_congr hε.le fun w hw => by
      simp only [hC.inv w (hS hw) γ hγ g]
  · have h0 := circle_zero hU (hC.hol g) hC.ne hε hB hroot (j := k - 1) (by omega)
    simp only [cf, h0, mul_zero, Pi.zero_apply]
  · intro ρ p hn M m ψ hψ b₀ g η hη
    obtain ⟨-, hcov⟩ := hPc D n ρ p hn M m ψ hψ b₀
    obtain ⟨C, hCc, hcover, -⟩ := hcov g
    obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D ρ p
    haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
    haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
    haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
    haveI : FirstCountableTopology (Mx D ρ p) := inferInstance
    haveI : FirstCountableTopology (Mx D ρ p × Mx D ρ p) := inferInstance
    obtain ⟨hμh, -, hμ1⟩ := m.hμ
    obtain ⟨-, -, hl1⟩ := m.hz
    haveI : SFinite m.μ := inferInstance
    haveI : IsFiniteMeasure (m.lz.restrict m.𝓖) := ⟨by rw [Measure.restrict_apply_univ, hl1]; exact ENNReal.one_lt_top⟩
    haveI : IsFiniteMeasure (m.μ.restrict m.𝓕) := ⟨by rw [Measure.restrict_apply_univ, hμ1]; exact ENNReal.one_lt_top⟩
    obtain ⟨hχc, hχ1⟩ := conj_chz ψ hψ b₀
    have hκ1 : Integrable (fun z : hermA D ρ => conj (chz ψ b₀ z)) (m.lz.restrict m.𝓖) :=
      Integrable.of_bound hχc.aestronglyMeasurable 1 (Eventually.of_forall fun z => (hχ1 z).le)
    have hκ2 : Integrable (fun _ : Mx D ρ p => (1 : ℂ)) (m.μ.restrict m.𝓕) := integrable_const _
    have hκ3 : Integrable (fun y => conj (η y)) m.μ :=
      Complex.conjCLE.toContinuousLinearMap.integrable_comp hη
    set pt : (Mx D ρ p × Mx D ρ p) × hermA D ρ → G D n :=
      fun u => M.nzx u.2 0 * (M.nzx 0 u.1.2 * (M.sh u.1.1 * g)) with hpt_def
    have hpt : Continuous pt :=
      (M.nzx_cont.comp (f := fun u : (Mx D ρ p × Mx D ρ p) × hermA D ρ => (u.2, (0 : Mx D ρ p))) (by fun_prop)).mul
        ((M.nzx_cont.comp (f := fun u : (Mx D ρ p × Mx D ρ p) × hermA D ρ => ((0 : hermA D ρ), u.1.2)) (by fun_prop)).mul
          ((M.sh_cont.comp (f := fun u : (Mx D ρ p × Mx D ρ p) × hermA D ρ => u.1.1) (by fun_prop)).mul continuous_const))
    have h0 : Fam U (fun w u => E w (pt u)) := by
      refine ⟨hC.cont.comp (continuous_fst.prodMk (hpt.comp continuous_snd)).continuousOn
        (fun q hq => ⟨hq.1, mem_univ _⟩), fun u => hC.hol _, fun K hK hKc => ?_⟩
      obtain ⟨B, hBd⟩ := (hKc.prod hCc).exists_bound_of_continuousOn
        (hC.cont.mono (prod_mono hK (subset_univ _)))
      refine ⟨B, fun w hw u => ?_⟩
      obtain ⟨γ, hγ, hmem⟩ := hcover u.2 u.1.2 u.1.1
      rw [show E w (pt u) = E w (γ * pt u) from (hC.inv w (hK hw) γ hγ _).symm]
      exact hBd (w, γ * pt u) ⟨hw, hmem⟩
    have h1 : Fam U (fun w (u : Mx D ρ p × Mx D ρ p) => zc M m ψ b₀ (E w) (M.nzx 0 u.2 * (M.sh u.1 * g))) :=
      h0.stage hU hκ1
    have h2 : Fam U (fun w (y : Mx D ρ p) => pc M m ψ b₀ (E w) (M.sh y * g)) := by
      have := h1.stage hU hκ2
      simp only [mul_one] at this
      exact this
    have h3 : Fam U (fun w (_ : Unit) => FJ M m ψ b₀ (E w) g η) :=
      (h2.comp (φ := fun u : Unit × Mx D ρ p => u.2) continuous_snd).stage hU hκ3
    refine ⟨h3.hol (), fun k => ?_⟩
    have e1 : ∀ y x, zc M m ψ b₀ (cf d E s₀ ε k) (M.nzx 0 x * (M.sh y * g)) =
        ∮ w in C(s₀, ε), a k w * zc M m ψ b₀ (E w) (M.nzx 0 x * (M.sh y * g)) := by
      intro y x
      have := (h0.comp (φ := fun z : hermA D ρ => ((y, x), z)) (by fun_prop)).swap hκ1 hε hS (ha k)
      simp only [zc, hcf, pt] at this ⊢
      exact this
    have e2 : ∀ y, pc M m ψ b₀ (cf d E s₀ ε k) (M.sh y * g) =
        ∮ w in C(s₀, ε), a k w * pc M m ψ b₀ (E w) (M.sh y * g) := by
      intro y
      have := (h1.comp (φ := fun x : Mx D ρ p => (y, x)) (by fun_prop)).swap hκ2 hε hS (ha k)
      simp only [mul_one] at this
      simp only [PositivityTheory.Rg.Rsw.pc, e1]
      exact this
    have e3 : FJ M m ψ b₀ (cf d E s₀ ε k) g η = ∮ w in C(s₀, ε), a k w * FJ M m ψ b₀ (E w) g η := by
      have := h2.swap hκ3 hε hS (ha k)
      simp only [FJ, e2]
      exact this
    rw [e3]
    exact ker_eq d _ s₀ ε k

end GlobalTheory.CompanionTheory.CfFJ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisExtra
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinActS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def sf {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, LF a b w) : ∀ i : Slot S, LF a b i.pl
  | .inl w => φ₁ w.1
  | .inr w => φ₂ w.1

end GlobalTheory.CompanionTheory.FinActS

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfimumOfEquality
section
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem infOfEq_holds : InfOfEq := by
  intro E _ _ _ N t ψ m τ m' hT hI hψ h0 hC
  have hS := hT E N t τ m' hI
  refine GlobalTheory.IsobaricOfPublished.multiset_eq_of_prod_map_add fun u => ?_
  exact smul_left_injective ℂ h0 ((hS.2 u ψ hψ).symm.trans (hC τ u))

end GlobalTheory.CompanionTheory.EGlue
end

