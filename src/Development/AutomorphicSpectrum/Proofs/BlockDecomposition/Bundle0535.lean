module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0521
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0436
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0437
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0509
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwistedDoubleCosets
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocHypSplit

theorem finite_of_subset_mul {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (T K' : Subgroup G)
    (hK' : IsOpen (K' : Set G)) (D : Set G) (hD : IsCompact D)
    (P : G → Prop) (hP : ∀ x, P x → ∃ t ∈ T, ∃ d ∈ D, x = t * d) :
    {q : DoubleCoset.Quotient (T : Set G) (K' : Set G) | P (Quotient.out q)}.Finite := by
  obtain ⟨s, hs⟩ := compact_covered_by_mul_left_translates hD
    (show (interior (K' : Set G)).Nonempty from ⟨1, hK'.interior_eq.symm ▸ K'.one_mem⟩)
  refine (s.finite_toSet.image fun g => DoubleCoset.mk T K' g⁻¹).subset ?_
  intro q hq
  obtain ⟨t, ht, d, hd, hx⟩ := hP _ hq
  have := hs hd
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
  obtain ⟨g, hg, hgd⟩ := this
  refine ⟨g, hg, ?_⟩
  rw [← DoubleCoset.out_eq' q, DoubleCoset.eq]
  exact ⟨t, ht, g * d, hgd, by simp [hx, mul_assoc]⟩


open scoped Pointwise in
theorem finite_doubleCosets_split : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (σ : H →* H) (K : Subgroup H) (d d' : H) (f : H × H → ℂ)
  (C₁ C₂ : Set H), Continuous σ → (∀ g, σ (σ g) = g) → IsOpen (K : Set H) → IsCompact (K : Set H) → (∀ k ∈ K, σ k ∈ K) →
  IsCompact C₁ → IsCompact C₂ → (∀ y, f y ≠ 0 → y.1 ∈ C₁ ∧ y.2 ∈ C₂) →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  {q : DoubleCoset.Quotient (twCent (swTw σ) (d, d') : Set (H × H)) (K.prod K : Set (H × H)) |
    ∃ k ∈ K.prod K, f ((Quotient.out q * k)⁻¹ * (d, d') * swTw σ (Quotient.out q * k)) ≠ 0}.Finite := by
  intro H _ _ _ σ K d d' f C₁ C₂ hσc hσ hKo hKc _ hC₁ hC₂ hf hfin
  open scoped Pointwise in
  have hC : IsCompact (C₁ * σ '' C₂) := hC₁.mul (hC₂.image hσc)
  have hSf := hfin _ hC
  set S := {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C₁ * σ '' C₂} with hS
  have hR : IsCompact ((fun q => Quotient.out q) '' S : Set H) := (hSf.image _).isCompact
  set A : Set H := ((fun q => Quotient.out q) '' S : Set H) * (K : Set H) with hAdef
  have hA : IsCompact A := hR.mul hKc
  set B : Set H := σ '' ((fun a => d⁻¹ * a) '' A * C₁) with hBdef
  have hB : IsCompact B := ((hA.image (continuous_const.mul continuous_id)).mul hC₁).image hσc
  have hKKo : IsOpen ((K.prod K : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hKo.prod hKo
  have hKKc : IsCompact ((K.prod K : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hKc.prod hKc
  have hD : IsCompact ((fun p : (H × H) × (H × H) => p.1 * p.2⁻¹) ''
      ((A ×ˢ B) ×ˢ ((K.prod K : Subgroup (H × H)) : Set (H × H)))) :=
    ((hA.prod hB).prod hKKc).image (continuous_fst.mul continuous_snd.inv)
  have key : ∀ y₁ y₂ : H, y₁⁻¹ * d * σ y₂ ∈ C₁ → y₂⁻¹ * d' * σ y₁ ∈ C₂ →
      ∃ t ∈ twCent (swTw σ) (d, d'), ∃ a ∈ A, ∃ b ∈ B, ((y₁, y₂) : H × H) = t * (a, b) := by
    intro y₁ y₂ h₁ h₂
    have hN : y₁⁻¹ * (d * σ d') * y₁ ∈ C₁ * σ '' C₂ := by
      refine Set.mem_mul.2 ⟨_, h₁, _, ⟨_, h₂, rfl⟩, ?_⟩
      simp only [map_mul, map_inv, hσ]
      group
    obtain ⟨h, hh, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id H) (d * σ d')) K y₁
    have ez : Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id H) (d * σ d')) K y₁) * k⁻¹ = h * y₁ := by
      rw [e, mul_inv_cancel_right]
    have hh' : h * (d * σ d') = d * σ d' * h := hh
    have hq : DoubleCoset.mk (twCent (MonoidHom.id H) (d * σ d')) K y₁ ∈ S := by
      refine ⟨k⁻¹, inv_mem hk, ?_⟩
      rw [ez, MonoidHom.id_apply]
      have : (h * y₁)⁻¹ * (d * σ d') * (h * y₁) = y₁⁻¹ * (d * σ d') * y₁ := by
        rw [_root_.mul_inv_rev, mul_assoc, ← mul_assoc (d * σ d') h y₁, ← hh']
        group
      rw [this]; exact hN
    have hw : h * y₁ ∈ A := by
      rw [← ez]
      exact Set.mem_mul.2 ⟨_, ⟨_, hq, rfl⟩, _, inv_mem hk, rfl⟩
    have ht := (mem_twCent_swTw σ hσ d d' (h⁻¹, d' * σ h⁻¹ * d'⁻¹)).2 ⟨inv_mem hh, rfl⟩
    set t₂ := d' * σ h⁻¹ * d'⁻¹ with ht₂
    have e₁ : h⁻¹ * d = d * σ t₂ := congrArg Prod.fst ht
    have e₂ : d⁻¹ * h * d = (σ t₂)⁻¹ := by
      have : σ t₂ = d⁻¹ * (h⁻¹ * d) := by rw [e₁]; group
      rw [this]; group
    refine ⟨(h⁻¹, t₂), ht, h * y₁, hw, t₂⁻¹ * y₂,
      ⟨(d⁻¹ * (h * y₁)) * (y₁⁻¹ * d * σ y₂), Set.mem_mul.2 ⟨_, ⟨_, hw, rfl⟩, _, h₁, rfl⟩, ?_⟩, ?_⟩
    · have : d⁻¹ * (h * y₁) * (y₁⁻¹ * d * σ y₂) = (d⁻¹ * h * d) * σ y₂ := by group
      rw [this, e₂, map_mul, map_inv, hσ, hσ]
    · ext <;> simp
  refine finite_of_subset_mul (twCent (swTw σ) (d, d')) (K.prod K) hKKo _ hD
    (fun x => ∃ k ∈ K.prod K, f ((x * k)⁻¹ * (d, d') * swTw σ (x * k)) ≠ 0) ?_
  rintro x ⟨k, hk, hx⟩
  obtain ⟨t, ht, a, ha, b, hb, e⟩ := key (x * k).1 (x * k).2 (hf _ hx).1 (hf _ hx).2
  have e' : x * k = t * (a, b) := e
  refine ⟨t, ht, (a, b) * k⁻¹, ⟨(((a, b)), k), ⟨⟨ha, hb⟩, hk⟩, rfl⟩, ?_⟩
  rw [← mul_assoc, ← e', mul_inv_cancel_right]

end GlobalTheory.CompanionTheory.LocHypSplit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteZSpanIntegralRepresentation
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep.GrowthKernel

open GroundTheory.Global GroundTheory.Automorphic.Reduction AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth GlobalTheory.CompanionTheory.HCRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_aeval_lapOp_eq_zero_of_finite (φ : Sm E a)
    (hk : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)))
    (hz : FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)))
    {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (horth : ∀ i j, archTraceForm E a (b i) (b j) = if i = j then ε i else 0)
    (hskew : ∀ i, ε i = -1 → b i ∈ archSkew E a) :
    ∃ P : Polynomial ℂ, P.Monic ∧ 0 < P.natDegree ∧ Polynomial.aeval (lapOp (⇑b)) P φ = 0 := by
  classical
  set Ω := omegaOp (E := E) (a := a) (⇑b) ε with hΩ
  set W := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) with hWdef
  haveI : FiniteDimensional ℂ W := hk
  have hZ : Ω ∈ Zalg E a := by
    rw [hΩ, GlobalTheory.T.omega_operator_eq_casimir_sum E a d b ε hε horth]
    refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun w _ => Subalgebra.add_mem _ ?_ ?_) _
    · exact GlobalTheory.T.casimir_mem_center_enveloping E a _
    · exact GlobalTheory.T.casimir_mem_center_enveloping E a _
  set Vz := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hVz
  haveI : FiniteDimensional ℂ Vz := hz
  have hVs : ∀ w ∈ Vz, Ω w ∈ Vz := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => Ω w ∈ Vz) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨z, hz, rfl⟩
      exact Submodule.subset_span ⟨Ω * z, Subalgebra.mul_mem _ hZ hz, rfl⟩
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ c hx
  have hφV : φ ∈ Vz := Submodule.subset_span ⟨1, Subalgebra.one_mem _, rfl⟩
  obtain ⟨q, hqm, -, hq⟩ := AutomorphicForm.exists_monic_aeval_apply_eq_zero Ω Vz hVs hφV
  have hqW : ∀ w ∈ W, Polynomial.aeval Ω q w = 0 := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => Polynomial.aeval Ω q w = 0) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k, rfl⟩
      have hcomm : ∀ m, cptRep E a k (Ω m) = Ω (cptRep E a k m) := fun m =>
        (congrArg (fun T : Module.End ℂ (Sm E a) => T m)
          (GlobalTheory.T.omega_operator_commutes_infinite_gl E a d b ε hε horth (Unitary.toUnits k))).symm
      have := AutomorphicForm.map_aeval_apply_of_intertwine (cptRep E a k) hcomm q φ
      rw [hq, map_zero] at this
      exact this.symm
    · rw [map_zero]
    · intro x y _ _ hx hy; rw [map_add (f := _), hx, hy, add_zero]
    · intro c x _ hx; rw [map_smul, hx, smul_zero]
  have hlap : Commute Ω (lapOp (⇑b)) := by
    simp only [lapOp, Commute, SemiconjBy]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : Ω * liB (b i) = liB (b i) * Ω := omegaOp_comm_liB b ε hε horth (b i)
    rw [← mul_assoc, h1, mul_assoc, h1, mul_assoc]
  have hTW : ∀ w ∈ W, (lapOp (⇑b) - Ω) w ∈ W := by
    intro w hw
    have e : (lapOp (E := E) (a := a) (⇑b) - Ω) w =
        ∑ i, ((1 : ℂ) - (ε i : ℂ)) • liB (b i) (liB (b i) w) := by
      simp only [hΩ, lapOp, omegaOp, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        Module.End.mul_apply]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      module
    rw [e]
    refine Submodule.sum_mem _ fun i _ => ?_
    rcases hε i with h | h
    · simp [h]
    · refine W.smul_mem _ ?_
      have hs := mem_archSkew.1 (hskew i h)
      exact _root_.GlobalTheory.CompanionTheory.HCRep.liB_skew_mem_span E a φ (b i) hs hk _ (_root_.GlobalTheory.CompanionTheory.HCRep.liB_skew_mem_span E a φ (b i) hs hk _ hw)
  have hφW : φ ∈ W := by
    refine Submodule.subset_span ⟨1, ?_⟩
    change cptRep E a 1 φ = φ
    rw [map_one]
    rfl
  have hc : Commute Ω (lapOp (⇑b) - Ω) := by
    refine LinearMap.ext fun x => ?_
    have h2 := LinearMap.congr_fun hlap.eq x
    simp only [Module.End.mul_apply] at h2 ⊢
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, h2]
  have hsum : Ω + (lapOp (⇑b) - Ω) = lapOp (⇑b) := LinearMap.ext fun x => by simp
  obtain ⟨P, hP1, hP2, hP3⟩ := exists_monic_aeval_add Ω (lapOp (⇑b) - Ω) hc W hTW q hqm hqW hφW
  refine ⟨P, hP1, hP2, ?_⟩
  rwa [hsum] at hP3

theorem exists_kernel_of_finite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) →
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) →
    ∀ [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)]
      (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure],
      ∃ κ : AutomorphicForm.archGroup E a → ℂ, Continuous κ ∧ HasCompactSupport κ ∧
        ∀ g : GA E a, φ.1 g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * κ y ∂ν := by
  intro E _ _ _ a φ hk hz _ _ ν _
  obtain ⟨d, b, ε, hε, horth, hskew⟩ := exists_archCartanBasis (K := E) (n := a)
  obtain ⟨P, hm, hd, hP⟩ := exists_aeval_lapOp_eq_zero_of_finite φ hk hz b ε hε horth hskew
  obtain ⟨κ, hκs, hκc, -, hκ⟩ := (isExpLieAlgebra E a).exists_kernel_eq_conv_of_aeval_laplacian ν b P
    hm hd Filter.univ_mem
  refine ⟨κ, IsExpLieAlgebra.continuous_of_isSmoothFun hκs, hκc, fun g => ?_⟩
  have h1 := hκ (sliceL g (smL E a φ)) (by rw [← sliceL_aeval_lapOp, hP, map_zero, map_zero]) 1
  simpa [archSlice_apply, smL] using h1

end GlobalTheory.CompanionTheory.HCRep.GrowthKernel

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameCompletes
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FrameComplete

open Matrix

section Abstract

variable {A : Type*} [CommRing A] [StarRing A] {ι α β ρ τ : Type*}
  [Fintype ι] [Fintype α] [Fintype β] [Fintype ρ] [Fintype τ]
  [DecidableEq ι] [DecidableEq ρ] [DecidableEq τ]

theorem gram_conj {G : Matrix ι ι A} (hG : Gᴴ = G) (M : Matrix ι α A) (N : Matrix ι β A) :
    (Mᴴ * (G * N))ᴴ = Nᴴ * (G * M) := by
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, Matrix.mul_assoc]

theorem orth_part {G : Matrix ι ι A} (hG : Gᴴ = G) {B Bi : Matrix ρ ρ A} (hB : B * Bi = 1)
    {e : A} {x : Matrix ι ρ A} {v : Matrix ι τ A} (hv : e • v = v)
    (hxx : xᴴ * (G * x) = e • B)
    (hq : vᴴ * (G * v) - (Bi * (xᴴ * (G * v)))ᴴ * (B * (Bi * (xᴴ * (G * v)))) = 0) :
    xᴴ * (G * (v - x * (Bi * (xᴴ * (G * v))))) = 0 ∧
      (v - x * (Bi * (xᴴ * (G * v))))ᴴ * (G * (v - x * (Bi * (xᴴ * (G * v))))) = 0 := by
  set c := xᴴ * (G * v) with hc
  set y := Bi * c with hy
  have hec : e • c = c := by
    conv_lhs => rw [hc, ← Matrix.mul_smul, ← Matrix.mul_smul, hv]
  have hBy : B * y = c := by rw [hy, ← Matrix.mul_assoc, hB, Matrix.one_mul]
  have h1 : xᴴ * (G * (v - x * y)) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, ← hc, ← Matrix.mul_assoc G, ← Matrix.mul_assoc, hxx,
      Matrix.smul_mul, hBy, hec, sub_self]
  refine ⟨h1, ?_⟩
  have h2 : (v - x * y)ᴴ * (G * x) = 0 := by
    rw [← gram_conj hG, h1, conjTranspose_zero]
  have h3 : (v - x * y)ᴴ * (G * v) = vᴴ * (G * v) - yᴴ * c := by
    rw [conjTranspose_sub, Matrix.sub_mul, conjTranspose_mul, Matrix.mul_assoc, ← hc]
  rw [Matrix.mul_sub, Matrix.mul_sub, h3, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * x), h2,
    Matrix.zero_mul, sub_zero, ← hBy]
  exact hq

theorem exists_dual {G Gi : Matrix ι ι A} (hG : Gᴴ = G) (hGi : G * Gi = 1)
    {e h : A} (he : e * e = e) (hse : star e = e) (hh : h + h = 1) (hsh : star h = h)
    {x : Matrix ι ρ A} {u : Matrix ι τ A} {L : Matrix τ ι A} (hu : e • u = u)
    (hxu : xᴴ * (G * u) = 0) (huu : uᴴ * (G * u) = 0) (hLx : L * x = 0) (hLu : L * u = e • 1) :
    ∃ w : Matrix ι τ A, e • w = w ∧ xᴴ * (G * w) = 0 ∧ uᴴ * (G * w) = e • 1 ∧ wᴴ * (G * w) = 0 := by
  set w₀ : Matrix ι τ A := Gi * (e • L)ᴴ with hw₀
  have hGw : G * w₀ = (e • L)ᴴ := by rw [hw₀, ← Matrix.mul_assoc, hGi, Matrix.one_mul]
  have hew : e • w₀ = w₀ := by
    rw [hw₀, ← Matrix.mul_smul, conjTranspose_smul, hse, smul_smul, he]
  have h1 : xᴴ * (G * w₀) = 0 := by
    rw [hGw, ← conjTranspose_mul, Matrix.smul_mul, hLx, smul_zero, conjTranspose_zero]
  have h2 : uᴴ * (G * w₀) = e • 1 := by
    rw [hGw, ← conjTranspose_mul, Matrix.smul_mul, hLu, smul_smul, he, conjTranspose_smul, hse,
      conjTranspose_one]
  have h3 : w₀ᴴ * (G * u) = e • 1 := by
    rw [← gram_conj hG, h2, conjTranspose_smul, hse, conjTranspose_one]
  set Q := w₀ᴴ * (G * w₀) with hQ
  have hQh : Qᴴ = Q := gram_conj hG w₀ w₀
  have heQ : e • Q = Q := by
    conv_lhs => rw [hQ, ← Matrix.mul_smul, ← Matrix.mul_smul, hew]
  have hP : (h • Q)ᴴ = h • Q := by rw [conjTranspose_smul, hsh, hQh]
  have hw : e • (w₀ - u * (h • Q)) = w₀ - u * (h • Q) := by
    rw [smul_sub, hew, ← Matrix.smul_mul, hu]
  have hxw : xᴴ * (G * (w₀ - u * (h • Q))) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, h1, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * u), hxu,
      Matrix.zero_mul, sub_zero]
  have huw : uᴴ * (G * (w₀ - u * (h • Q))) = e • 1 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, h2, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * u), huu,
      Matrix.zero_mul, sub_zero]
  refine ⟨w₀ - u * (h • Q), hw, hxw, huw, ?_⟩
  have h4 : w₀ᴴ * (G * (w₀ - u * (h • Q))) = Q - h • Q := by
    rw [Matrix.mul_sub, Matrix.mul_sub, ← hQ, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * u), h3,
      Matrix.smul_mul, Matrix.one_mul, smul_comm, heQ]
  rw [conjTranspose_sub, Matrix.sub_mul, h4, conjTranspose_mul, hP, Matrix.mul_assoc, huw,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, heQ, sub_sub, ← add_smul, hh, one_smul, sub_self]

theorem gram_three {G : Matrix ι ι A} {κ₁ κ₂ κ₃ : Type*} [Fintype κ₁] [Fintype κ₂] [Fintype κ₃]
    (x : Matrix ι κ₁ A) (u : Matrix ι κ₂ A) (w : Matrix ι κ₃ A) :
    (fromCols (fromCols x u) w)ᴴ * (G * fromCols (fromCols x u) w) =
      fromBlocks (fromBlocks (xᴴ * (G * x)) (xᴴ * (G * u)) (uᴴ * (G * x)) (uᴴ * (G * u)))
        (fromRows (xᴴ * (G * w)) (uᴴ * (G * w)))
        (fromCols (wᴴ * (G * x)) (wᴴ * (G * u))) (wᴴ * (G * w)) := by
  ext (( i | i) | i) ((j | j) | j) <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, conjTranspose_apply]

end Abstract

def gam {K ρ τ : Type*} [Zero K] [One K] [DecidableEq τ] (b : Matrix ρ ρ K) :
    Matrix ((ρ ⊕ τ) ⊕ τ) ((ρ ⊕ τ) ⊕ τ) K :=
  fromBlocks (fromBlocks b 0 0 0) (fromRows 0 1) (fromCols 0 1) 0

theorem gam_map {K L ρ τ : Type*} [Semiring K] [Semiring L] [DecidableEq τ] (f : K →+* L)
    (b : Matrix ρ ρ K) : (gam (τ := τ) b).map f = gam (b.map f) := by
  ext ((i | i) | i) ((j | j) | j) <;> simp [gam, Matrix.one_apply, apply_ite f]

theorem gam_det {K : Type*} [Field K] {r t : ℕ} (b : Matrix (Fin r) (Fin r) K) (hb : b.det ≠ 0) :
    (gam (τ := Fin t) b).det ≠ 0 := by
  have hinv : ∀ i j, ∑ a, b⁻¹ i a * b a j = if i = j then 1 else 0 := fun i j => by
    have := congrFun (congrFun (Matrix.nonsing_inv_mul b (isUnit_iff_ne_zero.2 hb)) i) j
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  refine Matrix.det_ne_zero_of_left_inverse (B := gam (τ := Fin t) b⁻¹) ?_
  ext ((i | i) | i) ((j | j) | j) <;>
    simp [gam, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, hinv]

section Involution

variable {A : Type} [CommRing A] {ι ρ τ : Type} [Fintype ι] [Fintype ρ] [Fintype τ]
  [DecidableEq ι] [DecidableEq ρ] [DecidableEq τ]

theorem complete_frame (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) {G Gi : Matrix ι ι A}
    (hG : (G.map σ)ᵀ = G) (hGi : G * Gi = 1) {B Bi : Matrix ρ ρ A} (hB : B * Bi = 1)
    {e h : A} (he : e * e = e) (hse : σ e = e) (hh : h + h = 1) (hsh : σ h = h)
    {x : Matrix ι ρ A} {v : Matrix ι τ A} {L : Matrix τ ι A} (hx : e • x = x) (hv : e • v = v)
    (hxx : (x.map σ)ᵀ * (G * x) = e • B)
    (hq : (v.map σ)ᵀ * (G * v) - ((Bi * ((x.map σ)ᵀ * (G * v))).map σ)ᵀ *
      (B * (Bi * ((x.map σ)ᵀ * (G * v)))) = 0)
    (hLx : L * x = 0) (hLv : L * v = e • 1) :
    ∃ N : Matrix ι ((ρ ⊕ τ) ⊕ τ) A, e • N = N ∧ (N.map σ)ᵀ * (G * N) = e • gam B ∧
      (∀ i j, N i (Sum.inl (Sum.inl j)) = x i j) ∧
      ∀ i j, N i (Sum.inl (Sum.inr j)) = (v - x * (Bi * ((x.map σ)ᵀ * (G * v)))) i j := by
  letI : StarRing A :=
    { star := σ
      star_involutive := hσ
      star_mul := fun a b => by rw [map_mul, mul_comm]
      star_add := map_add σ }
  have hmap : ∀ {α β : Type} (M : Matrix α β A), (M.map σ)ᵀ = Mᴴ := fun M => by
    ext i j; rfl
  simp only [hmap] at hG hxx hq ⊢
  obtain ⟨hxu, huu⟩ := orth_part hG hB hv hxx hq
  set u : Matrix ι τ A := v - x * (Bi * (xᴴ * (G * v))) with hu
  have heu : e • u = u := by
    have hy : e • (x * (Bi * (xᴴ * (G * v)))) = x * (Bi * (xᴴ * (G * v))) := by
      rw [← Matrix.smul_mul, hx]
    rw [hu, smul_sub, hv, hy]
  have hLu : L * u = e • 1 := by
    rw [hu, Matrix.mul_sub, hLv, ← Matrix.mul_assoc, hLx, Matrix.zero_mul, sub_zero]
  obtain ⟨w, hew, hxw, huw, hww⟩ :=
    exists_dual hG hGi he (show star e = e from hse) hh (show star h = h from hsh) heu hxu huu hLx hLu
  refine ⟨fromCols (fromCols x u) w, ?_, ?_, fun i j => rfl, fun i j => rfl⟩
  · ext i ((j | j) | j)
    · simpa using congrFun (congrFun hx i) j
    · simpa using congrFun (congrFun heu i) j
    · simpa using congrFun (congrFun hew i) j
  · have hux : uᴴ * (G * x) = 0 := by rw [← gram_conj hG, hxu, conjTranspose_zero]
    have hwx : wᴴ * (G * x) = 0 := by rw [← gram_conj hG, hxw, conjTranspose_zero]
    have hwu : wᴴ * (G * u) = e • 1 := by
      rw [← gram_conj hG, huw, conjTranspose_smul, conjTranspose_one]
      exact congrArg (· • (1 : Matrix τ τ A)) hse
    rw [gram_three, hxx, hxu, huu, hxw, huw, hww, hux, hwx, hwu]
    ext ((i | i) | i) ((j | j) | j) <;> simp [gam, Matrix.one_apply]

end Involution

theorem frame_completes : ∀ (D : D7) (r t : ℕ) (V : HSp D) (b₀ : HermE D r), b₀.1.det ≠ 0 → ∀ e : AE D, e * e = e → cA D e = e → ∃ Γ : Matrix ((Fin r ⊕ Fin t) ⊕ Fin t) ((Fin r ⊕ Fin t) ⊕ Fin t) D.host.E, Γ.det ≠ 0 ∧ ∀ z : Mx D V.rank r × Mx D V.rank t, Free e z → (e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0) → ∃ N : Matrix (Fin V.rank) ((Fin r ⊕ Fin t) ⊕ Fin t) (AE D), e • N = N ∧ (HMul.hMul (N.map (cA D))ᵀ (HMul.hMul (gA V) N : Matrix (Fin V.rank) ((Fin r ⊕ Fin t) ⊕ Fin t) (AE D)) : Matrix ((Fin r ⊕ Fin t) ⊕ Fin t) ((Fin r ⊕ Fin t) ⊕ Fin t) (AE D)) = e • Γ.map (incA D) ∧ (∀ i j, N i (Sum.inl (Sum.inl j)) = z.1 i j) ∧ ∀ i j, N i (Sum.inl (Sum.inr j)) = (z.2 - mm z.1 (yv V b₀ z)) i j := by
  intro D r t V b₀ hb e he hse
  refine ⟨gam b₀.1, gam_det _ hb, ?_⟩
  rintro ⟨x, v⟩ ⟨L₁, L₂, -, -, h21, h22⟩ ⟨hx, hv, hxx, hq⟩
  have hdet : IsUnit (HSpace.gram V).det := isUnit_iff_ne_zero.2 (isHermND_gram V).2
  have hGi : gA V * giA V = 1 := by
    have := rat_mul (D := D) (HSpace.gram V) (HSpace.gram V)⁻¹
    rw [Matrix.mul_nonsing_inv _ hdet] at this
    exact this.symm.trans (by simp [rat])
  have hB : rat (D := D) b₀.1 * rat b₀.1⁻¹ = 1 := by
    have := rat_mul (D := D) b₀.1 b₀.1⁻¹
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hb)] at this
    exact this.symm.trans (by simp [rat])
  have hh : incA D 2⁻¹ + incA D 2⁻¹ = 1 := by
    rw [← map_add (f := _), ← two_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have hsh : cA D (incA D 2⁻¹) = incA D 2⁻¹ := by
    rw [GlobalTheory.DualPairCheck.cA_incA, star_inv₀, star_ofNat]
  obtain ⟨N, h1, h2, h3, h4⟩ := complete_frame (cA D) cA_cA (G := gA V) (Gi := giA V) (adj_gA V) hGi
    hB he hse hh hsh (x := x) (v := v) (L := L₂) hx hv hxx hq h21 h22
  refine ⟨N, h1, ?_, h3, h4⟩
  rw [gam_map]
  exact h2

end GlobalTheory.CompanionTheory.FrameComplete
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCell
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory _root_.Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

def vH {K : Type} {M : ℕ} (a s : K) (Y : Fin M → K) : Fin (M + 2) → K :=
  Fin.cons a (Fin.cons s Y)

def tailH {K : Type} {M : ℕ} (x : Fin (M + 2) → K) : Fin M → K := fun i => x i.succ.succ

section Chart

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def halfR : R ⊗[F] E := inclR R (algebraMap F E (1 / 2))

def tHalf (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin (M + 2) → R ⊗[F] E) : R ⊗[F] E :=
  halfR (F := F) (E := E) R * hR R σ (hypOne J) x x

def cvec (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x v : Fin (M + 2) → R ⊗[F] E) :
    Fin (M + 2) → R ⊗[F] E :=
  vH (x 0 * v 0)
    (v 0 * x 1 + Ring.inverse (sigR R σ (x 0)) *
      (v 1 - tHalf R σ J x * v 0 - hR R σ J (tailH x) (tailH v)))
    (fun i => v 0 * x i.succ.succ + v i.succ.succ)

def chartS (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin (M + 2) → R ⊗[F] E)
    (a s : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E) : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E :=
  Fin.cons (x 0) fun j => cvec R σ J (x 0) (vH (a 0 j) (s 0 j - tHalf R σ J (x 0) * a 0 j) (Y j))


variable {R} in
def yPart {K : Type} [CommRing K] {M n : ℕ} (X : Fin (n + 1) → Fin (M + 2) → K) : Fin n → Fin M → K :=
  fun j i => X j.succ i.succ.succ - X j.succ 0 * Ring.inverse (X 0 0) * X 0 i.succ.succ

def freeCell (K : Type) [CommRing K] (M n : ℕ) : Set (Fin (n + 1) → Fin (M + 2) → K) :=
  {X | IsUnit (X 0 0) ∧ LinearIndependent K (yPart X)}

theorem sigR_sigR (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (y : R ⊗[F] E) : sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hσ]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

def qH (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {n : ℕ} (t : HermR R σ 1) (s a : Fin 1 → Fin n → R ⊗[F] E) :
    HermR R σ n :=
  ⟨Matrix.of fun i j => sigR R σ (a 0 i) * s 0 j + sigR R σ (s 0 i) * a 0 j -
      (t : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 * (sigR R σ (a 0 i) * a 0 j), by
    intro i j
    have ht : sigR R σ ((t : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) = (t : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 :=
      t.2 0 0
    simp only [Matrix.of_apply, map_add (f := _), map_sub, map_mul, sigR_sigR R σ hσ, ht]
    ring⟩

end Chart

theorem sig_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ]
  simp

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage
end
end

