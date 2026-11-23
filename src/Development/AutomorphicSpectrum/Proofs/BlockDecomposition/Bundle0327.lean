module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0254
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0321
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0311
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0251
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0256
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0319
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0315
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0313
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0323
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0320
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0191
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0226
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0215
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0200
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0208
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelDecompositionStatement
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0314
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0309
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.BijectiveToPushforwardComp
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0318
public import GroundTheory.AutomorphicForms.Bundle0023
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AmpleTwistedSectionsApproximation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

theorem step_uniform : UniformGen → ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∃ n₁ : ℤ, ∀ n, n₁ ≤ n → ∀ e, ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1) := by
  intro hG A _ _ I X _ _ H hH P hP S hS
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hPq : P.IsQuasicoherent := hP.1
  have hL : H.IsLB := hH.isLB
  obtain ⟨k, g, hg⟩ := exists_fin_generators I
  have hgI : ∀ i, g i ∈ I := fun i => hg ▸ Ideal.subset_span ⟨i, rfl⟩
  have hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i)) :=
    fun i => GlobalTheory.T.ideal_element_maps_closed_system_down I hPq S hS (g i) (hgI i)
  have hO : OpSeq k (fun e => gr (anti hS) e) (fun i e => grT (anti hS) (hr i) e) 0 :=
    ⟨fun e => _root_.GlobalTheory.CompanionTheory.GE.Step.isCoherent_gr I hP S hS e, fun i j e => grT_comm _ _ _ _,
      fun e _ U => GlobalTheory.T.graded_pieces_generated_by_ideal_generators I hPq S hS g hg hr e U⟩
  obtain ⟨n₁, h₁⟩ := @hG A _ _ X _ _ H hH k _ _ 0 hO
  have hS0 : IsCoherent (S 0 : X.Modules) := GlobalTheory.T.coherent_subobject_coherent hP (S 0) (hS.qcoh 0)
  obtain ⟨n₂, h₂⟩ := _root_.GlobalTheory.CompanionTheory.GE.Step.serre_vanishing_coh_one A H hH hS0
  refine ⟨max n₁ n₂, fun n hn e => ?_⟩
  have hl : ∀ e, Lifts I H hS n e := by
    intro e
    induction e with
    | zero => exact _root_.GlobalTheory.CompanionTheory.GE.Step.lifts_zero I H hL S hS n (h₂ n (le_of_max_le_right hn))
    | succ e ih => exact GlobalTheory.T.twisted_graded_generation_global_sections I H S hS g hgI hr n e (h₁ n (le_of_max_le_left hn) e (Nat.zero_le _)) ih
  exact GlobalTheory.T.lifting_inductive_successive_approximation I H hL S hS n e (hl (e + 1))

end GlobalTheory.CompanionTheory.GE.Step
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AsmMultMain
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem asmMult_main : AsmMult := by
  intro hL hU hR hS hE hQ h1 n _ _ μ _ E k k' val val' T T' hk hk'
  obtain ⟨m, c, w, g, ks, hb, hs, hv⟩ := hk
  obtain ⟨m', c', w', g', ks', hb', hs', hv'⟩ := hk'
  have hreg : ∀ i, KReg (ks i) := fun i => ⟨(hb i).2.1.continuousOn, (hb i).2.2.1⟩
  have hreg' : ∀ i, KReg (ks' i) := fun i => ⟨(hb' i).2.1.continuousOn, (hb' i).2.2.1⟩
  have hbp : ∀ p : Fin m × Fin m', IsBump (gconv (g p.1) (g' p.2)) (T + T') :=
    fun p => _root_.GlobalTheory.CompanionTheory.WaveMult.isBump_gconv _ _ _ _ (hb p.1).1 (hb' p.2).1
  choose K hK using fun p : Fin m × Fin m' => h1 n μ E (w p.1 ++ w' p.2) (gconv (g p.1) (g' p.2)) (T + T') (hbp p)
  have hconv : ∀ y ∈ GLs n, conv μ E k k' y = ∑ p : Fin m × Fin m', (c p.1 * c' p.2) • K p y := by
    intro y hy
    rw [_root_.GlobalTheory.CompanionTheory.WaveMult.conv_eq_sum_of_kernels hL n μ E c c' ks ks' k k' hreg hreg' hs hs' y hy, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [_root_.GlobalTheory.CompanionTheory.WaveMult.conv_eq_of_isKer hL hU hR hS hE hQ n μ E (w i) (w' j) (g i) (g' j) T T' (ks i) (ks' j) (K (i, j))
      (hb i).1 (hb' j).1 (hb i).2 (hb' j).2 (hK (i, j)) y hy]
  have hconv' : ∀ y ∈ GLs n, conv μ E k' k y = ∑ p : Fin m × Fin m', (c p.1 * c' p.2) • K p y := by
    intro y hy
    rw [_root_.GlobalTheory.CompanionTheory.WaveMult.conv_eq_sum_of_kernels hL n μ E c' c ks' ks k' k hreg' hreg hs' hs y hy, Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hsw := _root_.GlobalTheory.CompanionTheory.WaveMult.KerSwap.isKer_swap hS hR n μ E (w i) (w' j) _ (T + T') (K (i, j)) (hbp (i, j)) (hK (i, j))
    rw [gconv_comm] at hsw
    rw [_root_.GlobalTheory.CompanionTheory.WaveMult.conv_eq_of_isKer hL hU hR hS hE hQ n μ E (w' j) (w i) (g' j) (g i) T' T (ks' j) (ks i) (K (i, j))
      (hb' j).1 (hb i).1 (hb' j).2 (hb i).2 hsw y hy, mul_comm]
  refine ⟨?_, fun y hy => by rw [hconv y hy, hconv' y hy], ?_,
    _root_.GlobalTheory.CompanionTheory.WaveMult.act_eq_val_of_isMult hL n μ E k val T ⟨m, c, w, g, ks, hb, hs, hv⟩⟩
  · refine isMult_of_fintype μ E (fun p : Fin m × Fin m' => c p.1 * c' p.2) (fun p => w p.1 ++ w' p.2)
      (fun p => gconv (g p.1) (g' p.2)) K (fun p => ⟨hbp p, hK p⟩) hconv fun χ => ?_
    rw [Pi.mul_apply, hv χ, hv' χ, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [zVal_append, ← GlobalTheory.T.cosh_transform_convolution _ _ _ _ _ (hb i).1 (hb' j).1]
    ring
  · haveI := FiniteDimensional.complete ℂ E.V
    choose N d w₁ K₁ hK₁ hadj hval using fun i =>
      GlobalTheory.T.wave_kernel_decomposition hL hU hR hS hE hQ h1 n μ E (w i) (g i) T (ks i) (hb i).1 (hb i).2
    refine ⟨fun χ => ∑ q : (Σ i, Fin (N i)), (conj (c q.1) * d q.1 q.2) * zVal (w₁ q.1 q.2) χ * coshT (g q.1) (cas χ), ?_, ?_⟩
    · refine isMult_of_fintype μ E (fun q : (Σ i, Fin (N i)) => conj (c q.1) * d q.1 q.2) (fun q => w₁ q.1 q.2)
        (fun q => g q.1) (fun q => K₁ q.1 q.2) (fun q => ⟨(hb q.1).1, hK₁ q.1 q.2⟩) (fun y hy => ?_) fun χ => rfl
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hs _ (inv_mem_GLs hy), map_sum, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := hadj i y hy
      rw [map_smulₛₗ, this, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [smul_smul]
    · intro χ hχ
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hv χ, map_sum]
      beta_reduce
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, _root_.GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas n χ (g i) T hχ (hb i).1, hval i χ hχ, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

end GlobalTheory.CompanionTheory.WaveMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AutomorphicFormsFiniteGLOfGenFin
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.HCFin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem mul_mem_span_zalg_mul {J : Set (Module.End ℂ (Sm E a))} {x : Module.End ℂ (Sm E a)} (hx : x ∈ Zalg E a)
    {s : Module.End ℂ (Sm E a)} (hs : s ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E a, ∃ j ∈ J, y = x * j}) :
    x * s ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E a, ∃ j ∈ J, y = x * j} := by
  induction hs using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x', hx', j, hj, rfl⟩ := hy
    exact Submodule.subset_span ⟨x * x', Subalgebra.mul_mem _ hx hx', j, hj, (mul_assoc _ _ _).symm⟩
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy

end GlobalTheory.CompanionTheory.HCFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralTorusContractsLower
section
noncomputable section

namespace GlobalTheory.CompanionTheory.MoyPrasad

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead _root_.Topology

theorem lowC_central_contract : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ U ∈ 𝓝 (1 : GL (Fin n) k),
    ∃ t : Levi k (fun a => Fin (d a)), (∀ m, t * m = m * t) ∧
      ∀ c ∈ lowC k e, (leviEmb k e t)⁻¹ * c * leviEmb k e t ∈ U := by
  intro k _ _ _ _ n s d e U hU
  obtain ⟨V, hV, hVU⟩ : ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) k), Units.val ⁻¹' V ⊆ U := by
    rw [(isEmbedding_val_GL (k := k) n).nhds_eq_comap] at hU
    simpa using Filter.mem_comap.mp hU
  obtain ⟨W, hW, hWV⟩ := exists_entry_nhds hV
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff W).mp hW
  obtain ⟨c, hc0, hcγ, hc1⟩ : ∃ c : k, c ≠ 0 ∧ ValuativeRel.valuation k c < γ ∧
      ValuativeRel.valuation k c ≤ 1 := by
    obtain ⟨x, hx0, hx1⟩ := (Valuation.IsNontrivial.exists_lt_one : ∃ x : k, x ≠ 0 ∧ ValuativeRel.valuation k x < 1)
    obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (K := k) (γ : ValuativeRel.ValueGroupWithZero k)
    have hy0 : (0 : ValuativeRel.ValueGroupWithZero k) < ValuativeRel.valuation k y := by
      rw [hy]; exact Units.zero_lt γ
    rcases le_or_gt (ValuativeRel.valuation k y) 1 with hy1 | hy1
    · refine ⟨y * x, ?_, ?_, ?_⟩
      · exact mul_ne_zero (by rintro rfl; simp at hy0) hx0
      · rw [map_mul, ← hy]; exact mul_lt_of_lt_one_right hy0 hx1
      · rw [map_mul]; first | exact mul_le_one' hy1 hx1.le | exact mul_le_one₀ hy1 zero_le' hx1.le
    · refine ⟨x, hx0, ?_, hx1.le⟩
      rw [← hy]; exact hx1.trans hy1
  refine ⟨blockScalar hc0 (GlobalTheory.DepthZeroJac.expo s 1), blockScalar_central hc0 _, ?_⟩
  intro g hg
  simp only [lowC, Set.mem_ofPred_eq] at hg
  obtain ⟨hK, hlow⟩ := hg
  have hgint : ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    obtain ⟨h, -, rfl⟩ := Subgroup.mem_map.mp hK
    intro i j
    exact (h i j).2
  have h0W : (0 : k) ∈ W := mem_of_mem_nhds hW
  have hdiag : leviEmb k e (blockScalar hc0 (GlobalTheory.DepthZeroJac.expo s 1)) =
      GlobalTheory.DepthZeroJac.dia e hc0 (GlobalTheory.DepthZeroJac.expo s 1) := by
    refine Units.ext ?_
    rw [GlobalTheory.DepthZeroJac.dia_val]
    ext i j
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    by_cases h : a = b
    · subst h
      rw [leviEmb_apply_same]
      show ((c ^ GlobalTheory.DepthZeroJac.expo s 1 a) •
        (1 : Matrix (Fin (d a)) (Fin (d a)) k)) i' j' = _
      by_cases h2 : i' = j'
      · subst h2
        simp
      · rw [Matrix.smul_apply, Matrix.one_apply_ne h2, smul_zero, Matrix.diagonal_apply_ne]
        simpa using h2
    · rw [leviEmb_apply_ne k e _ h, Matrix.diagonal_apply_ne]
      exact fun h' => h (congrArg Sigma.fst (e.injective h'))
  rw [hdiag]
  refine hVU (hWV _ fun i j => ?_)
  have hentry : (((GlobalTheory.DepthZeroJac.dia e hc0 (GlobalTheory.DepthZeroJac.expo s 1))⁻¹ * g *
      GlobalTheory.DepthZeroJac.dia e hc0 (GlobalTheory.DepthZeroJac.expo s 1) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
      = (c ^ GlobalTheory.DepthZeroJac.expo s 1 (blk e i))⁻¹ * (g : Matrix (Fin n) (Fin n) k) i j *
          c ^ GlobalTheory.DepthZeroJac.expo s 1 (blk e j) := by
    simp [GlobalTheory.DepthZeroJac.dia, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [Matrix.sub_apply, hentry]
  by_cases hij : blk e j < blk e i
  · have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
    rw [Matrix.one_apply_ne hne, sub_zero]
    apply hγ
    exact ((valuation_conj_le hc0 hc1 (hgint i j) (GlobalTheory.CompanionTheory.MoyPrasad.expo_gap 1 hij)).trans_eq
      (pow_one _)).trans_lt hcγ
  · have h0 := hlow i j hij
    rw [Matrix.sub_apply, sub_eq_zero] at h0
    rw [h0]
    by_cases hij' : i = j
    · subst hij'
      simpa [hc0] using h0W
    · simpa [Matrix.one_apply_ne hij'] using h0W

end GlobalTheory.CompanionTheory.MoyPrasad

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemOpenIdealContainment
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.PSupp

theorem propSupp_of_closed_image : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩; ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, IsCoherent P → IsCoherent E → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ (Sb : Subobject P) (T : (O : Scheme.{0}).IdealSheafData), IsClosed (O.ι '' (T.support : Set (O : Scheme.{0}))) → (∀ V : X.Opens, Disjoint (V : Set X) (O.ι '' (T.support : Set (O : Scheme.{0}))) → secs Sb V = Set.univ) → ∀ Bb : Subobject P, (Bb : X.Modules).IsQuasicoherent → Bb ⊔ powSub I P 1 = Sb → ∀ B : Subobject E, (∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W = (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W)) → PropSupp A B := by
  intro A _ _ I hI X _ _ O
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
  intro P E hP hE f hf Sb T hTc hSb Bb hBq hBS B hB
  have hC : IsClosed (badSet Bb) := isClosed_badSet Bb
  have hCO : badSet Bb ⊆ (O : Set X) := subset_of_closedFibre I hI O (badSet Bb) hC
    (fun x hx hIx => by
      obtain ⟨y, _, rfl⟩ := mem_of_badSet_closedFibre I hP Bb hBq _ hTc
        (fun V hV => by rw [hBS]; exact hSb V hV) x hx hIx
      rw [← Scheme.Opens.range_ι O]
      exact ⟨y, rfl⟩)
  obtain ⟨T', hT'supp, hT'prop⟩ := ClosedSub.closed_subset_support_proper (A := A) O (badSet Bb) hC hCO
  have hBqc := isQuasicoherent_of_secs_image O hP.1 hE.1 f Bb hBq B hB
  refine ⟨T', hT'prop, ?_⟩
  rw [hT'supp]
  exact cokernel_supportedIn_preimage O hP.1 hE.1 f hf Bb B hBqc hB (badSet Bb)
    (fun U hU hd => GlobalTheory.T.sections_eq_univ_off_bad_support hP.1 Bb hBq U hU hd)

end GlobalTheory.CompanionTheory.GE.PSupp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentExtensionSurjectionOpen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Present

def toModPullZPowIso {X Y : Scheme.{0}} {L : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hL : L.IsLB) (f : Y ⟶ X) (m : ℤ) :
    GlobalTheory.LB.toMod ((GlobalTheory.lbZPow L m).pull f) ≅ GlobalTheory.LB.toMod (GlobalTheory.lbZPow (L.pull f) m) :=
  (GlobalTheory.Twist.unitTwistIso _).symm ≪≫ (GlobalTheory.Twist.twistZPullIso f hL _ m).symm ≪≫ GlobalTheory.Twist.unitTwistIso _

theorem exists_coherent_epi_restrict {X : Scheme.{0}} [IsNoetherian X] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X)
    (hH : GlobalTheory.IsAmpleLB H) (O : X.Opens) (E : (O : Scheme.{0}).Modules) (hE : IsCoherent E) :
    ∃ P : X.Modules, IsCoherent P ∧ ∃ f : P.restrict O.ι ⟶ E, Epi f := by
  haveI : CompactSpace (O : Scheme.{0}) :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (O : Set X))
  haveI : GlobalTheory.QCoh.IsFiniteQC E := ⟨hE.1, hE.2⟩
  have hA := hH.pull_of_isOpenImmersion O.ι
  obtain ⟨n, k, φ, hφ⟩ := (hA.eventually_exists_epi_sigma E).exists
  have hL := GlobalTheory.Twist.isLB_lbZPow hH.isLB (-n)
  haveI : GlobalTheory.QCoh.IsFiniteQC (GlobalTheory.LB.toMod (GlobalTheory.lbZPow H (-n))) := (GlobalTheory.VB.isVB_toMod hL).isFiniteQC
  let P : X.Modules := ∐ fun _ : Fin k => GlobalTheory.LB.toMod (GlobalTheory.lbZPow H (-n))
  have hP : GlobalTheory.QCoh.IsFiniteQC P := inferInstance
  let e : P.restrict O.ι ≅ ∐ fun _ : Fin k => GlobalTheory.LB.toMod (GlobalTheory.lbZPow (H.pull O.ι) (-n)) :=
    (Scheme.Modules.restrictFunctorIsoPullback O.ι).app P ≪≫
      PreservesCoproduct.iso (Scheme.Modules.pullback O.ι) _ ≪≫
      Sigma.mapIso (fun _ => GlobalTheory.LB.pullbackIso hL O.ι ≪≫ toModPullZPowIso hH.isLB O.ι (-n))
  exact ⟨P, ⟨hP.1, hP.2⟩, e.hom ≫ φ, epi_comp _ _⟩

end GlobalTheory.CompanionTheory.GE.Present
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteOfCommuteCyclicMatrixStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commute_of_commute_cyclic_matrix : ∀ (K : Type) [Field K] (R : Type) [CommRing R] [Algebra K R] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K), (∀ y : Fin n → K, ∃ h : K[X], y = aeval γ h *ᵥ v) → ∀ X Y : Matrix (Fin n) (Fin n) R, X * γ.map (algebraMap K R) = γ.map (algebraMap K R) * X → Y * γ.map (algebraMap K R) = γ.map (algebraMap K R) * Y → X * Y = Y * X := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.commute_of_commute_cyclic | exact GlobalTheory.CompanionTheory.TorusCh.commute_of_commute_cyclic | (intros; apply GlobalTheory.CompanionTheory.TorusCh.commute_of_commute_cyclic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnLambdaSubgroupStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_lambda_subgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (e : Matrix (Fin n) (Fin n) E), e * e = e → (∀ s : (Ad E)ˣ, logAbs (s : Ad E) = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ)) → ∀ H : Subgroup (GA E n), (∀ t ∈ H, t.val * rm e = rm e * t.val) → ContinuousOn (lam e) (H : Set (GA E n)) := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.continuousOn_lam | exact GlobalTheory.CompanionTheory.TorusCh.continuousOn_lam | (intros; apply GlobalTheory.CompanionTheory.TorusCh.continuousOn_lam <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimitiveIdempotentsSeparatingStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_idempotents_separating : ∀ (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K), γ.charpoly.Separable → ∃ S : Finset (Matrix (Fin n) (Fin n) K), (∀ e ∈ S, IsPrim γ e) ∧ ∀ x : Fin n → K, x ≠ 0 → ∃ e ∈ S, x ᵥ* e ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.exists_prim_cover | exact GlobalTheory.CompanionTheory.TorusCh.exists_prim_cover | (intros; apply GlobalTheory.CompanionTheory.TorusCh.exists_prim_cover <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinrankEqProdOfNonemptyEquiv
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.WhitRank

theorem finrank_piTensorProduct_eq_prod {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, AddCommGroup (E i)]
    [∀ i, Module ℂ (E i)] : Module.finrank ℂ (⨂[ℂ] i, E i) = ∏ i, Module.finrank ℂ (E i) := by
  open Module in
  rw [Module.finrank_eq_nat_card_basis (Basis.piTensorProduct fun i => Module.Free.chooseBasis ℂ (E i)),
    Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ => (Module.finrank_eq_nat_card_basis (Module.Free.chooseBasis ℂ (E i))).symm

theorem finrank_eq_prod_of_nonempty_equiv {ι A : Type} [Fintype ι] [AddCommGroup A] [Module ℂ A] (E : ι → Type)
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] (e : Nonempty (A ≃ₗ[ℂ] ⨂[ℂ] i, E i)) :
    Module.finrank ℂ A = ∏ i, Module.finrank ℂ (E i) := by
  obtain ⟨f⟩ := e
  rw [f.finrank_eq, finrank_piTensorProduct_eq_prod]

theorem whitRankProd_of_heredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], WhitHeredity k → WhitRankProd k := by
  intro k _ _ _ _ hW ψ hψ hψ1 h N x hd
  obtain ⟨f⟩ := hW ψ hψ hψ1 h N (fun a => (x a).fst) hd (fun a => (x a).snd.rep.V) (fun a => (x a).rep)
    (fun a => (x a).snd.rep.smooth)
  exact finrank_eq_prod_of_nonempty_equiv _ ⟨f⟩

end GlobalTheory.CompanionTheory.WhitRank

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianWeightTotalMass
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.FSCrofton

theorem integral_exp_neg_norm_sq : ∫ z : ℂ, Real.exp (-‖z‖ ^ 2) = Real.pi := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) (b := 1) one_pos
  have hd : (Module.finrank ℝ ℂ : ℝ) / 2 = 1 := by simp [Complex.finrank_real_complex]
  simp only [one_mul, div_one, hd, Real.rpow_one, neg_mul] at h
  exact h

theorem lintegral_exp_neg_norm_sq :
    ∫⁻ z : ℂ, ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) = ENNReal.ofReal Real.pi := by
  have hi : Integrable (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) := by
    by_contra hn
    have h0 := integral_undef hn
    rw [integral_exp_neg_norm_sq] at h0
    exact Real.pi_ne_zero h0
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le), integral_exp_neg_norm_sq]

theorem lintegral_gW (d : ℕ) (α : Type) [Fintype α] :
    ∫⁻ C : Fin d → α → ℂ, gW d α C = ENNReal.ofReal (Real.pi ^ (d * Fintype.card α)) := by
  have hw : ∀ C : Fin d → α → ℂ, gW d α C =
      ∏ k, ∏ j, ENNReal.ofReal (Real.exp (-‖C k j‖ ^ 2)) := by
    intro C
    unfold gW
    simp only [← Finset.sum_neg_distrib, Real.exp_sum]
    rw [ENNReal.ofReal_prod_of_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le]
    exact Finset.prod_congr rfl fun k _ =>
      ENNReal.ofReal_prod_of_nonneg fun _ _ => (Real.exp_pos _).le
  have hm : Measurable fun z : ℂ => ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) := by fun_prop
  have hrow : ∫⁻ r : α → ℂ, ∏ j, ENNReal.ofReal (Real.exp (-‖r j‖ ^ 2)) =
      ENNReal.ofReal Real.pi ^ Fintype.card α := by
    rw [volume_pi, GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (fun _ => hm.aemeasurable)]
    simp [lintegral_exp_neg_norm_sq]
  have hmr : Measurable fun r : α → ℂ => ∏ j, ENNReal.ofReal (Real.exp (-‖r j‖ ^ 2)) :=
    Finset.measurable_prod _ fun j _ => hm.comp (measurable_pi_apply j)
  simp only [hw]
  rw [volume_pi, GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (fun _ => hmr.aemeasurable)]
  simp only [hrow, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, mul_comm, ENNReal.ofReal_pow Real.pi_pos.le, mul_comm]

end GlobalTheory.CompanionTheory.FSCrofton
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivGaussianExponentialAtZeroStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDeriv_gaussian_exponential_at_zero : ∀ (m n : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ), Differentiable ℂ (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) ∧ ∀ r : ℕ, iteratedDeriv r (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 = PositivityTheory.Rg.Sw.evX ((PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X ^ r) 1) v * PositivityTheory.Rg.Sw.gs (2 * Real.pi) v := by
  first | exact @GlobalTheory.CompanionTheory.DilFam.main | exact GlobalTheory.CompanionTheory.DilFam.main | (intros; apply GlobalTheory.CompanionTheory.DilFam.main <;> assumption)
end

