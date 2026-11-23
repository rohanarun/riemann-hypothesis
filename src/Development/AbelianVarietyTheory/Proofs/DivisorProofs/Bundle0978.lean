module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0938
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenMapTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0937
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameA
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0914
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsolutelyIntegrallyClosedDomainTateTwistAcyclic
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.AicAcyc

theorem aic_of_isAlgClosed (K : Type) [Field K] [IsAlgClosed K] : AIC K := by
  intro p hp hdeg
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero]; exact_mod_cast hdeg.ne')
  exact ⟨a, ha⟩

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem isIso_spMap {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) : IsIso (spMap (e : A →+* B)) := by
  haveI : IsIso (CommRingCat.ofHom (e : A →+* B)) := (RingEquiv.toCommRingCatIso e).isIso_hom
  unfold spMap
  infer_instance

end GlobalTheory.EtC.AicAcyc

namespace GlobalTheory.EtC


open GlobalTheory.EtC.AicAcyc in
theorem b5 : B5 := by
  intro q A _ _ hA hq n i hn
  haveI := GlobalTheory.T.isAlgClosed_fractionRing_of_monic_polynomials_have_roots A hA
  have hK : SH (FractionRing A) :=
    GlobalTheory.T.isStrictlyHenselian_of_isField_monicRoots (FractionRing A) (Field.toIsField _) (aic_of_isAlgClosed _)
  have hE := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have heqv : Eqv (ZMod q) (spMap (algebraMap A (FractionRing A))) (tw q i) := by
    refine GlobalTheory.T.etaleCohomology_local_to_global_ringMap_indEtale (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) A A (FractionRing A)
      (Algebra.ofId A (FractionRing A)) ?_
    intro O _ _ hO hOind
    obtain ⟨hfield, haic⟩ := GlobalTheory.T.isField_monicRoots_tensor_fractionRing_strictlyHenselian A O hA hO hOind
    have hSH : SH (O ⊗[A] FractionRing A) := GlobalTheory.T.isStrictlyHenselian_of_isField_monicRoots _ hfield haic
    have hqO : IsUnit (q : O) := by
      simpa using hq.map (algebraMap A O)
    let e := Algebra.TensorProduct.rid A A O
    let j : O →ₐ[A] O ⊗[A] FractionRing A := Algebra.TensorProduct.includeLeft
    have hψ : (Algebra.TensorProduct.map (AlgHom.id A O) (Algebra.ofId A (FractionRing A))) =
        j.comp e.toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro o a
      simp [j, e, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [hψ]
    have h1 : Eqv (ZMod q) (spMap (j : O →+* O ⊗[A] FractionRing A)) (tw q i) :=
      GlobalTheory.T.eqv_spMap_tw_of_isUnit q i O _ (j : O →+* O ⊗[A] FractionRing A) hO hSH hqO
    have h2 : Eqv (ZMod q) (spMap ((e : O ⊗[A] A ≃+* O) : O ⊗[A] A →+* O)) (tw q i) := by
      haveI := isIso_spMap (e : O ⊗[A] A ≃+* O)
      exact hE.1 _ _ _ inferInstance
    have h3 := (hE.2.1 _ _ _ _ _).1 h1 h2
    rw [← spMap_comp] at h3
    exact h3
  have hacK : AcycF (ZMod q) (sp (FractionRing A)) (tw q i) :=
    fun m hm => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) (FractionRing A) hK (tw q i) m hm
  exact (hE.2.2.2 _ _ _ heqv).1 hacK n hn

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictTranslatedDiagonalMemStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartz_restrict_translated_diagonal_mem : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : (κ ⊕ κ → AF F) → ℂ), φ ∈ schA F (κ ⊕ κ) → ∀ u : κ → AF F, (fun t : κ → AF F => φ (Sum.elim (t + u) t)) ∈ schwartzBruhatPi (K := F) (ι := κ) := by
  first | exact @GlobalTheory.DiagShift.shift_mem_schwartzBruhatPi | exact GlobalTheory.DiagShift.shift_mem_schwartzBruhatPi | (intros; apply GlobalTheory.DiagShift.shift_mem_schwartzBruhatPi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicVacuumReadsMultipleClassicalVacuum
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.VacLine

theorem hostHalfRoot_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) :
    (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have := congrArg (algebraMap (𝓞 E) E) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
  rw [map_add (f := _), map_one] at this
  exact (congrArg _ (H.bar_eq _).symm).trans this

theorem isRelTraceOneIdempotentModTwo_hostElement {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) :
    GlobalTheory.Ker.IdemTwo (H.w0 : E) := by
  obtain ⟨k, hk⟩ : ∃ k, H.d = 16 * k + 7 := ⟨H.d / 16, by have := H.d_mod; omega⟩
  have h1 := hostHalfRoot_add_conj_eq_one H
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    rwa [map_mul, map_add, map_one, map_ofNat] at this
  have h3 : (H.rt : E) ^ 2 = -(16 * k + 7) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast, hk] at this
    exact this.trans (by push_cast; rfl)
  refine ⟨((2 * k + 1 : ℕ) : E), isIntegral_natCast _, ?_⟩
  rw [eq_sub_of_add_eq' h1]
  push_cast
  linear_combination (-(1 / 4 : E)) * h3 - (1 / 4 : E) * (2 * (H.w0 : E) - 1 + (H.rt : E)) * h2

theorem isAA_aMul {D : D7} {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    GlobalTheory.Ker.IsAA (LatOf.aMul Λ) Λ := by
  intro v
  constructor
  · intro h
    exact LatOf.aMul_induction (p := fun v => v ∈ AddSubgroup.closure
      {u | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ t ∈ Λ, u = a • t})
      (fun a ha t ht => AddSubgroup.subset_closure ⟨a, ha, t, ht, rfl⟩) (zero_mem _) (fun _ _ => add_mem) h
  · intro h
    exact (AddSubgroup.closure_le (LatOf.aMul Λ).toAddSubgroup).2 Submodule.subset_span h

theorem vac_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (Λ' : Lt D.host.E V.rank) (L : Lt D.host.E r), V.SigOK → W.SigOK → IsSelfDualC V ΛV → IsSelfDualC W ΛW → (∀ v : Fin V.rank → D.host.E, v ∈ Λ' ↔ (fun j => star (v j)) ∈ ΛV) → (∀ L₀ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E), L₀ = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ ΛW, w = a • v} → L = latR hr L₀) → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ v : TF V.rank g, IsVac X bas (H.w0 : D.host.E) (tens Λ' L) v → ∃ κ : ℂ, κ ≠ 0 ∧ Reads θ V W hr X bas idx f (κ • v) x := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV he hX hs H _ ΛV ΛW Λ' L _ _ hΛV hΛW hΛ' hL x s hx hsx f hf v hv
  obtain ⟨-, hsd, hU, hfg⟩ := LatOf.isLatOf_tens D ψ θ V W r g hr X bas idx hψ hθ hV he hX hs ΛV ΛW Λ' L hΛV hΛW hΛ' hL
  subst hr
  have hL' : L = LatOf.aMul ΛW := by
    rw [hL (LatOf.aMul ΛW) rfl]
    exact Submodule.map_id _
  subst hL'
  obtain ⟨X', m, hq', hq, bas', idx', hs', -, -, hEF, hh, -, -, hfr⟩ :=
    GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta D ψ θ V W g X bas idx hψ hθ he hV hX hs
  obtain ⟨⟨B, hB⟩, hall⟩ := hfr x hx
  obtain ⟨hIB, -, hsB, -, -, -, -, -, hrd⟩ := hall B hB
  set C : GlobalTheory.Ker.Ctx V W := ⟨ψ, hψ, θ, hθ, X', m, g, X.p0, hq', bas', idx', hs', he⟩ with hC
  obtain rfl := hsB s hsx
  have hsd' : SelfD C.X (LatOf.aMul ΛW) := by
    refine ⟨hsd.1, fun u => (hsd.2 u).trans ?_⟩
    change _ ↔ ∀ y ∈ LatOf.aMul ΛW, ∃ k : ℤ, EF X' u y = k
    simp only [hEF]
  have hv' : IsVac C.X C.bas (H.w0 : D.host.E) (tens Λ' (LatOf.aMul ΛW)) v := by
    refine ⟨hv.1, hv.2.1, fun y hy => ?_⟩
    change epsW X' _ y • heisG X' bas' y v = v
    have e : epsW X' (H.w0 : D.host.E) y = epsW X (H.w0 : D.host.E) y := by simp only [epsW, hEF]
    rw [e, hh]
    exact hv.2.2 y hy
  have hlat := hf.2.lat
  rw [GlobalTheory.Ker.LatTens.latO_eq_hatA D V W C ΛV Λ' ΛW _ hΛ' (isAA_aMul ΛW)] at hlat
  obtain ⟨t, ht⟩ := (GlobalTheory.Ker.latVac_th_line D V W C _ H.w0.isIntegral_coe (hostHalfRoot_add_conj_eq_one H) (isRelTraceOneIdempotentModTwo_hostElement H) 1 Λ'
    (VacProj.mem_vset ⟨Λ'⟩ hU hfg) _ hsd').2 B hIB v hv' f hf.2.theta hf.2.fock hlat
  refine ⟨t, ?_, ((hrd f (t • v) (TensVac.sb_smul _ hv.1)).2 ?_).2⟩
  · rintro rfl
    rw [zero_smul] at ht
    subst ht
    obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
    have := hn p hp
    simp [nrm2] at this
  · rw [(_root_.GlobalTheory.Ker.Ctx.th_laws D V W C _ ((_root_.GlobalTheory.Ker.onBasis_frame_period D V W C).2 B hIB).2.1 v hv.1).2.1]
    exact ht

end GlobalTheory.AdTh.VacLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisHenselExistsUniqueSqrtStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicIntegralTensorBasis_hensel_exists_unique_sqrt : ∀ (v : HeightOneSpectrum ℤ) (L : Type) [Field L] [NumberField L] (κ : Type) (bL : Module.Basis κ ℚ L),
    Valued.v (2 : v.adicCompletion ℚ) = 1 → IsIntB v bL 1 →
    (∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y)) →
    (∀ x y, IsIntB v bL x → IsSmallB v bL y → IsSmallB v bL (x * y)) →
    ∀ u : v.adicCompletion ℚ ⊗[ℚ] L, IsIntB v bL u → IsSmallB v bL (u - 1) →
    ∃ f : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, IsIntB v bL ↑f ∧ IsIntB v bL ↑f⁻¹ ∧ (f : v.adicCompletion ℚ ⊗[ℚ] L) ^ 2 = u ∧
      IsSmallB v bL (↑f - 1) ∧
      ∀ g : v.adicCompletion ℚ ⊗[ℚ] L, IsIntB v bL g → g ^ 2 = u → IsSmallB v bL (g - 1) → g = ↑f := by
  first | (exact @GlobalTheory.AdicSpan.HenselSqrt.exists_sqrt) | (exact GlobalTheory.AdicSpan.HenselSqrt.exists_sqrt) | (intros; apply GlobalTheory.AdicSpan.HenselSqrt.exists_sqrt  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisIffExistsIntegralMultipleStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicIntegralTensorBasis_iff_exists_integral_multiple : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ z : L,
      IsIntB v ℓ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] z) ↔ ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * z) := by
  first | (exact @GlobalTheory.AdicSpan.isIntB_one_tmul_iff_exists_isIntegral) | (exact GlobalTheory.AdicSpan.isIntB_one_tmul_iff_exists_isIntegral) | (intros; apply GlobalTheory.AdicSpan.isIntB_one_tmul_iff_exists_isIntegral  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisOfTraceMemEventuallyStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicIntegralTensorBasis_of_trace_mem_eventually : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (bL : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ E : v.adicCompletion ℚ ⊗[ℚ] L,
      (∀ i, Algebra.trace (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L)
          (E * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] bL i)) ∈ v.adicCompletionIntegers ℚ) →
        IsIntB v bL E := by
  first | (exact @GlobalTheory.LocIntSpan.isIntB_of_trace_mem) | (exact GlobalTheory.LocIntSpan.isIntB_of_trace_mem) | (intros; apply GlobalTheory.LocIntSpan.isIntB_of_trace_mem  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisRingEventuallyStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicIntegralTensorBasis_ring_eventually : ∀ (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (κ : Type) (b : Module.Basis κ ℚ A),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, IsIntB v b 1 ∧
      ∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z) := by
  first | (exact @GlobalTheory.AdicSpan.isIntB_one_mul_eventually) | (exact GlobalTheory.AdicSpan.isIntB_one_mul_eventually) | (intros; apply GlobalTheory.AdicSpan.isIntB_one_mul_eventually  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicTensorExistsRationalAddIntegralMulStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicTensor_exists_rational_add_integral_mul : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L)
    (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ ⊗[ℚ] L) (D : ℤ), D ≠ 0 →
    ∃ (y : L) (ρ : v.adicCompletion ℚ ⊗[ℚ] L), IsIntB v ℓ ρ ∧
      x = (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] y + (D : v.adicCompletion ℚ ⊗[ℚ] L) * ρ := by
  first | (exact @GlobalTheory.AdicSpan.exists_tmul_add_mul_isIntB) | (exact GlobalTheory.AdicSpan.exists_tmul_add_mul_isIntB) | (intros; apply GlobalTheory.AdicSpan.exists_tmul_add_mul_isIntB  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostAllPlacesBasisIntegral
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.almost_all_places_basis_integral : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C), (∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) →
    ∀ (κ : Type) (ℓ : Module.Basis κ ℚ L) (κ' : Type) (b : Module.Basis κ' ℚ C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L,
      IsIntB v b (∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i)) ↔ ∀ i, IsIntB v ℓ (β i) := by
  first | (exact @GlobalTheory.AdicSpan.LeftBasis.isIntB_sum_leftBasis_iff_eventually) | (exact GlobalTheory.AdicSpan.LeftBasis.isIntB_sum_leftBasis_iff_eventually) | (intros; apply GlobalTheory.AdicSpan.LeftBasis.isIntB_sum_leftBasis_iff_eventually  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticFibreDescriptionUnique
section
namespace GlobalTheory.AnUniq

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem exp_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ}
    {e e' : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : ∀ z w, e (z + w) = e z * e w)
    (he' : ∀ z w, e' (z + w) = e' z * e' w)
    (hol : IsHolTo Set.univ (fun z => (e z).left)) (hol' : IsHolTo Set.univ (fun z => (e' z).left))
    (u : Fin g → (Sp (DualNumber ℂ) ⟶ G.left)) (hd : ∀ i, IsDerivAt0 (fun z => (e z).left) (Pi.single i 1) (u i))
    (hd' : ∀ i, IsDerivAt0 (fun z => (e' z).left) (Pi.single i 1) (u i)) : e = e' := by
  have h0 : e 0 = e' 0 := (HolHom.map_zero_eq_one he).trans (HolHom.map_zero_eq_one he').symm
  refine HolHom.eq_of_fderiv_eq he he' hol hol' fun U hU f =>
    ContinuousLinearMap.coe_injective ((Pi.basisFun ℂ _).ext fun i => ?_)
  rw [Pi.basisFun_apply]
  exact (((HolHom.isDerivAt0_iff _ _ _).1 (hd i)).2 U hU f).symm.trans
    (((HolHom.isDerivAt0_iff _ _ _).1 (hd' i)).2 U (h0 ▸ hU :) f)

theorem fr_eq {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ Φ' : AnFr A L x0 g) (he : ∀ z, Φ'.e z = Φ.e z) (hH : ∀ z w, hermForm Φ'.Hm z w = hermForm Φ.Hm z w)
    (j : L.L.ι) (z : Fin g → ℂ) (hj : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j) : Φ.fr j z = Φ'.fr j z := by
  choose c hc using Φ.exists_chart_e
  have ne' : ∀ j z, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j → Φ'.fr j z ≠ 0 := fun j z h => Φ'.fr_ne j z (by rw [he]; exact h)
  let q : (Fin g → ℂ) → ℂ := fun z => Φ.fr (c z) z / Φ'.fr (c z) z
  have key : ∀ j z, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j → q z = Φ.fr j z / Φ'.fr j z := fun j z h => by
    have hz : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ (L.L.U j ⊓ L.L.U (c z)) := fun p hp => ⟨h hp, hc z hp⟩
    have h1 := Φ.fr_g j (c z) z hz
    have h2 := Φ'.fr_g j (c z) z (by rw [he]; exact hz)
    rw [he] at h2
    rw [h1, h2, mul_div_mul_left _ _ (left_ne_zero_of_mul (h1 ▸ Φ.fr_ne j z h))]
  have hq : Differentiable ℂ q := fun z0 => by
    have hO : IsOpen {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U (c z0)} := (Φ.hol (L.L.U (c z0)) 0).1
    have h' : DifferentiableOn ℂ (Φ'.fr (c z0)) {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U (c z0)} := by
      simpa only [he] using Φ'.fr_hol (c z0)
    have hd : DifferentiableOn ℂ q {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U (c z0)} :=
      ((Φ.fr_hol (c z0)).mul (h'.inv fun z hz => ne' _ z hz)).congr fun z hz =>
        (key _ z hz).trans (div_eq_mul_inv _ _)
    exact hd.differentiableAt (hO.mem_nhds (hc z0))
  have hper : ∀ z (a : Φ.lat), ‖q (z + Φ.lat.subtype a)‖ = ‖q z‖ := fun z a => by
    have ha' : (a : Fin g → ℂ) ∈ Φ'.lat := (Φ'.e_ker _).1 ((he _).trans ((Φ.e_ker _).2 a.2))
    have h : ⊤ ≤ (Φ.e (z + a)).left ⁻¹ᵁ L.L.U (c z) := by rw [Φ.e_add_lat a.2]; exact hc z
    have h1 := Φ.fr_per a a.2 (c z) z (hc z)
    have h2 := Φ'.fr_per a ha' (c z) z (by rw [he]; exact hc z)
    rw [hH, hH] at h2
    change ‖q (z + a)‖ = _
    rw [key _ _ h, key _ _ (hc z), h1, h2, norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_mul,
      Φ.χ_norm _ a.2, Φ'.χ_norm _ ha',
      mul_div_mul_left _ _ (mul_ne_zero one_ne_zero (norm_ne_zero_iff.2 (Complex.exp_ne_zero _)))]
  have hc0 := norm_periodic_const_range Φ.lat.subtype
    (by rw [AddSubgroup.coe_subtype, Subtype.range_coe]; exact Φ.span) q hq hper z 0
  have h0 : q 0 = 1 := by
    have := Φ'.fr_0 (c 0) (by rw [he]; exact hc 0)
    rw [← Φ.fr_0 (c 0) (hc 0)] at this
    change Φ.fr (c 0) 0 / Φ'.fr (c 0) 0 = 1
    rw [this, div_self (Φ.fr_ne _ _ (hc 0))]
  rw [h0, key j z hj] at hc0
  exact (div_eq_one_iff_eq (ne' j z hj)).1 hc0

end GlobalTheory.AnUniq

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AnUniq.anFib_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A A' : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → A.ex = A'.ex ∧ ∀ ϑ, A.Reads 1 y.s ϑ ↔ A'.Reads 1 y.s ϑ := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A A' hs hx hL
  have hex : A.ex = A'.ex := AnUniq.exp_eq A.ex_add A'.ex_add A.hol A'.hol (fun i => y.u (e i).1 (e i).2)
    (fun i => by simpa only [Equiv.symm_apply_apply] using A.der (e i))
    (fun i => by simpa only [Equiv.symm_apply_apply] using A'.der (e i))
  obtain ⟨Φ, k₁, f₁, -, m₁, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  obtain ⟨Φ', k₂, f₂, -, m₂, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A' hs hx hL
  have hfr := AnUniq.fr_eq Φ.toAnFr Φ'.toAnFr (fun z => by rw [k₁, k₂, hex]) (fun z w => by rw [m₁, m₂])
  simp only [k₁, f₁, f₂] at hfr
  refine ⟨hex, fun ϑ => ⟨fun h j z pt h1 h2 hj => ?_, fun h j z pt h1 h2 hj => ?_⟩⟩
  · rw [← hex] at h1 hj
    rw [← hfr j z hj]
    exact h j z pt h1 h2 hj
  · rw [hfr j z hj]
    rw [hex] at h1 hj
    exact h j z pt h1 h2 hj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionDivisorSupport
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxUnfold

theorem minpoly_units_conj {F A : Type*} [Field F] [Ring A] [Algebra F A] (u : Aˣ) (x : A) :
    minpoly F ((u : A) * x * ((u⁻¹ : Aˣ) : A)) = minpoly F x := by
  let e : A ≃ₐ[F] A :=
    { toFun := fun z => (u : A) * z * ((u⁻¹ : Aˣ) : A)
      invFun := fun z => ((u⁻¹ : Aˣ) : A) * z * u
      left_inv := fun z => by simp [mul_assoc]
      right_inv := fun z => by simp [mul_assoc]
      map_mul' := fun z w => by simp [mul_assoc]
      map_add' := fun z w => by simp [mul_add, add_mul]
      commutes' := fun r => by
        show (u : A) * algebraMap F A r * ((u⁻¹ : Aˣ) : A) = algebraMap F A r
        rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one] }
  exact minpoly.algEquiv_eq e x

theorem fixL_smul_iff {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β)
    (z : Fin G.n → ℂ) (c : ℂ) (hc : c ≠ 0) : FixL G v β y (c • z) ↔ FixL G v β y z := by
  unfold FixL
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    rw [Matrix.mulVec_smul, smul_comm d c z] at hd
    exact smul_right_injective _ hc hd
  · rintro ⟨d, hd⟩
    exact ⟨d, by rw [Matrix.mulVec_smul, hd, smul_comm]⟩

end GlobalTheory.CxUnfold

namespace GlobalTheory.CxUnfold

theorem rep_smul {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (η : grp G β)
    (l : PLv G v β) : ∃ c : ℂ, c ≠ 0 ∧
      Projectivization.rep ((η • l : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)) =
        c • ((toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
          Projectivization.rep (l : Projectivization ℂ (Fin G.n → ℂ))) := by
  set w := Projectivization.rep (l : Projectivization ℂ (Fin G.n → ℂ))
  have hw : w ≠ 0 := Projectivization.rep_nonzero _
  have hMw : (toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w ≠ 0 := by
    intro h0
    apply hw
    apply toV_injective G v β η
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h0, Matrix.mulVec_zero]
  have hl : ((η • l : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)) =
      Projectivization.mk ℂ ((toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w) hMw := by
    show Projectivization.map _ _ (l : Projectivization ℂ (Fin G.n → ℂ)) = _
    conv_lhs => rw [← Projectivization.mk_rep (l : Projectivization ℂ (Fin G.n → ℂ))]
    rw [Projectivization.map_mk]
    simp only [Matrix.toLin'_apply]
    rfl
  rw [hl]
  have h2 := Projectivization.mk_rep (Projectivization.mk ℂ ((toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w) hMw)
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ (Projectivization.rep_nonzero _) hMw).1 h2
  exact ⟨c, c.ne_zero, by rw [← hc, Units.smul_def]⟩

end GlobalTheory.CxUnfold

namespace GlobalTheory.CxUnfold

end GlobalTheory.CxUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaTwistedInvolutionEqComplexConjOfMarkedStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.betaTwistedInvolution_eq_complexConj_of_marked : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ → ∀ (τ : FM P →+* ℂ) (a : FM P), τ (iM P a) = (starRingEnd ℂ) (τ a) := by
  first | (exact @GlobalTheory.StabFin.iM_conj) | (exact GlobalTheory.StabFin.iM_conj) | (intros; apply GlobalTheory.StabFin.iM_conj  <;> assumption)
end

