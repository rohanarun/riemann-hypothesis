module

public import Mathlib
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0002
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalRingCardinality.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardFiniteSubgroupGLIntDvd
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.QuotientMetricDivisors.FinalW
public import Formalism.QuotientMetricDivisors.SixthReductionExplicit
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0086
public import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0110
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeToLevelOfDvdTrueDGam
section
noncomputable section

namespace GlobalTheory.DGamOnRecord

open Formalism.BasicNotions Formalism.MainNotions NumberField
open _root_.Formalism.L2.Col (Sp hStd autLat PosStar)
open Formalism.HermitianLatticesTheory (isom IsUnimodular)
open GlobalTheory.Mem.Col2 (DGam autOrd autO gamOrd gamRanks)

section Transport

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
  {V' : Type} [AddCommGroup V'] [Module E V'] [Module (𝓞 E) V'] [IsScalarTower (𝓞 E) E V']


omit [StarRing E] in
theorem card_dvd_of_minkMult {n N M : ℕ} (hM : MinkMult N M) (hN : Module.finrank ℚ E * n ≤ N)
    (G : Subgroup (Sp E n ≃ₗ[E] Sp E n)) [Finite G] : Nat.card G ∣ M := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hr : Module.finrank ℚ (Sp E n × (Fin k → ℚ)) = Module.finrank ℚ E * n + k := by
    rw [Module.finrank_prod, ← Module.finrank_mul_finrank ℚ E (Sp E n)]
    simp
  let b := Module.finBasisOfFinrankEq ℚ _ hr
  let r : G →* Module.End ℚ (Sp E n × (Fin k → ℚ)) :=
    { toFun := fun g => ((g.1 : Sp E n →ₗ[E] Sp E n).restrictScalars ℚ).prodMap LinearMap.id
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  have hr : Function.Injective r := fun g h hgh =>
    Subtype.ext (LinearEquiv.ext fun x => congrArg Prod.fst (LinearMap.congr_fun hgh (x, 0)))
  let φ : G →* Matrix.GeneralLinearGroup (Fin (Module.finrank ℚ E * n + k)) ℚ :=
    ((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom.comp r).toHomUnits
  have hφ : Function.Injective φ := fun g h hgh =>
    hr ((LinearMap.toMatrixAlgEquiv b).injective (congrArg Units.val hgh))
  have e := MonoidHom.ofInjective hφ
  rw [Nat.card_congr e.toEquiv]
  exact hM φ.range (Finite.of_equiv _ e.toEquiv)

end Transport

end GlobalTheory.DGamOnRecord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoefficientSeparation
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SpecTraceProof

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}


open Classical in
theorem isCopyFinDS_of_equiv {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ρ : GA D V →* (H →L[ℂ] H)} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {σ : Representation ℂ (GfC V) W} {σ' : Representation ℂ (GfC V) W'} (f : σ.Equiv σ')
    (h : IsCopyFinDS σ M ρ ⊤) : IsCopyFinDS σ' M ρ ⊤ := by
  obtain ⟨T, hT, hinj, hspan⟩ := h
  refine ⟨T ∘ₗ f.symm.toLinearEquiv.toLinearMap, ?_, hinj.comp f.symm.toLinearEquiv.injective, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := mem_homTensorPi.1 hT
    refine mem_homTensorPi.2 ⟨fun _ _ => Submodule.mem_top, fun g w y => ?_, fun i g w y => h3 i g _ y⟩
    have e : f.symm.toLinearEquiv (σ' g w) = σ g (f.symm.toLinearEquiv w) :=
      LinearMap.congr_fun (f.symm.isIntertwining' g) w
    have h2' := h2 g (f.symm.toLinearEquiv w) y
    rw [← e] at h2'
    exact h2'
  · rw [← hspan]
    congr 2
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Set.mem_setOf_eq]
    exact ⟨fun ⟨w, y, hv⟩ => ⟨_, y, hv⟩, fun ⟨w, y, hv⟩ => ⟨f.toLinearEquiv w, y, by simpa using hv⟩⟩


open Classical in
theorem isCopyFinDS_of_uEquiv {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    {ρ : GA D V →* (H →L[ℂ] H)} {ρ' : GA D V →* (H' →L[ℂ] H')} {W : Type} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GfC V) W} (hρ : UEquiv ρ ρ')
    (h : IsCopyFinDS σ M ρ ⊤) : IsCopyFinDS σ M ρ' ⊤ := by
  obtain ⟨A, hA⟩ := hρ
  obtain ⟨T, hT, hinj, hspan⟩ := h
  let C := (ContinuousLinearMap.compContinuousMultilinearMapL ℂ M.H H H'
    (A.toContinuousLinearEquiv : H →L[ℂ] H')).toLinearMap
  have hC : ∀ w y, (C ∘ₗ T) w y = A (T w y) := fun _ _ => rfl
  refine ⟨C ∘ₗ T, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := mem_homTensorPi.1 hT
    refine mem_homTensorPi.2 ⟨fun _ _ => Submodule.mem_top, fun g w y => ?_, fun i g w y => ?_⟩
    · rw [hC, hC, h2, hA]
    · rw [hC, hC, h3, hA]
  · intro w w' e
    refine hinj (ContinuousMultilinearMap.ext fun y => A.injective ?_)
    rw [← hC, ← hC, e]
  · have hS : {v | ∃ w y, v = (C ∘ₗ T) w y} = A '' {v | ∃ w y, v = T w y} := by
      ext v
      simp only [hC, Set.mem_setOf_eq, Set.mem_image]
      exact ⟨fun ⟨w, y, hv⟩ => ⟨_, ⟨w, y, rfl⟩, hv.symm⟩, fun ⟨_, ⟨w, y, rfl⟩, hv⟩ => ⟨w, y, hv.symm⟩⟩
    rw [hS]
    have hd : Dense ((Submodule.span ℂ {v | ∃ w y, v = T w y} : Submodule ℂ H) : Set H) :=
      Submodule.dense_iff_topologicalClosure_eq_top.2 hspan
    refine Submodule.dense_iff_topologicalClosure_eq_top.1 ?_
    have e2 : (Submodule.span ℂ ((A.toLinearEquiv : H →ₗ[ℂ] H') '' {v | ∃ w y, v = T w y}) : Set H') =
        (A.toLinearEquiv : H →ₗ[ℂ] H') '' (Submodule.span ℂ {v | ∃ w y, v = T w y} : Set H) := by
      rw [Submodule.span_image, Submodule.map_coe]
    have e3 : (A.toLinearEquiv : H →ₗ[ℂ] H') '' {v | ∃ w y, v = T w y} = A '' {v | ∃ w y, v = T w y} := rfl
    rw [← e3, e2]
    exact A.surjective.denseRange.dense_image A.continuous hd

theorem not_isIntegralOp_zero {G W : Type} [Group G] [MeasurableSpace G] [AddCommGroup W] [Module ℂ W]
    {ν : Measure G} {σ : Representation ℂ G W} {F : G → ℂ} {c : ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ F c) (hc : c ≠ 0) : ¬ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ F 0 := by
  intro h0
  obtain ⟨A, hA, -, rfl⟩ := h
  obtain rfl := hA.unique h0
  refine hc ?_
  have e : (LinearMap.restrict (0 : W →ₗ[ℂ] W) (p := LinearMap.range (0 : W →ₗ[ℂ] W))
      (q := LinearMap.range (0 : W →ₗ[ℂ] W)) fun v _ => LinearMap.mem_range_self _ v) = 0 :=
    LinearMap.ext fun x => Subtype.ext rfl
  rw [e, map_zero]

theorem specTrace : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → SpecTrace := by
  intro hDSC _ _ _ hFlath hChar hCO hPCT hPCS
  intro D V lam S M T U μa μf μ _ _ fa ff hTD ν hν n Ws _ _ σs hIrr hcover c hc
  have hcusp := _root_.GlobalTheory.TestFnCusp.isCuspidalOp_tensor hCO hPCT D V lam S M T U μa μf μ fa ff hTD
  have hpone := _root_.GlobalTheory.irrUnitary_trace_ne_zero_copyFinDS hDSC hFlath hChar hPCS D V lam S M T U μa μf μ fa ff hTD ν hν
  refine ⟨hcusp.traceClass, ?_⟩
  refine _root_.GlobalTheory.hasSum_eq_sum_of_matching_family (UDual (GA D V)) n (fun x => (mCusp V μ x.rep.π).toNat)
    (fun x => repTrace x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff)) (fun i => (mCuspDS μ (σs i) M).toNat) c
    (fun x i => IsCopyFinDS (σs i) M x.rep.π ⊤) _ hcusp.hasSum_trace ?_ ?_ ?_ ?_ ?_
  ·
    intro x hm ht
    have hm' : mCusp V μ x.rep.π ≠ 0 := fun h => hm (by rw [h]; simp)
    have htr : HasTrace (repOp x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff))
        (repTrace x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff)) := ⟨hcusp.traceClass_rep x hm', rfl⟩
    obtain ⟨W, _, _, σ, hσi, hσa, hcopy, hσt⟩ := hpone x.rep.H x.rep.π x.rep.isIrr _ htr ht
    have hmσ : mCuspDS μ σ M ≠ 0 := by
      rwa [← _root_.GlobalTheory.AutMult.mCusp_eq_mCuspDS D V S M μ x.rep.H x.rep.π x.rep.isIrr W σ hσi hσa hcopy]
    obtain ⟨i, ⟨f⟩⟩ := hcover W σ hσi hσa hmσ (not_isIntegralOp_zero hσt ht)
    exact ⟨i, isCopyFinDS_of_equiv f hcopy⟩
  ·
    intro i hi
    have hi' : mCuspDS μ (σs i) M ≠ 0 := fun h => hi (by rw [h]; simp)
    obtain ⟨H, _, _, π, hπ, hcopy⟩ := _root_.GlobalTheory.AutMult.exists_isIrrUnitary_isCopyFinDS D V S M μ (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hi'
    let R : IrrU (GA D V) := ⟨H, π, hπ⟩
    refine ⟨R.cl, isCopyFinDS_of_uEquiv ?_ hcopy⟩
    exact (IrrU.cl_eq_iff.1 (UDual.cl_rep R.cl)).symm
  ·
    intro x i hR
    refine ⟨?_, ?_⟩
    · rw [_root_.GlobalTheory.AutMult.mCusp_eq_mCuspDS D V S M μ x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hR]
    · exact (_root_.GlobalTheory.AutMult.hasTrace_repOp_of_isCopyFinDS D V lam S M T U μa μf μ fa ff hTD ν hν x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i)
        (hIrr.1 i) (hIrr.2.1 i) hR (c i) (hc i)).2
  ·
    intro x i j hi hj
    by_contra hne
    have e := (_root_.GlobalTheory.AutMult.isUnitEquiv_iff_nonempty_equiv_of_isCopyFinDS D V S M x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hi
      x.rep.H x.rep.π x.rep.isIrr (Ws j) (σs j) (hIrr.1 j) (hIrr.2.1 j) hj).1 (UEquiv.refl _)
    exact (hIrr.2.2 i j hne).false e.some
  ·
    intro x y i hx hy
    have e := (_root_.GlobalTheory.AutMult.isUnitEquiv_iff_nonempty_equiv_of_isCopyFinDS D V S M x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hx
      y.rep.H y.rep.π y.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hy).2 ⟨Representation.Equiv.refl _⟩
    rw [← UDual.cl_rep x, ← UDual.cl_rep y]
    exact IrrU.cl_eq_iff.2 e

end GlobalTheory.SpecTraceProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticInjectivePlaneCoordinates
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagr

theorem le_finrank_lagr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁),
    Module.finrank F E = 2 → d = d₁ + 2 → form σ W.J H'.x H'.y = 1 → (∀ u, form σ W.J (H'.ι *ᵥ u) H'.y = 0) →
    (Function.Injective fun z : Matrix (Fin n) (Fin d₁) E => z * H'.ιᵀ) →
    ∀ f : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F),
      Function.Injective f → (∀ x, hat (f x) = M.co.e (incM F x)) →
    ∀ K : Submodule F (Matrix (Fin n) (Fin d₁) E), Module.finrank F K = n * d₁ → (∀ z ∈ K, (M₁.co.e (incM F z)).1 = 0) →
      n * d ≤ Module.finrank F (lagr M M₁ H') := by
  intro F E _ _ _ _ _ σ n d d₁ X W W₁ M M₁ H' hE hd hxy hιy hι f hf hfe K hK hK0
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)

  let Φ : (Fin n → E) × K →ₗ[F] Matrix (Fin n) (Fin d) E :=
    { toFun := fun p => Matrix.vecMulVec p.1 H'.x + (p.2 : Matrix (Fin n) (Fin d₁) E) * H'.ιᵀ
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.add_vecMulVec, Matrix.add_mul]; abel
      map_smul' := fun c p => by
        ext i j
        simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Finset.smul_sum, smul_mul_assoc, smul_add] }
  have hΦ : ∀ p, Φ p = Matrix.vecMulVec p.1 H'.x + (p.2 : Matrix (Fin n) (Fin d₁) E) * H'.ιᵀ := fun _ => rfl
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [incM]
    · simp [incM, Matrix.one_apply, h]
  have hmem : ∀ p, f (Φ p) ∈ lagr M M₁ H' := by
    intro p
    rw [mem_lagr, hfe, LinearEquiv.symm_apply_apply]
    refine ⟨Matrix.vecMulVec (incV F p.1) (incV F H'.x), ⟨incV F p.1, rfl⟩, incM F (p.2 : Matrix (Fin n) (Fin d₁) E),
      hK0 _ p.2.2, ?_⟩
    rw [h1, Matrix.one_mul, hΦ]
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [incM, incV, Matrix.vecMulVec_apply, Matrix.mul_apply, map_sum, map_mul]
  have hform : ∀ (a : E) (u v : Fin d → E), form σ W.J (a • u + v) H'.y = a * form σ W.J u H'.y + form σ W.J v H'.y := by
    intro a u v
    simp [form, add_dotProduct, smul_dotProduct]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hΦ] at hp
    have hrow : ∀ i, (p.1 i) • H'.x + H'.ι *ᵥ ((p.2 : Matrix (Fin n) (Fin d₁) E) i) = 0 := by
      intro i
      funext j
      have := congrFun (congrFun hp i) j
      simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.zero_apply] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← this]
      congr 1
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hy : p.1 = 0 := by
      funext i
      have : form σ W.J ((p.1 i) • H'.x + H'.ι *ᵥ ((p.2 : Matrix (Fin n) (Fin d₁) E) i)) H'.y = form σ W.J 0 H'.y := by
        rw [hrow i]
      rw [hform, hxy, hιy] at this
      simpa [form] using this
    have hz : (p.2 : Matrix (Fin n) (Fin d₁) E) = 0 := by
      apply hι
      simp only
      rw [Matrix.zero_mul, ← hp, hy, Matrix.zero_vecMulVec, zero_add]
    exact Prod.ext hy (Subtype.ext hz)
  let g := (f ∘ₗ Φ).codRestrict (lagr M M₁ H') hmem
  have hg : Function.Injective g := by
    intro p q h
    apply hinj; apply hf
    simpa [g] using congrArg Subtype.val h
  have hle := LinearMap.finrank_le_finrank_of_injective hg
  have hdom : Module.finrank F ((Fin n → E) × K) = n * d := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype, hK]
    simp [hE, hd]
    ring
  omega

end GlobalTheory.MixedLagr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLagrangianSubspaceExists
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.MixedLagr

theorem rat_first_zero_dim : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W), Module.finrank F E = 2 →
    ∀ f : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F),
      Function.Injective f → (∀ x, hat (f x) = M.co.e (incM F x)) →
      ∃ K : Submodule F (Matrix (Fin n) (Fin d) E), Module.finrank F K = n * d ∧ ∀ z ∈ K, (M.co.e (incM F z)).1 = 0 := by
  intro F E _ _ _ _ _ σ n d X W M hE f hf hhat
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hdom : Module.finrank F (Matrix (Fin n) (Fin d) E) = n * d * 2 := by
    rw [Module.finrank_matrix, hE]; simp
  have hcod : Module.finrank F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) = n * d * 2 := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]; simp; ring
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hdom.trans hcod.symm)).mp hf
  set g := (LinearMap.fst F (Fin n × Fin d → F) (Fin n × Fin d → F)).comp f with hg
  have gsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hsurj (y, 0)
    exact ⟨x, by simp [hg, hx]⟩
  refine ⟨LinearMap.ker g, ?_, ?_⟩
  · have h1 := LinearMap.finrank_range_add_finrank_ker g
    rw [LinearMap.range_eq_top.mpr gsurj, finrank_top, Module.finrank_fintype_fun_eq_card, hdom] at h1
    simp at h1
    have : Fintype.card (Fin n × Fin d) = n * d := by simp
    omega
  · intro z hz
    rw [LinearMap.mem_ker] at hz
    rw [← hhat z]
    have hz' : (f z).1 = 0 := by simpa [hg] using hz
    funext i
    simp [hat, hz']

end GlobalTheory.MixedLagr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalModelCoordinates
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagr

theorem ratCoord_linear_injective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      M.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ f : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F),
      Function.Injective f ∧ ∀ x, hat (f x) = M.co.e (incM F x) := by
  intro F E _ _ _ _ _ σ n d X W M h
  choose y z hyz using h
  have hA : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective (𝓞 F) F
  have hg : ∀ x, hat ((y x, z x) : (Fin n × Fin d → F) × (Fin n × Fin d → F)) = M.co.e (incM F x) :=
    fun x => (hyz x).symm
  have hinj : Function.Injective (hat : (Fin n × Fin d → F) × (Fin n × Fin d → F) → _) := by
    intro a b hab
    simp only [hat, Prod.mk.injEq] at hab
    exact Prod.ext (funext fun i => hA (congrFun hab.1 i)) (funext fun i => hA (congrFun hab.2 i))
  have hadd : ∀ x x' : Matrix (Fin n) (Fin d) E, incM F (x + x') = incM F x + incM F x' := by
    intro x x'
    ext i j
    simp [incM, Matrix.map_apply, map_add (f := _)]
  have hsmul : ∀ (c : F) (x : Matrix (Fin n) (Fin d) E), incM F (c • x) = algebraMap F (AF F) c • incM F x := by
    intro c x
    ext i j
    simp only [incM, Matrix.map_apply, Matrix.smul_apply]
    show (Algebra.TensorProduct.includeRight : E →ₐ[F] _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (c • x i j) =
      algebraMap F (AF F) c • (Algebra.TensorProduct.includeRight : E →ₐ[F] _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (x i j)
    rw [map_smul, algebraMap_smul]
  have hI : Function.Injective (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    Matrix.map_injective (Algebra.TensorProduct.includeRight_injective hA)
  refine ⟨{ toFun := fun x => (y x, z x), map_add' := ?_, map_smul' := ?_ }, ?_, hg⟩
  · intro x x'
    apply hinj
    rw [hat_add, hg, hg, hg, hadd, map_add (f := _)]
  · intro c x
    apply hinj
    rw [RingHom.id_apply, hat_smul, hg, hg, hsmul, LinearEquiv.map_smul]
  · intro x x' hx
    apply hI
    apply M.co.e.injective
    rw [← hg, ← hg]
    exact congrArg hat hx

end GlobalTheory.MixedLagr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineContinuous
section
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff

namespace GlobalTheory.RealLineCont

theorem continuous_of_isRealLine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (γ : ℝ → GAd σ J), IsRealLine σ J γ → Continuous γ := by
  intro F E _ _ _ _ _ σ h n J γ ⟨w, τ, Z, _, hy⟩
  choose y hγ hy using hy
  have hc : Continuous y := by
    rw [(GlobalTheory.Orb.isEmbedding_archMat J h τ).continuous_iff]
    have e : (GlobalTheory.Orb.matCoord (GlobalTheory.Orb.archMat σ J τ) ∘ y) = fun t i j => NormedSpace.exp (t • Z) i j := by
      funext t i j; simp only [Function.comp_apply, GlobalTheory.Orb.matCoord, hy t]
    rw [e]
    have hexp : Continuous fun t : ℝ => NormedSpace.exp (t • Z) := by
      letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
      letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
      exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
    exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply i).comp hexp)
  have : γ = fun t => embArch σ J w (y t) := funext hγ
  rw [this]
  exact (continuous_embArch σ J w).comp hc

end GlobalTheory.RealLineCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineMemInfPoints
section
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.RealLineInf

theorem realLine_mem_infPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (β : ℝ → GAd σ J), IsRealLine σ J β → ∀ t, β t ∈ infPts σ J := by
  intro F E _ _ _ _ _ σ n J β hβ t
  obtain ⟨w, τ, Z, -, h⟩ := hβ
  obtain ⟨y, hy, -⟩ := h t
  rw [hy]
  exact mem_infPts.2 (projFin_embArch σ J w y)

end GlobalTheory.RealLineInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceComponentAdeleConjugationEqComplexConjStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceComponent_adeleConjugation_eq_complexConj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), piInf τ (cA σ z) = star (piInf τ z) := by
  first | exact @GlobalTheory.RealPlaceConj.piInf_cA_eq_star | exact GlobalTheory.RealPlaceConj.piInf_cA_eq_star | (intros; apply GlobalTheory.RealPlaceConj.piInf_cA_eq_star <;> assumption)
end

