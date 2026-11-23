module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0101
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0779
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0075
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinalAll
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Formalism.FormalDegreeBessel.StatementIO
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardResidueFieldOfRingEquivAdicCompletion
section
open ValuativeRel NumberField IsDedekindDomain

namespace GlobalTheory.LocalResidue

theorem card_residue_of_ringEquiv : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → Nat.card 𝓀[k] = Ideal.absNorm v.asIdeal := by
  intro F _ _ v k _ _ _ _ φ hφ
  let ψ : 𝒪[k] ≃+* v.adicCompletionIntegers F :=
    { toFun := fun a => ⟨φ a, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ((hφ a).2 a.2)⟩
      invFun := fun b => ⟨φ.symm b, (hφ _).1 (by
        rw [RingEquiv.apply_symm_apply]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 b.2)⟩
      left_inv := fun a => Subtype.ext (φ.symm_apply_apply a)
      right_inv := fun b => Subtype.ext (φ.apply_symm_apply b)
      map_mul' := fun a b => Subtype.ext (map_mul φ (a : k) (b : k))
      map_add' := fun a b => Subtype.ext (map_add φ (a : k) (b : k)) }
  have e := IsLocalRing.ResidueField.mapEquiv ψ
  have hF : ∀ s : 𝓞 F, Valued.v (algebraMap F (v.adicCompletion F) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  have hc := GlobalTheory.SplitUnif.card_residueField v (algebraMap F (v.adicCompletion F)) v (fun _ => rfl) fun s => by
    rw [hF, HeightOneSpectrum.intValuation_lt_one_iff_mem]
  rw [Nat.card_congr e.toEquiv, hc]

end GlobalTheory.LocalResidue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DenseKFiniteVectorsUnitaryGroupRep
section
open scoped InnerProductSpace

namespace GlobalTheory.CompactRep

theorem dense_finite_vectors (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [SecondCountableTopology K] (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : K →* H →L[ℂ] H)
    (hiso : ∀ k x, ‖π k x‖ = ‖x‖) (hcont : ∀ x, Continuous fun k => π k x) :
    Dense {v : H | ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧
      ∀ k, ∀ x ∈ S, π k x ∈ S} := by
  let N : Submodule ℂ H :=
    { carrier := {v : H | ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧
        ∀ k, ∀ x ∈ S, π k x ∈ S}
      add_mem' := by
        rintro a b ⟨S, hS, ha, hSs⟩ ⟨T, hT, hb, hTs⟩
        refine ⟨S ⊔ T, inferInstance, Submodule.add_mem_sup ha hb, ?_⟩
        intro k x hx
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
        rw [map_add (f := _)]
        exact Submodule.add_mem_sup (hSs k y hy) (hTs k z hz)
      zero_mem' := ⟨⊥, inferInstance, Submodule.zero_mem _, by
        intro k x hx
        rw [Submodule.mem_bot] at hx ⊢
        rw [hx, map_zero]⟩
      smul_mem' := by
        rintro c a ⟨S, hS, ha, hSs⟩
        exact ⟨S, hS, S.smul_mem c ha, hSs⟩ }
  have hNst : ∀ k, ∀ a ∈ N, π k a ∈ N := by
    rintro k a ⟨S, hS, ha, hSs⟩
    exact ⟨S, hS, hSs k a ha, hSs⟩
  have hinner : ∀ k a b, ⟪π k a, π k b⟫_ℂ = ⟪a, b⟫_ℂ := fun k a b =>
    (LinearIsometry.mk (π k).toLinearMap (hiso k)).inner_map_map a b
  have hinv : ∀ k a, π k (π k⁻¹ a) = a := by
    intro k a
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  have hOst : ∀ k, ∀ w ∈ Nᗮ, π k w ∈ Nᗮ := by
    intro k w hw
    rw [Submodule.mem_orthogonal] at hw ⊢
    intro a ha
    rw [← hinv k a, hinner]
    exact hw _ (hNst _ a ha)
  have hbot : Nᗮ = ⊥ := by
    by_contra hne
    haveI : Nontrivial Nᗮ := Submodule.nontrivial_iff_ne_bot.2 hne
    let ρ : K →* (Nᗮ →L[ℂ] Nᗮ) :=
      { toFun := fun k => ((π k).comp Nᗮ.subtypeL).codRestrict Nᗮ (fun w => hOst k w w.2)
        map_one' := by
          ext w
          simp
        map_mul' := by
          intro k l
          ext w
          show π (k * l) w = π k (π l w)
          rw [map_mul, ContinuousLinearMap.mul_apply] }
    have hρ : ∀ k (w : Nᗮ), ((ρ k w : Nᗮ) : H) = π k w := fun k w => rfl
    obtain ⟨S, hS0, hSf, hSs⟩ := exists_finiteDimensional_invariant K Nᗮ ρ
      (fun k w => hiso k w) (fun w => (hcont w).subtype_mk _)
    apply hS0
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hwN : (w : H) ∈ N := by
      refine ⟨S.map Nᗮ.subtype, inferInstance, ⟨w, hw, rfl⟩, ?_⟩
      rintro k x ⟨y, hy, rfl⟩
      exact ⟨ρ k y, hSs k y hy, rfl⟩
    have h0 : ⟪(w : H), (w : H)⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 w.2 _ hwN
    exact Subtype.ext (inner_self_eq_zero.1 h0)
  exact Submodule.dense_iff_topologicalClosure_eq_top.2
    (Submodule.topologicalClosure_eq_top_iff.2 hbot)

theorem dense_isKFin (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) : Dense {v : H | Formalism.MainNotions.S.IsKFin ε σ v} := by
  obtain ⟨⟨h1, hmul⟩, hiso, hcont⟩ := hσ
  have hemb : Topology.IsEmbedding (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Formalism.REAL.KG ε) := hemb.secondCountableTopology
  have hU : ∀ k : Formalism.REAL.KG ε, Formalism.REAL.toMK k ∈ Formalism.MainNotions.S.UJset ε := fun k => k.1.2
  let π : Formalism.REAL.KG ε →* (H →L[ℂ] H) :=
    { toFun := fun k => σ (Formalism.REAL.toMK k)
      map_one' := h1
      map_mul' := fun k l => hmul _ (hU k) _ (hU l) }
  have hd := dense_finite_vectors (Formalism.REAL.KG ε) H π (fun k x => hiso _ (hU k) x)
    (fun x => (hcont x).comp_continuous hemb.continuous hU)
  refine hd.mono ?_
  rintro v ⟨S, hS, hv, hSs⟩
  refine ⟨S, hS, hv, ?_⟩
  intro g hg x hx
  rw [← Formalism.REAL.range_toMK] at hg
  obtain ⟨k, rfl⟩ := hg
  exact hSs k x hx

end GlobalTheory.CompactRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstCoupledKernelFiniteDatumLevelSize
section
noncomputable section

namespace GlobalTheory.Core.Ht2.DatOneS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem smallDatum_xiCpl1_sharp : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (al : I.β (N.R.m - 2)) (p₀ : ChPt (R := N.R) sel mu u (N.R.m - 2)) (p : ChPt (R := N.R) sel mu u (N.R.m - 2 + 1)) (Y : Set (Sp X.E (N.R.N (N.R.m - 2 + 1)))), SmallDatum (Sall sel mu u) p₀.deco.1.N p.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiCpl1 Ch sel mu cst I (N.R.m - 2) al p₀ p Y) 1 := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hH al p₀ p Y
  obtain ⟨hrow, hG, hT, -⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hH
  have hI : I.Ok Ch sel mu cst G (N.R.m - 2) := hH.2.2.2.2.2.2.1
  have hfr : ∀ {j : ℕ} (r : ChPt (R := N.R) sel mu u j) (P : rowSG Pr sel mu) x,
      frsF sel mu r P x ∈ r.deco.1.at P.1 ↔ x ∈ stdAt X.E (N.R.N j) P.1 := by
    intro j r P x
    have hP := hrow P.1 P.2
    simp only [frsF, hP, dif_pos]
    exact (GlobalTheory.ColNorms.liftFr_lifts X.E _ _ _ r.deco ⟨P.1, hP⟩).1 x
  have key := @GlobalTheory.ColNorms.DatOne.smallDatum_of_frames X.E X.K _ _ _ _ _ _ (Pr.vT u) _ _ (rowSG Pr sel mu) (fun a b => Classical.propDecidable (a = b))
    p₀.deco.1 p.deco (frsF sel mu p₀) (frsF sel mu p) (hfr p₀) (hfr p) (Pr.T u * (Pr.g 0 * Pr.g 1))
    (fun P => Formalism.L2.Col.qOf P.1) ?_ ?_
    (fun P x => PsiAt Ch sel mu cst (N.R.m - 2) P (I.h (N.R.m - 2) al P) x ((frsF sel mu p P).symm (repY Y))) (fun _ => 1) ?_
  · rw [Finset.prod_const_one] at key
    exact key
  · intro P
    obtain ⟨i, -, hq, -⟩ := hG P.1 (hrow P.1 P.2)
    show Formalism.L2.Col.qOf P.1 ∣ _
    rw [hq]
    refine Dvd.dvd.mul_left ?_ _
    fin_cases i
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  · intro P hP
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hT P hP)
  · intro P
    have hm := hI.hm
    have h := GlobalTheory.T.movedDatum_small_typePrime_any_level CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hH (N.R.m - 2) (by omega) P
      (I.h (N.R.m - 2) al P) 1 (hI.stabG _ al P (hrow P.1 P.2)) (one_mem _)
    exact GlobalTheory.ColNorms.DatOne.locSmall_joinCol h _

end GlobalTheory.Core.Ht2.DatOneS

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IrreducibleKStableFiniteSubspace
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
open scoped InnerProductSpace

namespace GlobalTheory.AdmUnitary

theorem admissible_and_kFin_smooth : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S → ∀ v ∈ S, ∃ Y : Submodule ℂ H, FiniteDimensional ℂ Y ∧ v ∈ Y ∧ ∀ B : H →L[ℂ] H, (∀ k ∈ Formalism.REAL.Kset ε, ∀ u, B (σ k u) = σ k (B u)) → ∀ y ∈ Y, B y ∈ Y) ∧ ∀ v, IsKFin ε σ v → Formalism.QuantumDeterminants.SmoothOnH (Formalism.REAL.Jm ε) (fun g => σ g v) := by
  intro n ε H _ _ _ σ hσ hirr
  refine ⟨fun S hS hst v hv => ?_, fun v hv => CompanionTheory.D.gk.admitted.kFin_smooth n ε H σ hσ hirr v hv⟩
  obtain ⟨Y, hY, -, hvY, hT⟩ := CompanionTheory.D.gk.admitted.unitary_group_admissible n ε H σ hσ hirr S hst v hv
  exact ⟨Y, hY, hvY, hT⟩

end GlobalTheory.AdmUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFlagUnipotentFiniteAdelesIffFrameUnipotentRadi
section
open Matrix NumberField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UnipFin

open Formalism.L2.SG.HidaSetting

theorem mem_span_image_iff {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (v : ι → M) (s : Set ι) (w : M) :
    w ∈ Submodule.span R (v '' s) ↔ ∃ f : ι → R, (∀ i, i ∉ s → f i = 0) ∧ ∑ i, f i • v i = w := by
  rw [Finsupp.mem_span_image_iff_linearCombination]
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l, fun i hi => (Finsupp.mem_supported' R l).1 hl i hi, ?_⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; exact zero_smul R _
  · rintro ⟨f, hf, rfl⟩
    refine ⟨Finsupp.equivFunOnFinite.symm f, (Finsupp.mem_supported' R _).2 fun i hi => hf i hi, ?_⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    · rfl
    · intro i; exact zero_smul R _

variable (I : Formalism.MainNotions.S.AutInst)

theorem sigR_inclE (e : I.E) :
    Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F) (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (starRingEnd I.E e) := by
  show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Formalism.MainNotions.S.Af I.F)) (e ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F)) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem hA_incl_incl (p q : Fin I.n → I.E) :
    hA I (incl I p) (incl I q) =
      Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J p q) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hA, Formalism.UG.hform, incl, Matrix.map_apply, map_sum, map_mul, sigR_inclE]

variable {I} {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E)

theorem mulVec_flag (v : Fin ρ → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :
    (Matrix.of fun k a => c a * x a k).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) *ᵥ v =
      ∑ a, (v a * Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (c a)) • incl I (x a) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, incl, map_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem mulVec_dual (y : VA I) (a : Fin ρ) :
    ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map
      (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) *ᵥ y) a =
      Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (starRingEnd I.E (c a)) * hA I (incl I (x a)) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply,
    Matrix.of_apply, map_sum, map_mul, hA, Formalism.UG.hform, incl, sigR_inclE, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem unip_flag_iff_Nfin : ∀ (I : Formalism.MainNotions.S.AutInst) {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E) (z : Fin I.n → I.E), (∀ a, c a ≠ 0) → (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (x a) z = 0) → ∀ (N : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), GlobalTheory.BesselChar.Unip ((Matrix.of fun k a => c a * x a k).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))) ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))) N ↔ ((∀ a : Fin ρ, (N - 1) *ᵥ Formalism.L2.SG.HidaSetting.incl I (x a) ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ((fun b => Formalism.L2.SG.HidaSetting.incl I (x b)) '' {b | b.1 < a.1})) ∧ (N - 1) *ᵥ Formalism.L2.SG.HidaSetting.incl I z ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => Formalism.L2.SG.HidaSetting.incl I (x b)) ∧ ∀ y : Formalism.L2.SG.HidaSetting.VA I, (∀ a, Formalism.L2.SG.HidaSetting.hA I (Formalism.L2.SG.HidaSetting.incl I (x a)) y = 0) → (N - 1) *ᵥ y ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => Formalism.L2.SG.HidaSetting.incl I (x b))) := by
  intro I ρ x c z hc hz N

  let EA := (Matrix.of fun k a => c a * x a k).map (Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F))
  let w : Fin ρ → VA I := fun a => incl I (x a)
  have hcol : ∀ a, (fun k => EA k a) = Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) • w a := by
    intro a; funext k
    simp only [EA, w, Matrix.map_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, incl, map_mul]
  have hinv : ∀ a, Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) = 1 := fun a => by
    rw [← map_mul, inv_mul_cancel₀ (hc a), map_one]
  have hinv' : ∀ a, Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ = 1 := fun a => by
    rw [← map_mul, mul_inv_cancel₀ (hc a), map_one]

  have hK : ∀ y : VA I, (Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F)) *ᵥ y = 0 ↔
      ∀ a, hA I (incl I (x a)) y = 0 := by
    intro y
    constructor
    · intro h a
      have hs : starRingEnd I.E (c a) ≠ 0 := (map_ne_zero _).2 (hc a)
      have h1 := congrFun h a
      rw [mulVec_dual] at h1
      calc hA I (incl I (x a)) y
          = Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (starRingEnd I.E (c a))⁻¹ * (Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (starRingEnd I.E (c a)) * hA I (incl I (x a)) y) := by
            rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hs, map_one, one_mul]
        _ = 0 := by rw [h1, Pi.zero_apply, mul_zero]
    · intro h
      funext a
      rw [mulVec_dual, h a, mul_zero, Pi.zero_apply]

  have hspan : ∀ y : VA I, (∃ v, N *ᵥ y = y + EA *ᵥ v) ↔
      (N - 1) *ᵥ y ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range w) := by
    intro y
    rw [Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨fun a => v a * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a), ?_⟩
      rw [← mulVec_flag, Matrix.sub_mulVec, hv, Matrix.one_mulVec]
      abel
    · rintro ⟨f, hf⟩
      refine ⟨fun a => f a * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹, ?_⟩
      rw [mulVec_flag]
      simp_rw [mul_assoc, hinv, mul_one]
      rw [hf, Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
  constructor
  · rintro ⟨⟨T, hT, hNT⟩, h2⟩
    have hdual : ∀ y : VA I, (∀ a, hA I (incl I (x a)) y = 0) →
        (N - 1) *ᵥ y ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range w) :=
      fun y hy => (hspan y).1 (h2 y ((hK y).2 hy))
    refine ⟨fun a => ?_, hdual _ fun a => by rw [hA_incl_incl, hz a, map_zero], hdual⟩
    have hv : N *ᵥ (fun k => EA k a) = (fun k => EA k a) + EA *ᵥ (fun b => T b a) :=
      funext fun k => congrFun (congrFun hNT k) a
    rw [hcol, Matrix.mulVec_smul, mulVec_flag] at hv
    have hw : (N - 1) *ᵥ w a = ∑ b, (Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ * (T b a * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c b))) • w b := by
      have := congrArg (fun v => Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ • v) hv
      simp only [smul_add, smul_smul, hinv, one_smul, Finset.smul_sum] at this
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, this]
      abel
    refine (mem_span_image_iff w _ _).2 ⟨fun b => Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ * (T b a * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c b)), fun b hb => ?_, hw.symm⟩
    show _ * (T b a * _) = 0
    rw [hT b a (not_lt.1 hb), zero_mul, mul_zero]
  · rintro ⟨h1, -, h3⟩
    choose f hf0 hfs using fun a => (mem_span_image_iff w _ _).1 (h1 a)
    refine ⟨⟨fun b a => Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) * f a b * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c b)⁻¹, fun j i hij => ?_, ?_⟩, fun y hy => ?_⟩
    · show _ * f i j * _ = 0
      rw [hf0 i j (not_lt.2 hij), mul_zero, zero_mul]
    · ext k a
      suffices hv : N *ᵥ (fun k => EA k a) =
          (fun k => EA k a) + EA *ᵥ (fun b => Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) * f a b * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c b)⁻¹) from congrFun hv k
      rw [hcol, Matrix.mulVec_smul, mulVec_flag]
      simp_rw [mul_assoc, hinv, mul_one]
      have hN : N *ᵥ w a = w a + (N - 1) *ᵥ w a := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
      rw [hN, ← hfs a, smul_add, Finset.smul_sum]
      simp_rw [smul_smul]
      rfl
    · exact (hspan y).2 (h3 y ((hK y).1 hy))

end GlobalTheory.UnipFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFlagUnipotentMatrixIffJointlyBijectivePair
section
open Matrix

namespace GlobalTheory.BesselChar.JointSplit

variable {A R₁ R₂ : Type} [CommRing A] [CommRing R₁] [CommRing R₂]

theorem fwd (f : A →+* R₁) (g : A →+* R₂) (hinj : ∀ y, f y = 0 → g y = 0 → y = 0)
    (hsurj : ∀ a b, ∃ y, f y = a ∧ g y = b) {n ρ : ℕ} (E : Matrix (Fin n) (Fin ρ) A)
    (K : Matrix (Fin ρ) (Fin n) A) (M : Matrix (Fin n) (Fin n) A) (h : GlobalTheory.BesselChar.Unip E K M) :
    GlobalTheory.BesselChar.Unip (E.map f) (K.map f) (M.map f) := by
  obtain ⟨⟨T, hT, hMT⟩, h2⟩ := h
  refine ⟨⟨T.map f, fun j i hij => by simp [hT j i hij], ?_⟩, fun y₁ hy₁ => ?_⟩
  · rw [← Matrix.map_mul, hMT, Matrix.map_add _ (map_add f), Matrix.map_mul]
  · choose l hl1 hl2 using hsurj
    obtain ⟨y, hfy, hgy⟩ : ∃ y : Fin n → A, (fun i => f (y i)) = y₁ ∧ (fun i => g (y i)) = 0 :=
      ⟨fun i => l (y₁ i) 0, funext fun i => hl1 _ _, funext fun i => hl2 _ _⟩
    have hKy : K *ᵥ y = 0 := by
      funext i
      apply hinj
      · have := congrFun (GlobalTheory.BesselChar.mulVec_map f K y) i
        rw [hfy, hy₁] at this
        exact this.symm
      · have := congrFun (GlobalTheory.BesselChar.mulVec_map g K y) i
        rw [hgy, Matrix.mulVec_zero] at this
        exact this.symm
    obtain ⟨a, ha⟩ := h2 y hKy
    refine ⟨fun i => f (a i), ?_⟩
    subst hfy
    rw [GlobalTheory.BesselChar.mulVec_map, GlobalTheory.BesselChar.mulVec_map, ha]
    funext i
    simp only [Pi.add_apply, map_add (f := _)]

theorem bwd (f : A →+* R₁) (g : A →+* R₂) (hinj : ∀ y, f y = 0 → g y = 0 → y = 0)
    (hsurj : ∀ a b, ∃ y, f y = a ∧ g y = b) {n ρ : ℕ} (E : Matrix (Fin n) (Fin ρ) A)
    (K : Matrix (Fin ρ) (Fin n) A) (M : Matrix (Fin n) (Fin n) A)
    (h1 : GlobalTheory.BesselChar.Unip (E.map f) (K.map f) (M.map f))
    (h2 : GlobalTheory.BesselChar.Unip (E.map g) (K.map g) (M.map g)) : GlobalTheory.BesselChar.Unip E K M := by
  choose l hl1 hl2 using hsurj
  have l00 : l 0 0 = 0 := hinj _ (hl1 0 0) (hl2 0 0)
  have extM : ∀ {p q : ℕ} (X Y : Matrix (Fin p) (Fin q) A), X.map f = Y.map f → X.map g = Y.map g → X = Y := by
    intro p q X Y hf hg
    ext i j
    rw [← sub_eq_zero]
    apply hinj
    · rw [map_sub, sub_eq_zero]; exact congrFun (congrFun hf i) j
    · rw [map_sub, sub_eq_zero]; exact congrFun (congrFun hg i) j
  have extV : ∀ {p : ℕ} (x z : Fin p → A), (fun i => f (x i)) = (fun i => f (z i)) →
      (fun i => g (x i)) = (fun i => g (z i)) → x = z := by
    intro p x z hf hg
    funext i
    rw [← sub_eq_zero]
    apply hinj
    · rw [map_sub, sub_eq_zero]; exact congrFun hf i
    · rw [map_sub, sub_eq_zero]; exact congrFun hg i
  obtain ⟨⟨T₁, hT₁, e₁⟩, k₁⟩ := h1
  obtain ⟨⟨T₂, hT₂, e₂⟩, k₂⟩ := h2
  let T : Matrix (Fin ρ) (Fin ρ) A := Matrix.of fun i j => l (T₁ i j) (T₂ i j)
  have hTf : T.map f = T₁ := by ext i j; exact hl1 _ _
  have hTg : T.map g = T₂ := by ext i j; exact hl2 _ _
  refine ⟨⟨T, fun j i hij => ?_, ?_⟩, fun y hy => ?_⟩
  · show l (T₁ j i) (T₂ j i) = 0
    rw [hT₁ j i hij, hT₂ j i hij, l00]
  · apply extM
    · rw [Matrix.map_mul, Matrix.map_add _ (map_add f), Matrix.map_mul, hTf, e₁]
    · rw [Matrix.map_mul, Matrix.map_add _ (map_add g), Matrix.map_mul, hTg, e₂]
  · have hy₁ : K.map f *ᵥ (fun i => f (y i)) = 0 := by
      rw [GlobalTheory.BesselChar.mulVec_map, hy]; funext i; exact map_zero f
    have hy₂ : K.map g *ᵥ (fun i => g (y i)) = 0 := by
      rw [GlobalTheory.BesselChar.mulVec_map, hy]; funext i; exact map_zero g
    obtain ⟨a₁, ha₁⟩ := k₁ _ hy₁
    obtain ⟨a₂, ha₂⟩ := k₂ _ hy₂
    have ea₁ : (fun i => f (l (a₁ i) (a₂ i))) = a₁ := funext fun i => hl1 _ _
    have ea₂ : (fun i => g (l (a₁ i) (a₂ i))) = a₂ := funext fun i => hl2 _ _
    refine ⟨fun i => l (a₁ i) (a₂ i), extV _ _ ?_ ?_⟩
    · rw [← GlobalTheory.BesselChar.mulVec_map, ha₁]
      conv_lhs => rw [← ea₁, GlobalTheory.BesselChar.mulVec_map]
      funext i
      simp only [Pi.add_apply, map_add (f := _)]
    · rw [← GlobalTheory.BesselChar.mulVec_map, ha₂]
      conv_lhs => rw [← ea₂, GlobalTheory.BesselChar.mulVec_map]
      funext i
      simp only [Pi.add_apply, map_add (f := _)]

theorem unip_iff_of_joint : ∀ {A R₁ R₂ : Type} [CommRing A] [CommRing R₁] [CommRing R₂] (f : A →+* R₁) (g : A →+* R₂), (∀ y, f y = 0 → g y = 0 → y = 0) → (∀ a b, ∃ y, f y = a ∧ g y = b) → ∀ {n ρ : ℕ} (E : Matrix (Fin n) (Fin ρ) A) (K : Matrix (Fin ρ) (Fin n) A) (M : Matrix (Fin n) (Fin n) A), GlobalTheory.BesselChar.Unip E K M ↔ GlobalTheory.BesselChar.Unip (E.map f) (K.map f) (M.map f) ∧ GlobalTheory.BesselChar.Unip (E.map g) (K.map g) (M.map g) := by
  intro A R₁ R₂ _ _ _ f g hinj hsurj n ρ E K M
  refine ⟨fun h => ⟨fwd f g hinj hsurj E K M h, fwd g f (fun y hg hf => hinj y hf hg)
    (fun a b => (hsurj b a).imp fun _ h => h.symm) E K M h⟩, fun h => bwd f g hinj hsurj E K M h.1 h.2⟩

end GlobalTheory.BesselChar.JointSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KStableSubmoduleEqTopOfHighestWeightLe
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
open scoped InnerProductSpace

namespace GlobalTheory.HwSpan

theorem eq_top_of_hwSub_le : ∀ (p q : ℕ) (M : GKMod p q) (N : Submodule ℂ M.V), KStable M.act N →
    (∀ μ, hwSub M.act μ ≤ N) → N = ⊤ := by
  intro p q M N hN hhw
  have hL : Formalism.MainNotions.SchurIrreducible.IsKLieAct M.act := fun X Y _ _ => M.lie X Y
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨W, hfd, hvW, hW⟩ := M.kfin v
  have hle : W ≤ N := GlobalTheory.BlockReps.le_of_hw hL hW (fun x _ => M.wts x) hN
    (fun μ x _ hx => hhw μ hx.2)
  exact hle hvW

end GlobalTheory.HwSpan
end

