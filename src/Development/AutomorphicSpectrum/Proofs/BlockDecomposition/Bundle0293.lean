module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineFormsOfFormUniqueness
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import GroundTheory.AutomorphicForms.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0285
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulMPull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0286
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicDegreeFormula
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegAdelicProof

theorem exists_leftInv {K : Type} [Field K] {n k : ℕ} (M : Matrix (Fin n) (Fin k) K)
    (h : LinearIndependent K Mᵀ) : ∃ L : Matrix (Fin k) (Fin n) K, L * M = 1 := by
  have hinj : Function.Injective M.mulVec := Matrix.mulVec_injective_iff.2 h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective M.mulVecLin (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 : LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' M) = 1 := by
    rw [Matrix.toLin'_apply', hg, LinearMap.toMatrix'_id]
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at h1

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n k : ℕ}

theorem frame_mul (x t : GA E n) (s : GA E k) (M : Matrix (Fin n) (Fin k) E)
    (h : t.val * M.map (algebraMap E (Ad E)) = M.map (algebraMap E (Ad E)) * s.val) :
    frame (t * x) M = frame x M * (s⁻¹ : GA E k).val := by
  have h' : (t⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)) =
      M.map (algebraMap E (Ad E)) * (s⁻¹ : GA E k).val := by
    calc (t⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))
        = (t⁻¹ : GA E n).val * (M.map (algebraMap E (Ad E)) * (s.val * (s⁻¹ : GA E k).val)) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = (t⁻¹ : GA E n).val * (t.val * M.map (algebraMap E (Ad E))) * (s⁻¹ : GA E k).val := by
          rw [h, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = M.map (algebraMap E (Ad E)) * (s⁻¹ : GA E k).val := by
          rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  unfold frame
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, h', Matrix.mul_assoc]

theorem lognInf_mul (hI : MulI) (v : InfinitePlace E) (A : Matrix (Fin n) (Fin k) (Ad E))
    (S : Matrix (Fin k) (Fin k) (Ad E)) (hA : nI (A.map (cV v)) ≠ 0) (hS : IsUnit S.det) :
    lognInf v (A * S) = lognInf v A + Real.log (‖cV v S.det‖ ^ 2) := by
  have hd : (S.map (cV v)).det = cV v S.det := (RingHom.map_det (cV v) S).symm
  have h0 : cV v S.det ≠ 0 := (hS.map (cV v)).ne_zero
  change Real.log (nI ((A * S).map (cV v))) = Real.log (nI (A.map (cV v))) + _
  rw [Matrix.map_mul, (hI (Fin n) (Fin n) (Fin k) _).2.1, hd,
    Real.log_mul hA (pow_ne_zero 2 (norm_ne_zero_iff.2 h0))]

theorem lognFin_mul (hF : MulF) (w : HeightOneSpectrum (𝓞 E)) (A : Matrix (Fin n) (Fin k) (Ad E))
    (S : Matrix (Fin k) (Fin k) (Ad E)) (hA : nF (A.map (cW w)) ≠ 0) (hS : IsUnit S.det) :
    lognFin w (A * S) = lognFin w A + Real.log ‖cW w S.det‖ := by
  have hd : (S.map (cW w)).det = cW w S.det := (RingHom.map_det (cW w) S).symm
  have h0 : cW w S.det ≠ 0 := (hS.map (cW w)).ne_zero
  change Real.log (nF ((A * S).map (cW w))) = Real.log (nF (A.map (cW w))) + _
  rw [Matrix.map_mul, (hF _ (Fin n) (Fin n) (Fin k) _).2.1, hd,
    Real.log_mul hA (norm_ne_zero_iff.2 h0)]

theorem logAbs_inv (hL : LogAbsBasic) (u u' : Ad E) (hu : IsUnit u) (hu' : IsUnit u') (h : u * u' = 1) :
    logAbs u = -logAbs u' := by
  have h1 := (hL E).2.1 u u' hu hu'
  have h2 := (hL E).2.2 1 one_ne_zero
  rw [map_one] at h2
  rw [h, h2] at h1
  linarith

theorem frame_leftInv (x : GA E n) (M : Matrix (Fin n) (Fin k) E) (L : Matrix (Fin k) (Fin n) E)
    (hLM : L * M = 1) :
    (L.map (algebraMap E (Ad E)) * x.val) * frame x M = 1 := by
  unfold frame
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc x.val, Units.mul_inv, Matrix.one_mul,
    ← Matrix.map_mul, hLM, Matrix.map_one _ (map_zero _) (map_one _)]

theorem degAdelic_of (hF : MulF) (hI : MulI) (hL : LogAbsBasic) (hS : FinSupp) : DegAdelic := by
  intro E _ _ _ n k x t s M hM h
  obtain ⟨L, hLM⟩ := exists_leftInv M hM
  obtain ⟨h1, h2, h3⟩ := hS E (Fin n) (Fin k) (frame x M) _ (frame_leftInv x M L hLM)
  have hδ : IsUnit (s⁻¹ : GA E k).val.det := Matrix.isUnits_det_units _
  have hs : IsUnit s.val.det := Matrix.isUnits_det_units _
  have hmul : (s⁻¹ : GA E k).val.det * s.val.det = 1 := by
    rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
  have hinv := logAbs_inv hL _ _ hδ hs hmul
  have hfin₁ : (Function.support fun w => lognFin w (frame x M)).Finite := by
    refine h3.subset fun w hw hw1 => hw ?_
    change Real.log (nF ((frame x M).map (cW w))) = 0
    rw [show nF ((frame x M).map (cW w)) = 1 from hw1, Real.log_one]
  have hfin₂ := (hL E).1 _ hδ
  rw [degM, degM, frame_mul x t s M h]
  have e₁ : ∀ v, lognInf v (frame x M * (s⁻¹ : GA E k).val) =
      lognInf v (frame x M) + Real.log (‖cV v (s⁻¹ : GA E k).val.det‖ ^ 2) :=
    fun v => lognInf_mul hI v _ _ (h1 v) hδ
  have e₂ : ∀ w, lognFin w (frame x M * (s⁻¹ : GA E k).val) =
      lognFin w (frame x M) + Real.log ‖cW w (s⁻¹ : GA E k).val.det‖ :=
    fun w => lognFin_mul hF w _ _ (h2 w) hδ
  simp_rw [e₁, e₂]
  rw [Finset.sum_add_distrib, finsum_add_distrib hfin₁ hfin₂]
  unfold logAbs at hinv ⊢
  linarith

end GlobalTheory.CompanionTheory.DegAdelicProof

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineFormsOfFormUniquenessStatement
section
open CrystallineSemistableComparison CrystallineSemistableComparison.Onto
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_forms_of_form_uniqueness : CrystallineSemistableComparison.Onto.FormUniq → CrystallineSemistableComparison.Onto.AffOm := by
  first | exact @GlobalTheory.CompanionTheory.AffOmP.affOm | exact GlobalTheory.CompanionTheory.AffOmP.affOm | (intros; apply GlobalTheory.CompanionTheory.AffOmP.affOm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BernsteinZelevinskyGeometricLemma
section
set_option maxSynthPendingDepth 1

open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

noncomputable section

namespace GlobalTheory.CompanionTheory.GeomLemmaUniform

section Filtration

open GroundTheory.Automorphic GroundTheory.Automorphic.Parabolic Matrix GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.GLnLocal ValuativeRel _root_.Topology Set DoubleCoset Filter

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ}

theorem filtration_of_cellEnumeration {k : ℕ} (w : Fin k → Equiv.Perm (Fin n))
    (hcov : ∀ g : Matrix.GeneralLinearGroup (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j))
        (blockUpper F n β : Set (Matrix.GeneralLinearGroup (Fin n) F)) (blockUpper F n γ))
    (hanti : Antitone fun j => cellHeight β γ (permGL F (w j)))
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
    (hσ : IsSmooth σ) :
    ∃ V : ℕ → Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)),
      V 0 = ⊥ ∧ V k = ⊤ ∧ Monotone V ∧
      ∃ hV : ∀ i (m : levi F n γ), V i ≤ (V i).comap (jacquetRep F n γ (parabolicInd F n β σ) m),
        ∀ j : Fin k, ∃ Ψ : Representation.IntertwiningMap
            ((jacquetRep F n γ (parabolicInd F n β σ)).subrepresentation (V (j + 1)) (hV (j + 1)))
            (twist ((invSqrtModular F n γ).comp leviIncl)
              (indRep (cellLeviSub F β γ (w j)) (cellInducing β γ (w j) σ))),
          Function.Surjective Ψ ∧
            ∀ x, Ψ x = 0 ↔ (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ V j := by
  set C : Fin k → Set (Matrix.GeneralLinearGroup (Fin n) F) := fun l =>
    doubleCoset (permGL F (w l)) (blockUpper F n β : Set (Matrix.GeneralLinearGroup (Fin n) F))
      (blockUpper F n γ)
  have hdisj : Pairwise fun i j => Disjoint (C i) (C j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro g hgi hgj
    obtain ⟨l, -, hl⟩ := hcov g
    exact hij ((hl i hgi).trans (hl j hgj).symm)
  have hcov' : ∀ g, ∃ l, g ∈ C l := fun g => (hcov g).exists
  have hcl := closure_doubleCoset_subset_of_antitone hcov hanti
  refine ⟨fun i => jacquetFiltration γ (σ := σ) (cellUnion C i), ?_, ?_, ?_, ?_⟩
  · show jacquetFiltration γ (cellUnion C 0) = ⊥
    rw [cellUnion_zero, jacquetFiltration_empty]
  · show jacquetFiltration γ (cellUnion C k) = ⊤
    rw [cellUnion_of_cover hcov', jacquetFiltration_univ]
  · exact fun i i' h => jacquetFiltration_mono γ (cellUnion_mono h)
  refine ⟨fun i m => jacquetFiltration_le_comap γ (cellUnion_mul_mem w i).1 m, fun j => ?_⟩
  have hYo : IsOpen (cellUnion C ((j : ℕ) + 1)) := isOpen_cellUnion hdisj hcov' hcl _
  have hCY : closure (C j) ∩ cellUnion C ((j : ℕ) + 1) = C j :=
    closure_inter_cellUnion_succ hdisj hcl j
  have hYQ := (cellUnion_mul_mem (F := F) (β := β) (γ := γ) w ((j : ℕ) + 1)).1
  have hYP := (cellUnion_mul_mem (F := F) (β := β) (γ := γ) w ((j : ℕ) + 1)).2
  have hdiff : cellUnion C ((j : ℕ) + 1) \ C j = cellUnion C j := by
    rw [cellUnion_succ j, union_sdiff_right, (disjoint_cellUnion hdisj j).symm.sdiff_eq_left]
  refine ⟨⟨gradedJacquetMap γ (w j) σ hYo hCY hYQ, fun m => ?_⟩, ?_, fun x => ?_⟩
  · refine LinearMap.ext fun x => ?_
    exact gradedJacquetMap_jacquetRep σ hYo hCY hYQ m x
  · exact gradedJacquetMap_surjective σ hYo hCY hYQ (cellJacquetMap_surjective hYo hCY hYP hYQ hσ)
  · have := gradedJacquetMap_eq_zero_iff σ hYo hCY hYQ
      (fun f hf h0 => exists_sub_mem_ker_of_cellJacquet_eq_zero σ hσ hYo hCY hYQ hf h0) x
    rw [hdiff] at this
    exact this

theorem normalized_piece {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (levi F n β) W) (w : Equiv.Perm (Fin n))
    {A : Type} [AddCommGroup A] [Module ℂ A] {ρ : Representation ℂ (levi F n γ) A}
    (Ψ₀ : Representation.IntertwiningMap ρ
      (twist ((invSqrtModular F n γ).comp leviIncl)
        (indRep (cellLeviSub F β γ w) (cellInducing β γ w σ))))
    (hsurj : Function.Surjective Ψ₀) :
    ∃ Ψ : Representation.IntertwiningMap ρ (indRep (cellLeviSub F β γ w) (normInducing σ γ w)),
      Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ Ψ₀ x = 0 := by
  refine ⟨(indCongrHom σ w).comp ((indTwistHom σ w).comp Ψ₀), ?_, fun x => ?_⟩
  · exact (indCongrHom_surjective σ w).comp ((indTwistHom_surjective σ w).comp hsurj)
  · constructor
    · intro h
      apply indTwistHom_injective σ w
      apply indCongrHom_injective σ w
      rw [map_zero, map_zero]
      exact h
    · intro h
      show (indCongrHom σ w) ((indTwistHom σ w) (Ψ₀ x)) = 0
      rw [h, map_zero, map_zero]

end Filtration

theorem geometricLemma_uniform : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (β γ : Fin n → ℕ), ∃ (K : ℕ) (w : Fin K → Equiv.Perm (Fin n)), (∀ g : GL (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j)) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W), GroundTheory.Automorphic.IsSmooth σ → ∃ V : ℕ → Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)), V 0 = ⊥ ∧ V K = ⊤ ∧ Monotone V ∧ ∃ hV : ∀ i (m : levi F n γ), V i ≤ (V i).comap (jacquetRep F n γ (parabolicInd F n β σ) m), ∀ j : Fin K, ∃ Ψ : Representation.IntertwiningMap ((jacquetRep F n γ (parabolicInd F n β σ)).subrepresentation (V (j + 1)) (hV (j + 1))) (indRep (cellLeviSub F β γ (w j)) (normInducing σ γ (w j))), Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ V j := by
  intro F _ _ _ _ n β γ
  obtain ⟨k, w, hcov, hanti⟩ := GroundTheory.Automorphic.Parabolic.exists_cellEnumeration (F := F) β γ
  refine ⟨k, w, hcov, fun W _ _ σ hσ => ?_⟩
  obtain ⟨V, h0, hk, hmono, hV, hΨ⟩ := filtration_of_cellEnumeration (γ := γ) w hcov hanti σ hσ
  refine ⟨V, h0, hk, hmono, hV, fun j => ?_⟩
  obtain ⟨Ψ₀, hsurj, hker⟩ := hΨ j
  obtain ⟨Ψ, hΨs, hΨk⟩ := normalized_piece σ (w j) Ψ₀ hsurj
  exact ⟨Ψ, hΨs, fun x => (hΨk x).trans (hker x)⟩

end GlobalTheory.CompanionTheory.GeomLemmaUniform
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockCountReindexEquivs
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.Cell

theorem exists_block_equiv_of_cells {X α β : Type} {m : α → Type} (e : (Σ i, m i) ≃ X) (b : X → β)
    (c : α → β → ℕ) (E : ∀ i j, {x : X // (e.symm x).1 = i ∧ b x = j} ≃ Fin (c i j)) :
    ∃ f : ∀ i, (Σ j, Fin (c i j)) ≃ m i,
      ∀ i j t, e ⟨i, f i ⟨j, t⟩⟩ = ((E i j).symm t).1 := by
  have hι : ∀ i, Function.Bijective
      (fun y : m i => (⟨e ⟨i, y⟩, by simp⟩ : {x : X // (e.symm x).1 = i})) := by
    intro i
    constructor
    · intro a a' h
      have h1 : e ⟨i, a⟩ = e ⟨i, a'⟩ := congrArg Subtype.val h
      exact sigma_mk_injective (e.injective h1)
    · rintro ⟨x, hx⟩
      obtain ⟨⟨k, y⟩, rfl⟩ := e.surjective x
      simp only [Equiv.symm_apply_apply] at hx
      subst hx
      exact ⟨y, rfl⟩
  have hF : ∀ i, Function.Bijective
      (fun p : Σ j, Fin (c i j) =>
        (⟨((E i p.1).symm p.2).1, ((E i p.1).symm p.2).2.1⟩ : {x : X // (e.symm x).1 = i})) := by
    intro i
    constructor
    · rintro ⟨j, t⟩ ⟨j', t'⟩ h
      have h1 : ((E i j).symm t).1 = ((E i j').symm t').1 := congrArg Subtype.val h
      have hj : j = j' := by
        calc j = b ((E i j).symm t).1 := ((E i j).symm t).2.2.symm
          _ = b ((E i j').symm t').1 := by rw [h1]
          _ = j' := ((E i j').symm t').2.2
      subst hj
      have ht : t = t' := (E i j).symm.injective (Subtype.ext h1)
      subst ht
      rfl
    · rintro ⟨x, hx⟩
      refine ⟨⟨b x, E i (b x) ⟨x, hx, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      simp
  refine ⟨fun i => (Equiv.ofBijective _ (hF i)).trans (Equiv.ofBijective _ (hι i)).symm, ?_⟩
  intro i j t
  have key := (Equiv.ofBijective _ (hι i)).apply_symm_apply (Equiv.ofBijective _ (hF i) ⟨j, t⟩)
  exact congrArg Subtype.val key

theorem cell_row_column_partitions :
    ∀ {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ} {m : α → Type} {m' : β' → Type} (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (w : Equiv.Perm (Fin N)), ∃ (f : ∀ i, (Σ j, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m i) (g : ∀ j, (Σ i, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m' j), ∀ i j (t : Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)), w (e' ⟨j, g j ⟨i, t⟩⟩) = e ⟨i, f i ⟨j, t⟩⟩ := by
  intro α β' _ _ _ _ N m m' e e' w
  let E : ∀ i j, {x : Fin N // (e.symm x).1 = i ∧ blk e' (w.symm x) = j} ≃
      Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) :=
    fun i j => (Equiv.subtypeEquivRight (fun x => by
      rw [Finset.mem_filter]
      exact ⟨fun h => ⟨Finset.mem_univ _, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩)).trans
      (Finset.equivFin _)
  let E' : ∀ j i, {x : Fin N // ((e'.trans w).symm x).1 = j ∧ blk e x = i} ≃
      Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) :=
    fun j i => (Equiv.subtypeEquivRight (fun x => by
      rw [Finset.mem_filter]
      exact ⟨fun h => ⟨Finset.mem_univ _, h.2, h.1⟩, fun h => ⟨h.2.2, h.2.1⟩⟩)).trans
      (Finset.equivFin _)
  obtain ⟨f, hf⟩ := exists_block_equiv_of_cells e (fun x => blk e' (w.symm x))
    (fun i j => (Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) E
  obtain ⟨g, hg⟩ := exists_block_equiv_of_cells (e'.trans w) (fun x => blk e x)
    (fun j i => (Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) E'
  refine ⟨f, g, ?_⟩
  intro i j t
  rw [hf i j t]
  exact hg j i t

end GlobalTheory.CompanionTheory.Cell
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLiftTensorCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Diso GlobalTheory.CompanionTheory.DisoHm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lift_tensor_compat : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (h : OL l O) {W : X.Opens} {d : ℕ} (c : Coord q W d) (m : ℕ)
    (cL : Chart (pdm h m) l q (κm l O m) W d)
    (hcL : ∀ i, ev cL.D cL.inV (c.t i) = Ideal.Quotient.mk _ (cL.t i))
    (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) W d),
    letI := (strV q W).toAlgebra
    ∀ (e : O ⊗[O] Γ(X, W) ≃+* cO.D.B), (∀ r, e (r ⊗ₜ 1) = cO.D.i r) → (∀ i, e (1 ⊗ₜ c.t i) = cO.t i) →
      (∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (e (1 ⊗ₜ f))) →
      ∀ (hT : Good (l := l) cO.D m) (σ : cL.D ⟶ GObj h cO.D m hT),
        (∀ i, σ.φ (cL.t i) = Ideal.Quotient.mk _ (cO.t i)) → Function.Bijective σ.φ := by
  first | exact @GlobalTheory.CompanionTheory.DisoHm.cmp_bij | exact GlobalTheory.CompanionTheory.DisoHm.cmp_bij | (intros; apply GlobalTheory.CompanionTheory.DisoHm.cmp_bij <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernClassReductionCompatible
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.FirstChernClassFactorial

theorem pow_dvd_factorial_mul (l : ℕ) (hl : 0 < l) (n : ℕ) : l ^ n ∣ (l * n).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (l * n).factorial * l.factorial ∣ (l * n + l).factorial :=
      Nat.factorial_mul_factorial_dvd_factorial_add _ _
    have h2 : l ∣ l.factorial := Nat.dvd_factorial hl le_rfl
    rw [pow_succ, Nat.mul_succ]
    exact (mul_dvd_mul ih h2).trans h1

theorem factorial_acr {l : ℕ} [Fact l.Prime] (n k : ℕ) (hk : l * n ≤ k) : (k.factorial : (PAlg.base l).Acr n) = 0 := by
  obtain ⟨a, ha⟩ := (pow_dvd_factorial_mul l (Fact.out : l.Prime).pos n).trans (Nat.factorial_dvd_factorial hk)
  rw [ha, Nat.cast_mul, Nat.cast_pow, (PAlg.base l).pow_l_acr n, zero_mul]

theorem dlog_eq_of_factorial {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) {N N' : ℕ} (h : N ≤ N')
    (hf : ∀ k, N ≤ k → (k.factorial : A) = 0) (v : A) : B.dlog δ N' v = B.dlog δ N v := by
  unfold B.dlog
  refine (Finset.sum_subset (Finset.range_mono h) fun k _ hk => ?_).symm
  rw [hf k (by simpa using hk)]
  simp


open B in
theorem isFirstChern_base_change {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b b' : Base}
    {ht : b.t = 1} {ht' : b'.t = 1} {κ : O →+* b.R ⧸ b.I} {κ' : O →+* b'.R ⧸ b'.I}
    (σ : b.R →+* b'.R) (hp : b.p = b'.p) (hI : IsDPMorphism b.γ b'.γ σ) (τ : b.R ⧸ b.I →+* b'.R ⧸ b'.I)
    (hτ : τ.comp κ = κ') (hτσ : ∀ r, τ (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (σ r))
    {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (c' : Λ →+* b'.R) (hc : ∀ a, σ (c a) = c' (RingHom.id Λ a))
    (D : E.LineData X) {N N' : ℕ} (hN : N ≤ N') (hf : ∀ k, N ≤ k → (k.factorial : b'.R) = 0)
    (y : CH.H (OM ((schFn q).cr b ht κ) c) 2)
    (hy : IsFirstChernClassOfLineBundle (q := q) (b := b) (ht := ht) (κ := κ) D c N' y) :
    IsFirstChernClassOfLineBundle (q := q) (b := b') (ht := ht') (κ := κ') D c' N
      ((omMor (crMor (F := schFn q) (F' := schFn q) (b := b) (b' := b') (ht := ht) (ht' := ht') σ hp hI
        (basePt (schFn q) τ hτ) fun _ y r => congrArg y.1.1 (hτσ r)) (RingHom.id Λ) hc).pull 2 y) := by
  intro C _ G Lf
  let mm := omMor (c := c) (c' := c') (crMor (F := schFn q) (F' := schFn q) (b := b) (b' := b') (ht := ht) (ht' := ht') σ hp hI
        (basePt (schFn q) τ hτ) fun _ y r => congrArg y.1.1 (hτσ r)) (RingHom.id Λ) hc
  let G' : C ⥤ Thick ((schFn q).cr b ht κ) := G ⋙ mm.G
  let Lf' : CLift G' D := { p := Lf.p, hp := Lf.hp, w := Lf.w, hw := Lf.hw }
  obtain ⟨hz', hcl⟩ := hy C G' Lf'
  let m4 : CH.Mor (G' ⋙ OM _ c) (G ⋙ OM _ c') (RingHom.id _) :=
    { G := 𝟭 C, τ := fun T => mm.τ (G.obj T), nat := fun φ x => mm.nat (G.map φ) x }
  have hE : m4.pullC 2 (Lf'.coc c N') = Lf.coc c' N := by
    funext s
    refine dlog_eq_of_factorial (G.obj (s.obj (Fin.last 2))).δ hN (fun j hj => ?_) _
    have := congrArg (G.obj (s.obj (Fin.last 2))).i (hf j hj)
    rw [map_natCast, map_zero] at this
    exact this
  have hz : CH.d _ 2 (Lf.coc c' N) = 0 := by
    rw [← hE, m4.d_pullC, hz', map_zero]
  refine ⟨hz, ?_⟩
  have h1 : (CH.Mor.restrict (OM _ c') G).pull 2 (mm.pull 2 y) =
      m4.pull 2 ((CH.Mor.restrict (OM _ c) G').pull 2 y) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rfl
  refine Eq.trans ?_ h1.symm
  rw [← hcl]
  have key : ∀ (z : CH.Cn (G ⋙ OM _ c') 2) (h : CH.d _ 2 z = 0), z = Lf.coc c' N →
      (CH.cx _).cls z h = (CH.cx _).cls (Lf.coc c' N) hz := by
    rintro _ _ rfl
    rfl
  exact (key (m4.pullC 2 (Lf'.coc c N')) (by rw [m4.d_pullC, hz', map_zero]) hE).symm


open B in
theorem chern_class_reduction_compatible {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* OC l) (k : Bool)
    (D : E.LineData X) (n : ℕ) (y : B.Hc (schFn q) κ k (n + 1) 2)
    (hy : IsFirstChernClassOfLineBundle (q := q) (b := bs l k (n + 1)) (ht := rfl) (κ := κb κ k (n + 1)) D ((PAlg.base l).cris (n + 1)) (l * (n + 1)) y) :
    IsFirstChernClassOfLineBundle (q := q) (b := bs l k n) (ht := rfl) (κ := κb κ k n) D ((PAlg.base l).cris n) (l * n)
      (redHc (schFn q) κ k n.le_succ 2 y) :=
  isFirstChern_base_change (b := bs l k (n + 1)) (b' := bs l k n) ((PAlg.base l).red n.le_succ) rfl (dd_red k _ n.le_succ)
    (Ideal.quotientMap _ _ (red_le k n.le_succ)) (red_κb κ k n.le_succ) (fun _ => rfl) _ _ (red_cris _ n.le_succ) D
    (Nat.mul_le_mul_left l n.le_succ) (fun j hj => factorial_acr n j hj) y hy

theorem exists_C1H {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (D : E.LineData M.X)
    (hD : sSup (𝒱D D) = ⊤) : ∃ x : (M.HS false 2).lim, B.IsFirstChernFamily M.p D (okToOC l K) false x.1 := by
  have ex : ∀ n, ∃! x, B.IsFirstChernClassOfLineBundle (q := M.p) (b := B.bs l false n) (ht := rfl) (κ := B.κb (okToOC l K) false n) D
      ((PAlg.base l).cris n) (l * n) x := fun n =>
    GlobalTheory.T.existsUnique_chern_class_nilpotent_base (B.DD false (PAlg.base l) n) l (Fact.out : l.Prime).ne_zero M.p (B.κb (okToOC l K) false n) D hD
      ((PAlg.base l).cris n) (l * n) (factorial_acr n _ le_rfl)
  choose x hx hu using ex
  refine ⟨⟨x, fun n => ?_⟩, hx⟩
  exact hu n _ (chern_class_reduction_compatible M.p (okToOC l K) false D n (x (n + 1)) (hx (n + 1)))

end GlobalTheory.CompanionTheory.FirstChernClassFactorial
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingOperatorsKernelLiftStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_operators_kernel_lift : ∀ (ι : Type) [LinearOrder ι] (R : Type) [CommRing R] (g : ℕ) (ρ : Fin g → R) (T : ℕ → ℤ → Finset ι → Type) [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)] (res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S') (p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S) (mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S) (H : TowerAx ρ res p mm) (one : ∀ e (i : ι), T e 0 {i}), (∀ e i, p e 0 {i} (one (e + 1) i) = one e i) → (∀ e i t (a : T e t {i}), ∃ (k : ℕ) (q : MvPolynomial ι R) (t' : ℤ) (w : T e t' {i}), w ∈ Ideal.span (Set.range ρ) • (⊤ : Submodule R (T e t' {i})) ∧ (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of (hc e {i}) t a = q • GrSum.of (hc e {i}) 0 (one e i) + GrSum.of (hc e {i}) t' w) → ∀ i : ι, ∃ s : Finset (H.Tot hc {i}), ∀ m : H.Tot hc {i}, ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k • m ∈ Submodule.span (MvPolynomial ι (MvPolynomial (Fin g) R)) (s : Set (H.Tot hc {i})) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.tot_singleton_finite_up_to_X | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.tot_singleton_finite_up_to_X | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.tot_singleton_finite_up_to_X <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingOperatorsUniformCokernelStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_operators_uniform_cokernel : ∀ (ι : Type) [LinearOrder ι] (R : Type) [CommRing R] (g : ℕ) (ρ : Fin g → R) (T : ℕ → ℤ → Finset ι → Type) [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)] (res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S') (p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S) (mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S) (H : TowerAx ρ res p mm), (∀ e S j t (b : T e t (insert j S)), S.Nonempty → ∃ (k : ℕ) (t' : ℤ) (a : T e t' S), GrSum.of (hc e (insert j S)) t' (res e t' S (insert j S) (Finset.subset_insert j S) a) = (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc e (insert j S)) t b) → ∀ (S : Finset ι) (j : ι) (b : H.Tot hc (insert j S)), S.Nonempty → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k • b ∈ LinearMap.range (H.resTot hc S (insert j S) (Finset.subset_insert j S)) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.tower_kernels_lift_after_X_pow | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.tower_kernels_lift_after_X_pow | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.tower_kernels_lift_after_X_pow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingOperatorsUniformKernelStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_operators_uniform_kernel : ∀ (ι : Type) [LinearOrder ι] (R : Type) [CommRing R] (g : ℕ) (ρ : Fin g → R) (T : ℕ → ℤ → Finset ι → Type) [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)] (res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S') (p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S) (mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S) (H : TowerAx ρ res p mm), (∀ e S j t (a : T e t S), S.Nonempty → res e t S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc e S) t a = 0) → ∀ (S : Finset ι) (j : ι) (a : H.Tot hc S), S.Nonempty → H.resTot hc S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k • a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_X_pow_smul_eq_zero_of_resTot_eq_zero | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_X_pow_smul_eq_zero_of_resTot_eq_zero | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_X_pow_smul_eq_zero_of_resTot_eq_zero <;> assumption)
end

