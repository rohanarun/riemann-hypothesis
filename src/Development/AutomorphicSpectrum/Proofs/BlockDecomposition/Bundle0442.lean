module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0413
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0405

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionSmooth
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.FMem

variable {n : ℕ}

theorem contDiff_entry (a b : Fin n) : ContDiff ℝ ∞ (fun g : Mat n => g a b) :=
  contDiff_apply_apply ℝ a b

theorem contDiff_det_of_entries {ι : Type} [Fintype ι] [DecidableEq ι] {M : Mat n → Matrix ι ι ℂ}
    (h : ∀ a b, ContDiff ℝ ∞ fun g => M g a b) : ContDiff ℝ ∞ fun g => (M g).det := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  exact contDiff_prod fun i _ => h _ _

theorem contDiff_lm (j : Fin n) : ContDiff ℝ ∞ (lm j) :=
  contDiff_det_of_entries fun _ _ => contDiff_entry _ _

theorem contDiff_gm (j : Fin n) : ContDiff ℝ ∞ (gm j) := by
  refine contDiff_det_of_entries fun a b => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id]
  refine ContDiff.sum fun k _ => (contDiff_entry _ _).mul ?_
  exact Complex.conjCLE.contDiff.comp (contDiff_entry _ _)

theorem zpow_contDiffOn {f : Mat n → ℂ} {s : Set (Mat n)} (hf : ContDiffOn ℝ ∞ f s)
    (h : ∀ x ∈ s, f x ≠ 0) (m : ℤ) : ContDiffOn ℝ ∞ (fun x => f x ^ m) s := by
  obtain ⟨k, rfl | rfl⟩ := m.eq_nat_or_neg
  · simpa only [zpow_natCast] using hf.pow k
  · simp only [_root_.zpow_neg, zpow_natCast]
    exact (hf.pow k).inv fun x hx => pow_ne_zero k (h x hx)


open scoped ComplexOrder in
theorem gm_ne_zero (j : Fin n) {g : Mat n} (hg : g ∈ GLs n) : gm j g ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 : (g.submatrix (ini j) id)ᴴ *ᵥ v = 0 :=
    (Matrix.self_mul_conjTranspose_mulVec_eq_zero _ v).mp hAv
  have hu : IsUnit g.det := isUnit_iff_ne_zero.mpr hg
  have hAB : g.submatrix (ini j) id * (g⁻¹).submatrix id (ini j) = 1 := by
    have h2 := Matrix.submatrix_mul g g⁻¹ (ini j) id (ini j) Function.bijective_id
    have hi : Function.Injective (ini j) := Fin.castLE_injective _
    rw [Matrix.mul_nonsing_inv g hu, Matrix.submatrix_one _ hi] at h2
    exact h2.symm
  have hBA : ((g⁻¹).submatrix id (ini j))ᴴ * (g.submatrix (ini j) id)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hAB, Matrix.conjTranspose_one]
  apply hv
  calc v = (((g⁻¹).submatrix id (ini j))ᴴ * (g.submatrix (ini j) id)ᴴ) *ᵥ v := by
        rw [hBA, Matrix.one_mulVec]
    _ = ((g⁻¹).submatrix id (ini j))ᴴ *ᵥ ((g.submatrix (ini j) id)ᴴ *ᵥ v) :=
        (Matrix.mulVec_mulVec _ _ _).symm
    _ = 0 := by rw [h1, Matrix.mulVec_zero]

theorem muZ_antitone {lam : Fin n → ℤ} {lev : Fin n → ℕ} (hlam : Antitone lam) (hlev : Monotone lev) :
    Antitone (muZ lam lev) := by
  intro a b hab
  have h1 := hlam hab
  have h2 : lev a ≤ lev b := hlev hab
  have c1 : (univ.filter fun c => lev b < lev c).card ≤ (univ.filter fun c => lev a < lev c).card :=
    Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      omega
  have c2 : (univ.filter fun c => lev c < lev a).card ≤ (univ.filter fun c => lev c < lev b).card :=
    Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      omega
  simp only [muZ]
  omega

theorem dif_nonneg_of_antitone {v : Fin n → ℤ} (h : Antitone v) (j : Fin n) (hj : (j : ℕ) + 1 < n) :
    0 ≤ dif v j := by
  have hnext : j ≤ (⟨j + 1, hj⟩ : Fin n) := Fin.le_def.mpr (Nat.le_succ _)
  simpa only [dif, dite_eq_left hj, sub_nonneg] using h hnext

theorem lm_ne_zero (j : Fin n) (hj : ¬ (j : ℕ) + 1 < n) {g : Mat n} (hg : g ∈ GLs n) : lm j g ≠ 0 := by
  have hb : Function.Bijective (ini j) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨Fin.castLE_injective _, by
      have := j.isLt
      simp only [Fintype.card_fin]
      omega⟩
  have e : lm j g = g.det := Matrix.det_submatrix_equiv_self (Equiv.ofBijective _ hb) g
  rw [e]
  exact hg

end GlobalTheory.CompanionTheory.ModelS.FMem

namespace GlobalTheory.CompanionTheory.ModelS


open FMem in
theorem fRaw_mem_SmF : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    GlobalTheory.CompanionTheory.ModelS.fRaw lam lev ∈ GlobalTheory.CompanionTheory.ModelS.SmF n := by
  intro n lam hlam lev hlev
  refine ⟨?_, fun g hg => Set.indicator_of_notMem hg _⟩
  have key : ContDiffOn ℝ ∞
      (fun g => ∏ j, lm j g ^ dif (muZ lam lev) j * gm j g ^ dif (yZ lam lev) j) (GLs n) := by
    refine contDiffOn_prod fun j _ => ContDiffOn.mul ?_
      (zpow_contDiffOn (contDiff_gm j).contDiffOn (fun g hg => gm_ne_zero j hg) _)
    by_cases hj : (j : ℕ) + 1 < n
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (dif_nonneg_of_antitone (muZ_antitone hlam hlev.1) j hj)
      simp only [hk, zpow_natCast]
      exact ((contDiff_lm j).pow k).contDiffOn
    · exact zpow_contDiffOn (contDiff_lm j).contDiffOn (fun g hg => lm_ne_zero j hj hg) _
  exact key.congr fun g hg => Set.indicator_of_mem hg _

end GlobalTheory.CompanionTheory.ModelS
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedParabolicMulEmbeddedMirabolicStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_parabolic_mul_embedded_mirabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ),
    IsClosed {g : Mir k (m + (j + 1)) | ∃ h ∈ MirabolicParabolic k m (j + 1), ∃ x : Mir k (m + j), g = h * embedding₂ k (m + j) x} := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.Closed.isClosed_HGP_iota | exact GlobalTheory.CompanionTheory.LeibPhi.Closed.isClosed_HGP_iota | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.Closed.isClosed_HGP_iota <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximal
section
noncomputable section

namespace GlobalTheory.CompanionTheory.StdK

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter _root_.Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_intBasis : ∃ b : Module.Basis (Fin (Module.finrank F E)) F E, ∀ i, IsIntegral ℤ (b i) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h : ∀ x : E, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ (m • x) := fun x => by
    obtain ⟨m, hm, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (Algebra.IsAlgebraic.isAlgebraic x)).exists_integral_multiple
    exact ⟨m, hm, hi⟩
  choose m hm hi using h
  let b := Module.finBasis F E
  let u : Fin (Module.finrank F E) → Fˣ := fun i => Units.mk0 (m (b i) : F) (by exact_mod_cast hm _)
  refine ⟨b.unitsSMul u, fun i => ?_⟩
  rw [Module.Basis.unitsSMul_apply]
  have e : u i • b i = m (b i) • b i := by
    change ((m (b i) : F)) • b i = _
    exact Int.cast_smul_eq_zsmul F _ _
  rw [e]
  exact hi _

theorem isOpen_intAd : IsOpen {a : AF F | ∀ v, evFin F v a ∈ v.adicCompletionIntegers F} := by
  have h : IsOpen {f : FiniteAdeleRing (𝓞 F) F | ∀ v, f v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  exact h.preimage continuous_snd

theorem evFin_finOne (v : HeightOneSpectrum (𝓞 F)) : evFin F v (finOne F) = 1 := rfl

theorem evI_finOne_mul (a : AF F) : evI F (finOne F * a) = 0 := by
  have e : (finOne F * a).1 = 0 := by
    change (0 : Ainf F) * a.1 = 0
    exact zero_mul _
  unfold evI
  rw [e, map_zero]


variable (F E) in
def finInt : AddSubgroup (AE F E) :=
  (intHat F E).comap (DistribSMul.toAddMonoidHom (AE F E) (finOne F))

theorem mem_finInt {z : AE F E} : z ∈ finInt F E ↔ finOne F • z ∈ intHat F E := Iff.rfl

theorem smul_incl_mem_finInt {a : AF F} (ha : ∀ v, evFin F v a ∈ v.adicCompletionIntegers F) (o : 𝓞 E) :
    a • inclR (F := F) (E := E) (AF F) (o : E) ∈ finInt F E := by
  rw [mem_finInt, smul_smul]
  refine AddSubgroup.subset_closure ⟨finOne F * a, evI_finOne_mul a, fun v => ?_, o, rfl⟩
  rw [map_mul, evFin_finOne, one_mul]
  exact ha v

theorem isOpen_finInt : IsOpen (finInt F E : Set (AE F E)) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨b, hb⟩ := exists_intBasis (F := F) (E := E)
  let e := (Algebra.TensorProduct.basis (AF F) b).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hS : IsOpen {z : AE F E | ∀ i, ∀ v, evFin F v (e z i) ∈ v.adicCompletionIntegers F} := by
    have e0 : {z : AE F E | ∀ i, ∀ v, evFin F v (e z i) ∈ v.adicCompletionIntegers F} =
        ⋂ i, (fun z => e z i) ⁻¹' {a : AF F | ∀ v, evFin F v a ∈ v.adicCompletionIntegers F} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [e0]
    exact isOpen_iInter_of_finite fun i => (isOpen_intAd (F := F)).preimage ((continuous_apply i).comp he)
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (Filter.mem_of_superset (hS.mem_nhds ?_) ?_)
  · intro i v
    simp
  · intro z hz
    have e1 : z = ∑ i, e z i • (Algebra.TensorProduct.basis (AF F) b i) :=
      ((Algebra.TensorProduct.basis (AF F) b).sum_equivFun z).symm
    rw [e1]
    refine sum_mem fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
    exact smul_incl_mem_finInt (hz i) ⟨b i, hb i⟩

theorem isClosed_finInt : IsClosed (finInt F E : Set (AE F E)) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact AddSubgroup.isClosed_of_isOpen _ isOpen_finInt

theorem compFin_finOne_smul (v : HeightOneSpectrum (𝓞 F)) (z : AE F E) :
    compFin F E v (finOne F • z) = compFin F E v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  | tmul a e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp [compFin, map_mul, evFin_finOne]

theorem absFin_le_one_of_mem {z : AE F E} (hz : z ∈ intHat F E) (v : HeightOneSpectrum (𝓞 F)) :
    absFin F v (compFin F E v z) ≤ 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, o, rfl⟩ := hz
    have e : compFin F E v (a • inclR (F := F) (E := E) (AF F) (o : E)) = evFin F v a ⊗ₜ[F] (o : E) := by
      simp [compFin, inclR, TensorProduct.smul_tmul']
    rw [e]
    refine (absFin_tmul_le F v _ o).trans ?_
    exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 (ha v)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact (absFin_add_le F v _ _).trans (max_le hx hy)
  | neg x _ hx =>
    rw [map_neg, absFin_neg]
    exact hx

theorem opNorm_le_one {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ} (h : M * Mᴴ = 1) : opNorm M ≤ 1 := by
  have e : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M * star (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M) = 1 := by
    rw [← map_star, ← map_mul, Matrix.star_eq_conjTranspose, h, map_one]
  have h2 := CStarRing.norm_self_mul_star (x := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M)
  rw [e] at h2
  have h3 : ‖(1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h4 := norm_nonneg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M)
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M‖₊ ≤ 1
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  nlinarith

variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem heightGL_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] (B : Base F E) (hcm : IsCMExt F E σ)
    (g : GL ι (AE F E)) (hu : ∀ w, (g.1.map (piInf (B.emb w))) * (g.1.map (piInf (B.emb w)))ᴴ = 1)
    (hf : ∀ i j, g.1 i j ∈ finInt F E) (hf' : ∀ i j, (g⁻¹).1 i j ∈ finInt F E) : heightGL F g = 1 := by
  rw [heightGL_eq_one_iff]
  refine ⟨fun w => htOf_eq_one.2 ⟨?_, ?_⟩, fun v => htOf_eq_one.2 ⟨?_, ?_⟩⟩
  · rw [normInf_eq_opNorm hcm (B.emb w)]
    exact opNorm_le_one (hu w)
  · rw [normInf_eq_opNorm hcm (B.emb w), ← map_inv]
    change opNorm ((g⁻¹).1.map (piInf (B.emb w))) ≤ 1
    have hM : g.1.map (piInf (B.emb w)) * (g⁻¹).1.map (piInf (B.emb w)) = 1 := by
      rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have h1 := mul_eq_one_comm.1 (hu w)
    have h2 : (g⁻¹).1.map (piInf (B.emb w)) = (g.1.map (piInf (B.emb w)))ᴴ := by
      calc _ = (g.1.map (piInf (B.emb w)))ᴴ * g.1.map (piInf (B.emb w)) * (g⁻¹).1.map (piInf (B.emb w)) := by
            rw [h1, Matrix.one_mul]
        _ = _ := by rw [Matrix.mul_assoc, hM, Matrix.mul_one]
    rw [h2]
    exact opNorm_le_one (by rw [Matrix.conjTranspose_conjTranspose]; exact h1)
  · refine (normFin_le_iff F v).2 fun i j => ?_
    change absFin F v (compFin F E v (g.1 i j)) ≤ 1
    rw [← compFin_finOne_smul]
    exact absFin_le_one_of_mem (hf i j) v
  · refine (normFin_le_iff F v).2 fun i j => ?_
    rw [← map_inv]
    change absFin F v (compFin F E v ((g⁻¹).1 i j)) ≤ 1
    rw [← compFin_finOne_smul]
    exact absFin_le_one_of_mem (hf' i j) v

theorem isCompact_of_isStdK (B : Base F E) (hcm : IsCMExt F E σ) (b : GL (Fin n ⊕ Fin n) E)
    (K : Subgroup (G2 σ Y)) (hK : IsStdK (σ := σ) (Y := Y) B b K) : IsCompact (K : Set (G2 σ Y)) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  let bA : GL (Fin n ⊕ Fin n) (AE F E) := Formalism.UG.bc (inclR (F := F) (E := E) (AF F)) b
  let m : G2 σ Y → GL (Fin n ⊕ Fin n) (AE F E) := fun x => bA⁻¹ * x.1 * bA
  have hm : ∀ x, (m x).1 = inFrame b x := fun x => rfl
  have hv : Continuous fun x : G2 σ Y => (x.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :=
    Units.continuous_val.comp continuous_subtype_val
  have hfr : Continuous fun x : G2 σ Y => inFrame b x := (continuous_const.matrix_mul hv).matrix_mul continuous_const
  have hfi : Continuous fun x : G2 σ Y => inFrame b x⁻¹ := hfr.comp continuous_inv
  have hcl : IsClosed (K : Set (G2 σ Y)) := by
    have e1 : (K : Set (G2 σ Y)) = (⋂ w, {k : G2 σ Y | (inFrame b k).map (piInf (B.emb w)) *
          ((inFrame b k).map (piInf (B.emb w)))ᴴ = 1}) ∩
        ((⋂ i, ⋂ j, (fun k : G2 σ Y => inFrame b k i j) ⁻¹' (finInt F E : Set (AE F E))) ∩
          ⋂ i, ⋂ j, (fun k : G2 σ Y => inFrame b k⁻¹ i j) ⁻¹' (finInt F E : Set (AE F E))) := by
      ext k
      simp only [SetLike.mem_coe, hK k, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage,
        Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, mem_finInt]
    rw [e1]
    refine (isClosed_iInter fun w => isClosed_eq ?_ continuous_const).inter
      ((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_finInt.preimage ?_).inter
        (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_finInt.preimage ?_))
    · have h := hfr.matrix_map (GlobalTheory.ContMapReal.continuous_piInf (B.emb w))
      exact h.matrix_mul h.matrix_conjTranspose
    · exact (continuous_apply j).comp ((continuous_apply i).comp hfr)
    · exact (continuous_apply j).comp ((continuous_apply i).comp hfi)
  have hσ : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hUG : IsClosed (UG (cA σ) (dbl (incM F Y.J)) : Set (GL (Fin n ⊕ Fin n) (AE F E))) := by
    have hg : Continuous fun g : GL (Fin n ⊕ Fin n) (AE F E) => (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :=
      Units.continuous_val
    exact isClosed_eq ((hg.matrix_transpose.matrix_mul continuous_const).matrix_mul (hg.matrix_map hσ)) continuous_const
  have hC := hUG.isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_heightGL_le (E := E) (n := Fin n ⊕ Fin n) F (heightGL F bA * heightGL F bA⁻¹))
  refine hC.of_isClosed_subset hcl fun k hk => ?_
  obtain ⟨hu, hf⟩ := (hK k).1 hk
  have hinv : (m k)⁻¹ = m k⁻¹ := by
    change (bA⁻¹ * k.1 * bA)⁻¹ = bA⁻¹ * (k.1)⁻¹ * bA
    group
  have h1 : heightGL F (m k) = 1 := heightGL_eq_one B hcm (m k) hu
    (fun i j => mem_finInt.2 (hf k (by simp) i j))
    (fun i j => by
      rw [hinv]
      exact mem_finInt.2 (hf k⁻¹ (by simp) i j))
  have e2 : k.1 = bA * m k * bA⁻¹ := by
    change k.1 = bA * (bA⁻¹ * k.1 * bA) * bA⁻¹
    group
  change heightGL F k.1 ≤ _
  rw [e2]
  refine (heightGL_mul_le F _ _).trans ?_
  rw [(heightGL_mul_of_eq_one F h1 bA).1]

theorem isCompact_K : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → IsCompact (K : Set (G2 σ Y)) := by
  intro F E _ _ _ _ _ σ B n Y r s hB _ _ b K a _ hK _
  exact isCompact_of_isStdK B hB.cm b K hK

end GlobalTheory.CompanionTheory.StdK

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLeftInvariantOfIsAutForm
section
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.LeftInv

theorem ratGL_eq_diagonal (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (γ : GL (Fin a) E) : ratGL E a γ = AdelicGLn.diagonal E a γ :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem isLeftInvariant_of_isAutForm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (a : ℕ) (φ : Sm E a), IsAutForm φ → AutomorphicForm.IsLeftInvariant φ.1 := by
  intro E _ _ _ a φ h γ g
  rw [← ratGL_eq_diagonal]
  exact h.left γ g

end GlobalTheory.CompanionTheory.LeftInv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenRightInvarianceOrbitCoefficient
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OpenSmooth

theorem isOpen_rightPeriods {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (F : G → Z)
    (N : Set G) (hN : N ∈ nhds (1 : G)) (h : ∀ g ∈ N, ∀ m, F (m * g) = F m) :
    IsOpen {g : G | ∀ m, F (m * g) = F m} := by
  let T : Subgroup G :=
    { carrier := {g : G | ∀ m, F (m * g) = F m}
      mul_mem' := by
        intro a b ha hb m
        rw [← mul_assoc, hb, ha]
      one_mem' := by intro m; rw [mul_one]
      inv_mem' := by
        intro a ha m
        have := ha (m * a⁻¹)
        rw [inv_mul_cancel_right] at this
        exact this.symm }
  refine T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset hN ?_)
  intro g hg
  exact h g hg

theorem isOpen_stab_ind {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (v : smoothPart (ind H σ)) :
    IsOpen {x : G | ∀ y, v.1.1 (y * x) = v.1.1 y} := by
  have h : IsOpen {g : G | ind H σ g v.1 = v.1} := v.2
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx
    exact Subtype.ext (funext hx)
  · intro hx y
    exact congrFun (congrArg Subtype.val hx) y

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_castM {a b : ℕ} (h : a = b) : Continuous (castM k h) := by
  subst h
  exact continuous_id

theorem continuous_sEmb (n : ℕ) : Continuous (sEmb k n) :=
  GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM k n

theorem isOpen_dpowM_eq_one (n : ℕ) (s : ℝ) : IsOpen {g : Mir k n | dpowM n s g = 1} :=
  (GlobalTheory.CompanionTheory.LeibPhi.isOpen_ker_dpow k (n + 1) s).preimage continuous_subtype_val

variable {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}

theorem intO_mul_of_stab (f : XS τ σ) (κ : Mir k ((i + 1) + t + 1))
    (hκ : ∀ x : Mir k ((i + 1) + (t + 1)), evX f (x * κ) = evX f x) (y : Mir k ((i + 1) + t + 1)) :
    intO f (y * κ) = intO f y := by
  unfold intO
  congr 1
  funext d
  rw [← mul_assoc]
  exact hκ _

theorem eO_mul_of_stab (ψ : AddChar k Circle) (f : XS τ σ) (m g : Mir k (i + (t + 1)))
    (hd : dpowM (i + (t + 1)) (-1 / 2) g = 1)
    (hκ : ∀ x : Mir k ((i + 1) + (t + 1)),
      evX f (x * sEmb k _ (castM k (by omega : i + (t + 1) = (i + 1) + t) g)) = evX f x) :
    eO ψ f (m * g) = eO ψ f m := by
  unfold eO
  rw [map_mul, hd, mul_one, map_mul, map_mul, ← mul_assoc, intO_mul_of_stab f _ hκ]

theorem isOpen_evX_stab (f : XS τ σ) :
    IsOpen {x : Mir k ((i + 1) + (t + 1)) | ∀ y : Mir k ((i + 1) + (t + 1)), evX f (y * x) = evX f y} :=
  isOpen_stab_ind _ _ (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ)))

end GlobalTheory.CompanionTheory.BZPhiPG.OpenSmooth

namespace GlobalTheory.CompanionTheory.BZPhiPG


open GlobalTheory.CompanionTheory.BZPhiPG.OpenSmooth in
theorem isOpen_eO_rightPeriods : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ),
    IsOpen {g : Mir k (i + (t + 1)) | ∀ m, eO ψ f (m * g) = eO ψ f m} := by
  intro k _ _ _ _ i t ψ τ σ f
  have hs : i + (t + 1) = (i + 1) + t := by omega
  have hφ : Continuous fun g : Mir k (i + (t + 1)) => sEmb k _ (castM k hs g) :=
    (continuous_sEmb _).comp (continuous_castM hs)
  have hU : IsOpen ({g : Mir k (i + (t + 1)) | dpowM (i + (t + 1)) (-1 / 2) g = 1} ∩
      (fun g : Mir k (i + (t + 1)) => sEmb k _ (castM k hs g)) ⁻¹'
        {x : Mir k ((i + 1) + (t + 1)) | ∀ y : Mir k ((i + 1) + (t + 1)), evX f (y * x) = evX f y}) :=
    (isOpen_dpowM_eq_one _ _).inter ((isOpen_evX_stab f).preimage hφ)
  refine isOpen_rightPeriods (eO ψ f) _ (hU.mem_nhds ⟨map_one _, ?_⟩) ?_
  · intro y
    simp
  · rintro g ⟨hd, hst⟩ m
    exact eO_mul_of_stab ψ f m g hd hst

end GlobalTheory.CompanionTheory.BZPhiPG

end
end

