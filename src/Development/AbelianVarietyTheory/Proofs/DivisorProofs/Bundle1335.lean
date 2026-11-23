module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1316
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1309
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0977
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
section
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.CMImag

theorem exists_imag_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∃ c : E, c ≠ 0 ∧ σ c = -c := by
  intro F E _ _ _ _ _ σ h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hconj : ∀ x, τ (σ x) = star (τ x) := h.2.2.2 τ
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    apply τ.injective
    rw [hconj, hconj, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    have hTC := h.2.1
    apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hconj x
    rw [hall x] at this
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this.symm
  obtain ⟨x, hx⟩ := hne
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hinv, neg_sub]

end GlobalTheory.CMImag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledIntegralFiniteAdelePointsSubsetNhds
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.EvAdm

noncomputable section

namespace GlobalTheory.EvAdm

theorem norm_natCast_lt_one_of_dvd (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (c : ℕ) (hc : Ideal.absNorm v.asIdeal ∣ c) :
    ‖(c : v.adicCompletion F)‖ < 1 := by
  have hmem : (c : 𝓞 F) ∈ v.asIdeal := by
    obtain ⟨k, hk⟩ := hc
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hval := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (c : 𝓞 F)).2 hmem
  rw [Valued.toNormedField.norm_lt_one_iff]
  have e : (c : v.adicCompletion F) = (((algebraMap (𝓞 F) F (c : 𝓞 F)) : F) : v.adicCompletion F) := by
    rw [map_natCast]
    rw [show (((c : F)) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (c : F) from rfl,
      map_natCast]
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact hval

theorem exists_nat_scaled_subset (F : Type) [Field F] [NumberField F]
    (U : Set (FiniteAdeleRing (𝓞 F) F)) (hU : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ m : ℕ, m ≠ 0 → N ∣ m → ∀ x : FiniteAdeleRing (𝓞 F) F,
      (∀ v : HeightOneSpectrum (𝓞 F),
        (algebraMap F (v.adicCompletion F) (m : F))⁻¹ * x v ∈ v.adicCompletionIntegers F) → x ∈ U := by
  classical
  have hAopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun _ => Valued.isOpen_valuationSubring _
  have hU' : U ∈ Filter.map (RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)
      (𝓝 (fun v => ⟨0, zero_mem (v.adicCompletionIntegers F)⟩)) := by
    rw [← RestrictedProduct.nhds_eq_map_structureMap hAopen]
    exact hU
  have hU2 : (RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite) ⁻¹'
      (U : Set (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)) ∈
      𝓝 (fun v : HeightOneSpectrum (𝓞 F) => (⟨0, zero_mem (v.adicCompletionIntegers F)⟩ :
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)))) := hU'
  rw [nhds_pi, Filter.mem_pi] at hU2
  obtain ⟨I, hI, t, ht, hIt⟩ := hU2
  have hε : ∀ v : HeightOneSpectrum (𝓞 F), ∃ ε > (0 : ℝ),
      ∀ y : (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
        ‖(y : v.adicCompletion F)‖ < ε → y ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).1 (ht v)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hu
    refine ⟨ε, hε, fun y hy => hut (hball ?_)⟩
    simpa [Metric.mem_ball, dist_zero_right] using hy
  choose ε hεpos hεt using hε
  set c : ℕ := ∏ v ∈ hI.toFinset, Ideal.absNorm v.asIdeal with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Finset.prod_ne_zero_iff]
    intro v _
    exact (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hcv : ∀ v ∈ I, ‖(c : v.adicCompletion F)‖ < 1 := fun v hv =>
    norm_natCast_lt_one_of_dvd F v c (Finset.dvd_prod_of_mem _ (hI.mem_toFinset.2 hv))
  have hev : ∀ v ∈ I, ∀ᶠ k in atTop, ‖(c : v.adicCompletion F)‖ ^ k < ε v := fun v hv =>
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hcv v hv)).eventually
      (Iio_mem_nhds (hεpos v))
  obtain ⟨k, hk⟩ := ((Filter.eventually_all_finite hI).2 hev).exists
  refine ⟨c ^ k, pow_ne_zero _ hc0, fun m hm hdvd x hx => ?_⟩
  obtain ⟨d, hd⟩ := hdvd
  have hmv : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) (m : F) = (m : v.adicCompletion F) :=
    fun v => map_natCast _ m
  have hm0 : ∀ v : HeightOneSpectrum (𝓞 F), (m : v.adicCompletion F) ≠ 0 :=
    fun v => by rw [← hmv]; exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hm)
  have hxv : ∀ v : HeightOneSpectrum (𝓞 F),
      x v = (m : v.adicCompletion F) * ((m : v.adicCompletion F)⁻¹ * x v) := by
    intro v
    rw [← mul_assoc, mul_inv_cancel₀ (hm0 v), one_mul]
  have hmem : ∀ v : HeightOneSpectrum (𝓞 F), x v ∈
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    intro v
    have h1 := hx v
    rw [hmv] at h1
    rw [hxv v]
    exact mul_mem (natCast_mem _ _) h1
  have hxe : x = RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
      (fun v => ⟨_, hmem v⟩) := by
    ext v
    rfl
  rw [hxe]
  apply hIt
  intro v hv
  apply hεt
  show ‖x v‖ < ε v
  have h1 := hx v
  rw [hmv] at h1
  have hz1 : ‖(m : v.adicCompletion F)⁻¹ * x v‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h1
  have hd1 : ‖(d : v.adicCompletion F)‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (natCast_mem _ _)
  have hnm : ‖(m : v.adicCompletion F)‖ ≤ ‖(c : v.adicCompletion F)‖ ^ k := by
    rw [hd, Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow]
    calc ‖(c : v.adicCompletion F)‖ ^ k * ‖(d : v.adicCompletion F)‖
        ≤ ‖(c : v.adicCompletion F)‖ ^ k * 1 := by gcongr
      _ = _ := mul_one _
  rw [hxv v, norm_mul]
  calc ‖(m : v.adicCompletion F)‖ * ‖(m : v.adicCompletion F)⁻¹ * x v‖
      ≤ ‖(c : v.adicCompletion F)‖ ^ k * 1 := by gcongr
    _ < ε v := by rw [mul_one]; exact hk v hv

end GlobalTheory.EvAdm

namespace GlobalTheory.EvAdm

theorem exists_scaledInt_subset_of_mem_nhds : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (W : Set (κ → FiniteAdeleRing (𝓞 F) F)),
    W ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) → ∃ a : F, a ≠ 0 ∧
      (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ W := by
  intro F _ _ κ _ W hW
  classical
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, _, t, ht, hIt⟩ := hW
  have ht' : ∀ i, t i ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := fun i => ht i
  choose N hN0 hN using fun i => exists_nat_scaled_subset F (t i) (ht' i)
  have hP : (∏ i, N i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hN0 i
  refine ⟨((∏ i, N i : ℕ) : F), Nat.cast_ne_zero.2 hP, fun z hz => hIt ?_⟩
  intro i _
  exact hN i _ hP (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) (z i) (fun v => hz i v)

end GlobalTheory.EvAdm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelDomainReduction
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

namespace GlobalTheory.SiegelHt

theorem cone_low {r : ℕ} {c : ℝ} (hc : 0 < c) {t : Fin r → ℝ}
    (ht : t ∈ GlobalTheory.SiegelSet.cone r c) (i : Fin r) : min 1 c ^ r ≤ t i := by
  obtain ⟨hpos, hstep, hlast⟩ := ht
  have hm0 : 0 < min 1 c := lt_min one_pos hc
  have hm1 : min 1 c ≤ 1 := min_le_left _ _
  have key : ∀ k : ℕ, ∀ i : Fin r, i.val + k + 1 = r → min 1 c ^ (k + 1) ≤ t i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      simp only [zero_add, pow_one]
      exact (min_le_right _ _).trans (hlast i (by omega))
    | succ k ih =>
      intro i hi
      have hj : i.val + 1 < r := by omega
      have h1 := ih ⟨i.val + 1, hj⟩ (by simp; omega)
      have h2 := hstep i ⟨i.val + 1, hj⟩ rfl
      have h3 : 0 < t ⟨i.val + 1, hj⟩ := hpos _
      calc min 1 c ^ (k + 1 + 1) = min 1 c * min 1 c ^ (k + 1) := by ring
        _ ≤ min 1 c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_left h1 hm0.le
        _ ≤ c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_right (min_le_right _ _) h3.le
        _ ≤ t i := h2
  have := key (r - i.val - 1) i (by omega)
  refine le_trans ?_ this
  exact pow_le_pow_of_le_one hm0.le hm1 (by omega)

end GlobalTheory.SiegelHt


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymTranslate
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

open MonoidalCategory CartesianMonoidalCategory MonObj _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
noncomputable section
namespace GlobalTheory.RiemannExists

theorem exists_sym_translate : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left) (hL : L.IsLB), Out.RelAmple B L → Out.KTriv B L → ∃ (L' : LB B.left) (hL' : L'.IsLB), Out.Rigidified B L' ∧ Out.Sym B L' ∧ Out.RelAmple B L' ∧ Out.KTriv B L' ∧ lam (cls L' hL') (fst B B) (snd B B) = lam (cls L hL) (fst B B) (snd B B) := by
  intro K _ _ B _ hB L hL ha hk
  have := hB.comm
  obtain ⟨c, hc⟩ := exists_gen_theta_of_isAbelianScheme K B hB L hL
  have hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen := ⟨c, hc⟩
  obtain ⟨O, hO, eO⟩ := CechPic.cls_surj (CechPic.pull (GrpObj.inv : B ⟶ B).left (cls L hL) - cls L hL)
  have hlam : lam (cls O hO) (fst B B) (snd B B) = 0 := by
    rw [eO, PrimitiveOverField.lam_sub, CechPic.lam_pull, ← Hom.inv_def, ← Hom.inv_def,
      FormPoly.lam_inv_left hL hΘ, FormPoly.lam_inv_right hL hΘ, neg_neg, sub_self]
  obtain ⟨b, hb⟩ := _root_.GlobalTheory.PointTranslate.exists_point_cls_eq_lam K B hB L hL hk O hO hlam
  obtain ⟨a, hab⟩ := SS.SemiDivisible.pow_surj_abelian K B hB (n := 2) (by norm_num) b
  have hL' : (RigidTranslate.rigTransl L a).IsLB := DVR.linComb_isLB _ hL _ _
  refine ⟨_, hL', RigidTranslate.rigidified_rigTransl hL, _root_.GlobalTheory.SymTranslate.sym_rigTransl_of_sq K B L hL hΘ a (by rw [← eO, hb, hab]),
    _root_.GlobalTheory.RigidTranslate.relAmple_rigTransl_point K B hB L hL a ha, _root_.GlobalTheory.RigidTranslate.kTriv_rigTransl_any _ B L hL a hk, ?_⟩
  have e := (CechPic.cls_eq_iff (LB.isLB_linComb hL' _ _) (pull_isLB (LB.isLB_linComb hL _ _) _)).2
    (RigidTranslate.lam_rigTransl (t := a) hL c hc)
  rw [CechPic.cls_pull (LB.isLB_linComb hL _ _), CechPic.pull_id] at e
  exact (CechPic.cls_cube_two hL' _ _ _).symm.trans (e.trans (CechPic.cls_cube_two hL _ _ _))

end GlobalTheory.RiemannExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticGroupMatrixOfPreservesPhaseSpace
section
open scoped SchwartzMap Matrix

namespace GlobalTheory

open Matrix

theorem sympl_eq_neg_dotProduct_J {l : Type} [Fintype l] [DecidableEq l] (w w' : l ⊕ l → ℝ) :
    GlobalTheory.RealWeil.sympl w w' = -(w ⬝ᵥ (J l ℝ *ᵥ w')) := by
  simp only [GlobalTheory.RealWeil.sympl, GlobalTheory.RealWeil.pPart, GlobalTheory.RealWeil.qPart, J, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fintype.sum_sum_type, fromBlocks_mulVec, Matrix.one_apply, Finset.sum_neg_distrib, mul_comm, Matrix.neg_mulVec, Matrix.one_mulVec]
  ring

theorem exists_symplecticGroup_of_sympl (l : Type) [Fintype l] [DecidableEq l]
    (ψ : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (h : ∀ w w', GlobalTheory.RealWeil.sympl (ψ w) (ψ w') = GlobalTheory.RealWeil.sympl w w') :
    ∃ M : Matrix.symplecticGroup l ℝ, ∀ w, (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w = ψ w := by
  set M := LinearMap.toMatrix' ψ with hM
  have hMv : ∀ w, M *ᵥ w = ψ w := fun w => by rw [hM, LinearMap.toMatrix'_mulVec]
  have key : ∀ w w', w ⬝ᵥ ((Mᵀ * J l ℝ * M) *ᵥ w') = w ⬝ᵥ (J l ℝ *ᵥ w') := by
    intro w w'
    have := h w w'
    rw [sympl_eq_neg_dotProduct_J, sympl_eq_neg_dotProduct_J, ← hMv, ← hMv] at this
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    linarith
  have hmem : M ∈ Matrix.symplecticGroup l ℝ := by
    rw [SymplecticGroup.mem_iff']
    ext i j
    have := key (Pi.single i 1) (Pi.single j 1)
    simpa [single_dotProduct, mulVec_single] using this
  exact ⟨⟨M, hmem⟩, hMv⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueArchimedeanMatrixAdeleExtensionOfCom
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.ArchMatCoords

theorem existsUnique_at_map_piInf :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    [Fintype α] [Fintype β] (τ : ∀ w : InfinitePlace F, EmbOver E w), IsCMExt F E σ →
    ∀ M : InfinitePlace F → Matrix α β ℂ, ∃! u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u ∧ ∀ w, u.map (piInf (τ w)) = M w := by
  intro F E _ _ _ _ _ σ α β _ _ τ hCM M
  have hex := fun i j => GlobalTheory.ThK.exists_at_evI_piInf_eq F E σ hCM τ (fun w => M w i j)
  choose z hzA hz using hex
  refine ⟨Matrix.of fun i j => z i j, ⟨?_, ?_⟩, ?_⟩
  · intro a ha
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact hzA i j a ha
  · intro w
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    exact hz i j w
  · rintro v ⟨hvA, hvM⟩
    ext i j
    simp only [Matrix.of_apply]
    have hd : v i j - z i j = 0 := by
      refine GlobalTheory.ArchInj.eq_zero_of_at_of_piInf F E σ hCM τ _ ?_ ?_
      · intro a ha
        have h1 : (a • v) i j = 0 := by rw [hvA a ha]; rfl
        rw [Matrix.smul_apply] at h1
        rw [smul_sub, h1, hzA i j a ha, sub_zero]
      · intro w
        have h2 := congrFun (congrFun (hvM w) i) j
        rw [Matrix.map_apply] at h2
        rw [map_sub, h2, hz i j w, sub_self]
    exact sub_eq_zero.1 hd

end GlobalTheory.ArchMatCoords
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryConjIffExistsCentralizerNorm
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitaryConj

theorem inv_h_form {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (h : GL (Fin n) K) :
    (h.val * cT σ h.val)⁻¹ = cT σ (h⁻¹).val * (h⁻¹).val := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (h⁻¹).val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul, cT_units]

theorem main : ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (γ h : GL (Fin n) K), (∃ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) K), h⁻¹ * γ * h = g⁻¹ * γ * g) ↔ ∃ c : Matrix (Fin n) (Fin n) K, c * γ.val = γ.val * c ∧ cT σ c * c = (h.val * cT σ h.val)⁻¹ := by
  intro K _ σ n γ h
  rw [inv_h_form]
  constructor
  · rintro ⟨g, hg, hconj⟩
    have hg' : cT σ g.val * 1 * g.val = 1 := hg
    rw [Matrix.mul_one] at hg'
    refine ⟨(g * h⁻¹).val, ?_, ?_⟩
    · have e : g * h⁻¹ * γ = γ * (g * h⁻¹) := by
        calc g * h⁻¹ * γ = g * (h⁻¹ * γ * h) * h⁻¹ := by group
          _ = g * (g⁻¹ * γ * g) * h⁻¹ := by rw [hconj]
          _ = γ * (g * h⁻¹) := by group
      simpa only [Units.val_mul] using congrArg Units.val e
    · rw [Units.val_mul, cT_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ g.val), hg', Matrix.one_mul]
  · rintro ⟨c, hc, hcc⟩
    have hdet : c.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hcc
      rw [Matrix.det_mul, h0, mul_zero] at this
      have hne : (cT σ (h⁻¹).val * (h⁻¹).val).det ≠ 0 := det_ne σ h
      exact hne this.symm
    let cu : GL (Fin n) K := ((Matrix.isUnit_iff_isUnit_det c).mpr (isUnit_iff_ne_zero.mpr hdet)).unit
    have hcu : cu.val = c := rfl
    have hcom : cu⁻¹ * γ * cu = γ := by
      have e : cu * γ = γ * cu := Units.ext (by simpa only [Units.val_mul, hcu] using hc)
      calc cu⁻¹ * γ * cu = cu⁻¹ * (γ * cu) := by group
        _ = cu⁻¹ * (cu * γ) := by rw [e]
        _ = γ := by group
    refine ⟨cu * h, ?_, ?_⟩
    · show cT σ (cu * h).val * 1 * (cu * h).val = 1
      rw [Matrix.mul_one, Units.val_mul, cT_mul, hcu, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ c), hcc]
      simp only [Matrix.mul_assoc]
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one, ← cT_mul, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, cT_one]
    · calc h⁻¹ * γ * h = h⁻¹ * (cu⁻¹ * γ * cu) * h := by rw [hcom]
        _ = (cu * h)⁻¹ * γ * (cu * h) := by group

end GlobalTheory.UnitaryConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalWeightEqCharacterExponentAdd
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict


open GlobalTheory.HolRead in
theorem extWt_arr_eq_wtCol {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : HCParam D.R) (p q : ℕ)
    (hpq : p + q = D.R.r) (hr : V.rank = D.R.r) (ρ : D.what₂.Tau)
    (hS : S ρ = Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q)) (c : Fin V.rank) :
    extWt M ρ (arr (nNeg (M.ε ρ)) c) = (wtCol h p q c : ℝ) := by
  have hn : p + q = V.rank := hpq.trans hr.symm
  have hp : p ≤ V.rank := by omega
  have he : IsEnum (Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q)) (M.lam ρ) (M.ε ρ) := hS ▸ M.enum ρ
  have hε : ∀ a, M.ε ρ a = decide ((a : ℕ) < p) := fun a => (isEnum_holPar_kapW h hr hn he a).2
  obtain ⟨hn', hx⟩ := GlobalTheory.HolDS.lowK_holPar (Formalism.L2.NTheta.holOK_kapW h p q hpq) he
  have hc := c.2
  by_cases hcq : (c : ℕ) < q
  · rw [extWt_arr M ρ hp hε c (Fin.cast hn' (finSumFinEquiv (Sum.inr ⟨c, hcq⟩ : Fin p ⊕ Fin q)))
      (by rw [if_pos (by omega)]; simp), hx]
    simp only [wtCol, if_pos hcq, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, Sum.elim_inr]
  · rw [extWt_arr M ρ hp hε c (Fin.cast hn' (finSumFinEquiv (Sum.inl ⟨c - q, by omega⟩ : Fin p ⊕ Fin q)))
      (by rw [if_neg (by omega)]; simp; omega), hx]
    simp only [wtCol, if_neg hcq, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, Sum.elim_inl]

theorem muVal_castDict {D : D7} {V W : HSp D} (hV : V = W) {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) :
    MuVal W χ (castDict hV mu) := by
  subst hV
  exact h

theorem extWt_eq_laU_add : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, ∀ w, WtIs (R.MW i σ) w → ∃ e : D.what₂.Tau → ℤ, (∀ u ∈ GinfC (Wc D i), castDict hV (T.mu ((i : ℕ) + 1) (res T σ)) u = ∏ ρ, (archM (Wc D i) (R.θ ρ) u).det ^ e ρ) ∧ ∀ k ρ (τ : ((T.U ((i : ℕ) + 1) (res T σ)).X k).Ψ), τ.1 = tauE D ρ → ∀ a : Fin (Wc D i).rank, w ρ a = (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) k τ (Fin.cast (rank_Wc i) a) + e ρ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hM ht i σ hσ hV w hw
  choose e he using fun ρ => (D.hc (lab σ ρ)).e_int i
  refine ⟨fun ρ => -e ρ, ?_, fun k ρ τ hτ a => ?_⟩
  · exact GlobalTheory.HolRead.mu_real_eq_prod_det D R.θ _ _ _ e hM.inf (muVal_castDict hV (ht.laws.muVal _ (inR i) _ hσ))
      fun ρ => he ρ ▸ (ht.chiR i σ hσ).2.2.1 ρ
  · have hs : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
    have hr : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.r := by
      have := D.R.m_add_three_le_k
      have hi := i.2
      simp only [Ranks.sigW, Ranks.r]
      omega
    have h1 := extWt_arr_eq_wtCol (R.MW i σ) (D.hc (lab σ ρ)) _ _ (hs ▸ hr :
      ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = D.R.r) (rank_Wc i) ρ
      (if_pos ((GlobalTheory.ConjReading.branch_of_pins T ht.alg ht.laws.pins σ ρ).1 hσ)) a
    rw [← hw ρ a, hs] at h1
    rw [GlobalTheory.HolRead.SecWt.laU_eq_wtCol D T κ ht.laws ht.alg ht.kap i σ hσ e (fun ρ => (he ρ).symm) k ρ τ hτ,
      Int.cast_injective h1]
    simp

end GlobalTheory.HolDict
end

