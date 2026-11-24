module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarCapelliTruncatedPerelomovPopov
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0112
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
public import Formalism.PeriodIntegrals.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiCentreEigenfunctionDiscreteSeries

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CapelliOfGelfand
section
open Formalism.REAL Finset Polynomial

open GlobalTheory.Dec (gelfVal)

namespace GlobalTheory.CapelliNewton

theorem gelfVal_zero (m : ℕ) (χ : Fin (m+1) → ℂ) : gelfVal χ 0 = (m:ℂ) + 1 := by
  simp [gelfVal, Matrix.one_apply]

theorem etr_apply_all {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℕ)
    (E : Fin (m+1) → Fin (m+1) → Module.End ℂ V) (χ : Fin (m+1) → ℂ)
    (hetr : ∀ (k : ℕ) (v : V), etr E (k + 1) v = gelfVal χ (k + 1) • v) (k : ℕ) (w : V) :
    etr E k w = gelfVal χ k • w := by
  cases k with
  | zero => rw [gelfVal_zero]; simp [etr, epow, add_smul]; rw [Nat.cast_smul_eq_nsmul]
  | succ k => exact hetr k w

noncomputable def polyOf {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) : ℂ[X] :=
  ∑ i ∈ range (d + 1), C (φ (c i v)) * X ^ i

theorem polyOf_eval {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) (u : ℂ) :
    (polyOf d c φ v).eval u = φ ((∑ i ∈ range (d + 1), u ^ i • c i) v) := by
  unfold polyOf
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eval_finsetSum, LinearMap.sum_apply, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, LinearMap.smul_apply, map_smul, smul_eq_mul, mul_comm]

theorem polyOf_natDegree {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) : (polyOf d c φ v).natDegree ≤ d := by
  unfold polyOf
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  exact Nat.lt_succ_iff.mp (mem_range.mp hi)

theorem polyOf_coeff {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) : (polyOf d c φ v).coeff d = φ (c d v) := by
  unfold polyOf
  rw [finsetSum_coeff, sum_eq_single d]
  · simp
  · intro b _ hb; simp [coeff_C_mul_X_pow, hb.symm]
  · intro h; exact absurd (self_mem_range_succ d) h

noncomputable def capQ (m : ℕ) (χ : Fin (m+1) → ℂ) : ℂ[X] := ∏ s, (X + C (χ s - (m : ℂ) / 2))

theorem capQ_eval (m : ℕ) (χ : Fin (m+1) → ℂ) (u : ℂ) :
    (capQ m χ).eval u = ∏ s, (u - (m : ℂ) / 2 + χ s) := by
  simp [capQ, eval_prod]; refine prod_congr rfl fun s _ => by ring

theorem capQ_monic (m : ℕ) (χ : Fin (m+1) → ℂ) : (capQ m χ).Monic :=
  monic_prod_of_monic _ _ fun s _ => monic_X_add_C _

theorem capQ_natDegree (m : ℕ) (χ : Fin (m+1) → ℂ) : (capQ m χ).natDegree = m + 1 := by
  unfold capQ
  rw [natDegree_prod_of_monic _ _ fun s _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem main_succ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ)
    (E : Fin (m+1) → Fin (m+1) → Module.End ℂ V) (χ : Fin (m+1) → ℂ) (hE : GlRel E)
    (hetr : ∀ (k : ℕ) (v : V), etr E (k + 1) v = gelfVal χ (k + 1) • v) (u : ℂ) (v : V) :
    qdet E u v = (∏ s, (u - (m : ℂ) / 2 + χ s)) • v := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun φ => ?_
  obtain ⟨c, hc1, hc⟩ := _root_.GlobalTheory.qdet_polyMap_monic (Module.End ℂ V) (m + 1) E
  set P := polyOf (m + 1) c φ v with hPdef
  have hP : ∀ w : ℂ, φ (qdet E w v) = P.eval w := fun w => by rw [polyOf_eval, hc]

  have hmin : ∀ i j : Fin (m + 1), ∃ c' : ℕ → Module.End ℂ V, ∀ w : ℂ,
      qminor E (Fin.succAbove j) (Fin.succAbove i) w = ∑ d ∈ range (m + 1), w ^ d • c' d := by
    intro i j
    obtain ⟨c', hc'⟩ := GlobalTheory.qminor_polyMap (Module.End ℂ V) (m + 1) m E (Fin.succAbove j) (Fin.succAbove i) 0
    exact ⟨c', fun w => by simpa using hc' w⟩
  choose cm hcm using hmin
  let N := m + 1
  let Rc : ℕ → Module.End ℂ V := fun d => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V) * cm i j d * epow E (N + 1) j i
  have hR : ∀ w : ℂ, ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V) * qminor E (Fin.succAbove j) (Fin.succAbove i) w * epow E (N + 1) j i
      = ∑ d ∈ range (m + 1), w ^ d • Rc d := by
    intro w
    simp only [Rc, hcm, mul_sum, sum_mul, smul_sum, mul_smul_comm, smul_mul_assoc]
    conv_lhs => enter [2, x]; rw [sum_comm]
    rw [sum_comm]
  set Rp := polyOf m Rc φ v
  have hrec : ∀ w : ℂ, (w - m) ^ (N + 1) * (P.eval (w + 1) - P.eval w) - P.eval w * ∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * gelfVal χ k = (C (-(-1) ^ N) * Rp).eval w := by
    intro w
    have h1 := congrArg (fun T : Module.End ℂ V => φ (T v)) (_root_.GlobalTheory.TracedComatrix.traced_comatrix (Module.End ℂ V) m E hE w N)
    rw [← _root_.GlobalTheory.qdet_add_one_sub_eq_sum_qminor, hR] at h1
    have h2 : (qdet E w * ∑ k ∈ range (N + 1), algebraMap ℂ (Module.End ℂ V) ((-1) ^ k * (w - m) ^ (N - k)) * etr E k) v
        = (∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * gelfVal χ k) • qdet E w v := by
      rw [Module.End.mul_apply, LinearMap.sum_apply]
      simp only [Module.End.mul_apply, Module.algebraMap_end_apply, etr_apply_all m E χ hetr, smul_smul]
      rw [← sum_smul, map_smul]
    rw [h2] at h1
    simp only [LinearMap.add_apply, Module.End.mul_apply, Module.algebraMap_end_apply, map_add (f := _), map_smul, LinearMap.sub_apply, map_sub, smul_eq_mul] at h1
    rw [← polyOf_eval] at h1
    simp only [hP] at h1
    simp only [eval_mul, eval_neg, eval_pow, eval_C]
    linear_combination h1
  obtain ⟨rs, hrs, hrsE⟩ := _root_.GlobalTheory.ScalarNewton.scalar_newton m N χ
  have hf := _root_.GlobalTheory.newton_recursion_poly_unique m N (gelfVal χ) (P - C (φ v) * capQ m χ) (C (-(-1) ^ N) * Rp - C (φ v) * rs)
    (Nat.lt_succ_self m) (gelfVal_zero m χ) ?_ ?_ ?_
  · have := congrArg (eval u) hf
    simp only [eval_sub, eval_mul, eval_C, eval_zero, capQ_eval] at this
    rw [map_sub, map_smul, hP, smul_eq_mul]; linear_combination this
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_sub, coeff_C_mul]
    rcases Nat.lt_or_ge (m + 1) k with h | h
    · rw [coeff_eq_zero_of_natDegree_lt ((polyOf_natDegree _ _ _ _).trans_lt h),
        coeff_eq_zero_of_natDegree_lt (by rw [capQ_natDegree]; exact h)]; simp
    · have hk' : k = m + 1 := le_antisymm h hk
      subst hk'
      have := (capQ_monic m χ).coeff_natDegree
      rw [capQ_natDegree] at this
      rw [this, polyOf_coeff, hc1]; simp
  · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_C_mul_le _ _ |>.trans (polyOf_natDegree _ _ _ _)
    · exact natDegree_C_mul_le _ _ |>.trans hrs
  · intro w
    have h1 := hrec w
    have h2 := hrsE w
    rw [← capQ_eval m χ (w + 1), ← capQ_eval m χ w] at h2
    simp only [eval_sub, eval_mul, eval_C] at h1 h2 ⊢
    linear_combination h1 - φ v * h2

end GlobalTheory.CapelliNewton

namespace GlobalTheory.CapelliNewton

theorem capelli_of_gelfand : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ), GlRel E → (∀ (k : ℕ) (v : V), etr E (k + 1) v = gelfVal χ (k + 1) • v) → ∀ (Y : ℂ) (v : V), qdet E (Y + ((n : ℂ) - 1) / 2) v = (∏ s, (Y + χ s)) • v := by
  intro V _ _ n E χ hE hetr Y v
  cases n with
  | zero => simp [qdet, qminor]
  | succ m =>
    rw [main_succ V m E χ hE hetr]
    congr 1
    refine prod_congr rfl fun s _ => ?_
    push_cast; ring

end GlobalTheory.CapelliNewton
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CasselmanWallachOfHyp
section
noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix Filter GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined
open scoped Topology

namespace GlobalTheory.CWGeneral

variable {n : ℕ} {ε : Fin n → Bool}

section Sub

variable {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]


end Sub

section KFin

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx n → (H →L[ℂ] H)}

theorem dense_smoothAll_of_irred (hσ : IsURepOn (UJset ε) σ) (hi : IsIrredOn (UJset ε) σ) :
    Dense (smoothAll (Jm ε) σ : Set H) := by
  rcases subsingleton_or_nontrivial H with hs | hn
  · intro x
    rw [Subsingleton.elim x 0]
    exact subset_closure (smoothAll (Jm ε) σ).zero_mem
  · refine dense_of_irred hi (fun g hg v hv k x hx hxG => ?_) ?_
    · letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
      letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
      have h1 := hv k (fun t => x t * g) (hx.mul contDiff_const) fun t => mul_mem_UJ (hxG t) hg
      convert h1 using 2 with t
      exact (sigma_mul hσ (hxG t) hg v).symm
    · obtain ⟨v, hv, hs⟩ := GlobalTheory.GardingVec.exists_garding hσ
      exact (Submodule.ne_bot_iff _).2 ⟨v, hs, hv⟩

theorem sm_of_isKFin (hHC : GlobalTheory.Published.HarishChandraModules) (hσ : IsURepOn (UJset ε) σ)
    (hi : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) : Sm ε σ v := by
  have := hHC.smoothVec hσ hi hv (P := 1) (G := Jm ε) isUnit_one (by simp)
  rwa [conj_one_eq] at this

theorem isKFin_dRep_of_irred (hHC : GlobalTheory.Published.HarishChandraModules) (hσ : IsURepOn (UJset ε) σ)
    (hi : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) {X : Mx n} (hX : X ∈ lieSet ε) :
    IsKFin ε σ (dRep σ X v) := by
  obtain ⟨S, h1, h2, h3⟩ := hv
  have hS : S ≤ smooth (Jm ε) σ := fun s hs => sm_of_isKFin hHC hσ hi ⟨S, h1, hs, h3⟩
  let b := Module.finBasis ℝ (lie (Jm ε))
  let L : Fin (Module.finrank ℝ (lie (Jm ε))) → (S →ₗ[ℂ] H) := fun i =>
    (smooth (Jm ε) σ).subtype ∘ₗ dOp (isUnit_Jm ε) hσ (b i).2 ∘ₗ Submodule.inclusion hS
  let T : Submodule ℂ H := ⨆ i, LinearMap.range (L i)
  have hT : ∀ Y ∈ lieSet ε, ∀ s ∈ S, dRep σ Y s ∈ T := by
    intro Y hY s hs
    have e : Y = ∑ i, b.repr ⟨Y, hY⟩ i • (b i : Mx n) := by
      have := congrArg Subtype.val (b.sum_repr ⟨Y, hY⟩)
      simpa only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] using this.symm
    rw [e, GlobalTheory.LowTypeDetermined.dRep_sum (isUnit_Jm ε) hσ (dense_smoothAll_of_irred hσ hi) (fun i => (b i).2)
      (hS hs)]
    refine T.sum_mem fun i _ => T.smul_mem _ ?_
    exact Submodule.mem_iSup_of_mem i ⟨⟨s, hs⟩, rfl⟩
  refine ⟨T, inferInstance, hT X hX v h2, fun k hk w hw => ?_⟩
  have hg := K_le_UJ hk
  have : T ≤ T.comap (σ k : H →ₗ[ℂ] H) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨s, rfl⟩
    have hinv : (k⁻¹)⁻¹ = k := Matrix.inv_eq_left_inv (mul_inv_UJ hg)
    have hY : k * (b i : Mx n) * k⁻¹ ∈ lieSet ε := by
      have := conj_mem_lie (isUnit_Jm ε) (inv_mem_UJ hg) (b i).2
      rwa [hinv] at this
    have e := Dw_translate hσ hg (hS s.2) (l := [k * (b i : Mx n) * k⁻¹]) (by simpa using hY)
    have e2 : k⁻¹ * (k * (b i : Mx n) * k⁻¹) * k = b i := by
      rw [← mul_assoc, ← mul_assoc, inv_mul_UJ hg, one_mul, mul_assoc, inv_mul_UJ hg, mul_one]
    simp only [Dw, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, e2] at e
    show σ k (dRep σ (b i) s) ∈ T
    rw [← e]
    exact hT _ hY _ (h3 k hk s s.2)
  exact this hw

end KFin

end GlobalTheory.CWGeneral

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefIntegralEq
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

def emb {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (y : Mx D a b) : WO V W :=
  HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D))

def meanX {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)) (F : WO V W → ℂ)
    (x : WO V W) : ℂ :=
  ∫ y in 𝓨, F (emb V W P Q y + x) ∂μ

theorem emb_add {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (y y' : Mx D a b) :
    emb V W P Q (y + y') = emb V W P Q y + emb V W P Q y' := by
  simp only [emb, Matrix.mul_add, Matrix.add_mul]

theorem emb_zero {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) : emb V W P Q (0 : Mx D a b) = 0 := by
  simp [emb]

theorem meanX_translate : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne ((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b)).range μ 𝓨 → ∀ F : WO V W → ℂ, IsThetaFunO ψ V W F → ∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∀ y₀ : Mx D a b, GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F (GlobalTheory.IsoMean.emb V W P Q y₀ + x) = GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F x := by
  intro D V W a b P Q hiso ψ hψ μ 𝓨 hμ F hF x hx y₀
  obtain ⟨hHaar, h𝓨, -⟩ := hμ
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH0 : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e

  set f : Mx D a b → ℂ := fun y => F (emb V W P Q y + x) with hf
  have per : ∀ γ ∈ ((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b)).range, ∀ y, f (γ + y) = f y := by
    rintro _ ⟨γ, rfl⟩ y
    have hr : emb V W P Q ((incA D).toAddMonoidHom.mapMatrix γ) = ratW W V (P * γ * Q) := by
      simp [emb, ratW, Matrix.map_mul]
    simp only [hf]
    rw [emb_add, add_assoc, hr, hF.quasi, ← hr, l2, hH0 _ _ (hiso _ _), skew, hH0 _ _ (hx _), neg_zero,
      add_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]
  have e1 : meanX V W P Q μ 𝓨 F (emb V W P Q y₀ + x) = ∫ y in 𝓨, f (y₀ + y) ∂μ := by
    unfold meanX
    congr 1; funext y
    simp only [hf, emb_add]
    congr 1; abel
  rw [e1]
  haveI : Countable D.host.E := by
    haveI : FiniteDimensional ℚ D.host.E := inferInstance
    exact (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  have hmp : MeasurePreserving (fun y : Mx D a b => y₀ + y) μ μ := measurePreserving_add_left μ y₀
  have hemb : MeasurableEmbedding (fun y : Mx D a b => y₀ + y) := (MeasurableEquiv.addLeft y₀).measurableEmbedding
  haveI : Countable (Matrix (Fin a) (Fin b) D.host.E) := inferInstanceAs (Countable (Fin a → Fin b → D.host.E))
  haveI : Countable (((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b)).range) := (Set.countable_range _).to_subtype
  rw [← hmp.setIntegral_image_emb hemb f 𝓨]
  haveI : VAddInvariantMeasure (Mx D a b) (Mx D a b) μ := ⟨fun c s _ => measure_preimage_add μ c s⟩
  have h2 := h𝓨.vadd_of_comm y₀
  rw [← Set.image_vadd] at h2
  exact h2.setIntegral_eq h𝓨 fun g y => per g g.2 y

theorem coef_integral_eq : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (κ : Measure (Mx D a b)), κ.IsAddHaarMeasure → ∀ (g : GA D V) (h : GA D W), (∀ y : Mx D a b, actO V W g h (GlobalTheory.IsoMean.emb V W P Q y) = GlobalTheory.IsoMean.emb V W P Q y) → (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∃ y : Mx D a b, actO V W g h x = x + GlobalTheory.IsoMean.emb V W P Q y) → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ f f' : WO V W → ℂ, IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → ∀ w : WO V W, (∀ y : Mx D a b, symplO V W w (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) (ω (g, h) f) u * star (ω (g, h) f' u) ∂ν) ∂κ = ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) f u * star (f' u) ∂ν) ∂κ := by
  intro D V W a b P Q ψ χS χT ω hω κ hκ g h hfix hunip ν 𝓕 hν h𝓕 f f' hf hf' w hw
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  have hψ := hω.std
  obtain ⟨y₀, hy₀⟩ := hunip w hw
  have key : ∀ y : Mx D a b,
      ∫ u in 𝓕, heisO ψ V W (w + emb V W P Q (y₀ + y)) (ω (g, h) f) u * star (ω (g, h) f' u) ∂ν =
        ∫ u in 𝓕, heisO ψ V W (w + emb V W P Q y) f u * star (f' u) ∂ν := by
    intro y
    have e : ω (g, h) (heisO ψ V W (w + emb V W P Q y) f) =
        heisO ψ V W (w + emb V W P Q (y₀ + y)) (ω (g, h) f) := by
      have hadd : actO V W g h (w + emb V W P Q y) = actO V W g h w + actO V W g h (emb V W P Q y) := by
        simp only [actO, Matrix.mul_add, Matrix.add_mul]
      rw [hω.om_heis g h _ f hf, hadd, hy₀, hfix, emb_add, add_assoc]
    rw [← e]
    exact GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ V W ν 𝓕 hν h𝓕 (ω (g, h)) (fun f hf => hω.om_pres _ f hf)
      (fun f hf => hω.om_unit ν 𝓕 hν h𝓕 _ f hf) _ f' (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _) hf'
  rw [← integral_add_left_eq_self _ y₀]
  exact integral_congr_ae (Filter.Eventually.of_forall key)

end GlobalTheory.IsoMean

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletionTensorAllRootsMapBijectiveCm
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll GlobalTheory.TrEll.RealTorus
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RealTorus

theorem subring_pi_mem_of_const_of_injective {ι : Type} [Fintype ι] [DecidableEq ι] (R : Subring (ι → ℂ))
    (hc : ∀ c : ℂ, (fun _ => c) ∈ R) (a : ι → ℂ) (ha : Function.Injective a) (haR : a ∈ R) (x : ι → ℂ) :
    x ∈ R := by
  have hp : ∀ p : ℂ[X], (fun i => p.eval (a i)) ∈ R := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      have := R.add_mem hp hq
      convert this using 1
      ext i; simp
    | monomial n c =>
      have := R.mul_mem (hc c) (R.pow_mem haR n)
      convert this using 1
      ext i; simp [eval_monomial]
  have := hp (Lagrange.interpolate Finset.univ a x)
  convert this using 1
  ext i
  exact (Lagrange.eval_interpolate_at_node x ha.injOn (Finset.mem_univ i)).symm

theorem exists_extensionEmbedding_eq_ofReal {F : Type} [Field F] [NumberField F] {w : InfinitePlace F}
    (hw : w.IsReal) (t : ℝ) : ∃ a : w.Completion, InfinitePlace.Completion.extensionEmbedding w a = (t : ℂ) := by
  refine ⟨(InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t, ?_⟩
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw,
    ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply]

theorem PsiAll_surjective {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} [_root_.NumberField.IsTotallyComplex E] {r : ℕ} (P : PPol σ r) {w : InfinitePlace F} (hw : w.IsReal)
    (τ : EmbOver E w) : Function.Surjective (PsiAll P τ) := by
  intro x
  have hτ : ¬ ComplexEmbedding.IsReal τ.1 := IsTotallyComplex.complexEmbedding_not_isReal τ.1
  have : ∃ e : E, (τ.1 e).im ≠ 0 := by
    by_contra h
    push_neg at h
    apply hτ
    rw [ComplexEmbedding.isReal_iff]
    ext e
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.2 (h e)
  obtain ⟨e, he⟩ := this
  refine subring_pi_mem_of_const_of_injective (PsiAll P τ).range ?_ (cxRoots τ.1 P) (cxRoots_injective P τ) ?_ x
  · intro c
    obtain ⟨a, ha⟩ := exists_extensionEmbedding_eq_ofReal hw (c.re - c.im / (τ.1 e).im * (τ.1 e).re)
    obtain ⟨b, hb⟩ := exists_extensionEmbedding_eq_ofReal hw (c.im / (τ.1 e).im)
    refine ⟨a ⊗ₜ[F] 1 + b ⊗ₜ[F] algebraMap E (Fld P) e, ?_⟩
    ext i : 1
    rw [PsiAll_apply, map_add (f := _), Psi_tmul, Psi_tmul, psiL_algebraMap, map_one, ha, hb, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]; ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul]; field_simp; ring
  · refine ⟨1 ⊗ₜ[F] alpha P, ?_⟩
    ext i : 1
    rw [PsiAll_apply, Psi_tmul, psiL_alpha, map_one, one_mul]

theorem PsiAll_bijective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), Function.Bijective (PsiAll P τ) := by
  intro F E _ _ _ _ _ σ hCM r P w τ
  haveI : IsTotallyReal F := hCM.1
  haveI : IsTotallyComplex E := hCM.2.1
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  have hw : w.IsReal := IsTotallyReal.isReal w
  have hs := PsiAll_surjective P hw τ
  refine ⟨?_, hs⟩
  letI : Algebra w.Completion ℂ := (InfinitePlace.Completion.extensionEmbedding w).toAlgebra
  let f : w.Completion ⊗[F] Fld P →ₗ[w.Completion] (Fin r → ℂ) :=
    { toFun := PsiAll P τ
      map_add' := map_add _
      map_smul' := fun a y => by
        rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply]
        ext i
        rw [Pi.mul_apply, PsiAll_apply, Psi_tmul, map_one, mul_one, Pi.smul_apply, Algebra.smul_def]
        rfl }
  have hk : Module.finrank w.Completion ℂ = 2 := by
    rw [Algebra.finrank_eq_of_equiv_equiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (RingEquiv.refl ℂ) ?_,
      Complex.finrank_real_complex]
    ext x
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw x
  haveI : Module.Finite w.Completion ℂ := Module.finite_of_finrank_pos (by omega)
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  haveI : Module.Finite E (Fld P) := (AdjoinRoot.powerBasis P.2.2.1.ne_zero).finite
  haveI : Module.Finite F (Fld P) := Module.Finite.trans E (Fld P)
  have hd : Module.finrank w.Completion (w.Completion ⊗[F] Fld P) = Module.finrank w.Completion (Fin r → ℂ) := by
    rw [Module.finrank_baseChange, ← Module.finrank_mul_finrank F E (Fld P), h2, finrank_Fld,
      Module.finrank_pi_fintype]
    simp [hk, mul_comm]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f) hd).2 hs

end GlobalTheory.TrEll.RealTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ElementaryTracePowerCyclicWords
section
open scoped InnerProductSpace

namespace GlobalTheory.TraceCycWord

theorem etr_succ_eq_sum_cycWord : ∀ {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (m : ℕ),
    Formalism.REAL.etr E (m + 1) = ∑ a : Fin (m + 1) → Fin n, ((GlobalTheory.Dec.cycWord a).map fun p => E p.1 p.2).prod := by
  intro A _ n E m
  rw [GlobalTheory.PhiEigenfun.sum_cycWord, Formalism.REAL.etr]
  exact Finset.sum_congr rfl fun c _ => GlobalTheory.PhiEigenfun.epow_eq E (m + 1) c c

end GlobalTheory.TraceCycWord
end

