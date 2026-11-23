module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0753
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0815
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0009
public import Formalism.LocalToGlobal.Columns.MtAdWt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightSpanOfIndep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellDecompositionLatticeIntegralUnfolding
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCell.CptMod

variable {E : Type} [Field E] [NumberField E]

theorem continuous_finGL_cpt {a : ℕ} : Continuous (finGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) :=
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

theorem exists_pLoc_ite {n : ℕ} (c : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin n) (w.adicCompletion E))
    (T : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ h : GL (Fin n) (Af E), ∀ w, GeneralLinearGroup.map (pLoc E w) h = if w ∈ T then c w else 1 := by
  induction T using Finset.induction_on with
  | empty => exact ⟨1, fun w => by simp⟩
  | insert v T hvT ih =>
    obtain ⟨h, hh⟩ := ih
    refine ⟨locGL E n v (c v) * h, fun w => ?_⟩
    rw [map_mul, hh w]
    by_cases hw : w = v
    · subst hw
      rw [pLoc_locGL, if_neg hvT, if_pos (Finset.mem_insert_self _ _), mul_one]
    · rw [pLoc_locGL_of_ne hw, one_mul]
      simp [Finset.mem_insert, hw]

theorem isCompact_intGL (n : ℕ) :
    IsCompact {κ : GL (Fin n) (Af E) | ∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ GlobalTheory.LFun.KGL w (n := n)} := by
  convert GlobalTheory.isCompact_KGL E n using 1
  ext κ
  simp only [Set.mem_setOf_eq, GlobalTheory.LFun.KGL, GlobalTheory.CellDec.mem_GLint_iff_entries_cell, ← map_inv]
  constructor
  · intro h
    exact ⟨fun i j v => (h v).1 i j, fun i j v => (h v).2 i j⟩
  · intro h v
    exact ⟨fun i j => h.1 i j v, fun i j => h.2 i j v⟩

theorem row_mul_inv {R : Type} [CommRing R] {n : ℕ} {A B : GL (Fin n) R} {i : Fin n}
    (h : (A : Matrix (Fin n) (Fin n) R) i = (B : Matrix (Fin n) (Fin n) R) i) :
    ((A * B⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i = (1 : Matrix (Fin n) (Fin n) R) i := by
  funext j
  rw [Units.val_mul, Matrix.mul_apply, h, ← Matrix.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem row_last_unip_mul {R : Type} [CommRing R] {m : ℕ} {u : GL (Fin (m + 1)) R}
    (hu : u ∈ GlobalTheory.SmGL.unipB R (Fin (m + 1))) (k : GL (Fin (m + 1)) R) :
    ((u * k : GL (Fin (m + 1)) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (Fin.last m) =
      (k : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (Fin.last m) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 hu
  funext j
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
  · rw [h2, one_mul]
  · intro i _ hi
    rw [h1 _ _ (lt_of_le_of_ne (Fin.le_last i) hi), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem row_tl_mul {n : ℕ} (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {i : Fin n} (hl : ∀ w, l w i = 0) (g : GA E n) :
    ((GlobalTheory.CellDec.tl n ϖ l * g : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i = (g : Matrix (Fin n) (Fin n) (Ad E)) i := by
  have h0 : Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l = 0 := by
    ext w
    simp [hl w]
  funext j
  rw [GlobalTheory.CellDec.tl_eq_diagT, Units.val_mul, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_mul]
  simp only [h0, GlobalTheory.CellDec.adl_zero, map_one, Units.val_one, one_mul]

theorem compV_tl_eq_one {n : ℕ} (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {w : HeightOneSpectrum (𝓞 E)} (hw : l w = 0) :
    GlobalTheory.CellDec.compV E n w (GlobalTheory.CellDec.tl n ϖ l) = 1 := by
  rw [GlobalTheory.CellDec.compV_tl, hw]
  apply Units.ext
  rw [GlobalTheory.IwaCell.val_tD]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply]

theorem tl_mul_comm [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) {T : Finset (HeightOneSpectrum (𝓞 E))}
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (hl : ∀ v ∈ T, l v = 0) {p : GA E n}
    (hp : ∀ w ∉ T, GlobalTheory.CellDec.compV E n w p = 1) :
    GlobalTheory.CellDec.tl n ϖ l * p = p * GlobalTheory.CellDec.tl n ϖ l := by
  apply ga_ext
  · simp [GlobalTheory.CellDec.tl, map_mul]
  · apply GlobalTheory.CellDec.GL_ext_pLoc
    intro w
    change GlobalTheory.CellDec.compV E n w (GlobalTheory.CellDec.tl n ϖ l * p) = GlobalTheory.CellDec.compV E n w (p * GlobalTheory.CellDec.tl n ϖ l)
    rw [map_mul, map_mul]
    by_cases hw : w ∈ T
    · rw [compV_tl_eq_one ϖ l (hl w hw), one_mul, mul_one]
    · rw [hp w hw, one_mul, mul_one]

end GlobalTheory.RSCell.CptMod

namespace GlobalTheory.RSCell.CptMod

open scoped Pointwise

theorem exists_isCompact_mod_NA : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (F : GA E (m + 1) → ℂ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T) (U : Subgroup (GL (Fin (m + 1)) (Af E))) (Φ : (Fin (m + 1) → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (C : Set (GA E (m + 1))), IsCompact C →
    (∀ w, l₀.1 w (Fin.last m) = 0) → (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * p ∈ C) →
    HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ KGL w (n := (m + 1))) ∧ (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∃ K : Set (GA E (m + 1)), IsCompact K ∧ ∀ (x : ℝ) (g : GA E (m + 1)), g ∈ GlobalTheory.CellDec.C0 E (m + 1) T →
      GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * g ∈ K := by
  intro E _ _ _ m T ϖ hϖ F l₀ U Φ J C hC hl0 hU hKT hN hsupp hΦ hΦs hJ horb
  set K₁ : Set (GA E (m + 1)) :=
    finGL E (m + 1) '' {κ | ∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ GlobalTheory.LFun.KGL w (n := (m + 1))} with hK₁d
  set K₂ : Set (GA E (m + 1)) :=
    (fun u => infGL E (m + 1) (GlobalTheory.RSTheta.rowGL (Fin.last m) u)) '' tsupport Φ with hK₂d
  have hK₁ : IsCompact K₁ := (isCompact_intGL (m + 1)).image continuous_finGL_cpt
  have hK₂ : IsCompact K₂ := (show IsCompact (tsupport Φ) from hΦ).image_of_continuousOn
    (GlobalTheory.CuspQuot.continuous_infGL.comp_continuousOn ((GlobalTheory.RSTheta.continuousOn_rowGL (Fin.last m)).mono hΦs))
  refine ⟨C * K₁ * K₂ * K₁, ((hC.mul hK₁).mul hK₂).mul hK₁, ?_⟩
  intro x g hg hB
  obtain ⟨u₁, hu₁, k, hk, rfl⟩ := hg
  set t := GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 with ht
  have hrow : ((t * (u₁ * k) : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) =
      (k : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) := by
    rw [row_tl_mul ϖ l₀.1 hl0, row_last_unip_mul hu₁]
  set u : Fin (m + 1) → Cinf E := fun i => pInf E ((k : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) i) with hud
  set yf : Fin (m + 1) → Af E := fun i => pFin E ((k : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) i) with hyf
  set σ := infGL E (m + 1) (GlobalTheory.RSTheta.rowGL (Fin.last m) u) with hσ
  have hB1 := left_ne_zero_of_mul hB
  rw [enorm_ne_zero] at hB1
  unfold GlobalTheory.RSTheta.rsPsi GlobalTheory.ThetaPoisson.thetaFn at hB1
  rw [hrow] at hB1
  obtain ⟨hB2, hlat⟩ := mul_ne_zero_iff.1 hB1
  have hlat' : yf - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J := Set.mem_of_indicator_ne_zero hlat
  unfold GlobalTheory.RSTheta.rsInf at hB2
  obtain ⟨hB3, hΦu⟩ := mul_ne_zero_iff.1 hB2
  have hW : GlobalTheory.JSW.whit F (t * (u₁ * k) * σ⁻¹) ≠ 0 := left_ne_zero_of_mul hB3
  have hu_supp : u ∈ tsupport Φ := subset_tsupport _ (Function.mem_support.2 hΦu)
  have hunit : IsUnit (u (Fin.last m)) := GlobalTheory.RSTheta.isUnit_of_mem_rowSet (hΦs hu_supp)
  obtain ⟨κ, hκU, hκK, hκ1, hκrow⟩ := horb yf hlat'
  obtain ⟨hf, hhf⟩ := exists_pLoc_ite (fun w => GlobalTheory.CellDec.compV E (m + 1) w k) T
  set h := infGL E (m + 1) (GeneralLinearGroup.map (pInf E) k) * finGL E (m + 1) hf with hhd
  set kT := h⁻¹ * k with hkTd
  have hcV_inf : ∀ w (y : GL (Fin (m + 1)) (Cinf E)), GlobalTheory.CellDec.compV E (m + 1) w (infGL E (m + 1) y) = 1 := by
    intro w y
    change GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (infGL E (m + 1) y)) = 1
    rw [pFin_infGL, map_one]
  have hcV_h : ∀ w, GlobalTheory.CellDec.compV E (m + 1) w h = if w ∈ T then GlobalTheory.CellDec.compV E (m + 1) w k else 1 := by
    intro w
    rw [hhd, map_mul, hcV_inf, GlobalTheory.CellDec.compV_finGL, hhf w, one_mul]
  have hinf_h : GeneralLinearGroup.map (pInf E) h = GeneralLinearGroup.map (pInf E) k := by
    rw [hhd, map_mul, pInf_infGL, pInf_finGL, mul_one]
  have hkT_inf : GeneralLinearGroup.map (pInf E) kT = 1 := by
    rw [hkTd, map_mul, map_inv, hinf_h, inv_mul_cancel]
  have hkT_T : ∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w kT = 1 := by
    intro w hw
    rw [hkTd, map_mul, map_inv, hcV_h, if_pos hw, inv_mul_cancel]
  have hkT_US : kT ∈ GlobalTheory.CellDec.US E (m + 1) T := GlobalTheory.CellDec.mem_US.2 fun w hw => by
    rw [hkTd, map_mul, map_inv, hcV_h, if_neg hw, inv_one, one_mul]
    exact GlobalTheory.CellDec.mem_US.1 hk w hw
  have hkT_fin : kT = finGL E (m + 1) (GeneralLinearGroup.map (pFin E) kT) := by
    conv_lhs => rw [← infGL_mul_finGL kT]
    rw [hkT_inf, map_one, one_mul]
  have hkT_K : ∀ w, GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) kT) ∈ GlobalTheory.LFun.KGL w (n := (m + 1)) := by
    intro w
    change GlobalTheory.CellDec.compV E (m + 1) w kT ∈ _
    by_cases hw : w ∈ T
    · rw [hkT_T w hw]
      exact one_mem _
    · exact GlobalTheory.CellDec.mem_US.1 hkT_US w hw
  set B := finGL E (m + 1) κ * σ with hBd
  have hrowB : (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) =
      (B : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) := by
    funext j
    apply ad_ext
    · change (GeneralLinearGroup.map (pInf E) h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j =
        (GeneralLinearGroup.map (pInf E) B : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j
      rw [hinf_h, hBd, map_mul, pInf_finGL, one_mul, hσ, pInf_infGL, GlobalTheory.RSTheta.val_rowGL hunit,
        GlobalTheory.RSTheta.rowMat, Matrix.updateRow_self]
      rfl
    · apply IsDedekindDomain.FiniteAdeleRing.ext
      intro w
      change (GlobalTheory.CellDec.compV E (m + 1) w h : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
        (GlobalTheory.CellDec.compV E (m + 1) w B : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j
      rw [hcV_h, hBd, map_mul, GlobalTheory.CellDec.compV_finGL, hσ, hcV_inf, mul_one]
      split_ifs with hw
      · rw [hκrow w hw j]
        rfl
      · rw [hκ1 w hw]
  set p := h * B⁻¹ with hpd
  have hp_sup : ∀ w ∉ T, GlobalTheory.CellDec.compV E (m + 1) w p = 1 := by
    intro w hw
    rw [hpd, map_mul, map_inv, hcV_h, if_neg hw, hBd, map_mul, GlobalTheory.CellDec.compV_finGL, hκ1 w hw, hσ, hcV_inf,
      mul_one, inv_one, one_mul]
  have hp_mir : p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) := by
    refine ⟨fun w hw => hp_sup w hw, fun j => ?_⟩
    have e := congrFun (row_mul_inv hrowB) j
    rw [← hpd] at e
    rw [e, Matrix.one_apply]
    by_cases hj : j = Fin.last m
    · rw [if_pos hj.symm, if_pos hj]
    · rw [if_neg (Ne.symm hj), if_neg hj]
  have hcomm : kT * σ⁻¹ = σ⁻¹ * kT := by
    rw [hkT_fin, hσ, ← map_inv]
    exact (infGL_comm _ _).symm
  have hnorm : ‖GlobalTheory.JSW.whit F (t * (u₁ * k) * σ⁻¹)‖ = ‖GlobalTheory.JSW.whit F (p * t)‖ := by
    have e1 : t * (u₁ * k) * σ⁻¹ = (t * u₁ * t⁻¹) * (t * k * σ⁻¹) := by group
    rw [e1, hN _ (GlobalTheory.CellDec.tl_conj_mem ϖ l₀.1 hu₁)]
    have e2 : t * k * σ⁻¹ = t * h * σ⁻¹ * kT := by
      rw [mul_assoc (t * h), ← hcomm, hkTd]
      group
    rw [e2, hKT kT hkT_US hkT_inf hkT_T]
    have e3 : t * h * σ⁻¹ = t * p * finGL E (m + 1) κ := by
      rw [hpd, hBd]
      group
    rw [e3, hU κ hκU, tl_mul_comm ϖ l₀.1 l₀.2 hp_sup]
  have hWp : GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 := by
    rw [← ht, ← norm_ne_zero_iff, ← hnorm, norm_ne_zero_iff]
    exact hW
  obtain ⟨u₂, hu₂, hu₂C⟩ := hsupp p hp_mir hWp
  refine ⟨u₂ * u₁⁻¹, mul_mem hu₂ (inv_mem hu₁), ?_⟩
  have e : u₂ * u₁⁻¹ * (u₁ * k) = u₂ * p * finGL E (m + 1) κ * σ * finGL E (m + 1) (GeneralLinearGroup.map (pFin E) kT) := by
    rw [← hkT_fin, hpd, hBd, hkTd]
    group
  rw [e]
  exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul hu₂C ⟨κ, hκK, rfl⟩) ⟨u, hu_supp, rfl⟩) ⟨_, hkT_K, rfl⟩

end GlobalTheory.RSCell.CptMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContragredientPolynomialWeightUniqueHighestWeigh
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.MtContraHw

open GlobalTheory.CoefModel _root_.Formalism.L2.Col

section Irr

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι]

theorem pair_inv (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) (γ : ReciprocityTheory.Aut.GQ L n) (x y : VV ℂ lam) :
    pairBK lam (mtRep emb lam γ x) (tenRep emb lam γ y) = pairBK lam x y :=
  (pairBK_apply lam _ _).trans ((pairingBInvariantK_holds ℂ ι n lam
    (mtwEmb emb (mtwRat (L := L) (n := n) γ)) (x : VV ℂ lam).1
    (y : VV ℂ lam).1).trans (pairBK_apply lam x y).symm)

theorem tenIrr_conj (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) (h : TenIrr emb lam) :
    TenIrr (mtwConj emb) lam := by
  unfold TenIrr
  rw [mtRep_eq_tenRep, mtwConj_conj]
  haveI : FiniteDimensional ℂ (VV ℂ lam) := Module.Finite.of_basis (bVV ℂ lam)
  have hd := GlobalTheory.WtDual.dual_isIrreducible (mtRep emb lam) h
  let Φ : VV ℂ lam →ₗ[ℂ] Module.Dual ℂ (VV ℂ lam) := (pairBK lam).flip
  have hΦ : ∀ x y, Φ y x = pairBK lam x y := fun x y => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact (pairingBNondegenerate_holds ℂ ι n lam).2 y fun x => by
      rw [← hΦ, hy]
      rfl
  have hdim : Module.finrank ℂ (VV ℂ lam) = Module.finrank ℂ (Module.Dual ℂ (VV ℂ lam)) :=
    (Subspace.dual_finrank_eq).symm
  let E := LinearMap.linearEquivOfInjective Φ hinj hdim
  have hE : ∀ y, E y = Φ y := fun y => rfl
  refine GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv (mtRep emb lam).dual (tenRep emb lam) E.symm
    (fun g f => ?_) hd
  apply E.injective
  rw [LinearEquiv.apply_symm_apply, hE]
  obtain ⟨y, rfl⟩ := E.surjective f
  rw [LinearEquiv.symm_apply_apply, hE]
  ext x
  rw [hΦ, Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, hΦ]
  have := pair_inv emb lam g ((mtRep emb lam g⁻¹) x) y
  rw [Representation.self_inv_apply] at this
  exact this

end Irr
end GlobalTheory.MtContraHw

namespace GlobalTheory.MtContraHw

open GlobalTheory.CoefModel _root_.Formalism.L2.Col

section Omega

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] (e : K →+* ℂ) (lam : ι → DomWeight n)

def bC : Module.Basis (VVIdx lam) ℂ (VV ℂ lam) :=
  Module.Basis.mk (linearIndependent_mapVV e lam) (span_mapVV e lam).ge

theorem bC_apply (i : VVIdx lam) : bC e lam i = mapVV e lam (bVV K lam i) := by
  simp [bC]

variable {W : Type} [AddCommGroup W] [Module K W] (T : W ≃ₗ[K] VV K lam)

def omegaV : Module.Dual K W →ₛₗ[e] Module.Dual ℂ (VV ℂ lam) where
  toFun f := (bC e lam).constr ℂ fun i => e (f (T.symm (bVV K lam i)))
  map_add' f g := by
    rw [← ((bC e lam).constr ℂ).map_add]
    congr 1
    funext i
    simp only [Pi.add_apply, LinearMap.add_apply, map_add]
  map_smul' c f := by
    rw [← ((bC e lam).constr ℂ).map_smul]
    congr 1
    funext i
    simp only [Pi.smul_apply, LinearMap.smul_apply, smul_eq_mul, map_mul]

theorem omegaV_bC (f : Module.Dual K W) (i : VVIdx lam) :
    omegaV e lam T f (bC e lam i) = e (f (T.symm (bVV K lam i))) := by
  simp [omegaV, Module.Basis.constr_basis]

theorem omegaV_mapVV (f : Module.Dual K W) (x : VV K lam) :
    omegaV e lam T f (mapVV e lam x) = e (f (T.symm x)) := by
  conv_lhs => rw [← (bVV K lam).sum_repr x]
  conv_rhs => rw [← (bVV K lam).sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, ← bC_apply, LinearMap.map_smul, omegaV_bC, smul_eq_mul, map_mul, RingHom.id_apply, LinearEquiv.map_smul, LinearMap.map_smul]

end Omega
end GlobalTheory.MtContraHw

namespace GlobalTheory.MtContraHw

open GlobalTheory.CoefModel _root_.Formalism.L2.Col

section Props

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] (e : K →+* ℂ) (lam : ι → DomWeight n)
  {W : Type} [AddCommGroup W] [Module K W] (T : W ≃ₗ[K] VV K lam)

def coordK : Module.Dual K W →ₗ[K] VV K lam :=
  (bVV K lam).equivFun.symm.toLinearMap ∘ₗ LinearMap.pi fun i => Module.Dual.eval K W (T.symm (bVV K lam i))

def coordC : Module.Dual ℂ (VV ℂ lam) →ₗ[ℂ] VV ℂ lam :=
  (bC e lam).equivFun.symm.toLinearMap ∘ₗ LinearMap.pi fun i => Module.Dual.eval ℂ (VV ℂ lam) (bC e lam i)

theorem coordK_ker : LinearMap.ker (coordK lam T) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro f hf
  have h1 : ∀ i, f (T.symm (bVV K lam i)) = 0 := by
    intro i
    have h0 := congrArg (bVV K lam).equivFun hf
    simp only [coordK, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, map_zero] at h0
    simpa using congrFun h0 i
  have h2 : f ∘ₗ T.symm.toLinearMap = 0 := (bVV K lam).ext fun i => by simpa using h1 i
  ext w
  have := LinearMap.congr_fun h2 (T w)
  simpa using this

theorem coordC_omegaV (f : Module.Dual K W) : coordC e lam (omegaV e lam T f) = mapVV e lam (coordK lam T f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coordC, coordK, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply,
    LinearMap.pi_apply, Module.Dual.eval_apply, map_sum, LinearMap.map_smulₛₗ, omegaV_bC, bC_apply, omegaV_mapVV]

theorem omegaV_li (κ : Type) (v : κ → Module.Dual K W) (hv : LinearIndependent K v) :
    LinearIndependent ℂ fun x => omegaV e lam T (v x) := by
  refine LinearIndependent.of_comp (coordC e lam) ?_
  refine LinearIndependent.of_comp (VV ℂ lam).subtype ?_
  have h1 : LinearIndependent K fun x => ((coordK lam T (v x) : VV K lam) : Pol K ι n) :=
    (hv.map' (coordK lam T) (coordK_ker lam T)).map' (VV K lam).subtype (Submodule.ker_subtype _)
  convert Formalism.L2.Col.linearIndependent_map e _ h1 using 1
  funext x
  simp [coordC_omegaV, mapVV_coe]

theorem omegaV_coord (i : VVIdx lam) :
    omegaV e lam T ((bVV K lam).coord i ∘ₗ T.toLinearMap) = (bC e lam).coord i := by
  refine (bC e lam).ext fun j => ?_
  rw [omegaV_bC]
  simp [Module.Basis.coord_apply, Finsupp.single_apply]

theorem omegaV_span : Submodule.span ℂ (Set.range (omegaV e lam T)) = ⊤ := by
  classical
  rw [eq_top_iff, ← (bC e lam).dualBasis.span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨_, by rw [omegaV_coord, Module.Basis.coe_dualBasis]⟩

end Props
end GlobalTheory.MtContraHw

namespace GlobalTheory.MtContraHw

open GlobalTheory.CoefModel _root_.Formalism.L2.Col

theorem omegaV_comm {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type}
    [Field K] (e : K →+* ℂ) (emb : ι → L →+* K) (lam : ι → DomWeight n) {W : Type} [AddCommGroup W] [Module K W]
    (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (T : W ≃ₗ[K] VV K lam)
    (hT : ∀ γ x, T (ρ γ x) = rhoVr emb lam (mtwRat (L := L) (n := n) γ) (T x)) (γ : ReciprocityTheory.Aut.GQ L n) (f : Module.Dual K W) :
    omegaV e lam T (ρ.dual γ f) = (mtRep (fun t => e.comp (emb t)) lam).dual γ (omegaV e lam T f) := by
  refine (bC e lam).ext fun j => ?_
  have h1 : (mtRep (fun t => e.comp (emb t)) lam).dual γ (omegaV e lam T f) (bC e lam j) =
      omegaV e lam T f (mapVV e lam (rhoVr emb lam (mtwRat (L := L) (n := n) γ⁻¹) (bVV K lam j))) := by
    rw [GlobalTheory.ConjTwist.mapVV_rhoVr, bC_apply]
    rfl
  rw [h1, bC_apply, omegaV_mapVV, omegaV_mapVV]
  show e (f (ρ γ⁻¹ (T.symm (bVV K lam j)))) = _
  congr 2
  apply T.injective
  rw [hT, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.MtContraHw


open GlobalTheory.CoefModel Formalism.L2.Col in
theorem GlobalTheory.mtRatDual_hw : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', e.comp (emb t) ≠ ComplexEmbedding.conjugate (e.comp (emb t'))) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (lam : ι → DomWeight n), Formalism.L2.Col.TenIrr (fun t => e.comp (emb t)) lam → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (T : W ≃ₗ[K] VV K lam), (∀ γ x, T (ρ γ x) = rhoVr emb lam (Formalism.L2.Col.mtwRat (L := L) (n := n) γ) (T x)) → ∀ (t : ι) (lam0 : Fin n → ℤ), NX.HWAtF c ρ.dual (emb t) lam0 → lam0 = (lam t).w := by
  intro L _ _ _ n ι _ K _ e emb hinj hcm c hc lam hten W _ _ _ ρ T hT t lam0 hw
  have h' := GlobalTheory.MtContraHw.tenIrr_conj (fun t => e.comp (emb t)) lam hten
  have hwa := GlobalTheory.hwAt_of_hwAtF L n K e c hc (Module.Dual K W) ρ.dual
    (GlobalTheory.WtDual.dualWt (mtWt (fun t => e.comp (emb t)) lam hten)) (GlobalTheory.MtContraHw.omegaV e lam T)
    (GlobalTheory.MtContraHw.omegaV_li e lam T) (GlobalTheory.MtContraHw.omegaV_span e lam T)
    (GlobalTheory.MtContraHw.omegaV_comm e emb lam ρ T hT) (emb t) lam0 hw
  exact mtWt_hw_dual (fun t => e.comp (emb t)) hinj hcm lam hten h' t _ lam0 (GlobalTheory.WtDual.isDual_dualWt _) hwa
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalWhittakerCoefficientContinuousNormInvarian
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.JSW.WhitNorm

theorem continuous_whit_and_norm_mul : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ), Continuous F →
    (∀ γ g, F (ratGL E a γ * g) = F g) →
    Continuous (GlobalTheory.JSW.whit F) ∧ ∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖ := by
  intro E _ _ _ a F hF hl
  refine ⟨?_, fun u hu g => ?_⟩
  · have e : GlobalTheory.JSW.whit F = GroundTheory.Automorphic.FourierWhittaker.partialCoeff F 0 :=
      funext fun g => GroundTheory.Automorphic.FourierWhittaker.whittaker_eq_partialCoeff_zero hF g
    rw [e]
    exact GroundTheory.Automorphic.FourierWhittaker.continuous_partialCoeff hF 0
  · have hu' : u ∈ GlobalTheory.JSW.NA (E := E) (a := a) := (GlobalTheory.SmGL.mem_unipB _).1 hu
    rw [GlobalTheory.JSW.WhitModel.whit_mul hF hl hu' g, norm_mul, GlobalTheory.JSW.psiN, Circle.norm_coe, one_mul]

end GlobalTheory.JSW.WhitNorm
end
end

