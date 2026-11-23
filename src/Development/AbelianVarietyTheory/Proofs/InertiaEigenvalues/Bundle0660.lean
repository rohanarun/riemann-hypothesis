module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDerivativeInducedTensorForms
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0649
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0054
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IwasawaDecompositionSmoothNearOne
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

open scoped Matrix.Norms.Operator

noncomputable section

namespace GlobalTheory.SmoothIwasawaNear

variable (E : Type) [Field E] [NumberField E] {c N : ℕ} {n : Fin c → ℕ} (e : (Σ i, Fin (n i)) ≃ Fin N)

def lowPart (X : Matrix (Fin N) (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E) :=
  Matrix.of fun p q => if blk e q < blk e p then X p q else 0

def skewLin : Matrix (Fin N) (Fin N) (Cinf E) →ₗ[ℝ] Matrix (Fin N) (Fin N) (Cinf E) where
  toFun X := lowPart E e X - (lowPart E e X).conjTranspose
  map_add' X Y := by
    refine Matrix.ext fun p q => ?_
    simp only [lowPart, Matrix.add_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    split_ifs <;> simp [star_add] <;> abel
  map_smul' r X := by
    refine Matrix.ext fun p q => ?_
    simp only [lowPart, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      RingHom.id_apply]
    split_ifs <;> simp [star_smul, smul_sub]

def skew : Matrix (Fin N) (Fin N) (Cinf E) →L[ℝ] Matrix (Fin N) (Fin N) (Cinf E) :=
  LinearMap.toContinuousLinearMap (skewLin E e)

theorem skew_apply (X : Matrix (Fin N) (Fin N) (Cinf E)) : skew E e X = lowPart E e X - (lowPart E e X).conjTranspose := rfl

theorem skew_conjTranspose (X : Matrix (Fin N) (Fin N) (Cinf E)) : (skew E e X).conjTranspose = -skew E e X := by
  rw [skew_apply, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, neg_sub]

theorem blockTriangular_up (X : Matrix (Fin N) (Fin N) (Cinf E)) :
    (1 + (X - skew E e X)).BlockTriangular (blk e) := by
  intro i j h
  have hij : i ≠ j := fun hh => by subst hh; exact lt_irrefl _ h
  simp [skew_apply, lowPart, Matrix.conjTranspose_apply, Matrix.one_apply_ne hij, h, not_lt_of_gt h]

def Fm (X : Matrix (Fin N) (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E) :=
  (1 + (X - skew E e X)) * NormedSpace.exp (skew E e X)

theorem contDiff_exp' {k : WithTop ℕ∞} :
    ContDiff ℝ k (NormedSpace.exp : Matrix (Fin N) (Fin N) (Cinf E) → Matrix (Fin N) (Fin N) (Cinf E)) :=
  contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt

theorem contDiff_Fm {k : WithTop ℕ∞} : ContDiff ℝ k (Fm E e) :=
  (contDiff_const.add (contDiff_id.sub (skew E e).contDiff)).mul ((contDiff_exp' E).comp (skew E e).contDiff)

theorem Fm_zero : Fm E e 0 = 1 := by simp [Fm, NormedSpace.exp_zero]

theorem hasFDerivAt_Fm : HasFDerivAt (Fm E e)
    ((ContinuousLinearEquiv.refl ℝ (Matrix (Fin N) (Fin N) (Cinf E)) : _ →L[ℝ] _)) 0 := by
  have h1 : HasFDerivAt (fun X : Matrix (Fin N) (Fin N) (Cinf E) => 1 + (X - skew E e X))
      (ContinuousLinearMap.id ℝ _ - skew E e) 0 :=
    ((hasFDerivAt_id 0).sub (skew E e).hasFDerivAt).const_add 1
  have h0 := hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix (Fin N) (Fin N) (Cinf E))
  rw [← map_zero (skew E e)] at h0
  have h2 := h0.comp (0 : Matrix (Fin N) (Fin N) (Cinf E)) (skew E e).hasFDerivAt
  have h3 := h1.mul' h2
  refine h3.congr_fderiv (ContinuousLinearMap.ext fun X => ?_)
  have hs0 : skew E e 0 = 0 := map_zero _
  show (1 + (0 - skew E e 0)) * skew E e X + (X - skew E e X) * NormedSpace.exp (skew E e 0) = X
  rw [hs0, NormedSpace.exp_zero, sub_zero, add_zero, one_mul, mul_one]
  abel

theorem exists_local_iwasawa : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (e : (Σ i, Fin (n i)) ≃ Fin N), ∃ (p : Lie E N → parab (Cinf E) e) (k : Lie E N → Kinf E N), ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => toL (p y).1.val) (oneL E N) ∧ ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => toL (k y).1) (oneL E N) ∧ p (oneL E N) = 1 ∧ k (oneL E N) = 1 ∧ ∀ᶠ y in nhds (oneL E N), Matrix.of y = (p y).1.val * (k y).1 := by
  intro E _ _ _ c N n e
  classical
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hF : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Fm E e) 0 := (contDiff_Fm E e).contDiffAt
  have hF' := hasFDerivAt_Fm E e
  set G := hF.localInverse hF' hn with hGdef
  have hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (Fm E e 0) := hF.to_localInverse hF' hn
  have hG1 : G (Fm E e 0) = 0 := hF.localInverse_apply_image hF' hn
  have hinv : ∀ᶠ X in nhds (Fm E e 0), Fm E e (G X) = X :=
    (hF.hasStrictFDerivAt' hF' hn).eventually_right_inverse
  rw [Fm_zero] at hG hG1 hinv
  let T : Lie E N ≃L[ℝ] Matrix (Fin N) (Fin N) (Cinf E) := (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv
  let φ : Matrix (Fin N) (Fin N) (Cinf E) → Matrix (Fin N) (Fin N) (Cinf E) := fun X => 1 + (G X - skew E e (G X))
  let ψ : Matrix (Fin N) (Fin N) (Cinf E) → Matrix (Fin N) (Fin N) (Cinf E) :=
    fun X => NormedSpace.exp (skew E e (G X))
  have hφ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ 1 :=
    contDiffAt_const.add (hG.sub ((skew E e).contDiff.contDiffAt.comp _ hG))
  have hψ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ 1 :=
    (contDiff_exp' E).contDiffAt.comp _ ((skew E e).contDiff.contDiffAt.comp _ hG)
  have hφ1 : φ 1 = 1 := by simp [φ, hG1]
  have hψ1 : ψ 1 = 1 := by simp [ψ, hG1, NormedSpace.exp_zero]
  have hunit : ∀ᶠ X in nhds (1 : Matrix (Fin N) (Fin N) (Cinf E)), IsUnit (φ X) :=
    hφ.continuousAt.eventually_mem (by rw [hφ1]; exact Units.isOpen.mem_nhds isUnit_one)
  have hTt : Filter.Tendsto (fun y : Lie E N => Matrix.of y) (nhds (oneL E N)) (nhds 1) :=
    T.continuous.tendsto (oneL E N)
  have hunitV : ∀ᶠ y in nhds (oneL E N), IsUnit (φ (Matrix.of y)) := hTt.eventually hunit
  have hinvV : ∀ᶠ y in nhds (oneL E N), Fm E e (G (Matrix.of y)) = Matrix.of y := hTt.eventually hinv
  have hU : ∀ X, ψ X ∈ Matrix.unitaryGroup (Fin N) (Cinf E) := fun X => by
    show NormedSpace.exp (skew E e (G X)) ∈ _
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      skew_conjTranspose, ← Matrix.exp_add_of_commute _ _ (Commute.refl (skew E e (G X))).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]
  have hφT : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ (T (oneL E N)) := hφ
  have hψT : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ (T (oneL E N)) := hψ
  refine ⟨fun y => if h : IsUnit (φ (Matrix.of y)) then ⟨h.unit, blockTriangular_up E e (G (Matrix.of y))⟩ else 1,
    fun y => ⟨ψ (Matrix.of y), hU _⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => T.symm (φ (T y))) (oneL E N) :=
      T.symm.contDiff.contDiffAt.comp _ (hφT.comp (oneL E N) T.contDiff.contDiffAt)
    refine hsm.congr_of_eventuallyEq ?_
    filter_upwards [hunitV] with y hy
    simp only [dif_pos hy]
    show toL (hy.unit : Matrix (Fin N) (Fin N) (Cinf E)) = _
    rw [hy.unit_spec]
    rfl
  · exact T.symm.contDiff.contDiffAt.comp _ (hψT.comp (oneL E N) T.contDiff.contDiffAt)
  · have h1 : IsUnit (φ (Matrix.of (oneL E N))) := by
      show IsUnit (φ 1)
      rw [hφ1]
      exact isUnit_one
    refine Subtype.ext (Units.ext ?_)
    simp only [dif_pos h1]
    exact (IsUnit.unit_spec _).trans hφ1
  · exact Subtype.ext hψ1
  · filter_upwards [hunitV, hinvV] with y hy hy'
    simp only [dif_pos hy]
    show Matrix.of y = (hy.unit : Matrix (Fin N) (Fin N) (Cinf E)) * ψ (Matrix.of y)
    rw [hy.unit_spec]
    exact hy'.symm

end GlobalTheory.SmoothIwasawaNear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetModuleInStagesRefinedBlocks
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages

namespace GlobalTheory.JacStagesProof

section Groups

open Matrix

variable {R : Type} [CommRing R]

theorem mem_unipRad_iff_entries' {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ ∀ i j, ¬ blk e i < blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad]
  constructor
  · rintro ⟨hp, hd⟩ i j hij
    rcases lt_or_eq_of_le (not_lt.1 hij) with h | h
    · rw [mem_parab.1 hp i j h, one_apply_ne (fun hij' => by rw [hij'] at h; exact lt_irrefl _ h)]
    · obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
      simp only [blk_apply] at h
      subst h
      rw [hd _ x y]
      by_cases hxy : x = y <;> simp [Matrix.one_apply, hxy]
  · intro h
    refine ⟨fun i j hji => ?_, fun a x y => ?_⟩
    · rw [h i j (not_lt.2 hji.le), one_apply_ne (fun hij' => by rw [hij'] at hji; exact lt_irrefl _ hji)]
    · rw [h _ _ (by simp)]
      by_cases hxy : x = y <;> simp [Matrix.one_apply, hxy]

variable {s n : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}

theorem sigma_eq_of_refine (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (a : Fin s) (y : Fin (d a)) :
    ∀ (p : Σ a, Fin (t a)) (i : Fin (d' p.1 p.2)),
      (⟨p.1, e' p.1 ⟨p.2, i⟩⟩ : Σ a, Fin (d a)) = ⟨a, y⟩ → p = ⟨a, blk (e' a) y⟩ := by
  rintro ⟨a', b⟩ i h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h
  obtain rfl := eq_of_heq h2
  simp

theorem symm_blk_refinePlace (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (a : Fin s) (y : Fin (d a)) :
    finSigmaFinEquiv.symm (blk (refinePlace e e') (e ⟨a, y⟩)) = ⟨a, blk (e' a) y⟩ := by
  obtain ⟨⟨c, i⟩, hc⟩ := (refinePlace e e').surjective (e ⟨a, y⟩)
  rw [← hc, blk_apply]
  rw [refinePlace_apply] at hc
  exact sigma_eq_of_refine e' a y _ i (e.injective hc)

theorem blk_eq_fst (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (x : Fin n) :
    blk e x = (finSigmaFinEquiv.symm (blk (refinePlace e e') x)).1 := by
  obtain ⟨⟨a, y⟩, rfl⟩ := e.surjective x
  rw [symm_blk_refinePlace, blk_apply]

theorem blk_refine_lt_iff (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (x y : Fin n) :
    blk (refinePlace e e') x < blk (refinePlace e e') y ↔
      toLex (finSigmaFinEquiv.symm (blk (refinePlace e e') x)) <
        toLex (finSigmaFinEquiv.symm (blk (refinePlace e e') y)) :=
  (GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex s t).lt_iff_lt.symm

theorem blk_refine_lt_of_lt (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {x y : Fin n} (h : blk e x < blk e y) : blk (refinePlace e e') x < blk (refinePlace e e') y := by
  rw [blk_refine_lt_iff]
  rw [blk_eq_fst e e', blk_eq_fst e e' y] at h
  exact Sigma.Lex.lt_def.2 (Or.inl h)

theorem blk_refine_lt_iff_same (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (a : Fin s) (x y : Fin (d a)) :
    blk (refinePlace e e') (e ⟨a, x⟩) < blk (refinePlace e e') (e ⟨a, y⟩) ↔ blk (e' a) x < blk (e' a) y := by
  rw [blk_refine_lt_iff, symm_blk_refinePlace, symm_blk_refinePlace, Sigma.Lex.lt_def]
  constructor
  · rintro (h | ⟨h, h2⟩)
    · exact absurd h (lt_irrefl _)
    · exact h2
  · intro h
    exact Or.inr ⟨rfl, h⟩

end Groups

end GlobalTheory.JacStagesProof

namespace GlobalTheory.JacStagesProof

section Groups2

open Matrix

variable {R : Type} [Field R] [ValuativeRel R] [TopologicalSpace R] [IsNonarchimedeanLocalField R] {s n : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}

theorem one_apply_e (e : (Σ a, Fin (d a)) ≃ Fin n) (a : Fin s) (x y : Fin (d a)) :
    (1 : Matrix (Fin n) (Fin n) R) (e ⟨a, x⟩) (e ⟨a, y⟩) = (1 : Matrix (Fin (d a)) (Fin (d a)) R) x y := by
  by_cases hxy : x = y <;> simp [Matrix.one_apply, hxy]

theorem unipRad_le_refine (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) :
    unipRad R e ≤ unipRad R (refinePlace e e') := by
  intro u hu
  rw [mem_unipRad_iff_entries'] at hu ⊢
  exact fun i j h => hu i j fun h' => h (blk_refine_lt_of_lt e e' h')

theorem leviEmb_mem_unipRad_refine (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (l : ∀ a, GL (Fin (d a)) R) (hl : l ∈ relUnipD R e') :
    leviEmb R e l ∈ unipRad R (refinePlace e e') := by
  rw [mem_unipRad_iff_entries']
  intro i j h
  obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, one_apply_e]
    have := mem_unipRad_iff_entries'.1 (hl a (Set.mem_univ a)) x y
      (fun h' => h ((blk_refine_lt_iff_same e e' a x y).2 h'))
    exact this
  · rw [leviEmb_apply_ne R e l hab, one_apply_ne]
    intro h'
    exact hab (congrArg Sigma.fst (e.injective h'))

theorem exists_decomp_refine (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (u : GL (Fin n) R) (hu : u ∈ unipRad R (refinePlace e e')) :
    ∃ l ∈ relUnipD R e', ∃ u' ∈ unipRad R e, u = leviEmb R e l * u' := by
  have hu' := mem_unipRad_iff_entries'.1 hu
  have hp : u ∈ parab R e := by
    refine mem_parab.2 fun i j hji => ?_
    have h1 := blk_refine_lt_of_lt e e' hji
    rw [hu' i j (not_lt.2 h1.le), one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hji
  obtain ⟨w, hw, hdec⟩ := exists_levi_mul_unip R e ⟨u, hp⟩
  refine ⟨leviProj R e ⟨u, hp⟩, fun a _ => ?_, w, hw, hdec⟩
  show leviProj R e ⟨u, hp⟩ a ∈ unipRad R (e' a)
  rw [mem_unipRad_iff_entries']
  intro x y h
  rw [leviProj_apply, ← one_apply_e e]
  exact hu' _ _ fun h' => h ((blk_refine_lt_iff_same e e' a x y).1 h')

theorem leviEmb_relEmbD_ne (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (g : ∀ a b, GL (Fin (d' a b)) R) :
    ∀ (p p' : Σ a, Fin (t a)), p ≠ p' → ∀ (x : Fin (d' p.1 p.2)) (y : Fin (d' p'.1 p'.2)),
      (leviEmb R e (relEmbD R e' g) : Matrix (Fin n) (Fin n) R) (e ⟨p.1, e' _ ⟨p.2, x⟩⟩)
        (e ⟨p'.1, e' _ ⟨p'.2, y⟩⟩) = 0 := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ hne x y
  by_cases ha : a = a'
  · subst ha
    have hb : b ≠ b' := fun h => hne (by rw [h])
    rw [leviEmb_apply_same, relEmbD_apply]
    exact leviEmb_apply_ne R (e' a) (g a) hb x y
  · exact leviEmb_apply_ne R e _ ha _ _

theorem leviEmb_refine_flatHom (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (g : ∀ a b, GL (Fin (d' a b)) R) :
    leviEmb R (refinePlace e e') (flatHom (fun a b => GL (Fin (d' a b)) R) g) =
      leviEmb R e (relEmbD R e' g) := by
  ext i j
  obtain ⟨⟨c, x⟩, rfl⟩ := (refinePlace e e').surjective i
  obtain ⟨⟨c', y⟩, rfl⟩ := (refinePlace e e').surjective j
  by_cases hc : c = c'
  · subst hc
    rw [leviEmb_apply_same, refinePlace_apply, refinePlace_apply, leviEmb_apply_same, relEmbD_apply,
      leviEmb_apply_same, flatHom_apply]
  · rw [leviEmb_apply_ne R _ _ hc, refinePlace_apply, refinePlace_apply]
    exact (leviEmb_relEmbD_ne e e' g _ _ (fun h => hc (finSigmaFinEquiv.symm.injective h)) x y).symm

end Groups2

end GlobalTheory.JacStagesProof

namespace GlobalTheory.JacStagesProof

theorem deltaHalf_relUnipD {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (l : ∀ a, GL (Fin (d a)) k) (hl : l ∈ relUnipD k e') :
    deltaHalf k (fun a => Fin (d a)) l = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  rw [det_eq_one_of_mem_unipRad k (hl a (Set.mem_univ a)), map_one]

theorem jac_refinePlace_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s n : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V),
    Nonempty (Representation.Equiv ((GlobalTheory.SmGL.jac (refinePlace e e') π).comp (flatHom fun a b => GL (Fin (d' a b)) k))
      (relJacD e' (GlobalTheory.SmGL.jac e π))) := by
  intro k _ _ _ _ s n d e t d' e' V _ _ π
  classical
  set A := twKer π (unipRad k e) 1 with hA
  set B := twKer π (unipRad k (refinePlace e e')) 1 with hB
  set C : Submodule ℂ V := Submodule.span ℂ
    {w | ∃ (l : relUnipD k e') (v : V), w = π (leviEmb k e (l : ∀ a, GL (Fin (d a)) k)) v - v} with hC
  have hAB : A ≤ B := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    exact Submodule.subset_span ⟨⟨u, unipRad_le_refine e e' u.2⟩, v, rfl⟩
  have hCB : C ≤ B := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, v, rfl⟩
    exact Submodule.subset_span ⟨⟨_, leviEmb_mem_unipRad_refine e e' l.1 l.2⟩, v, by simp⟩
  have hBAC : B ≤ A ⊔ C := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    obtain ⟨l, hl, u', hu', hu⟩ := exists_decomp_refine e e' u.1 u.2
    have : π (u : GL (Fin n) k) v - ((1 : unipRad k (refinePlace e e') →* ℂˣ) u : ℂ) • v =
        (π u' v - ((1 : unipRad k e →* ℂˣ) ⟨u', hu'⟩ : ℂ) • v) +
          (π (leviEmb k e l) (π u' v) - π u' v) := by
      rw [hu, map_mul, Module.End.mul_apply]; simp
    rw [SetLike.mem_coe, this]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨⟨u', hu'⟩, v, rfl⟩)
      (Submodule.subset_span ⟨⟨l, hl⟩, π u' v, rfl⟩)
  have hK : twKer (GlobalTheory.SmGL.jac e π) (relUnipD k e') 1 = B.map A.mkQ := by
    have hB' : B.map A.mkQ = C.map A.mkQ := by
      rw [le_antisymm hBAC (sup_le hAB hCB), Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
    rw [hB', hC, Submodule.map_span]
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨l, x, rfl⟩
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      refine Submodule.subset_span ⟨_, ⟨l, v, rfl⟩, ?_⟩
      rw [jac_mk, deltaHalf_relUnipD e' l.1 l.2]
      simp
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨l, v, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨l, Submodule.Quotient.mk v, ?_⟩
      rw [jac_mk, deltaHalf_relUnipD e' l.1 l.2]
      simp
  let φ : (V ⧸ B) ≃ₗ[ℂ] (V ⧸ A) ⧸ twKer (GlobalTheory.SmGL.jac e π) (relUnipD k e') 1 :=
    (Submodule.quotientQuotientEquivQuotient A B hAB).symm.trans (Submodule.quotEquivOfEq _ _ hK.symm)
  have hφ : ∀ v : V, φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (Submodule.Quotient.mk v) := by
    intro v
    simp only [φ, LinearEquiv.trans_apply]
    rw [show (Submodule.quotientQuotientEquivQuotient A B hAB).symm (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (Submodule.Quotient.mk v) from
        (LinearEquiv.symm_apply_eq _).2 rfl]
    rfl
  refine ⟨Representation.Equiv.mk φ fun g => ?_⟩
  refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe, MonoidHom.coe_comp,
    Function.comp_apply]
  rw [jac_mk, map_smul, hφ, hφ, relJacD_mk, jac_mk, leviEmb_refine_flatHom, _root_.GlobalTheory.JacStages.deltaHalf_flatHom k s d t d' e' g, Submodule.Quotient.mk_smul, smul_smul, mul_inv,
    Units.val_mul, mul_comm]

end GlobalTheory.JacStagesProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanKilledUnionAveragesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_annihilated_union_class_averages : ∀ {G M : Type} [Group G] [Fintype G] [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (π : G → Module.End ℂ M), (∀ g, ∀ v ∈ S, π g v ∈ S) → (∀ v ∈ S, π 1 v = v) → (∀ g h, ∀ v ∈ S, π (g * h) v = π h (π g v)) → ∀ (C : Set (G → ℂ)), (∀ c ∈ C, ∀ x : G, (fun g => c (x * g * x⁻¹)) ∈ C) → ∀ v ∈ S, v ∈ Submodule.span ℂ ({w | w ∈ S ∧ ∀ c ∈ C, ∑ g, c g • π g w = 0} ∪ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w}) := by
  first | exact @GlobalTheory.mem_span_killed_union_averages | exact GlobalTheory.mem_span_killed_union_averages | (intros; apply GlobalTheory.mem_span_killed_union_averages <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicAverageEqCoeffSinglePlaceElementStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolicAverage_eq_coeff_singlePlaceElement : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eR : G ≃* G0g D.nd)
    (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)) →
    ∀ (i : Fin D.R.m) (kv0 : Σ k : Fin 2, D.nd.PlG k) (a : Fin D.R.r → kP (plg kv0).1) (b : Bool) (ε : ℤ) (y : G),
    haveI : Fact (D.host.g kv0.1).Prime := ⟨D.host.g_prime kv0.1⟩
    GlobalTheory.DownLift.mirC R i (plg kv0) a b ε y = (open Classical in if ∀ kv, kv ≠ kv0 → eR y kv = 1 then
      (GlobalTheory.MirAvg.mirEl ((zpowGroupHom ε).comp ((R.chi ((i : ℕ) + 1) (plg kv0).1).comp
        (Units.map (iso kv0 : ZMod (D.host.g kv0.1) →* kP (plg kv0).1))))
        (fun j => (iso kv0).symm (a j)) b).coeff (eR y kv0) else 0) := by
  first | exact @GlobalTheory.MirAvg.mirC_eq_coeff_mirEl | exact GlobalTheory.MirAvg.mirC_eq_coeff_mirEl | (intros; apply GlobalTheory.MirAvg.mirC_eq_coeff_mirEl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotient
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem hasSupport_of_isSubquotient_prinSeries :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (χ : Fin n → kˣ →* ℂˣ) (hχ : ∀ i, IsSmoothChar (χ i)) (π : IrrRep (GL (Fin n) k)), GlobalTheory.SmGL.IsSubquotient π.ρ (prinSeries χ) → HasSupport π.ρ (Finset.univ.val.map fun i => IrrGL.ofChar (χ i) (hχ i)) := by
  intro k _ _ _ _ _ n χ hχ π h

  have hd : ∑ a : Fin n, (IrrGL.ofChar (χ a) (hχ a)).1 = n := by
    simp [IrrGL.ofChar]
  refine hasSupport_of_isSubquotient π.irr (fun a => IrrGL.isCusp_ofChar (χ a) (hχ a)) (hd := hd) ?_
  refine h.trans ((GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ).trans ?_)

  have he : stdBlocks (fun a => (IrrGL.ofChar (χ a) (hχ a)).1) hd =
      Equiv.sigmaUnique (Fin n) (fun _ => Fin 1) := by
    ext ⟨a, i⟩
    rw [stdBlocks_val]
    simp [IrrGL.ofChar, Fin.fin_one_eq_zero i]
    rfl
  unfold prodIrr
  rw [he]

  let φ := multiProdEquiv (Equiv.sigmaUnique (Fin n) (fun _ => Fin 1))
    (fun a => equivRep (IrrRep.det (Fin 1) (χ a) (hχ a)))
  exact IsSubquotient.of_injective φ.toIntertwiningMap (fun u v huv => φ.toLinearEquiv.injective huv)

end GlobalTheory.LocLanglands
end

