module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
public import GroundTheory.GlobalFields.TateThesis.GlobalZetaInfinite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0017
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGrowthUniform
section
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing
open IsDedekindDomain _root_.Matrix Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BoxBound

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem norm_toL_mul_le (A B : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (A * B)‖ ≤ a * (‖toL A‖ * ‖toL B‖) := by
  have hA : ∀ i k, ‖A i k‖ ≤ ‖toL A‖ := fun i k =>
    (norm_le_pi_norm (toL A i) k).trans (norm_le_pi_norm (toL A) i)
  have hB : ∀ i k, ‖B i k‖ ≤ ‖toL B‖ := fun i k =>
    (norm_le_pi_norm (toL B i) k).trans (norm_le_pi_norm (toL B) i)
  have h0 : 0 ≤ (a : ℝ) * (‖toL A‖ * ‖toL B‖) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  change ‖(A * B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (‖toL A‖ * ‖toL B‖) fun k _ => ?_).trans_eq (by simp)
  exact (norm_mul_le _ _).trans (mul_le_mul (hA i k) (hB k j) (norm_nonneg _) (norm_nonneg _))

theorem height_mul_le' (y z : GL (Fin a) (Cinf E)) :
    CuspRep.height (y * z) ≤ (1 + 2 * a) * (CuspRep.height y * CuspRep.height z) := by
  have h1 := norm_toL_mul_le (y.val) (z.val)
  have h2 := norm_toL_mul_le ((z⁻¹).val) ((y⁻¹).val)
  have e1 : (y * z).val = y.val * z.val := rfl
  have e2 : ((y * z)⁻¹).val = (z⁻¹).val * (y⁻¹).val := by rw [_root_.mul_inv_rev]; rfl
  have hy := one_le_height y
  have hz := one_le_height z
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL z.val)
  have n3 := norm_nonneg (toL (y⁻¹).val)
  have n4 := norm_nonneg (toL (z⁻¹).val)
  have m1 : ‖toL y.val‖ * ‖toL z.val‖ ≤ CuspRep.height y * CuspRep.height z :=
    mul_le_mul (by unfold CuspRep.height; linarith) (by unfold CuspRep.height; linarith) n2 (by linarith)
  have m2 : ‖toL (z⁻¹).val‖ * ‖toL (y⁻¹).val‖ ≤ CuspRep.height y * CuspRep.height z := by
    rw [mul_comm]
    exact mul_le_mul (by unfold CuspRep.height; linarith) (by unfold CuspRep.height; linarith) n4 (by linarith)
  have m3 : 1 ≤ CuspRep.height y * CuspRep.height z := one_le_mul_of_one_le_of_one_le hy hz
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have : CuspRep.height (y * z) = 1 + ‖toL (y * z).val‖ + ‖toL ((y * z)⁻¹).val‖ := rfl
  rw [this, e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left m1 ha, mul_le_mul_of_nonneg_left m2 ha]

theorem continuous_height : Continuous (CuspRep.height : GL (Fin a) (Cinf E) → ℝ) := by
  have h1 : Continuous fun y : GL (Fin a) (Cinf E) => (y.val : Matrix (Fin a) (Fin a) (Cinf E)) :=
    Units.continuous_val
  have h2 : Continuous fun y : GL (Fin a) (Cinf E) => ((y⁻¹).val : Matrix (Fin a) (Fin a) (Cinf E)) :=
    Units.continuous_coe_inv
  have n1 : Continuous fun y : GL (Fin a) (Cinf E) => ‖toL y.val‖ := (continuous_norm (E := Lie E a)).comp h1
  have n2 : Continuous fun y : GL (Fin a) (Cinf E) => ‖toL (y⁻¹).val‖ := (continuous_norm (E := Lie E a)).comp h2
  unfold CuspRep.height
  exact (continuous_const.add n1).add n2

abbrev gInf (g : GA E a) : GL (Fin a) (Cinf E) := GeneralLinearGroup.map (pInf E) g

abbrev gFin (g : GA E a) : GL (Fin a) (Af E) := GeneralLinearGroup.map (pFin E) g

theorem continuous_gInf : Continuous (gInf : GA E a → GL (Fin a) (Cinf E)) :=
  GASplit.continuous_glMap a (pInf E) (GASplit.continuous_pInf E)

theorem continuous_gFin : Continuous (gFin : GA E a → GL (Fin a) (Af E)) :=
  GASplit.continuous_glMap a (pFin E) (GASplit.continuous_pFin E)

theorem exists_height_bound {S : Set (GA E a)} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ S, CuspRep.height (gInf g) ≤ B := by
  obtain ⟨B, hB⟩ := (hS.image (continuous_height.comp continuous_gInf)).bddAbove
  exact ⟨max B 0, le_max_right _ _, fun g hg => (hB ⟨g, hg, rfl⟩).trans (le_max_left _ _)⟩

theorem exists_growth_uniform {φ : Sm E a} (hφ : IsAutForm φ) {T : Set (GL (Fin a) (Af E))} (hT : IsCompact T) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ t ∈ T, ∀ y, ‖φ.1 (finGL E a t * infGL E a y)‖ ≤ C * CuspRep.height y ^ N := by
  choose Cf Nf hf using fun x : GL (Fin a) (Af E) => hφ.growth (finGL E a x)
  have hU : ∀ x ∈ T, {t | x⁻¹ * t ∈ {k | finRep E a k φ = φ}} ∈ 𝓝 x := fun x _ =>
    (hφ.level.preimage (continuous_const.mul continuous_id :
      Continuous fun t : GL (Fin a) (Af E) => x⁻¹ * t)).mem_nhds (by
        change finRep E a (x⁻¹ * x) φ = φ
        rw [inv_mul_cancel, map_one]; rfl)
  obtain ⟨s, -, hs⟩ := hT.elim_nhds_subcover _ hU
  refine ⟨∑ x ∈ s, |Cf x|, s.sup Nf, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun t ht y => ?_⟩
  obtain ⟨x, hx, hxt⟩ := Set.mem_iUnion₂.1 (hs ht)
  have hk : finRep E a (x⁻¹ * t) φ = φ := hxt
  have e : φ.1 (finGL E a t * infGL E a y) = φ.1 (finGL E a x * infGL E a y) := by
    have h1 : finGL E a t = finGL E a x * finGL E a (x⁻¹ * t) := by
      rw [← map_mul, mul_inv_cancel_left]
    have h2 := congrFun (congrArg Subtype.val hk) (finGL E a x * infGL E a y)
    refine Eq.trans ?_ h2
    change _ = φ.1 (finGL E a x * infGL E a y * finGL E a (x⁻¹ * t))
    rw [h1, mul_assoc, mul_assoc, infGL_comm]
  rw [e]
  have hy := one_le_height y
  refine (hf x y).trans ?_
  refine (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans ?_
  refine mul_le_mul (Finset.single_le_sum (f := fun x => |Cf x|) (fun _ _ => abs_nonneg _) hx)
    (pow_le_pow_right₀ hy (Finset.le_sup hx)) (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem norm_pInf_apply (x : Ad E) (w : InfinitePlace E) : ‖pInf E x w‖ = ‖x.1 w‖ :=
  norm_isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w) (x.1 w)

abbrev dg (a : ℕ) (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i) : GA E a :=
  diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i))

theorem gFin_dg (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i) : gFin (dg (E := E) a ρ hρ) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change pFin E ((diagonal fun i => ((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E) : 𝔸[E])) i j) = (1 : Matrix (Fin a) (Fin a) (Af E)) i j
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · subst h
    exact FiniteAdeleRing.ext _ fun v => posIdele_finite (K := E) (ρ i) (hρ i) v
  · exact map_zero _

theorem height_gInf_dg_le (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i) {L : ℝ} (hL1 : 1 ≤ L)
    (hL : ∀ i, ρ i ≤ L ∧ (ρ i)⁻¹ ≤ L) : CuspRep.height (gInf (dg (E := E) a ρ hρ)) ≤ 3 * L := by
  have hL0 : 0 ≤ L := by linarith
  have key : ∀ i w, ‖pInf E ((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E) : 𝔸[E]) w‖ = ρ i := fun i w => by
    rw [norm_pInf_apply]; exact norm_posIdele_infinite (K := E) (ρ i) (hρ i) w
  have key' : ∀ i w, ‖pInf E (((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E)⁻¹ : IdeleGroup E) : 𝔸[E]) w‖ = (ρ i)⁻¹ := fun i w => by
    have h1 : pInf E ((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E) : 𝔸[E]) w *
        pInf E (((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E)⁻¹ : IdeleGroup E) : 𝔸[E]) w = 1 := by
      rw [← Pi.mul_apply, ← map_mul, Units.mul_inv, map_one, Pi.one_apply]
    have h2 := congrArg norm h1
    rw [norm_mul, key, norm_one] at h2
    exact eq_inv_of_mul_eq_one_right h2
  have b1 : ‖toL (gInf (dg (E := E) a ρ hρ)).val‖ ≤ L := by
    refine (pi_norm_le_iff_of_nonneg hL0).2 fun i => (pi_norm_le_iff_of_nonneg hL0).2 fun j =>
      (pi_norm_le_iff_of_nonneg hL0).2 fun w => ?_
    change ‖pInf E ((diagonal fun i => ((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E) : 𝔸[E])) i j) w‖ ≤ L
    rw [Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rw [key]; exact (hL i).1
    · simpa using hL0
  have b2 : ‖toL ((gInf (dg (E := E) a ρ hρ))⁻¹).val‖ ≤ L := by
    rw [← map_inv]
    refine (pi_norm_le_iff_of_nonneg hL0).2 fun i => (pi_norm_le_iff_of_nonneg hL0).2 fun j =>
      (pi_norm_le_iff_of_nonneg hL0).2 fun w => ?_
    change ‖pInf E ((diagonal fun i => (((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E)⁻¹ : IdeleGroup E) : 𝔸[E])) i j) w‖ ≤ L
    rw [Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rw [key']; exact (hL i).2
    · simpa using hL0
  unfold CuspRep.height
  linarith

theorem gFin_infEmb (y : AutomorphicForm.archGroup E a) : gFin (AutomorphicForm.infEmb E a y : GA E a) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h := AutomorphicForm.prodEquiv_infEmb (K := E) (n := a) y
  have h2 := congrArg (fun p => (p.2 : GL (Fin a) (Af E)) i j) h
  exact h2

theorem finGL_mul_infGL (g : GA E a) : finGL E a (gFin g) * infGL E a (gInf g) = g := by
  rw [← infGL_comm]; exact infGL_mul_finGL g

theorem box_bound : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → (∀ ω : Set (AdelicGLn.AdelicGL E a), IsCompact ω → ∃ N : ℕ, ∀ Q : Set (AutomorphicForm.archGroup E a), IsCompact Q → ∃ C : ℝ,
    ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), ∀ kk ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL E a)), ∀ y ∈ Q, ∀ L : ℝ, 1 ≤ L →
      (∀ i, ρ i ≤ L ∧ (ρ i)⁻¹ ≤ L) →
      ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * kk * AutomorphicForm.infEmb E a y)‖ ≤ C * L ^ N) := by
  intro E _ _ _ a φ hφ ω hω
  have hK : IsCompact (maxCompact (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)) := isCompact_maxCompact
  have hT : IsCompact ((fun p : GA E a × GA E a => gFin p.1 * gFin p.2) '' (ω ×ˢ (maxCompact (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)))) :=
    (hω.prod hK).image ((continuous_gFin.comp continuous_fst).mul (continuous_gFin.comp continuous_snd))
  obtain ⟨C₀, N, hC₀, hgrow⟩ := exists_growth_uniform hφ hT
  refine ⟨N, fun Q hQ => ?_⟩
  obtain ⟨B₁, hB₁, h₁⟩ := exists_height_bound (E := E) (a := a) hω
  obtain ⟨B₂, hB₂, h₂⟩ := exists_height_bound (E := E) (a := a) hK
  obtain ⟨B₃, hB₃, h₃⟩ := exists_height_bound (E := E) (a := a)
    (hQ.image (AutomorphicForm.continuous_infEmb (K := E) (n := a)))
  set c : ℝ := 1 + 2 * a with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨C₀ * (c * (c * (c * (B₁ * 3)) * B₂) * B₃) ^ N, fun b hb ρ hρ kk hk y hy L hL1 hL => ?_⟩
  set D : GA E a := dg a ρ hρ with hD
  set Y : GA E a := AutomorphicForm.infEmb E a y with hY
  set x : GA E a := b * D * kk * Y with hx
  have hfin : gFin x = gFin b * gFin kk := by
    simp only [hx, map_mul, hD, gFin_dg, hY, gFin_infEmb, mul_one]
  have hinf : gInf x = gInf b * gInf D * gInf kk * gInf Y := by
    simp only [hx, map_mul]
  have hb' := h₁ b hb
  have hk' := h₂ kk hk
  have hy' := h₃ Y ⟨y, hy, rfl⟩
  have hd' : CuspRep.height (gInf D) ≤ 3 * L := height_gInf_dg_le ρ hρ hL1 hL
  have hH : CuspRep.height (gInf x) ≤ (c * (c * (c * (B₁ * 3)) * B₂) * B₃) * L := by
    have o1 := one_le_height (gInf b)
    have o2 := one_le_height (gInf D)
    have o3 := one_le_height (gInf kk)
    have o4 := one_le_height (gInf Y)
    have s1 : CuspRep.height (gInf b * gInf D) ≤ c * (B₁ * (3 * L)) :=
      (height_mul_le' _ _).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul hb' hd' (by linarith) hB₁) hc0)
    have s2 : CuspRep.height (gInf b * gInf D * gInf kk) ≤ c * ((c * (B₁ * (3 * L))) * B₂) :=
      (height_mul_le' _ _).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul s1 hk' (by linarith) (by positivity)) hc0)
    have s3 : CuspRep.height (gInf b * gInf D * gInf kk * gInf Y) ≤ c * ((c * ((c * (B₁ * (3 * L))) * B₂)) * B₃) :=
      (height_mul_le' _ _).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul s2 hy' (by linarith) (by positivity)) hc0)
    rw [hinf]
    exact s3.trans_eq (by ring)
  have hbound := hgrow (gFin x) ⟨(b, kk), ⟨hb, hk⟩, hfin.symm⟩ (gInf x)
  rw [finGL_mul_infGL] at hbound
  refine hbound.trans ?_
  rw [mul_assoc, ← mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ hC₀
  exact pow_le_pow_left₀ (by linarith [one_le_height (gInf x)]) hH N

end GlobalTheory.CompanionTheory.BoxBound

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermShiftedWeightEqInfChar
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.ReversedBlocks

variable {n : ℕ}

theorem lower_iff (P : Fin n → Prop) [DecidablePred P] (hP : ∀ a b, a ≤ b → P b → P a) (b : Fin n) :
    P b ↔ (b : ℕ) < (univ.filter P).card :=
  _root_.UpperTheory.Reformulated.B.Re1.lower_iff P hP b

def lowC (lev : Fin n → ℕ) (a : Fin n) : ℕ := (univ.filter fun b => lev b < lev a).card

def topC (lev : Fin n → ℕ) (a : Fin n) : ℕ := (univ.filter fun b => lev b ≤ lev a).card

theorem lt_iff {lev : Fin n → ℕ} (hm : Monotone lev) (a b : Fin n) : lev b < lev a ↔ (b : ℕ) < lowC lev a :=
  lower_iff (fun b => lev b < lev a) (fun _ _ h hb => lt_of_le_of_lt (hm h) hb) b

theorem le_iff {lev : Fin n → ℕ} (hm : Monotone lev) (a b : Fin n) : lev b ≤ lev a ↔ (b : ℕ) < topC lev a :=
  lower_iff (fun b => lev b ≤ lev a) (fun _ _ h hb => le_trans (hm h) hb) b

theorem high_add_topC (lev : Fin n → ℕ) (a : Fin n) :
    (univ.filter fun b => lev a < lev b).card + topC lev a = n := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun b => lev a < lev b)
  simp only [not_lt, Finset.card_univ, Fintype.card_fin] at h
  unfold topC
  exact h

def rv (lev : Fin n → ℕ) (a : Fin n) : ℕ := lowC lev a + (topC lev a - 1) - a

theorem rv_bounds {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) :
    lowC lev a ≤ a ∧ (a : ℕ) < topC lev a ∧ rv lev a + a + 1 = lowC lev a + topC lev a := by
  have h1 : ¬ (a : ℕ) < lowC lev a := fun h => lt_irrefl _ ((lt_iff hm a a).2 h)
  have h2 : (a : ℕ) < topC lev a := (le_iff hm a a).1 le_rfl
  unfold rv
  omega

theorem rv_lt {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : rv lev a < n := by
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  have := high_add_topC lev a
  omega

def rf {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : Fin n := ⟨rv lev a, rv_lt hm a⟩

theorem lev_rf {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : lev (rf hm a) = lev a := by
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  apply le_antisymm
  · exact (le_iff hm a _).2 (by simp only [rf]; omega)
  · exact not_lt.1 fun h => by
      have := (lt_iff hm a _).1 h
      simp only [rf] at this
      omega

theorem rf_rf {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : rf hm (rf hm a) = a := by
  have hl := lev_rf hm a
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  obtain ⟨k1, k2, k3⟩ := rv_bounds hm (rf hm a)
  have e1 : lowC lev (rf hm a) = lowC lev a := by simp only [lowC, hl]
  have e2 : topC lev (rf hm a) = topC lev a := by simp only [topC, hl]
  apply Fin.ext
  have e3 : ((rf hm a : Fin n) : ℕ) = rv lev a := rfl
  have e4 : ((rf hm (rf hm a) : Fin n) : ℕ) = rv lev (rf hm a) := rfl
  omega

theorem exists_perm_yZ : ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), IsLev lam lev →
    ∃ σ : Equiv.Perm (Fin n), ∀ a : Fin n,
      (GlobalTheory.CompanionTheory.ModelS.yZ lam lev a : ℂ) + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ) = infOf lam false (σ a) := by
  intro n lam lev h
  obtain ⟨hm, hc⟩ := h
  refine ⟨Function.Involutive.toPerm (rf hm) (rf_rf hm), fun a => ?_⟩
  have hv : (Function.Involutive.toPerm (rf hm) (rf_rf hm)) a = rf hm a := rfl
  rw [hv]
  have hl : lam (rf hm a) = lam a := hc _ _ (lev_rf hm a)
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  have h4 := high_add_topC lev a
  have c3 : ((rv lev a : ℕ) : ℂ) + ((a : ℕ) : ℂ) + 1 = (lowC lev a : ℂ) + (topC lev a : ℂ) := by exact_mod_cast h3
  have c4 : (((univ.filter fun b => lev a < lev b).card : ℕ) : ℂ) + (topC lev a : ℂ) = (n : ℂ) := by exact_mod_cast h4
  have e3 : (((rf hm a : Fin n) : ℕ) : ℂ) = (rv lev a : ℂ) := rfl
  have hlow : (((univ.filter fun b => lev b < lev a).card : ℕ) : ℂ) = (lowC lev a : ℂ) := rfl
  simp only [GlobalTheory.CompanionTheory.ModelS.yZ, GlobalTheory.CompanionTheory.ModelS.muZ, infOf, hl, e3]
  push_cast
  rw [hlow]
  linear_combination (-1 : ℂ) * c3 - c4

end GlobalTheory.CompanionTheory.ModelS.ReversedBlocks
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimOfAnnihilatingPolyEigenspaces
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.LinAlg

open Polynomial

theorem finiteDimensional_of_roots_of_eigenspaces {M : Type} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) (s : Multiset ℂ) :
    ∀ V : Submodule ℂ M, (∀ v ∈ V, T v ∈ V) →
      (∀ v ∈ V, aeval T ((s.map fun a => (X - C a : ℂ[X])).prod) v = 0) →
      (∀ c : ℂ, FiniteDimensional ℂ (Submodule.span ℂ {v | v ∈ V ∧ T v = c • v})) →
      FiniteDimensional ℂ V := by
  induction s using Multiset.induction_on with
  | empty =>
    intro V _ hker _
    have hbot : V = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      exact (Submodule.mem_bot ℂ).mpr (by simpa using hker v hv)
    subst hbot
    infer_instance
  | cons a s ih =>
    intro V hV hker hfin
    set f : Module.End ℂ M := aeval T (X - C a : ℂ[X]) with hf
    have hfv : ∀ v, f v = T v - a • v := by
      intro v
      simp [f]
    have hWV : ∀ w ∈ V.map f, w ∈ V := by
      rintro w ⟨v, hv, rfl⟩
      rw [hfv]
      exact V.sub_mem (hV v hv) (V.smul_mem a hv)
    have hW1 : ∀ w ∈ V.map f, T w ∈ V.map f := by
      rintro w ⟨v, hv, rfl⟩
      refine ⟨T v, hV v hv, ?_⟩
      simp [hfv, map_sub, map_smul]
    have hW2 : ∀ w ∈ V.map f,
        aeval T ((s.map fun b => (X - C b : ℂ[X])).prod) w = 0 := by
      rintro w ⟨v, hv, rfl⟩
      have h := hker v hv
      rw [Multiset.map_cons, Multiset.prod_cons, mul_comm, map_mul] at h
      exact h
    have hW3 : ∀ c : ℂ, FiniteDimensional ℂ
        (Submodule.span ℂ {v | v ∈ V.map f ∧ T v = c • v}) := by
      intro c
      haveI := hfin c
      have hsub : {v | v ∈ V.map f ∧ T v = c • v} ⊆ {v | v ∈ V ∧ T v = c • v} :=
        fun v hv => ⟨hWV v hv.1, hv.2⟩
      exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)
    have hWfin : FiniteDimensional ℂ (V.map f) := ih (V.map f) hW1 hW2 hW3
    apply Module.Finite.iff_fg.mpr
    apply Submodule.fg_of_fg_map_of_fg_inf_ker f
    · exact Module.Finite.iff_fg.mp hWfin
    · haveI := hfin a
      have hle : V ⊓ LinearMap.ker f ≤ Submodule.span ℂ {v | v ∈ V ∧ T v = a • v} := by
        rintro v ⟨hv, hk⟩
        apply Submodule.subset_span
        refine ⟨hv, ?_⟩
        have h0 : f v = 0 := hk
        rw [hfv, sub_eq_zero] at h0
        exact h0
      haveI := Submodule.finiteDimensional_of_le hle
      exact Module.Finite.iff_fg.mp inferInstance

theorem finiteDimensional_of_polynomial_of_eigenspaces :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (V : Submodule ℂ M),
      (∀ v ∈ V, T v ∈ V) → ∀ p : Polynomial ℂ, p ≠ 0 →
      (∀ v ∈ V, Polynomial.aeval T p v = 0) →
      (∀ c : ℂ, FiniteDimensional ℂ (Submodule.span ℂ {v | v ∈ V ∧ T v = c • v})) →
      FiniteDimensional ℂ V := by
  intro M _ _ T V hV p hp hker hfin
  have hsplit : p = C p.leadingCoeff * (p.roots.map fun a => (X - C a : ℂ[X])).prod := by
    first
      | exact Polynomial.eq_prod_roots_of_splits_id (IsAlgClosed.splits p)
      | exact (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
          (IsAlgClosed.card_roots_eq_natDegree (k := ℂ))).symm
  refine finiteDimensional_of_roots_of_eigenspaces T p.roots V hV ?_ hfin
  intro v hv
  have h := hker v hv
  rw [hsplit, map_mul, Polynomial.aeval_C] at h
  have h' : p.leadingCoeff • aeval T ((p.roots.map fun a => (X - C a : ℂ[X])).prod) v = 0 := by
    rw [← h, Algebra.algebraMap_eq_smul_one]
    rfl
  exact (smul_eq_zero.mp h').resolve_left (Polynomial.leadingCoeff_ne_zero.mpr hp)

end GlobalTheory.CompanionTheory.LinAlg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalKerSubId
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CompactFix

theorem finiteDimensional_ker_sub_id {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : X →L[ℂ] X) (hT : IsCompactOperator T) :
    FiniteDimensional ℂ (LinearMap.ker ((T : X →ₗ[ℂ] X) - LinearMap.id)) := by
  set K : Submodule ℂ X := LinearMap.ker ((T : X →ₗ[ℂ] X) - LinearMap.id) with hK
  have hfix : ∀ x ∈ K, T x = x := by
    intro x hx
    have : (T : X →ₗ[ℂ] X) x - x = 0 := by simpa [hK] using hx
    simpa [sub_eq_zero] using this
  have hclosed : IsClosed (K : Set X) := by
    have : (K : Set X) = {x | T x = x} := by
      ext x
      constructor
      · exact hfix x
      · intro h
        have h' : T x = x := h
        simp [hK, h']
    rw [this]
    exact isClosed_eq T.continuous continuous_id
  obtain ⟨C, hC, hCsub⟩ := hT
  have hpre : (T ⁻¹' C) ∈ nhds (0 : X) := hCsub
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hpre
  have hcomp : IsCompact (Metric.closedBall (0 : K) r) := by
    have hemb : Topology.IsClosedEmbedding (Subtype.val : K → X) := hclosed.isClosedEmbedding_subtypeVal
    rw [hemb.isCompact_iff]
    refine hC.of_isClosed_subset ?_ ?_
    · have : (Subtype.val '' Metric.closedBall (0 : K) r) = (K : Set X) ∩ Metric.closedBall 0 r := by
        ext x
        simp [Metric.mem_closedBall, dist_eq_norm, and_comm]
      rw [this]
      exact hclosed.inter Metric.isClosed_closedBall
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : (x : X) ∈ Metric.closedBall (0 : X) r := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      have := hball hx'
      simpa [hfix x x.2] using this
  exact FiniteDimensional.of_isCompact_closedBall ℂ hr hcomp

end GlobalTheory.CompanionTheory.CompactFix
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintEqOfLe
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.HintSmaller

theorem hint_eq_of_le : ∀ {H : Type} [Group H] (K S : Subgroup H) (u : H → ℂ), S ≤ K → S ≤ rStab u →
    S.relIndex K ≠ 0 → (Function.support fun q : H ⧸ S => u q.out).Finite →
    hint K u = ((S.relIndex K : ℂ))⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  intro H _ K S u hSK hSu hfin _
  exact GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K S u hSK hSu hfin

end GlobalTheory.CompanionTheory.HintSmaller
end
end

