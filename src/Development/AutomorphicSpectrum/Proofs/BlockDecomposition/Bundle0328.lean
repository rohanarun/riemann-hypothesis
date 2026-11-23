module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormConsMul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0302
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0309
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0284
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0319
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0287
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0318
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0285
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0322
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0300
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0324
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.BWMorL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0325
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DCupZero
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

theorem d_cup_zero {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (P : CH.Pairing F₁ F₂ F₃)
    {p n m : ℕ} {r : CH.Cn F₁ p} {z : CH.Cn F₂ n} (hr : CH.d F₁ p r = 0) (hz : CH.d F₂ n z = 0) (h : p + n = m) :
    CH.d F₃ m (P.cupC h r z) = 0 := by
  rw [CrystallineSemistableComparison.P.leibniz, hr, hz]
  simp

section Over
variable {K : Type} [Field K] [CharZero K] {W Y : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Y}
open GlobalTheory.CompanionTheory.RelInjAbs GlobalTheory.CompanionTheory.RelInjZ

set_option maxHeartbeats 2000000 in
theorem kill_over [IsSeparated q] [IsClosedImmersion i] (hTop : TopRes) (hFU : FormUniq) (hOR : OmRes) (hSL : SiteLaws) (hCD : CovDesc) (hZR : ZarRel)
    (hAO : AffOm) (hAR : AffRel) (hFL : FormLaws) (hDW : DWedge) (hDL : DLog) (hFC : FormCup) (hC1 : FirstChernCoboundary) (hCK : ConeKill)
    (D : E.LineData Y) (hQ : Cosieve (On q i))
    (bf : ∀ {V : Scheme.{0}} (a : V ⟶ D.Y), Γ(V, ⊤))
    (bf_nat : ∀ {V' V : Scheme.{0}} (g : V' ⟶ V) (a : V ⟶ D.Y), bf (g ≫ a) = g.appTop.hom (bf a))
    (bf_u : ∀ {V : Scheme.{0}} (a b : V ⟶ D.Y) (h : a ≫ D.f = b ≫ D.f), bf a = (D.u a b h : Γ(V, ⊤)) * bf b)
    {m : ℕ} (U : Fin m → Y.Opens) (σ : ∀ α, (U α : Scheme.{0}) ⟶ D.Y) (hσ : ∀ α, σ α ≫ D.f = (U α).ι)
    (hU : (⨆ α, U α) = ⊤) (haff : ∀ α α', IsAffineOpen (U α ⊓ U α'))
    (hcov : ∀ α (V : Y.Opens) (h : V ≤ U α), IsAffineOpen V →
      (∃ n, Nonempty (Coord q V n)) ∧ (∃ n, Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) n)) ∧
      RingHom.ker (i.app V).hom = Ideal.span {V.topIso.hom.hom (bf (Y.homOfLE h ≫ σ α))} ∧
      ∀ (a : ℕ) (ω : Om K (Sec q V) a), (show Sec q V from V.topIso.hom.hom (bf (Y.homOfLE h ≫ σ α))) • ω = 0 → ω = 0)
    (r : CH.Cn (G q 1) 2) (hr : CH.d (G q 1) 2 r = 0) (hc1 : IsDlogFirstChernClass q D (clsH (a := 1) q r hr))
    (a n : ℕ) (z : CH.Cn (G q a) n) (hz : CH.d (G q a) n z = 0) (hzr : z ∈ relS (G q a) (On q i) n) :
    RelNull (G q (a + 1)) (On q i) (n + 2)
      (cupC q (a := 1) (a' := a) (Nat.add_comm 1 a) (Nat.add_comm 2 n) r z) := by
  classical
  obtain ⟨hc, -, htop, -, -, -⟩ := hSL K W Y Y q i (𝟙 Y)
  obtain ⟨ε, β, hβ, hβu⟩ := hC1 K Y q D (Fin m) U σ hσ r hr hc1
  let Uc : Fin m → ObjectProperty (Thick (smFun Y q)) := fun α => inU q (U α)
  let Vs : Finset (Fin m) → Y.Opens := fun S => S.inf U
  have hVle : ∀ {α : Fin m} {S : Finset (Fin m)}, α ∈ S → Vs S ≤ U α := fun h => Finset.inf_le h
  have hVT : ∀ {S T : Finset (Fin m)}, S ⊆ T → Vs T ≤ Vs S := fun h => Finset.inf_mono h
  have hVaff : ∀ S : Finset (Fin m), S.Nonempty → IsAffineOpen (Vs S) := fun S hS =>
    affine_finset_inf q U S hS fun o _ => by simpa using haff o o
  have hP : ∀ S : Finset (Fin m), S.Nonempty → capU Uc S = inU q (Vs S) := fun S hS =>
    capU_nonempty _ _ S hS fun T => inU_finset_inf hSL i U S T
  have hk : ∀ {S T : Finset (Fin m)}, S ⊆ T → inU q (Vs T) ≤ inU q (Vs S) := fun h T' hT =>
    (inU_finset_inf hSL i U _ T').2 fun o ho => (inU_finset_inf hSL i U _ T').1 hT o (h ho)
  have hd₁ : ∀ S : Finset (Fin m), S.Nonempty → ∃ d, Nonempty (Coord q (Vs S) d) := fun S ⟨α, hα⟩ =>
    (hcov α (Vs S) (hVle hα) (hVaff S ⟨α, hα⟩)).1
  have hd₂ : ∀ S : Finset (Fin m), S.Nonempty → ∃ d, Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ Vs S) d) := fun S ⟨α, hα⟩ =>
    (hcov α (Vs S) (hVle hα) (hVaff S ⟨α, hα⟩)).2.1
  choose dd hdd using hd₁
  choose dd' hdd' using hd₂
  have hE : ∀ (S : Finset (Fin m)) (hS : S.Nonempty) (b : ℕ),
      ∃ e : Om K (Sec q (Vs S)) b →ₗ[K] HV q (Vs S) b b, IsOm q (Vs S) b e ∧ Function.Bijective e := fun S hS b =>
    (hAO K Y q (Vs S) (dd S hS) (hdd S hS) b).2
  choose E hEom hEb using hE
  have hOm := fun (S T : Finset (Fin m)) (h : S ⊆ T) => hOR K Y q (Vs S) (Vs T) (hVT h) (hk h)
  choose φ hφ1 hφ2 hφ3 using hOm
  let P := (grOk (smFun Y q) (Nat.add_comm 1 a)).pair
  have hUc : ∀ α, Cosieve (Uc α) := fun α => hc _
  have h1 : (covSy (G q a) Uc hQ).One a := fun S hS j hj =>
    one_P hAR hQ (hP S hS) (hdd S hS) (hdd' S hS) a j hj
  have h2 : (covSy (G q (a + 1)) Uc hQ).One (a + 1) := fun S hS j hj =>
    one_P hAR hQ (hP S hS) (hdd S hS) (hdd' S hS) (a + 1) j hj
  let e₂ : ∀ S : Finset (Fin m), S.Nonempty → (Om K (Sec q (Vs S)) a →ₗ[K] HU (G q a) (capU Uc S) a) := fun S hS =>
    (castH (G q a) (hP S hS) a).toLinearMap ∘ₗ E S hS a
  let e₃ : ∀ S : Finset (Fin m), S.Nonempty → (Om K (Sec q (Vs S)) (a + 1) →ₗ[K] HU (G q (a + 1)) (capU Uc S) (a + 1)) :=
    fun S hS => (castH (G q (a + 1)) (hP S hS) (a + 1)).toLinearMap ∘ₗ E S hS (a + 1)
  let fS : ∀ (α : Fin m) (S : Finset (Fin m)), α ∈ S → Sec q (Vs S) := fun α S hα =>
    (Vs S).topIso.hom.hom (bf (Y.homOfLE (hVle hα) ≫ σ α))
  have pf : ∀ (α α' : Fin m) (S : Finset (Fin m)) (hα : α ∈ S) (hα' : α' ∈ S),
      (Y.homOfLE (hVle hα) ≫ σ α) ≫ D.f = (Y.homOfLE (hVle hα') ≫ σ α') ≫ D.f := fun α α' S hα hα' => by
    simp [hσ]
  let uS : ∀ (α α' : Fin m) (S : Finset (Fin m)), α ∈ S → α' ∈ S → (Sec q (Vs S))ˣ := fun α α' S hα hα' =>
    Units.map (M := Γ((Vs S : Scheme.{0}), ⊤)) (N := Sec q (Vs S)) ((Vs S).topIso.hom.hom : _ →+* Γ(Y, Vs S)).toMonoidHom
      (D.u (Y.homOfLE (hVle hα) ≫ σ α) (Y.homOfLE (hVle hα') ≫ σ α') (pf α α' S hα hα'))
  have hφf : ∀ (α : Fin m) {S T : Finset (Fin m)} (h : S ⊆ T) (hα : α ∈ S), φ S T h (fS α S hα) = fS α T (h hα) := by
    intro α S T h hα
    rw [hφ1]
    refine (rs_topIso (hVT h) _).trans ?_
    rw [← bf_nat, ← Category.assoc, Scheme.homOfLE_homOfLE]
  let kk : ∀ {S T : Finset (Fin m)}, S ⊆ T → capU Uc T ≤ capU Uc S := fun h _ hT => ⟨hT.1, fun α hα => hT.2 α (h hα)⟩
  have huf : ∀ α α' S hα hα', fS α S hα = uS α α' S hα hα' * fS α' S hα' := fun α α' S hα hα' =>
    (congrArg (Vs S).topIso.hom.hom (bf_u _ _ (pf α α' S hα hα'))).trans (map_mul _ _ _)
  have hcup : ∀ α α' S hα hα' (y : CH.Cn ((capU Uc S).ι ⋙ G q a) a) (hy : CH.d _ a y = 0) (ω : Om K (Sec q (Vs S)) a)
      (w : Om K (Sec q (Vs S)) a →ₗ[Sec q (Vs S)] Om K (Sec q (Vs S)) (a + 1)),
      (∀ g₀ (g : Fin a → Sec q (Vs S)), w (form K g₀ g) = form K g₀ (Fin.cons (uS α α' S hα hα' : Sec q (Vs S)) g)) →
      (CH.cx _).cls y hy = e₂ S ⟨α, hα⟩ ω → ∀ hz,
      (CH.cx ((capU Uc S).ι ⋙ G q (a + 1))).cls ((pairU P (capU Uc S)).cupC (Nat.add_comm 1 a)
        ((resU (G q 1) (capU_le Uc S hα)).pullC 1 (β α) - (resU (G q 1) (capU_le Uc S hα')).pullC 1 (β α')) y) hz =
        e₃ S ⟨α, hα⟩ ((ε : ℤ) • ((↑(uS α α' S hα hα')⁻¹ : Sec q (Vs S)) • w ω)) := by
    intro α α' S hα hα' y hy ω w hw hcls hz
    have := cup_P hFL hFU hFC (hP S ⟨α, hα⟩) (capU_le Uc S hα) (capU_le Uc S hα') (β α) (β α') (E S ⟨α, hα⟩ a)
      (E S ⟨α, hα⟩ (a + 1)) (hEom S _ a) (hEom S _ (a + 1)) ((ε : ℤ) • (↑(uS α α' S hα hα')⁻¹ : Sec q (Vs S)))
      (uS α α' S hα hα' : Sec q (Vs S))
      (fun k₁ k₂ => hβu α α' (Vs S) (hVle hα) (hVle hα') k₁ k₂ (uS α α' S hα hα') (by
        change (Vs S).topIso.inv.hom ((Vs S).topIso.hom.hom _) = _
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
        rfl)) w hw y hy ω hcls hz
    rw [smul_assoc] at this
    exact this
  let x : ((covSy (G q a) Uc hQ).K ∅).X n :=
    ⟨(CH.Mor.restrict (G q a) (capU Uc ∅).ι).pullC n z, fun s hs => hzr _ hs⟩
  have hx : ((covSy (G q a) Uc hQ).K ∅).d n x = 0 := Subtype.ext (by
    change CH.d _ n ((CH.Mor.restrict (G q a) (capU Uc ∅).ι).pullC n z) = 0
    rw [CH.Mor.d_pullC, hz, map_zero])
  have hB := cov_kill hCK hCD hDW hDL hFL P Uc hUc hQ a h1 h2 r hr β hβ (fun S => Sec q (Vs S)) e₂ e₃
    (fun S hS => (castH (G q a) (hP S hS) a).bijective.comp (hEb S hS a))
    (fun S hS => inj_P hAR hQ (hP S hS) (hdd S hS) (hdd' S hS) (a + 1) (E S hS (a + 1)) (hEom S hS (a + 1)))
    (fun S => kerI q i (Vs S))
    (fun S hS ω => range_P hAR hQ (hP S hS) (hdd S hS) (hdd' S hS) a (E S hS a) (hEom S hS a) ω)
    (fun S hS ω => range_P hAR hQ (hP S hS) (hdd S hS) (hdd' S hS) (a + 1) (E S hS (a + 1)) (hEom S hS (a + 1)) ω)
    fS (fun α S hα => (hcov α (Vs S) (hVle hα) (hVaff S ⟨α, hα⟩)).2.2.1)
    (fun α S hα ω => (hcov α (Vs S) (hVle hα) (hVaff S ⟨α, hα⟩)).2.2.2 (a + 1) ω) (ε : ℤ)
    (fun {S T} h => φ S T h) hφf kk
    (fun {S T} h hS hT ω => pull_P (hP S hS) (hP T hT) (kk h) a (E S hS a) (E T hT a) (omMap (φ S T h) a)
      (fun k' ω => hφ3 S T h a _ _ (hEom S hS a) (hEom T hT a) ω) ω)
    (fun {S T} h hS hT ω => pull_P (hP S hS) (hP T hT) (kk h) (a + 1) (E S hS (a + 1)) (E T hT (a + 1))
      (omMap (φ S T h) (a + 1)) (fun k' ω => hφ3 S T h (a + 1) _ _ (hEom S hS (a + 1)) (hEom T hT (a + 1)) ω) ω)
    uS huf hcup n x hx
  have hZ := bij_res_of_eq (capU_empty Uc) hQ (fun _ _ => htop _) (fun _ _ => htop _) (n + 2)
    (hZR K W Y q i hQ (Fin m) ⊤ U hU (fun _ _ => htop _) (a + 1) (n + 2))
  have hd : CH.d (G q (a + 1)) (n + 2) (P.cupC (Nat.add_comm 2 n) r z) = 0 := d_cup_zero P hr hz _
  exact relNull_top hTop (G q (a + 1)) hQ (inU q ⊤) (capU Uc ∅) htop _ hZ (P.cupC (Nat.add_comm 2 n) r z) hd
    (cup_mem_relS P hQ _ r z hzr) _ rfl hB

end Over

end GlobalTheory.CompanionTheory.RelKill
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetConjUnitary
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Vol

def I0 : ℝ≥0∞ := ∫⁻ z : ℂ, ENNReal.ofReal (((1 + ‖z‖) ^ 3)⁻¹)

theorem I0_lt_top : I0 < ⊤ := by
  have h := integrable_one_add_norm (E := ℂ) (μ := volume) (r := 3)
    (by rw [Complex.finrank_real_complex]; norm_num)
  have h2 := h.lintegral_lt_top
  refine lt_of_le_of_lt (le_of_eq ?_) h2
  refine lintegral_congr fun z => ?_
  congr 1
  rw [Real.rpow_neg (by positivity), show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]

def wt (l : ℝ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 + ‖z‖) ^ 3)⁻¹ * ((1 + |l| * ‖z‖) ^ 3)⁻¹)

theorem measurable_wt (l : ℝ) : Measurable (wt l) := by
  unfold wt
  fun_prop

theorem lint_scale {l : ℝ} (hl : l ≠ 0) :
    ∫⁻ z : ℂ, ENNReal.ofReal (((1 + |l| * ‖z‖) ^ 3)⁻¹) = ENNReal.ofReal ((l ^ 2)⁻¹) * I0 := by
  have hr : |l| ≠ 0 := abs_ne_zero.mpr hl
  have hm := Measure.map_addHaar_smul (volume : Measure ℂ) hr
  have hF : Measurable fun w : ℂ => ENNReal.ofReal (((1 + ‖w‖) ^ 3)⁻¹) := by fun_prop
  have h1 : ∫⁻ z : ℂ, ENNReal.ofReal (((1 + |l| * ‖z‖) ^ 3)⁻¹)
      = ∫⁻ w : ℂ, ENNReal.ofReal (((1 + ‖w‖) ^ 3)⁻¹) ∂(Measure.map (fun x : ℂ => |l| • x) volume) := by
    rw [lintegral_map hF (measurable_const_smul _)]
    refine lintegral_congr fun z => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_abs]
  rw [h1, hm, lintegral_smul_measure, Complex.finrank_real_complex]
  simp only [smul_eq_mul, I0]
  congr 2
  rw [abs_of_nonneg (by positivity), sq_abs]

theorem one_var (l : ℝ) :
    ∫⁻ z : ℂ, wt l z ≤ ENNReal.ofReal (2 * I0.toReal * (1 + l ^ 2)⁻¹) := by
  have hI : ENNReal.ofReal I0.toReal = I0 := ENNReal.ofReal_toReal I0_lt_top.ne
  have hI0 : 0 ≤ I0.toReal := ENNReal.toReal_nonneg
  rcases le_or_gt |l| 1 with h | h
  · have h1 : ∫⁻ z : ℂ, wt l z ≤ I0 := by
      refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
      have ha : (0:ℝ) ≤ ((1 + ‖z‖) ^ 3)⁻¹ := by positivity
      have hb : ((1 + |l| * ‖z‖) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀
        (one_le_pow₀ (by nlinarith [norm_nonneg z, abs_nonneg l]))
      nlinarith
    refine h1.trans ?_
    conv_lhs => rw [← hI]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : l ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg l]
    have h3 : (1 : ℝ) ≤ 2 * (1 + l ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith
    nlinarith
  · have hl : l ≠ 0 := by
      rintro rfl
      simp at h
      linarith
    have h1 : ∫⁻ z : ℂ, wt l z ≤ ∫⁻ z : ℂ, ENNReal.ofReal (((1 + |l| * ‖z‖) ^ 3)⁻¹) := by
      refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
      have ha : (0:ℝ) ≤ ((1 + |l| * ‖z‖) ^ 3)⁻¹ := by positivity
      have hb : ((1 + ‖z‖) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀
        (one_le_pow₀ (by linarith [norm_nonneg z]))
      nlinarith
    refine h1.trans ?_
    rw [lint_scale hl]
    conv_lhs => rw [← hI]
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : 1 ≤ l ^ 2 := by
      rw [← sq_abs]
      nlinarith
    have h3 : (l ^ 2)⁻¹ ≤ 2 * (1 + l ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    nlinarith

theorem pi_bound {n : ℕ} (l : Fin n → ℝ) :
    ∫⁻ z : Fin n → ℂ, ∏ i, wt (l i) (z i) ≤
      ENNReal.ofReal ((2 * I0.toReal) ^ n * (∏ i, (1 + l i ^ 2))⁻¹) := by
  have hI0 : 0 ≤ I0.toReal := ENNReal.toReal_nonneg
  rw [volume_pi, GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod
    (f := fun i => wt (l i)) fun i => (measurable_wt (l i)).aemeasurable]
  refine (Finset.prod_le_prod' fun i _ => one_var (l i)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => by positivity, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_inv_distrib]

theorem prod_le_pow {n K : ℕ} (hK : 3 * n ≤ K) {x : Fin n → ℝ} {a : ℝ} (h0 : ∀ i, 0 ≤ x i)
    (hx : ∀ i, x i ≤ a) (ha : 0 ≤ a) :
    ((1 + a) ^ K)⁻¹ ≤ ∏ i, ((1 + x i) ^ 3)⁻¹ := by
  rw [Finset.prod_inv_distrib]
  refine inv_anti₀ (Finset.prod_pos fun i _ => by have := h0 i; positivity) ?_
  calc ∏ i, (1 + x i) ^ 3 ≤ ∏ _i : Fin n, (1 + a) ^ 3 :=
        Finset.prod_le_prod₀ (fun i _ => by have := h0 i; positivity)
          fun i _ => pow_le_pow_left₀ (by have := h0 i; positivity) (by linarith [hx i]) 3
    _ = (1 + a) ^ (3 * n) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
    _ ≤ (1 + a) ^ K := pow_le_pow_right₀ (by linarith) hK

theorem weight_le {n K : ℕ} (hK : 3 * n ≤ K) (l : Fin n → ℝ) {a d : ℝ} (z : Fin n → ℂ)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (h1 : ∀ i, ‖z i‖ ≤ a) (h2 : ∀ i, |l i| * ‖z i‖ ≤ d) :
    ENNReal.ofReal (((1 + a) ^ K)⁻¹ * ((1 + d) ^ K)⁻¹) ≤ ∏ i, wt (l i) (z i) := by
  unfold wt
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => by positivity, Finset.prod_mul_distrib]
  refine ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul (prod_le_pow hK (fun i => norm_nonneg _) h1 ha)
    (prod_le_pow hK (fun i => by positivity) h2 hd) (by positivity)
    (Finset.prod_nonneg fun i _ => by positivity)

theorem det_conj_unitary {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    det ((U : Matrix (Fin n) (Fin n) ℂ) * X * star (U : Matrix (Fin n) (Fin n) ℂ)) = det X := by
  rw [det_mul, det_mul, mul_comm (det (U : Matrix (Fin n) (Fin n) ℂ)), mul_assoc, ← det_mul,
    mem_unitaryGroup_iff.mp U.2, det_one, mul_one]

theorem detW_eq {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) :
    detW b = ∏ i, (1 + hb.eigenvalues i ^ 2) := by
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hb.eigenvalues) with hD
  have hs := hb.spectral_theorem
  have h1 : 1 + b * b = Unitary.conjStarAlgAut ℂ _ hb.eigenvectorUnitary (1 + D * D) := by
    rw [map_add (f := _), map_one, map_mul, ← hs]
  have h2 : 1 + D * D = diagonal fun i => (((1 + hb.eigenvalues i ^ 2 : ℝ)) : ℂ) := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one, diagonal_add]
    congr 1
    ext i
    simp [sq]
  rw [detW, h1, Unitary.conjStarAlgAut_apply, det_conj_unitary, h2, det_diagonal,
    ← Complex.ofReal_prod, Complex.ofReal_re]

theorem repr_apply_lin {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (y : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    hb.eigenvectorBasis.repr (Matrix.toEuclideanLin b y) i =
      (hb.eigenvalues i : ℂ) * hb.eigenvectorBasis.repr y i := by
  have hs : (Matrix.toEuclideanLin b).IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hb
  have he : Matrix.toEuclideanLin b (hb.eigenvectorBasis i) =
      (hb.eigenvalues i : ℂ) • hb.eigenvectorBasis i := by
    have := hb.mulVec_eigenvectorBasis i
    apply PiLp.ext
    intro j
    have h2 := congrFun this j
    simpa [toLpLin_apply] using h2
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply, ← hs, he, inner_smul_left]
  simp

theorem map_isometry {n : ℕ} (m : Measure (EuclideanSpace ℂ (Fin n))) [m.IsAddHaarMeasure]
    (R : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    MeasurePreserving R m m := by
  have hp := LinearIsometryEquiv.measurePreserving
    (⟨R.toLinearEquiv.restrictScalars ℝ, R.norm_map⟩ :
      EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n))
  have hc := Measure.isAddLeftInvariant_eq_smul m (volume : Measure (EuclideanSpace ℂ (Fin n)))
  refine ⟨R.continuous.measurable, ?_⟩
  have hm : Measure.map R (volume : Measure (EuclideanSpace ℂ (Fin n))) = volume := hp.map_eq
  conv_lhs => rw [hc]
  rw [Measure.map_smul, hm, ← hc]
  exact R.continuous.aemeasurable

theorem exists_scale (n : ℕ) (m : Measure (EuclideanSpace ℂ (Fin n))) [m.IsAddHaarMeasure] :
    ∃ c : NNReal, ∀ P : (Fin n → ℂ) → ℝ≥0∞, Measurable P →
      ∫⁻ y, P (WithLp.ofLp y) ∂m = c * ∫⁻ x, P x := by
  let e := EuclideanSpace.equiv (Fin n) ℂ
  haveI : (Measure.map e m).IsAddHaarMeasure := e.isAddHaarMeasure_map m
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map e m = c • (volume : Measure (Fin n → ℂ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  refine ⟨c, fun P hP => ?_⟩
  have h1 : ∫⁻ y, P (WithLp.ofLp y) ∂m = ∫⁻ x, P x ∂(Measure.map e m) := by
    rw [lintegral_map hP e.continuous.measurable]
    rfl
  rw [h1, hc, lintegral_smul_measure]
  rfl

theorem volume_bound : ∀ (n K : ℕ), 3 * n ≤ K → ∀ m : Measure (EuclideanSpace ℂ (Fin n)), m.IsAddHaarMeasure →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : Matrix (Fin n) (Fin n) ℂ, b.IsHermitian →
    ∫⁻ y, ENNReal.ofReal (((1 + ‖y‖) ^ K)⁻¹ * ((1 + ‖Matrix.toEuclideanLin b y‖) ^ K)⁻¹) ∂m ≤
      ENNReal.ofReal (C * (detW b)⁻¹) := by
  intro n K hK m hm
  obtain ⟨c, hc⟩ := exists_scale n m
  have hI0 : 0 ≤ I0.toReal := ENNReal.toReal_nonneg
  refine ⟨c * (2 * I0.toReal) ^ n, by positivity, fun b hb => ?_⟩
  set l := hb.eigenvalues with hl
  set R := hb.eigenvectorBasis.repr with hR
  let P : (Fin n → ℂ) → ℝ≥0∞ := fun x => ∏ i, wt (l i) (x i)
  have hP : Measurable P :=
    Finset.measurable_prod _ fun i _ => (measurable_wt (l i)).comp (measurable_pi_apply i)
  have hG : Measurable fun y : EuclideanSpace ℂ (Fin n) => P (WithLp.ofLp y) :=
    hP.comp (EuclideanSpace.equiv (Fin n) ℂ).continuous.measurable
  have h1 : ∀ y : EuclideanSpace ℂ (Fin n),
      ENNReal.ofReal (((1 + ‖y‖) ^ K)⁻¹ * ((1 + ‖Matrix.toEuclideanLin b y‖) ^ K)⁻¹) ≤
        P (WithLp.ofLp (R y)) := by
    intro y
    refine weight_le hK l _ (norm_nonneg _) (norm_nonneg _) (fun i => ?_) (fun i => ?_)
    · rw [← R.norm_map y]
      exact PiLp.norm_apply_le (R y) i
    · rw [← R.norm_map (Matrix.toEuclideanLin b y)]
      refine le_trans (le_of_eq ?_) (PiLp.norm_apply_le (R (Matrix.toEuclideanLin b y)) i)
      rw [hR, repr_apply_lin hb, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc _ ≤ ∫⁻ y, P (WithLp.ofLp (R y)) ∂m := lintegral_mono h1
    _ = ∫⁻ y, P (WithLp.ofLp y) ∂m := (map_isometry m R).lintegral_comp hG
    _ = c * ∫⁻ x, P x := hc P hP
    _ ≤ c * ENNReal.ofReal ((2 * I0.toReal) ^ n * (∏ i, (1 + l i ^ 2))⁻¹) := by
        gcongr
        exact pi_bound l
    _ = ENNReal.ofReal (c * (2 * I0.toReal) ^ n * (detW b)⁻¹) := by
        rw [detW_eq hb, mul_assoc, ENNReal.ofReal_mul (p := (c : ℝ)) (by positivity),
          ENNReal.ofReal_coe_nnreal]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Vol
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetInducedTwoCharacters
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SmGL.Bernstein

theorem proportional_of_equiv {G V V' W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ G V} {τ' : Representation ℂ G V'} {σ : Representation ℂ G W}
    (E : τ.Equiv τ')
    (h : ∀ φ ψ : τ'.IntertwiningMap σ, φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap)
    (φ ψ : τ.IntertwiningMap σ) :
    φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap := by
  rcases h (φ.comp E.symm.toIntertwiningMap) (ψ.comp E.symm.toIntertwiningMap) with h0 | ⟨c, hc⟩
  · left
    ext v
    have := LinearMap.congr_fun h0 (E v)
    simpa using this
  · right
    refine ⟨c, ?_⟩
    ext v
    have := LinearMap.congr_fun hc (E v)
    simpa using this

theorem eq_zero_of_equiv {G V V' W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ G V} {τ' : Representation ℂ G V'} {σ : Representation ℂ G W}
    (E : τ.Equiv τ') (h : ∀ φ : τ'.IntertwiningMap σ, φ.toLinearMap = 0)
    (φ : τ.IntertwiningMap σ) : φ.toLinearMap = 0 := by
  ext v
  have := LinearMap.congr_fun (h (φ.comp E.symm.toIntertwiningMap)) (E v)
  simpa using this

theorem exists_diagonal_sizeMatrix (a b : ℕ) :
    ∃ D : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b)),
      ∀ B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b)), B = D ↔ B.1 false true = 0 := by
  have card_f : Fintype.card (Two (Fin a) (Fin b) false) = a := Fintype.card_fin a
  have card_t : Fintype.card (Two (Fin a) (Fin b) true) = b := Fintype.card_fin b
  refine ⟨⟨fun i j => if i = j then (if i then b else a) else 0, ?_, ?_⟩, fun B => ⟨?_, ?_⟩⟩
  · intro i; cases i <;> simp [card_f, card_t]
  · intro j; cases j <;> simp [card_f, card_t]
  · rintro rfl; simp
  · intro hB
    have r0 := B.2.1 false
    have r1 := B.2.1 true
    have c0 := B.2.2 false
    have c1 := B.2.2 true
    simp only [Fintype.sum_bool, card_f, card_t] at r0 r1 c0 c1
    apply Subtype.ext
    funext i j
    cases i <;> cases j <;> simp <;> omega


set_option maxHeartbeats 600000 in
theorem mackey_maps_proportional : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), JacquetOfInducedFiltration k → IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) → (∀ φ ψ : (GlobalTheory.SmGL.jac (two (stdSum (rfl : a + b = a + b))) (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro k _ _ _ _ a b χ₁ χ₂ hJ h₁ h₂ u₁ u₂ hne
  have hc : Continuous (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom :=
    continuous_prodMk.2 ⟨continuous_apply _, continuous_apply _⟩
  have hsm : IsSmooth ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp
      (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) :=
    isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff _).2 h₁.detChar)
      ((isSmooth_ofChar_iff _).2 h₂.detChar)) _ hc
  obtain ⟨N, bb, hb⟩ := hJ Bool Bool (Fin (a + b)) (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))
    (two (stdSum (rfl : a + b = a + b))) (two (stdSum (rfl : a + b = a + b)))
  obtain ⟨S, hm, hbot, htop, hE⟩ := hb (TensorProduct ℂ ℂ ℂ) _ hsm
  obtain ⟨D, hD⟩ := exists_diagonal_sizeMatrix a b
  obtain ⟨t₀, ht₀⟩ := bb.surjective D
  refine _root_.GlobalTheory.CompanionTheory.Filtration.intertwining_proportional _ ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) N S hm hbot htop t₀ ?_ ?_
  · exact proportional_of_equiv (hE t₀ (SizeMatrix.nonempty_rows (bb t₀)).some (SizeMatrix.nonempty_cols (bb t₀)).some).some
      (_root_.GlobalTheory.CompanionTheory.CellDiag.diag_cell_at_most_one_map k a b χ₁ χ₂ (bb t₀) _ _ ((hD _).1 ht₀))
  · intro t ht
    exact eq_zero_of_equiv (hE t (SizeMatrix.nonempty_rows (bb t)).some (SizeMatrix.nonempty_cols (bb t)).some).some
      (GlobalTheory.T.cell_functor_nonscalar_offdiag k a b χ₁ χ₂ h₁ h₂ u₁ u₂ hne (bb t) _ _ fun h0 =>
        ht (bb.injective (((hD _).2 h0).trans ht₀.symm)))

end GlobalTheory.CompanionTheory.SmGL.Bernstein
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelOperatorsEventuallyGenerateStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_operators_eventually_generate : GlobalTheory.CompanionTheory.GE.GradedNoeth → ∀ {X : AlgebraicGeometry.Scheme.{0}} [AlgebraicGeometry.IsLocallyNoetherian X] {k : ℕ} {M : ℕ → X.Modules} {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (hM : GlobalTheory.CompanionTheory.GE.OpSeq (k + 1) M T d) (U : X.affineOpens), ∃ d₁ : ℕ, ∀ e, d₁ ≤ e → Submodule.span Γ(X, U) (⋃ i, Set.range ((GlobalTheory.CompanionTheory.GE.UV.kerOps hM.comm i e).app U)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GE.UV.kerOps_gen_bounded | exact GlobalTheory.CompanionTheory.GE.UV.kerOps_gen_bounded | (intros; apply GlobalTheory.CompanionTheory.GE.UV.kerOps_gen_bounded <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothModelTensorWittComparisonStatement
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_model_tensor_witt_comparison : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K), M.Sm → ∀ j n, Tens (WittVector l r.k) (N := fun _ : Unit => AW r) (M := fun _ => (Wc.HS l (B.schFn M.p) r.ρ j).M n) (M' := Mid.HM r M n j) fun _ a y => idA r a • bWL r M n j y := by
  first | exact @GlobalTheory.CompanionTheory.BcAcris.bc_tens | exact GlobalTheory.CompanionTheory.BcAcris.bc_tens | (intros; apply GlobalTheory.CompanionTheory.BcAcris.bc_tens <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformFirstCohomologyKernelsExistStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_first_cohomology_kernels_exist : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] [IsNoetherianRing R] (g : ℕ) (ρ : Fin g → R) (T : ℕ → ℤ → Finset ι → Type) [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)] (res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S') (p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S) (mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S) (one : ∀ e (i : ι), T e 0 {i}) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S), (∀ e t S (h : S ⊆ S) a, res e t S S h a = a) → (∀ e t S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res e t S' S'' h' (res e t S S' h a) = res e t S S'' (h.trans h') a) → (∀ e t S S' (h : S ⊆ S') a, S.Nonempty → p e t S' (res (e + 1) t S S' h a) = res e t S S' h (p e t S a)) → (∀ j e t S a, S.Nonempty → p e (t + 1) S (mm j (e + 1) t S a) = mm j e t S (p e t S a)) → (∀ j e t S S' (h : S ⊆ S') a, S.Nonempty → res e (t + 1) S S' h (mm j e t S a) - mm j e t S' (res e t S S' h a) ∈ Ideal.span (Set.range ρ) • (⊤ : Submodule R (T e (t + 1) S'))) → (∀ e t S, S.Nonempty → Function.Surjective (p e t S)) → (∀ e t S, S.Nonempty → LinearMap.ker (p e t S) = Ideal.span (Set.range ρ) ^ (e + 1) • ⊤) → (∀ e t S, S.Nonempty → Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T e t S)) = ⊥) → (∀ i e t S, i ∈ S → Function.Bijective (mm i e t S)) → (∀ e S j t (a : T e t S), S.Nonempty → res e t S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc e S) t a = 0) → (∀ e S j t (b : T e t (insert j S)), S.Nonempty → ∃ (k : ℕ) (t' : ℤ) (a : T e t' S), GrSum.of (hc e (insert j S)) t' (res e t' S (insert j S) (Finset.subset_insert j S) a) = (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc e (insert j S)) t b) → (∀ e i, p e 0 {i} (one (e + 1) i) = one e i) → (∀ e i t (a : T e t {i}), ∃ (k : ℕ) (q : MvPolynomial ι R) (t' : ℤ) (w : T e t' {i}), w ∈ Ideal.span (Set.range ρ) • (⊤ : Submodule R (T e t' {i})) ∧ (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of (hc e {i}) t a = q • GrSum.of (hc e {i}) 0 (one e i) + GrSum.of (hc e {i}) t' w) → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∀ e (c : ∀ i j : ι, T (e + 1) t {i, j}), (∀ i j, p e t {i, j} (c i j) = 0) → (∀ i j k, res (e + 1) t {i, j} {i, j, k} (sub_triple_ij i j k) (c i j) + res (e + 1) t {j, k} {i, j, k} (sub_triple_jk i j k) (c j k) = res (e + 1) t {i, k} {i, j, k} (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i, T (e + 1) t {i}, (∀ i, p e t {i} (b i) = 0) ∧ ∀ i j, c i j = res (e + 1) t {i} {i, j} (sub_pair_left i j) (b i) - res (e + 1) t {j} {i, j} (sub_pair_right i j) (b j) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_uniform_h1_kernels | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_uniform_h1_kernels | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_uniform_h1_kernels <;> assumption)
end

