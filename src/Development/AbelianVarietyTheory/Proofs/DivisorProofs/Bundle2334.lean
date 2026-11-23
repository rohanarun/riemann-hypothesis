module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ActionProductEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendsTaylorPowerSeriesRing
section
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory.FormalOrigin.Extend

noncomputable def pdZ {σ R : Type} [CommRing R] (j : σ) : Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R) where
  toFun := MvPowerSeries.pderiv (R := R) j
  map_add' := map_add _
  map_smul' m x := by simpa using map_zsmul (MvPowerSeries.pderiv (R := R) j) m x
  map_one_eq_zero' := MvPowerSeries.pderiv_one
  leibniz' := (MvPowerSeries.pderiv (R := R) j).leibniz

theorem pdZ_apply {σ R : Type} [CommRing R] (j : σ) (F : MvPowerSeries σ R) :
    pdZ j F = MvPowerSeries.pderiv (R := R) j F := rfl

theorem add_sum_apply {σ R ι : Type} [CommRing R] [Fintype ι] (E : Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R))
    (G : ι → MvPowerSeries σ R) (P : ι → Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R))
    (F : MvPowerSeries σ R) : (E + ∑ j, G j • P j) F = E F + ∑ j, G j * P j F := by
  rw [Derivation.add_apply]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  change ∑ j, (G j • P j) F = ∑ j, G j * P j F
  simp [Derivation.smul_apply, smul_eq_mul]

theorem derivation_extends : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (inc : R →+* A) (ev : A →+* R), (∀ r, ev (inc r) = r) → ∀ (n : ℕ) (ds : Fin n → Derivation ℤ A A) (z : Fin n → A), (∀ i, ev (z i) = 0) → (∀ a i, ev (ds a (z i)) = if a = i then 1 else 0) → maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z) → (∀ a r, ds a (inc r) = 0) → ∀ (d : Derivation ℤ A A) (D : Derivation ℤ R R), (∀ r, d (inc r) = inc (D r)) → ∃ dΩ : Derivation ℤ (MvPowerSeries (Fin n) R) (MvPowerSeries (Fin n) R), (∀ r, dΩ (MvPowerSeries.C r) = MvPowerSeries.C (D r)) ∧ ∀ f, dΩ (taylor ev (fun i => ⇑(ds i)) f) = taylor ev (fun i => ⇑(ds i)) (d f) := by
  intro R A _ _ _ _ _ _ _ _ inc ev hev n ds z hz hdz hm hinc d D hdD
  obtain ⟨T, hT⟩ := taylor_isRingHom A R n ev ds
  simp only [← hT]
  obtain ⟨E, hE⟩ := _root_.GlobalTheory.mvPowerSeries_derivation_coeffwise (Fin n) R D
  have hEC : ∀ r, E (MvPowerSeries.C r) = MvPowerSeries.C (D r) := by
    intro r; ext α
    rw [hE, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
    split_ifs <;> simp
  have hTinc : ∀ r, T (inc r) = MvPowerSeries.C r := by
    intro r; rw [hT, taylor_const A R n ev ds (inc r) (fun i => hinc i r), hev]
  obtain ⟨G, hG⟩ := _root_.GlobalTheory.powerSeries_matrix_solve n R (fun i j => pdZ j (T (z i))) (by
    intro i j
    simp only [pdZ_apply]
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv, zero_add, hT,
      _root_.GlobalTheory.FormalOrigin.Extend.taylor_coeff_single, hdz]
    simp [eq_comm]) (fun i => T (d (z i)) - E (T (z i)))
  set dΩ : Derivation ℤ (MvPowerSeries (Fin n) R) (MvPowerSeries (Fin n) R) := E + ∑ j, G j • pdZ j with hdΩ
  have hΩ : ∀ F, dΩ F = E F + ∑ j, G j * pdZ j F := fun F => add_sum_apply E G _ F
  refine ⟨dΩ, fun r => ?_, ?_⟩
  · simp [hΩ, hEC, pdZ_apply]
  ·
    set e : A → MvPowerSeries (Fin n) R := fun f => dΩ (T f) - T (d f) with he
    have e_add : ∀ f g, e (f + g) = e f + e g := by
      intro f g; simp only [he, map_add (f := _)]; ring
    have e_mul : ∀ f g, e (f * g) = T f * e g + T g * e f := by
      intro f g; simp only [he, map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _)]; ring
    have e_neg : ∀ f, e (-f) = - e f := by
      intro f; simp only [he, map_neg]; ring
    have e_one : e 1 = 0 := by simp [he]
    let Q : Subring A :=
      { carrier := {f | e f = 0}
        mul_mem' := fun {f g} hf hg => by simp only [Set.mem_setOf_eq] at *; rw [e_mul, hf, hg]; ring
        one_mem' := e_one
        add_mem' := fun {f g} hf hg => by simp only [Set.mem_setOf_eq] at *; rw [e_add, hf, hg]; ring
        zero_mem' := by simp [he]
        neg_mem' := fun {f} hf => by simp only [Set.mem_setOf_eq] at *; rw [e_neg, hf, neg_zero] }
    have hQ : Subring.closure (Set.range inc ∪ Set.range z) ≤ Q := by
      rw [Subring.closure_le]
      rintro _ (⟨r, rfl⟩ | ⟨i, rfl⟩)
      · change e (inc r) = 0
        simp [he, hTinc, hdD, hΩ, hEC, pdZ_apply]
      · change e (z i) = 0
        have := hG i
        simp only [he, hΩ]
        rw [this]; ring

    have hc0 : ∀ x, MvPowerSeries.constantCoeff (T x) = ev x := by
      intro x
      rw [hT, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      change (∏ i, (((0 : Fin n →₀ ℕ) i).factorial : ℚ))⁻¹ • ev (iterOp _ 0 x) = _
      rw [iterOp_zero]; simp
    have hloc : ∀ x ∈ maximalIdeal A, ev x ∈ maximalIdeal R := by
      intro x hx
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h1 : x - inc (ev x) ∈ maximalIdeal A := by
        apply le_maximalIdeal (RingHom.ker_ne_top ev)
        rw [RingHom.mem_ker, map_sub, hev, sub_self]
      have h2 : inc (ev x) ∈ maximalIdeal A := by simpa using Ideal.sub_mem _ hx h1
      exact (mem_maximalIdeal _).1 h2 (hu.map inc)
    have hT1 : ∀ x ∈ maximalIdeal A, T x ∈ filt (maximalIdeal R) 1 := by
      intro x hx α
      by_cases hα : α = 0
      · subst hα
        simp only [map_zero, Nat.sub_zero, pow_one]
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hc0]
        exact hloc x hx
      · have : 1 - α.degree = 0 := by
          have : α.degree ≠ 0 := by
            intro h0; exact hα ((Finsupp.degree_eq_zero_iff α).1 h0)
          omega
        rw [this, pow_zero, Ideal.one_eq_top]; trivial
    have hTk : ∀ k, ∀ x ∈ maximalIdeal A ^ k, T x ∈ filt (maximalIdeal R) k := by
      intro k
      induction k with
      | zero => intro x _ α; simp
      | succ k ih =>
        intro x hx
        rw [pow_succ'] at hx
        refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
        · rw [map_mul, add_comm]
          exact GlobalTheory.T.mvPowerSeriesDegreeAdicFiltration_mul_le (Fin n) R _ 1 k (Ideal.mul_mem_mul (hT1 a ha) (ih b hb))
        · rw [map_add (f := _)]; exact Ideal.add_mem _ ha hb
    have hek : ∀ k, ∀ x ∈ maximalIdeal A ^ (k + 1), e x ∈ filt (maximalIdeal R) k := by
      intro k
      induction k with
      | zero => intro x _ α; simp
      | succ k ih =>
        intro x hx
        rw [pow_succ'] at hx
        refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
        · rw [e_mul]
          refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ (hTk _ b hb))
          rw [add_comm]
          exact GlobalTheory.T.mvPowerSeriesDegreeAdicFiltration_mul_le (Fin n) R _ 1 k (Ideal.mul_mem_mul (hT1 a ha) (ih b hb))
        · rw [e_add]; exact Ideal.add_mem _ ha hb
    intro f
    have : e f = 0 := by
      refine eq_zero_of_forall_mem_filt (maximalIdeal R) _ fun k => ?_
      obtain ⟨p, hp, hfp⟩ := GlobalTheory.T.exists_coordinate_polynomial_sub_mem_maximalIdeal_pow R A inc ev hev n z hm (k + 1) f
      have h1 : e f = e p + e (f - p) := by rw [← e_add]; congr 1; ring
      rw [h1, show e p = 0 from hQ hp, zero_add]
      exact hek k _ hfp
    exact sub_eq_zero.1 this

end GlobalTheory.FormalOrigin.Extend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentDatumCarriesTranslateChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

section

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G' : Over S} [GrpObj G']

theorem Near.datum_pt (N : Near π G') {φ} (hφ : N.Datum φ) {T : Scheme.{0}} (s : T ⟶ pullback π π)
    (x₀ x₀' : T ⟶ pullback N.U.hom π) (z : T ⟶ pullback G'.hom (pullback.fst π π))
    (h₁ : x₀' ≫ pullback.fst _ _ = x₀ ≫ pullback.fst _ _) (h₂ : x₀ ≫ pullback.snd _ _ = s ≫ pullback.fst π π)
    (h₃ : x₀' ≫ pullback.snd _ _ = s ≫ pullback.snd π π) (hz₁ : z ≫ pullback.fst _ _ = x₀ ≫ N.u)
    (hz₂ : z ≫ pullback.snd _ _ = s) :
    z ≫ φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) = x₀' ≫ N.u := by
  obtain ⟨x₁, e₁, e₂, e₃⟩ := hφ.2 T (x₀ ≫ pullback.fst _ _) z
    ⟨x₀, rfl, by rw [← Category.assoc, hz₂, h₂], hz₁.symm⟩
  have : x₁ = x₀' := pullback.hom_ext (e₁.trans h₁.symm) (by rw [e₂, ← Category.assoc, hz₂, h₃])
  rw [← e₃, this]

theorem transl_pt {T : Scheme.{0}} (t : T ⟶ S) (g : Over.mk t ⟶ G') (y : Over.mk (𝟙 S) ⟶ G') :
    g ≫ transl y = g * (Over.homMk t (Category.comp_id t) ≫ y) := by
  unfold transl
  rw [comp_mul, Category.comp_id, ← Category.assoc]
  congr 2
  ext
  simp [Over.w g]

theorem pull_pt_ext {S' : Scheme.{0}} (f : S' ⟶ S) {T : Scheme.{0}} {s : T ⟶ S'}
    (a b : Over.mk s ⟶ (Over.pullback f).obj G') (h : a.left ≫ pullback.fst G'.hom f = b.left ≫ pullback.fst G'.hom f) :
    a = b :=
  Over.OverMorphism.ext (pullback.hom_ext h ((Over.w a).trans (Over.w b).symm))

end

theorem Near.datum_chart {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S)
    [GrpObj G'] (N : Near π G') (n : ℕ) (a : Fin n → (Sp R ⟶ N.U.left)) (x : Fin n → (Over.mk (𝟙 S) ⟶ G'))
    (hx : ∀ i, N.Pt (𝟙 S) (π ≫ a i) (x i).left) (φ) (hφ : N.Datum φ) (j : Option (Fin n)) (T : Scheme.{0})
    (y₁ y₂ : T ⟶ pullback N.U.hom π) (s : T ⟶ pullback π π)
    (hy : y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _) (h₁ : y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π)
    (h₂ : y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π) (z : T ⟶ pullback G'.hom (pullback.fst π π))
    (hz₁ : z ≫ pullback.fst _ _ = y₁ ≫ N.chart x j) (hz₂ : z ≫ pullback.snd _ _ = s) :
    z ≫ φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) = y₂ ≫ N.chart x j := by
  cases j with
  | none => exact N.datum_pt hφ s y₁ y₂ z hy.symm h₁ h₂ hz₁ hz₂
  | some k =>
  haveI := hφ.1
  rw [Near.chart_some] at hz₁ ⊢
  obtain ⟨x₀, e₁, e₂, e₃⟩ := hx k
  have hxo : (x k).left ≫ G'.hom = 𝟙 S := Over.w (x k)
  have c₁ : (y₁ ≫ N.u) ≫ G'.hom = s ≫ pullback.fst π π := by rw [Category.assoc, N.u_over, h₁]
  have c₂ : (y₂ ≫ N.u) ≫ G'.hom = s ≫ pullback.snd π π := by rw [Category.assoc, N.u_over, h₂]
  have d₁ : (s ≫ pullback.fst π π ≫ (x k).left) ≫ G'.hom = s ≫ pullback.fst π π := by
    simp only [Category.assoc, hxo, Category.comp_id]
  have d₂ : (s ≫ pullback.snd π π ≫ (x k).left) ≫ G'.hom = s ≫ pullback.snd π π := by
    simp only [Category.assoc, hxo, Category.comp_id]
  let G₁ := (Over.pullback (pullback.fst π π)).obj G'
  let G₂ := (Over.pullback (pullback.snd π π)).obj G'
  let W₁ : Over.mk s ⟶ G₁ := Over.homMk (pullback.lift _ _ c₁) (pullback.lift_snd _ _ _)
  let X₁ : Over.mk s ⟶ G₁ := Over.homMk (pullback.lift _ _ d₁) (pullback.lift_snd _ _ _)
  let W₂ : Over.mk s ⟶ G₂ := Over.homMk (pullback.lift _ _ c₂) (pullback.lift_snd _ _ _)
  let X₂ : Over.mk s ⟶ G₂ := Over.homMk (pullback.lift _ _ d₂) (pullback.lift_snd _ _ _)
  let Z₁ : Over.mk s ⟶ G₁ := Over.homMk z hz₂
  let P₁ := pushHom (isGrpPullback_pullback G' (pullback.fst π π)) (Over.mk s)
  let P₂ := pushHom (isGrpPullback_pullback G' (pullback.snd π π)) (Over.mk s)
  let w₁ : Over.mk (s ≫ pullback.fst π π) ⟶ G' := Over.homMk (y₁ ≫ N.u) c₁
  let w₂ : Over.mk (s ≫ pullback.snd π π) ⟶ G' := Over.homMk (y₂ ≫ N.u) c₂
  have pW₁ : P₁ W₁ = w₁ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have pW₂ : P₂ W₂ = w₂ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have pX₁ : P₁ X₁ = Over.homMk (s ≫ pullback.fst π π) (Category.comp_id _) ≫ x k :=
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have pX₂ : P₂ X₂ = Over.homMk (s ≫ pullback.snd π π) (Category.comp_id _) ≫ x k :=
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)

  have hZ : Z₁ = W₁ * X₁⁻¹ := by
    apply pull_pt_ext
    have e : P₁ Z₁ = P₁ (W₁ * X₁⁻¹) := by
      rw [map_mul, map_inv, pW₁, pX₁, ← GrpObj.comp_inv, ← transl_pt]
      exact Over.OverMorphism.ext (by
        show z ≫ pullback.fst _ _ = (y₁ ≫ N.u) ≫ (transl (x k)⁻¹).left
        rw [hz₁, Category.assoc])
    exact congrArg (fun q => q.left) e
  have hW : W₁ ≫ φ.hom = W₂ := by
    apply pull_pt_ext
    rw [Over.comp_left, Category.assoc]
    refine (N.datum_pt hφ s y₁ y₂ _ hy.symm h₁ h₂ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)).trans ?_
    exact (pullback.lift_fst _ _ _).symm
  have hX : X₁ ≫ φ.hom = X₂ := by
    apply pull_pt_ext
    rw [Over.comp_left, Category.assoc]
    refine (N.datum_pt hφ s (s ≫ pullback.fst π π ≫ x₀) (s ≫ pullback.snd π π ≫ x₀) _ ?_ ?_ ?_ ?_
      (pullback.lift_snd _ _ _)).trans ?_
    · simp only [Category.assoc, e₁]
      rw [← Category.assoc (pullback.snd π π), ← pullback.condition, Category.assoc]
    · simp only [Category.assoc, e₂, Category.comp_id]
    · simp only [Category.assoc, e₂, Category.comp_id]
    · rw [pullback.lift_fst]; simp only [Category.assoc, e₃]
    · refine Eq.trans ?_ (pullback.lift_fst _ _ d₂).symm
      simp only [Category.assoc, e₃]
  have e : P₂ (Z₁ ≫ φ.hom) = w₂ ≫ transl (x k)⁻¹ := by
    rw [hZ, mul_comp, GrpObj.inv_comp, hW, hX, map_mul, map_inv, pW₂, pX₂, ← GrpObj.comp_inv, ← transl_pt]
  have e' : (z ≫ φ.hom.left) ≫ pullback.fst G'.hom (pullback.snd π π) = (y₂ ≫ N.u) ≫ (transl (x k)⁻¹).left :=
    congrArg (fun q => q.left) e
  simpa only [Category.assoc] using e'

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerPolyAlgebraHomotopyIdentity
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem homotopy_identity : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η → (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) → (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (ε : Q.P →+* B) (hε : SemiHom (RingHom.id R) ε), IsDPMorphism η δ ε → (∀ b, ε (algebraMap B Q.P b) = b) → (∀ n, ε (Q.e (n + 1)) = 0) → ∀ (N : ℕ) (x : DR R Q.P), x - h.mDR (hε.mDR x) - dDR R Q.P (hot v Q.e N x) - hot v Q.e N (dDR R Q.P x) ∈ filDR R η N := by
  intro R B _ _ _ J δ Q _ _ η v g hstd hvb hve hvd ε hε hεd hεb hεe N

  have hfilE : ∀ k, Q.e k ∈ fil η k := fun k ↦ by
    have := (GlobalTheory.PDA.fil_properties Q.P (Q.ext J) η).2.2.2.2.1 k (Q.e 1) (Q.e_one_mem_ext J)
    rwa [hstd.var] at this
  obtain ⟨hot_add, hot_alg, -, hot_rel, hot_fil⟩ := _root_.GlobalTheory.PDForm.HotFil.hot_fil R Q.P (Q.ext J) η v Q.e N hvd hfilE
  obtain ⟨hrel_mul, -, -, -, hfil0, hfil_anti, hfil_smul⟩ := _root_.GlobalTheory.PDForm.rel_two_sided_and_bot.1 R Q.P (Q.ext J) η
  have hd_fil : ∀ n, ∀ x ∈ filDR R η (n + 1), dDR R Q.P x ∈ filDR R η n := fun n ↦
    (_root_.GlobalTheory.PDForm.ctr_lie_rel_filDR.2 R Q.P (Q.ext J) η v hvd n).2.1
  have hrel_le : rel R η ≤ filDR R η N := le_sup_right
  let H : DR R Q.P →+ DR R Q.P := AddMonoidHom.mk' (hot v Q.e N) hot_add
  have hH : ∀ x, H x = hot v Q.e N x := fun _ ↦ rfl
  have hrelgen : ∀ m, ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1)) ∈ rel R η := fun m ↦ by
    have : ι1 (D R Q.P (η.dpow (m + 1) (Q.e 1)) - η.dpow m (Q.e 1) • D R Q.P (Q.e 1)) ∈ rel R η :=
      Ideal.subset_span ⟨m, Q.e 1, Q.e_one_mem_ext J, rfl⟩
    rwa [hstd.var, hstd.var, map_sub, map_smul] at this
  have hD0 : ι1 (D R Q.P (Q.e 0)) = 0 := by rw [Q.e_zero, Derivation.map_one_eq_zero, map_zero]
  have hε1 : ε (Q.e 1) = 0 := by simpa using hεe 0
  have hcomp : ∀ α : DR R B, hε.mDR (g.mDR α) = α := by
    intro α
    induction α using indDR with
    | h b => rw [g.mDR_algebraMap, hε.mDR_algebraMap, hεb]
    | hd b => rw [g.mDR_ι, hε.mDR_ι, g.m1_D, hε.m1_D, hεb]
    | hm x y hx hy => rw [map_mul, map_mul, hx, hy]
    | ha x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hεD1 : hε.mDR (ι1 (D R Q.P (Q.e 1))) = 0 := by
    rw [hε.mDR_ι, hε.m1_D, hε1, Derivation.map_zero, map_zero]

  have big : ∀ M, ∀ x ∈ filDR R η M, N ≤ M →
      x - dDR R Q.P (hot v Q.e N x) - hot v Q.e N (dDR R Q.P x) ∈ filDR R η N := by
    intro M x hx hM
    refine sub_mem (sub_mem (hfil_anti N M hM hx) ?_) ?_
    · exact hfil_anti N M hM (hd_fil M _ (hot_fil M x hx))
    · cases M with
      | zero => rw [Nat.le_zero.1 hM, hfil0]; trivial
      | succ k => exact hfil_anti N (k + 1) hM (hot_fil k _ (hd_fil k x hx))
  have hsmul_mem : ∀ n (y : DR R Q.P), Q.e n • y ∈ filDR R η n := fun n y ↦ by
    simpa using hfil_smul n 0 (Q.e n) (hfilE n) y (by rw [hfil0]; trivial)
  intro x
  refine _root_.GlobalTheory.PDForm.pdPoly_forms_induction R B J δ Q η v g hstd hvb hve hvd
    (fun x ↦ x - g.mDR (hε.mDR x) - dDR R Q.P (hot v Q.e N x) - hot v Q.e N (dDR R Q.P x) ∈ filDR R η N)
    ?_ ?_ ?_ ?_ x
  ·
    intro x hx
    refine sub_mem (sub_mem (sub_mem (hrel_le hx) (hrel_le ?_)) (hrel_le ?_)) (hrel_le ?_)
    · exact mDR_mem_rel g hstd.dp (mDR_mem_rel hε hεd hx)
    · exact dDR_mem_rel R η (hot_rel x hx)
    · exact hot_rel _ (dDR_mem_rel R η hx)
  ·
    intro x y hx hy
    have := add_mem hx hy
    convert this using 1
    simp only [map_add (f := _), hot_add]
    abel
  ·
    intro n α
    have hz := (_root_.GlobalTheory.PDForm.hot_values R B J δ Q η v g hstd hvb hve hvd N n α).1
    have hz' := (_root_.GlobalTheory.PDForm.hot_values R B J δ Q η v g hstd hvb hve hvd N n (dDR R B α)).1
    have hdx : dDR R Q.P (Q.e n • g.mDR α) = ι1 (D R Q.P (Q.e n)) * g.mDR α + Q.e n • g.mDR (dDR R B α) := by
      rw [dDR_smul, g.mDR_dDR]
    have hmx : g.mDR (hε.mDR (Q.e n • g.mDR α)) = algebraMap B Q.P (ε (Q.e n)) • g.mDR α := by
      rw [hε.mDR_smul, hcomp, g.mDR_smul]
    rw [hmx, hz, hdx, hot_add, hz', map_zero]
    cases n with
    | zero =>
      rw [hD0, zero_mul, Q.e_zero, map_one, map_one, one_smul, ← hH, map_zero]
      simp
    | succ m =>
      rw [hεe m, map_zero, zero_smul]
      rcases lt_or_ge m N with hm | hm
      · have hv := (_root_.GlobalTheory.PDForm.hot_values R B J δ Q η v g hstd hvb hve hvd N m α).2 hm
        have hr : (ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α ∈ rel R η :=
          hrel_mul _ (hrelgen m) _
        have key : ι1 (D R Q.P (Q.e (m + 1))) * g.mDR α =
            (ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α +
              Q.e m • (ι1 (D R Q.P (Q.e 1)) * g.mDR α) := by
          rw [sub_mul, smul_mul_assoc]; abel
        rw [key, hot_add, hv]
        have : Q.e (m + 1) • g.mDR α - 0 - 0 -
            (hot v Q.e N ((ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α) +
              Q.e (m + 1) • g.mDR α + 0) =
            -hot v Q.e N ((ι1 (D R Q.P (Q.e (m + 1))) - Q.e m • ι1 (D R Q.P (Q.e 1))) * g.mDR α) := by abel
        rw [this]
        exact hrel_le (neg_mem (hot_rel _ hr))
      · have hb := big (m + 1) _ (hsmul_mem (m + 1) (g.mDR α)) (by omega)
        rw [hz, hdx, hot_add, hz', map_zero] at hb
        simpa using hb
  ·
    intro n α
    have hdy : dDR R Q.P (ι1 (D R Q.P (Q.e 1)) * g.mDR α) = -(ι1 (D R Q.P (Q.e 1)) * g.mDR (dDR R B α)) := by
      rw [dDR_mul, sgn_ι, dDR_D, zero_mul, add_zero, neg_mul, g.mDR_dDR]
    have hmx : g.mDR (hε.mDR (Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α))) = 0 := by
      rw [hε.mDR_smul, map_mul, hεD1, zero_mul, smul_zero, map_zero]
    rw [hmx, sub_zero]
    rcases lt_or_ge n N with hn | hn
    · have hv := (_root_.GlobalTheory.PDForm.hot_values R B J δ Q η v g hstd hvb hve hvd N n α).2 hn
      have hv' := (_root_.GlobalTheory.PDForm.hot_values R B J δ Q η v g hstd hvb hve hvd N n (dDR R B α)).2 hn

      have hr2 : ι1 (D R Q.P (Q.e n)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) ∈ rel R η := by
        cases n with
        | zero => rw [hD0, zero_mul]; exact zero_mem _
        | succ k =>
          have : ι1 (D R Q.P (Q.e (k + 1))) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) =
              (ι1 (D R Q.P (Q.e (k + 1))) - Q.e k • ι1 (D R Q.P (Q.e 1))) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) := by
            have hsq : Q.e k • ι1 (D R Q.P (Q.e 1)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) = 0 := by
              rw [smul_mul_assoc, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, smul_zero]
            rw [sub_mul, hsq, sub_zero]
          rw [this]
          exact hrel_mul _ (hrelgen k) _
      have hr1 : (ι1 (D R Q.P (Q.e (n + 1))) - Q.e n • ι1 (D R Q.P (Q.e 1))) * g.mDR α ∈ rel R η :=
        hrel_mul _ (hrelgen n) _
      have hdx : dDR R Q.P (Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α)) =
          ι1 (D R Q.P (Q.e n)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α) -
            Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR (dDR R B α)) := by
        rw [dDR_smul, hdy, smul_neg, sub_eq_add_neg]
      have hdh : dDR R Q.P (Q.e (n + 1) • g.mDR α) =
          (ι1 (D R Q.P (Q.e (n + 1))) - Q.e n • ι1 (D R Q.P (Q.e 1))) * g.mDR α +
            Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α) + Q.e (n + 1) • g.mDR (dDR R B α) := by
        rw [dDR_smul, g.mDR_dDR, sub_mul, smul_mul_assoc]; abel
      rw [hv, hdh, hdx, ← hH, map_sub, hH, hH, hv']
      have : Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α) -
          ((ι1 (D R Q.P (Q.e (n + 1))) - Q.e n • ι1 (D R Q.P (Q.e 1))) * g.mDR α +
            Q.e n • (ι1 (D R Q.P (Q.e 1)) * g.mDR α) + Q.e (n + 1) • g.mDR (dDR R B α)) -
          (hot v Q.e N (ι1 (D R Q.P (Q.e n)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α)) -
            Q.e (n + 1) • g.mDR (dDR R B α)) =
          -((ι1 (D R Q.P (Q.e (n + 1))) - Q.e n • ι1 (D R Q.P (Q.e 1))) * g.mDR α) -
            hot v Q.e N (ι1 (D R Q.P (Q.e n)) * (ι1 (D R Q.P (Q.e 1)) * g.mDR α)) := by abel
      rw [this]
      exact hrel_le (sub_mem (neg_mem hr1) (hot_rel _ hr2))
    · exact big n _ (hsmul_mem n _) hn

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ActionProductEqOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.e8_act_prod_eq_one : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ) (K : Type) [Field K] (P' : PolAV (Sp K))
  (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  letI := P'.isAb.comm
  act 0 * act 1 = 𝟙 P'.A ∧
  LBIso (cubeLB P'.A ![fst P'.A P'.A ≫ act 0, snd P'.A P'.A] P'.L) (cubeLB P'.A ![fst P'.A P'.A, snd P'.A P'.A ≫ act 1] P'.L) ∧
  LBIso P'.L (cubeLB P'.A ![𝟙 P'.A, act 0] P'.L) := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.PrimPic.e8_act_endomorphism_prod_eq_id | exact GlobalTheory.Poinc.Sep.E8Fibration.PrimPic.e8_act_endomorphism_prod_eq_id | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.PrimPic.e8_act_endomorphism_prod_eq_id <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ActionRelativelyAmpleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.e8_act_linComb_relAmple : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∃ κ : ℕ, ∀ (gQ : ℕ) (K : Type) [Field K] [IsAlgClosed K] (P' : PolAV (Sp K))
  (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  ∀ i, Out.RelAmple P'.A (LB.LinComb P'.L (K := Fin 2) ![𝟙 P'.A.left, (act i).left] ![(κ : ℤ), -1]) := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound.exists_bound_relAmple | exact GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound.exists_bound_relAmple | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound.exists_bound_relAmple <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFibreIsoEqCoordinatewisePowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighth_power_fibre_iso_eq_coordinatewise_power : ∀ (l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∀ j, 1 ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsUnit (l : V₁) → ∀ (Q : Data V) (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁), ∀ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4) (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))), (∀ a, IsMonHom (pr a)) → (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) → w.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (σ : K ≃+* K), ∀ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f → LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) → (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) → ∃ f₁ : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left, IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f₁ ∧ ∀ (a : Fin 8) (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left) (y : T ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), y ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.fst D.P.A.hom (spMap ev) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) → y ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd D.P.A.hom (spMap ev) → x ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = y ≫ f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) := by
  first | exact @GlobalTheory.PoincDiag.fibreIso_eq_pow | exact GlobalTheory.PoincDiag.fibreIso_eq_pow | (intros; apply GlobalTheory.PoincDiag.fibreIso_eq_pow <;> assumption)
end

