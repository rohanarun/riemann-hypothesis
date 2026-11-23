module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkLoc
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0137
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0117
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0115
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0143
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentComplexPointTangents
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0145
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0076

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenProjectorDenominator
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sandwich

open NumberField Polynomial _root_.GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E]

theorem exists_uniform_factor (w : 𝓞 E) :
    ∃ x : 𝓞 E, x ≠ 0 ∧ ∀ (Ω : Type) [Field Ω] (V : Type) [AddCommGroup V] [Module Ω V]
      (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω),
      ∃ T ∈ opRing ρ σ, (ρ w - scal V σ w) * T = 0 ∧ ∀ v, ρ w v = σ w • v → T v = σ x • v := by
  obtain ⟨f, -, hroot, hder⟩ := exists_sep_poly w
  have key : ∀ p : ℤ[X], eval₂ (Int.castRingHom (𝓞 E)) w p = aeval w p := fun p => by
    rw [aeval_def, algebraMap_int_eq]
  have hF : (f.map (Int.castRingHom (𝓞 E))).IsRoot w := by
    rw [IsRoot, eval_map, key]
    exact hroot
  set g := f.map (Int.castRingHom (𝓞 E)) /ₘ (X - C w) with hg
  have hfac : (X - C w) * g = f.map (Int.castRingHom (𝓞 E)) :=
    (mul_divByMonic_eq_iff_isRoot).2 hF
  refine ⟨g.eval w, ?_, ?_⟩
  · have hd : (derivative (f.map (Int.castRingHom (𝓞 E)))).eval w = g.eval w := by
      rw [← hfac, derivative_mul]
      simp
    rw [← hd, derivative_map, eval_map, key]
    exact hder
  · intro Ω _ V _ _ ρ σ
    refine ⟨eval₂ (scal V σ) (ρ w) g, eval₂_mem_opRing ρ σ w g, ?_, ?_⟩
    · have hcomm : ∀ k, Commute (scal V σ (g.coeff k)) (ρ w) :=
        fun k => commute_scal σ (g.coeff k) (ρ w)
      have h1 : ρ w - scal V σ w = eval₂ (scal V σ) (ρ w) (X - C w) := by
        simp [eval₂_sub]
      rw [h1, ← eval₂_mul_noncomm _ _ hcomm, hfac, eval₂_map]
      have hc : (scal V σ).comp (Int.castRingHom (𝓞 E)) = ρ.comp (Int.castRingHom (𝓞 E)) :=
        RingHom.ext_int _ _
      rw [hc, ← hom_eval₂, key, hroot, map_zero]
    · intro v hv
      exact eval₂_apply_of_eigen ρ σ w hv g

private theorem mem_eigSp_iff_geometry {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]
    (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω) (v : V) :
    v ∈ eigSp ρ σ ↔ ∀ a, ρ a v = σ a • v := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem exists_uniform_product (W : Finset (𝓞 E)) :
    ∃ x : 𝓞 E, x ≠ 0 ∧ ∀ (Ω : Type) [Field Ω] (V : Type) [AddCommGroup V] [Module Ω V]
      (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω),
      ∃ T ∈ opRing ρ σ, (∀ w ∈ W, (ρ w - scal V σ w) * T = 0) ∧ ∀ v ∈ eigSp ρ σ, T v = σ x • v := by
  classical
  induction W using Finset.induction_on with
  | empty =>
    refine ⟨1, one_ne_zero, ?_⟩
    intro Ω _ V _ _ ρ σ
    exact ⟨1, (opRing ρ σ).one_mem, by simp, fun v _ => by simp⟩
  | @insert a W' ha ih =>
    obtain ⟨x', hx', hT'⟩ := ih
    obtain ⟨xa, hxa, hTa⟩ := exists_uniform_factor a
    refine ⟨xa * x', mul_ne_zero hxa hx', ?_⟩
    intro Ω _ V _ _ ρ σ
    obtain ⟨T', hT'm, hT'k, hT'e⟩ := hT' Ω V ρ σ
    obtain ⟨Ta, hTam, hTak, hTae⟩ := hTa Ω V ρ σ
    refine ⟨Ta * T', (opRing ρ σ).mul_mem hTam hT'm, ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw'
      · rw [← mul_assoc, hTak, zero_mul]
      · have hc : Commute (ρ w - scal V σ w) Ta :=
          (commute_opRing hTam w).symm.sub_left (commute_scal σ w Ta)
        rw [← mul_assoc, hc.eq, mul_assoc, hT'k w hw', mul_zero]
    · intro v hv
      have hva : ρ a v = σ a • v := (mem_eigSp_iff_geometry ρ σ v).1 hv a
      change Ta (T' v) = _
      rw [hT'e v hv, map_smul, hTae v hva, smul_smul, map_mul, mul_comm (σ xa)]

theorem exists_eigen_op_uniform : ∀ (E : Type) [Field E] [NumberField E], ∃ D : ℕ, 0 < D ∧
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] (V : Type) [AddCommGroup V] [Module Ω V]
      (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω),
      ∃ T ∈ opRing ρ σ, (∀ v, T v ∈ eigSp ρ σ) ∧ ∀ v ∈ eigSp ρ σ, T v = (D : Ω) • v := by
  intro E _ _
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)
  obtain ⟨x, hx, hT⟩ := exists_uniform_product S
  have hint : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
  have hbot := Ideal.comap_ne_bot_of_integral_mem hx (Ideal.mem_span_singleton_self x) hint
  obtain ⟨c, hcmem, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, algebraMap_int_eq, eq_intCast] at hcmem
  obtain ⟨y0, hy0⟩ := hcmem
  obtain ⟨n, hn0, y, hy⟩ : ∃ n : ℕ, 0 < n ∧ ∃ y : 𝓞 E, x * y = (n : 𝓞 E) := by
    rcases Int.natAbs_eq c with h | h
    · refine ⟨c.natAbs, Int.natAbs_pos.2 hc0, y0, ?_⟩
      rw [← hy0]
      conv_lhs => rw [h]
      simp
    · refine ⟨c.natAbs, Int.natAbs_pos.2 hc0, -y0, ?_⟩
      rw [mul_neg, ← hy0]
      conv_lhs => rw [h]
      simp
  refine ⟨n, hn0, ?_⟩
  intro Ω _ _ V _ _ ρ σ
  obtain ⟨T, hTm, hTk, hTe⟩ := hT Ω V ρ σ
  have hall : ∀ v, ∀ a : 𝓞 E, ρ a (T v) = σ a • T v := by
    intro v a
    have ha : a ∈ Submodule.span ℤ (S : Set (𝓞 E)) := by
      rw [hS]
      trivial
    induction ha using Submodule.span_induction with
    | mem w hw =>
      have h := congrArg (fun U : Module.End Ω V => U v) (hTk w hw)
      change (ρ w - scal V σ w) (T v) = 0 at h
      rw [LinearMap.sub_apply, scal_apply, sub_eq_zero] at h
      exact h
    | zero => simp
    | add a b _ _ iha ihb =>
      rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, iha, ihb, add_smul]
    | smul m a _ ih =>
      rw [map_zsmul, map_zsmul, LinearMap.smul_apply, ih, smul_assoc]
  have hs : scal V σ y ∈ opRing ρ σ := by
    simpa using eval₂_mem_opRing ρ σ 0 (C y)
  refine ⟨scal V σ y * T, (opRing ρ σ).mul_mem hs hTm, ?_, ?_⟩
  · intro v
    change scal V σ y (T v) ∈ eigSp ρ σ
    rw [scal_apply]
    exact Submodule.smul_mem _ _ ((mem_eigSp_iff_geometry ρ σ (T v)).2 (hall v))
  · intro v hv
    change scal V σ y (T v) = _
    rw [scal_apply, hTe v hv, smul_smul, ← map_mul, mul_comm y x, hy, map_natCast]

end GlobalTheory.CompanionTheory.Ar.Sandwich
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualBC
section
noncomputable section

namespace GlobalTheory.CompanionTheory.HtLink

open PositivityTheory.HtPt.Htat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.BT hiding genPt
open GlobalTheory.CompanionTheory.Ar.HTTie
open GlobalTheory.CompanionTheory.Ar.HTChart (dual_comp snd_epsMul)

section Alg

variable {A Ω : Type} [CommRing A] [Field Ω] [Algebra A Ω] {L₀ : Type} [AddCommGroup L₀] [Module A L₀]

theorem clear_denom [Module.Finite A L₀] (hinj : Function.Injective (algebraMap A Ω)) (B : Subring Ω)
    (hB : ∀ b ∈ B, ∃ u a : A, algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ B ∧
      algebraMap A Ω u * b = algebraMap A Ω a)
    (w : L₀ →ₗ[A] Ω) (hw : ∀ b, w b ∈ B) :
    ∃ (u : A) (w₀ : Module.Dual A L₀), algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ B ∧
      ∀ b, algebraMap A Ω (w₀ b) = algebraMap A Ω u * w b := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := L₀)
  have key : ∀ s : Finset L₀, ∃ u : A, algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ B ∧
      ∀ b ∈ s, ∃ a, algebraMap A Ω a = algebraMap A Ω u * w b := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by simp, by simp, by simp⟩
    | insert b s _ ih =>
      obtain ⟨u, h1, h2, h3⟩ := ih
      obtain ⟨u', a, h1', h2', h3'⟩ := hB _ (hw b)
      refine ⟨u * u', by rw [map_mul]; exact mul_ne_zero h1 h1', by rw [map_mul, mul_inv]; exact mul_mem h2 h2',
        fun c hc => ?_⟩
      rcases Finset.mem_insert.1 hc with rfl | hc
      · exact ⟨u * a, by rw [map_mul, map_mul, ← h3']; ring⟩
      · obtain ⟨a', ha'⟩ := h3 c hc
        exact ⟨u' * a', by rw [map_mul, map_mul, ha']; ring⟩
  obtain ⟨u, h1, h2, h3⟩ := key s
  have hall : ∀ b, ∃ a, algebraMap A Ω a = algebraMap A Ω u * w b := by
    intro b
    have hb : b ∈ Submodule.span A (s : Set L₀) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem c hc => exact h3 c hc
    | zero => exact ⟨0, by simp⟩
    | add c d _ _ hc hd =>
      obtain ⟨a, ha⟩ := hc
      obtain ⟨a', ha'⟩ := hd
      exact ⟨a + a', by rw [map_add (f := _), map_add (f := _), ha, ha', mul_add]⟩
    | smul r c _ hc =>
      obtain ⟨a, ha⟩ := hc
      exact ⟨r * a, by rw [map_mul, map_smul, ha, Algebra.smul_def]; ring⟩
  choose w₀ hw₀ using hall
  refine ⟨u, ⟨⟨w₀, fun a b => hinj ?_⟩, fun r a => hinj ?_⟩, h1, h2, hw₀⟩
  · rw [map_add (f := _), hw₀, hw₀, hw₀, map_add (f := _), mul_add]
  · show algebraMap A Ω (w₀ (r • a)) = algebraMap A Ω (r * w₀ a)
    rw [map_mul, hw₀, hw₀, map_smul, Algebra.smul_def]; ring

variable {Li : Type} [AddCommGroup Li] [Module Ω Li] [Module A Li] [IsScalarTower A Ω Li]

theorem exists_dualBC [IsDomain A] [IsFractionRing A Ω] [Module.Finite A L₀] (j₀ : L₀ →ₗ[A] Li)
    (hj₀ : IsBaseChange Ω j₀) :
    ∃ j : Module.Dual A L₀ →ₗ[A] Module.Dual Ω Li, IsBaseChange Ω j ∧
      ∀ w b, j w (j₀ b) = algebraMap A Ω (w b) := by
  have hinj := IsFractionRing.injective A Ω
  let J : Module.Dual A L₀ → Module.Dual Ω Li := fun w => hj₀.lift (Algebra.linearMap A Ω ∘ₗ w)
  have hJ : ∀ w b, J w (j₀ b) = algebraMap A Ω (w b) := fun w b => hj₀.lift_eq _ b
  have hext : ∀ w w' : Module.Dual Ω Li, (∀ b, w (j₀ b) = w' (j₀ b)) → w = w' := fun w w' h => hj₀.algHom_ext _ _ h
  have hsm : ∀ (a : A) (w : Module.Dual Ω Li) e, (a • w) e = algebraMap A Ω a * w e := fun a w e => by
    rw [← algebraMap_smul Ω a w]; rfl
  let j : Module.Dual A L₀ →ₗ[A] Module.Dual Ω Li :=
    { toFun := J
      map_add' := fun w w' => hext _ _ fun b => by simp [hJ]
      map_smul' := fun a w => hext _ _ fun b => by simp [hJ, hsm] }
  refine ⟨j, (isLocalizedModule_iff_isBaseChange (nonZeroDivisors A) Ω j).1 ⟨fun s => ?_, fun w => ?_, ?_⟩, hJ⟩
  · have hs : algebraMap A Ω s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    rw [Module.End.isUnit_iff]
    refine ⟨fun w w' h => ?_, fun w => ⟨(algebraMap A Ω s)⁻¹ • w, ?_⟩⟩
    · have h' : (s : A) • w = (s : A) • w' := h
      rw [← algebraMap_smul Ω, ← algebraMap_smul Ω (s : A) w'] at h'
      exact smul_right_injective _ hs h'
    · show (s : A) • ((algebraMap A Ω s)⁻¹ • w) = w
      rw [← algebraMap_smul Ω, smul_smul, mul_inv_cancel₀ hs, one_smul]
  · obtain ⟨u, w₀, h1, -, h3⟩ := clear_denom hinj ⊤ (fun b _ => by
      obtain ⟨a, u, hu, rfl⟩ := IsFractionRing.div_surjective (A := A) b
      have := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := Ω) hu
      exact ⟨u, a, this, trivial, by field_simp⟩) ((w.restrictScalars A) ∘ₗ j₀) (fun _ => trivial)
    refine ⟨⟨w₀, ⟨u, mem_nonZeroDivisors_of_ne_zero fun h => h1 (by rw [h, map_zero])⟩⟩, hext _ _ fun b => ?_⟩
    show ((u : A) • w) (j₀ b) = J w₀ (j₀ b)
    rw [hsm, hJ, h3]; rfl
  · intro w w' h
    refine ⟨1, ?_⟩
    have : w = w' := LinearMap.ext fun b => hinj (by rw [← hJ, ← hJ]; exact LinearMap.congr_fun h _)
    rw [this]

end Alg

section Geo

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {A : Type} [CommRing A] [Algebra A Ω] {x : Spec (CommRingCat.of A) ⟶ X}

theorem regAt_frac (hξ : IsCptGen ξ) (hk : Function.Injective (algebraMap A Ω))
    (hx : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ x = ξ) (p : PrimeSpectrum A) (q : Cpt ξ) (hp : x p = q.1)
    (hsub : ∀ a, algebraMap A Ω a ∈ regAt ξ q) :
    (∀ u ∉ p.asIdeal, algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ regAt ξ q) ∧
      ∀ b ∈ regAt ξ q, ∃ u a : A, u ∉ p.asIdeal ∧ algebraMap A Ω u * b = algebraMap A Ω a := by
  obtain ⟨_, hS, -, hg⟩ := stalk_loc hξ _ hk x hx p q hp hsub
  have hg' : ∀ a, genMap ξ q (algebraMap A _ a) = algebraMap A Ω a := RingHom.congr_fun hg
  refine ⟨fun u hu => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := (IsLocalization.map_units (X.presheaf.stalk q.1)
      (⟨u, hu⟩ : p.asIdeal.primeCompl)).exists_right_inv
    have h1 : algebraMap A Ω u * genMap ξ q t = 1 := by rw [← hg', ← map_mul, ht, map_one]
    exact ⟨left_ne_zero_of_mul_eq_one h1, t, (eq_inv_of_mul_eq_one_right h1)⟩
  · rintro _ ⟨c, rfl⟩
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj p.asIdeal.primeCompl c
    exact ⟨s, a, s.2, by rw [← hg', ← hg', ← h, map_mul, mul_comm]⟩

variable {G : Over X} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {Li : Type} [AddCommGroup Li] [Module Ω Li]
  (M : LieModel G ξ Li) {L₀ : Type} [AddCommGroup L₀] [Module A L₀] (M₀ : LieModel G x L₀)

omit [IsCommMonObj G] in
theorem exists_lieBC (hx : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ x = ξ) [Module A Li]
    [IsScalarTower A Ω Li] : ∃ j₀ : L₀ →ₗ[A] Li, IsBaseChange Ω j₀ ∧ ∀ v, (M.pt (j₀ v)).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left := by
  subst hx
  obtain ⟨j, hj, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts X G A Ω (algebraMap A Ω) x L₀ Li M₀ M
  have hj' : ∀ v, (M.pt (j v)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left :=
    fun v => (Category.comp_id _).symm.trans (hj v)
  let j₀ : L₀ →ₗ[A] Li :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun a v => by rw [j.map_smulₛₗ, algebraMap_smul]; rfl }
  exact ⟨j₀, (lie_proj X G A x L₀ M₀).2.2 Ω Li M j₀ hj', hj'⟩

omit [IsCommMonObj G] [Smooth G.hom] in
theorem tan_ext {O : Type} [CommRing O] [Algebra A O] {z : Spec (CommRingCat.of O) ⟶ X}
    (hzs : Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ x = z) (g : O →+* Ω)
    (hg : g.comp (algebraMap A O) = algebraMap A Ω) (j₀ : L₀ → Li)
    (hj : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left)
    (b : L₀) : ∃ v : epsAt z ⟶ G, IsTanAt G z v ∧
      (M.pt (j₀ b)).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left := by
  let ψ := LieCarrier.epsHom (algebraMap A O) x _ hzs
  have hleft : (ψ ≫ M₀.pt b).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap A O))) ≫ (M₀.pt b).left := rfl
  refine ⟨ψ ≫ M₀.pt b, ?_, ?_⟩
  · have t : _ ≫ (M₀.pt b).left = _ := M₀.tan b
    rw [one_left] at t
    show _ ≫ (ψ ≫ M₀.pt b).left = _
    rw [hleft, one_left, ← Category.assoc, ← spec_comp, dual_fst, spec_comp, Category.assoc, t]
    simp only [Over.mk_hom]
    rw [← Category.assoc, hzs]
  · rw [hleft, hj, ← Category.assoc, ← spec_comp, dual_comp, hg]

theorem tan_denom {O : Type} [CommRing O] [Algebra A O] (S : Submonoid A) [IsLocalization S O]
    {z : Spec (CommRingCat.of O) ⟶ X}
    (hzs : Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ x = z) (g : O →+* Ω)
    (hg : g.comp (algebraMap A O) = algebraMap A Ω) (j₀ : L₀ → Li)
    (hj : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left)
    (e : Li) (v : epsAt z ⟶ G) (hv : IsTanAt G z v)
    (he' : (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left) :
    ∃ u ∈ S, ∃ b, algebraMap A Ω u • e = j₀ b := by
  obtain ⟨u, hu, b, hub⟩ := exists_denom lie_proj G S x M₀ hzs v hv
  have hgu : g (algebraMap A O u) = algebraMap A Ω u := RingHom.congr_fun hg u
  refine ⟨u, hu, b, hgu ▸ M.inj (Over.OverMorphism.ext ?_)⟩
  rw [M.smul, he', hj, ← hg, ← dual_comp, spec_comp, Category.assoc, ← hub, ← Category.assoc, ← Category.assoc,
    ← spec_comp, ← spec_comp, dual_eps]

theorem mem_omLat_iff (hξ : IsCptGen ξ) (hk : Function.Injective (algebraMap A Ω))
    (hx : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ x = ξ) (j₀ : L₀ → Li)
    (hj : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left)
    (q : Cpt ξ) (hq : q.1 ∈ Set.range x) (hsub : ∀ a, algebraMap A Ω a ∈ regAt ξ q) (w : Module.Dual Ω Li) :
    w ∈ M.omLat q ↔ ∀ b, w (j₀ b) ∈ regAt ξ q := by
  obtain ⟨p, hp⟩ : ∃ p : PrimeSpectrum A, x p = q.1 := hq
  obtain ⟨_, hS, hzs, hg⟩ := stalk_loc hξ _ hk x hx p q hp hsub
  have hlat := (lieLat_carrier X G Ω ξ Li M q).1
  refine ⟨fun h b => h _ ((hlat _).2 ?_), fun h e he => ?_⟩
  · exact tan_ext M M₀ hzs (genMap ξ q) hg j₀ hj b
  · obtain ⟨v, hv, he'⟩ := (hlat e).1 he
    obtain ⟨u, hu, b, hje⟩ := tan_denom M M₀ p.asIdeal.primeCompl hzs (genMap ξ q) hg j₀ hj e v hv he'
    obtain ⟨h1, h2⟩ := (regAt_frac hξ hk hx p q hp hsub).1 u hu
    have : w e = (algebraMap A Ω u)⁻¹ * w (j₀ b) := by
      rw [← hje, map_smul, smul_eq_mul, ← _root_.mul_assoc, inv_mul_cancel₀ h1, _root_.one_mul]
    rw [this]
    exact mul_mem h2 (h b)

end Geo

end GlobalTheory.CompanionTheory.HtLink
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameAtComponentPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames

theorem exists_affine_eigenframes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (p₀ : Cpt (Z.ξ₀ ≫ Y.j)), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → p₀ ∈ Z.genFib → ∃ (A : Y.X.Opens) (hA : IsAffineOpen A) (EB : Type) (_ : AddCommGroup EB) (_ : Module Γ(Y.X, A) EB) (MB : LieModel Y.t.G hA.fromSpec EB) (e₁ : Fin D.p → EB) (e₂ : Fin D.q → EB) (v₁ : Fin D.p → Z.V) (v₂ : Fin D.q → Z.V), p₀.1 ∈ A ∧ (∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 ∈ A → (Z.eig τ).IsFrameAt v₁ q ∧ (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt v₂ q) ∧ (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → y ≫ Y.s = spMap (σ.comp β) → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → IsEigFrame Y.t.act y (σ.comp (tauIn c τ)) v ∧ IsEigFrame Y.t.act y (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w) ∧ (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → genPt (Z.ξ₀ ≫ Y.j) ⤳ centre y → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → (∀ i, Z.M.ValAt y (v₁ i) (v i)) ∧ ∀ j, Z.M.ValAt y (v₂ j) (w j)) := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ b₁ b₂ p₀ hO hτ h1 h2 h3 h4 hp₀
  obtain ⟨hinj, hnoeth, hfr⟩ := hO
  haveI := hnoeth
  have := projProper _ _ _ Y.proj
  haveI : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  haveI : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  haveI : Smooth Y.t.G.hom := Y.t.semi.smooth
  obtain ⟨-, -, h3c, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.isVBOn_eig_genFib E H D l Xo c O β Y U Z τ ⟨hinj, hnoeth, hfr⟩ hτ
  obtain ⟨g, b, hb, hS⟩ := h3c p₀ hp₀
  obtain ⟨S₁, hS₁⟩ := hS τ
  obtain ⟨S₂, hS₂⟩ := hS (ComplexEmbedding.conjugate τ)
  obtain ⟨hspan, N, hpN, hN⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieVB.isFrameAt_span_and_nhd Y.X Y.t.G Z.Ω _ Z.V Z.M p₀ g b hb
  have e₁ := _root_.GlobalTheory.CompanionTheory.Ar.LocalFrames.span_eq_of_saturated Y.X Z.Ω _ Z.V Z.M.lat (eigSp Z.ρ (Z.inc.comp (tauIn c τ))) p₀ g b S₁ Z.gen hspan hb.2 hS₁
  have e₂ := _root_.GlobalTheory.CompanionTheory.Ar.LocalFrames.span_eq_of_saturated Y.X Z.Ω _ Z.V Z.M.lat (eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) p₀ g b S₂
    Z.gen hspan hb.2 hS₂
  have card : ∀ (S : Finset (Fin g)) (n : ℕ) (u : Fin n → Z.V), LinearIndependent Z.Ω u →
      Submodule.span Z.Ω (Set.range u) = Submodule.span Z.Ω (b '' S) → S.card = n := by
    intro S n u hu hsp
    have a₁ := finrank_span_eq_card hu
    have a₂ := finrank_span_eq_card (hb.1.comp (Subtype.val : S → Fin g) Subtype.val_injective)
    have a₃ : Set.range (b ∘ (Subtype.val : S → Fin g)) = b '' S := by
      rw [Set.range_comp, Subtype.range_coe]
    rw [a₃, ← hsp, a₁] at a₂
    simpa using a₂.symm
  have c₁ := card S₁ D.p b₁ h1 (h2.trans e₁)
  have c₂ := card S₂ D.q b₂ h3 (h4.trans e₂)
  let ι₁ := S₁.orderEmbOfFin c₁
  let ι₂ := S₂.orderEmbOfFin c₂
  have r₁ : Set.range (b ∘ ι₁) = b '' S₁ := by
    rw [Set.range_comp, Finset.range_orderEmbOfFin]
  have r₂ : Set.range (b ∘ ι₂) = b '' S₂ := by
    rw [Set.range_comp, Finset.range_orderEmbOfFin]
  obtain ⟨W, hW, hWd⟩ := GlobalTheory.ModelChart.exists_open_isDomain Y.X p₀.1
  have hmem : ∀ i, b i ∈ Z.M.lat p₀ := fun i => by
    rw [hb.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨A, hA, EB, i₁, i₂, MB, e, hpA, hAN, hval⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LocFrames.Chart.exists_chart_values Y.X Y.t.G Z.Ω _ Z.V Z.M p₀ (N ⊓ W) (Fin g) b ⟨hpN, hW⟩ hmem
  have hd : IsDomain Γ(Y.X, A) := hWd A hpA (hAN.trans inf_le_right)
  have hcl := _root_.GlobalTheory.CompanionTheory.Ar.LocFrames.genPt_specializes_of_isDomain Y.X Z.Ω _ A hA p₀ Z.gen hd hpA
  have hcA : ∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X), y = spMap f ≫ hA.fromSpec → centre y ∈ A := by
    intro f y hy
    have h5 : centre y ∈ Set.range hA.fromSpec := by
      subst hy
      exact ⟨spMap f (IsLocalRing.closedPoint ℂ), (Scheme.Hom.comp_apply _ _ _).symm⟩
    rwa [hA.range_fromSpec] at h5
  refine ⟨A, hA, EB, i₁, i₂, MB, e ∘ ι₁, e ∘ ι₂, b ∘ ι₁, b ∘ ι₂, hpA, fun q hq => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact _root_.GlobalTheory.CompanionTheory.Ar.SubFrame.isFrameAt_comp Y.X Z.Ω _ Z.V Z.M.lat _ q g D.p b ι₁ ι₁.injective hb.1 (hN q (hAN hq).1).2 (by rw [r₁]; exact e₁)
  · exact _root_.GlobalTheory.CompanionTheory.Ar.SubFrame.isFrameAt_comp Y.X Z.Ω _ Z.V Z.M.lat _ q g D.q b ι₂ ι₂.injective hb.1 (hN q (hAN hq).1).2 (by rw [r₂]; exact e₂)
  · intro f y v w hy hs hv hw
    have hyA := hcA f y hy
    have h := hcl _ hyA
    have hq := (hN ⟨centre y, h⟩ (hAN hyA).1).2
    exact ⟨_root_.GlobalTheory.CompanionTheory.Ar.LocFrames.EigValue.isEigFrame_value E H D l Xo c O β Y U Z τ σ D.p _ y h v hinj hfr hs
        (_root_.GlobalTheory.CompanionTheory.Ar.SubFrame.isFrameAt_comp Y.X Z.Ω _ Z.V Z.M.lat _ _ g D.p b ι₁ ι₁.injective hb.1 hq (by rw [r₁]; exact e₁))
        (fun i => hval y f h hy (ι₁ i) (v i) (hv i)),
      _root_.GlobalTheory.CompanionTheory.Ar.LocFrames.EigValue.isEigFrame_value E H D l Xo c O β Y U Z _ σ D.q _ y h w hinj hfr hs
        (_root_.GlobalTheory.CompanionTheory.Ar.SubFrame.isFrameAt_comp Y.X Z.Ω _ Z.V Z.M.lat _ _ g D.q b ι₂ ι₂.injective hb.1 hq (by rw [r₂]; exact e₂))
        (fun j => hval y f h hy (ι₂ j) (w j) (hw j))⟩
  · intro f y v w hy h hv hw
    exact ⟨fun i => hval y f h hy (ι₁ i) (v i) (hv i), fun j => hval y f h hy (ι₂ j) (w j) (hw j)⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootLinesFlagDegree
section
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert

theorem rootLine_unitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (r : CMType H × Fin (D.p + D.q)) (q : Cpt 𝔐.ξ) (cc : (k : K) → J k) (b : Fin (labelRk D (HodgeCpt.rootIdx D r).1) → 𝔐.Li) (t : Ω), Fl.RootLines xdeg e → InChart 𝔐.ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) cc q → (∀ j, flagStep Ω b j = flagStep Ω (Fl.b (HodgeCpt.rootIdx D r).1) j) → (𝔐.V (HodgeCpt.rootIdx D r).1).IsFrameAt b q → b (HodgeCpt.rootIdx D r).2 - t • Fl.b (HodgeCpt.rootIdx D r).1 (HodgeCpt.rootIdx D r).2 ∈ flagStep Ω (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2 → unitAt 𝔐.ξ q ((∏ k, y ⟨k, cc k⟩ ^ xdeg r k) * e r / t ^ HodgeCpt.rootSgn D r) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 Fl xdeg e r q cc b t hd hq hF hL hc
  have ht := FlagModel.gr_isGenAt _ b (Fl.b (HodgeCpt.rootIdx D r).1) q hL hF _ t hc
  have hT : (Fl.rootLat r).IsGenAt q (t ^ HodgeCpt.rootSgn D r) := by
    simpa [HodgeCpt.Flag.rootLat] using FlagModel.tens_isGenAt
      (fun _ : Unit => (𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2)
      (fun _ => HodgeCpt.rootSgn D r) q (fun _ => t) fun _ => ht
  obtain ⟨he, h⟩ := hd r
  have h1 := h q (Set.mem_univ _) cc hq
  have hy : (∏ k, y ⟨k, cc k⟩ ^ xdeg r k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k hk => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hq.1 k hk)
  have hW : (Fl.rootLat r).IsGenAt q ((∏ k, y ⟨k, cc k⟩ ^ xdeg r k) * e r) := ⟨mul_ne_zero hy he, h1⟩
  have hw0 := hW.1
  have ht0 := hT.1
  refine ⟨div_ne_zero hw0 ht0, ?_, ?_⟩
  · simpa using FlagModel.zpow_ratio _ q _ _ hT hW 1
  · simpa using FlagModel.zpow_ratio _ q _ _ hW hT 1

end GlobalTheory.CompanionTheory.Ar.OrVert
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_pairing_pullback : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (n : ℕ) (e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ), GenWeil G L ξ n e → FullTorsion G ξ n → ∀ (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → FullTorsion G' ξ' n → ∀ (L' : LB G'.left) (e' : (Over.mk ξ' ⟶ G') → (Over.mk ξ' ⟶ G') → Ω'ˣ), GenWeil G' L' ξ' n e' → ∀ (y : Over.mk ξ ⟶ G) (y' : Over.mk ξ' ⟶ G'), y ^ n = 1 → y' ^ n = 1 → (∀ (g : Over.mk ξ ⟶ G) (g' : Over.mk ξ' ⟶ G'), g ^ n = 1 → g' ^ n = 1 → g'.left ≫ φ = spMap i ≫ g.left → (e' y' g' : Ω') = i (e y g)) → (∀ (g : Over.mk ξ ⟶ G), g ^ n = 1 → ∃ g' : Over.mk ξ' ⟶ G', g' ^ n = 1 ∧ g'.left ≫ φ = spMap i ≫ g.left) → (∀ (g' : Over.mk ξ' ⟶ G'), g' ^ n = 1 → ∃ g : Over.mk ξ ⟶ G, g ^ n = 1 ∧ g'.left ≫ φ = spMap i ≫ g.left) → ∀ (W : G.left.Opens) (s : Γ(G.left, W)),
  (∀ (k : Type) [Field k] [IsAlgClosed k] (τ : Ω →+* k) (xk g : Over.mk (spMap τ ≫ ξ) ⟶ G) (c : kˣ) (h : ⊤ ≤ g.left ⁻¹ᵁ W), xk.left = spMap τ ≫ y.left → g ^ n = 1 → Out.WeilIs G L n xk g (unitOn c) → secVal (B := k) g.left W h s = c) →
  (∀ (k : Type) [Field k] [IsAlgClosed k] (τ : Ω' →+* k) (xk g : Over.mk (spMap τ ≫ ξ') ⟶ G') (c : kˣ) (h : ⊤ ≤ g.left ⁻¹ᵁ (φ ⁻¹ᵁ W)), xk.left = spMap τ ≫ y'.left → g ^ n = 1 → Out.WeilIs G' L' n xk g (unitOn c) → secVal (B := k) g.left (φ ⁻¹ᵁ W) h (φ.app W s) = c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HtTorPull.torsion_clause | exact GlobalTheory.CompanionTheory.Ar.HtTorPull.torsion_clause | (intros; apply GlobalTheory.CompanionTheory.Ar.HtTorPull.torsion_clause <;> assumption)
end

