module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegrality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1427
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnModelDescends
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfGrowthOn
section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree
open scoped ENNReal

namespace GlobalTheory.DegTop

theorem growth_mono (D : ℕ) {s s' : ℕ → ℕ∞} (h : ∀ k, 1 ≤ k → s k ≤ s' k) : growth D s ≤ growth D s' :=
  Filter.limsup_le_limsup ((Filter.eventually_ge_atTop 1).mono fun k hk => ENNReal.div_le_div_right
    (mul_le_mul_right (ENat.toENNReal_le.2 (h k hk)) _) _)

theorem growth_top (D : ℕ) : growth D (fun _ => ⊤) = ⊤ := by
  rw [growth, ← Filter.limsup_const (f := (Filter.atTop : Filter ℕ)) (⊤ : ℝ≥0∞)]
  refine Filter.limsup_congr (Filter.Eventually.of_forall fun k => ?_)
  rw [ENat.toENNReal_top, ENNReal.mul_top (Nat.cast_ne_zero.2 D.factorial_ne_zero)]
  exact ENNReal.top_div_of_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top k))

theorem of_not_finiteDimensional {K V : Type} [Field K] [AddCommGroup V] [Module K V] (h : ¬ FiniteDimensional K V) :
    (∃ v : V, v ≠ 0) ∧ Cardinal.aleph0 ≤ Module.rank K V := by
  refine ⟨?_, not_lt.1 fun h2 => h (Module.rank_lt_aleph0_iff.1 h2)⟩
  by_contra h0
  push Not at h0
  have : Subsingleton V := subsingleton_of_forall_eq 0 h0
  exact h inferInstance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem mem_holSub_iff {Cp : Type} (X : Cp → Data E r) (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X) :
    P ∈ holSub X la ↔ ∀ k, P k ∈ (X k).SS (la k) := by
  refine ⟨fun h => ?_, holCusp_mem_holSub X la⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.1
  | add x y _ _ hx hy => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.1 _ (hx k) _ (hy k)
  | smul a x _ hx => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 a _ (hx k)

theorem eq_zero_of_genVal {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) (h0 : genVal Z f = 0) :
    f = 0 := by
  refine secZ_eq_zero_of_genVal hf.1.1 fun Z' => ?_
  by_cases hZ : Z' = Z
  · rw [hZ, h0]
  · exact evC_eq_zero (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1 hZ hf.2

theorem mul_mem_cuspOn {Z : Comp Xo c} {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2) {f g : Rul Xo c}
    (hf : f ∈ cuspOn U Z G) (hg : g ∈ cuspW Xo c U G') : f * g ∈ cuspOn U Z (G + G') := by
  refine ⟨?_, by rw [mul_comm]; exact mul_mem_suppOn _ hf.2⟩
  have hf' := mem_cuspW.1 hf.1
  rw [mem_cuspW] at hg
  refine mem_cuspW.2 ⟨?_, fun σ hσ => ?_⟩
  · have e : exZ Dw (G + G') = exZ Dw G + exZ Dw G' := funext fun i => exZ_add _ _ _
    rw [e]
    exact mul_mem_secZ hf'.1 hg.1
  · rw [AllWt.rdU_mul, mem_holSub_iff]
    intro k
    rw [modelWt_add (U σ) hG hG' k]
    exact (siegelSpaceAlgebra_holds (E := E) r _ _ _ 0).2.1 _ ((mem_holSub_iff _ _ _).1 (hf'.2 σ hσ) k) _
      ((mem_holSub_iff _ _ _).1 (hg.2 σ hσ) k).1


omit [NumberField E] [IsCMField E] in
theorem even_nsmul {G : WTZ E} (hG : Even G.2) (n : ℕ) : Even (n • G).2 := by
  rw [Prod.smul_snd, nsmul_eq_mul]; exact hG.mul_left n

section

set_option synthInstance.maxHeartbeats 100000

theorem range_pow_le {Z : Comp Xo c} {G : WTZ E} (hG : Even G.2) (n : ℕ) :
    (LinearMap.range (genPoint Z (cuspOn U Z G))) ^ (n + 1) ≤
      (cuspOn U Z ((n + 1) • G)).map (genVal Z).toLinearMap := by
  induction n with
  | zero =>
    rintro _ hy
    rw [zero_add, pow_one] at hy
    obtain ⟨v, rfl⟩ := hy
    exact ⟨v, by simp, rfl⟩
  | succ n ih =>
    rw [pow_succ]
    refine Submodule.mul_le.2 fun a ha b hb => ?_
    obtain ⟨f, hf, rfl⟩ := ih ha
    obtain ⟨v, rfl⟩ := hb
    refine ⟨f * v, ?_, map_mul (genVal Z) _ _⟩
    rw [succ_nsmul]
    exact mul_mem_cuspOn (even_nsmul hG _) hG hf v.2.1

theorem hilb_le {Z : Comp Xo c} {G : WTZ E} (hG : Even G.2) {τ : ℕ} (hτ : 1 ≤ τ) :
    hilb (genPoint Z (cuspOn U Z G)) τ ≤ Cardinal.toENat (Module.rank c.F (cuspOn U Z (τ • G))) := by
  obtain ⟨n, rfl⟩ : ∃ n, τ = n + 1 := ⟨τ - 1, by omega⟩
  exact OrderHomClass.mono Cardinal.toENat ((Submodule.rank_mono (range_pow_le hG n)).trans (rank_map_le _ _))

theorem rank_map_mul {Z : Comp Xo c} {G : WTZ E} {θ : Rul Xo c} (hθ : genVal Z θ ≠ 0) :
    Module.rank c.F ((cuspOn U Z G).map ((genVal Z).toLinearMap ∘ₗ LinearMap.mulLeft c.F θ)) =
      Module.rank c.F (cuspOn U Z G) := by
  have hi : Function.Injective (((genVal Z).toLinearMap ∘ₗ LinearMap.mulLeft c.F θ) ∘ₗ (cuspOn U Z G).subtype) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    have h1 : genVal Z (θ * f) = 0 := hf
    rw [map_mul] at h1
    exact Subtype.ext (eq_zero_of_genVal f.2 ((mul_eq_zero.1 h1).resolve_left hθ))
  rw [← rank_range_of_injective _ hi, LinearMap.range_comp, Submodule.range_subtype]

theorem finiteDimensional_of_growthOn {Z : Comp Xo c} {G : WTZ E} (hG : Even G.2) (h : growthOn U Z G ≠ ⊤) :
    FiniteDimensional c.F (cuspOn U Z G) := by
  by_contra hfd
  obtain ⟨⟨v, hv⟩, hr⟩ := of_not_finiteDimensional hfd
  have hv' : genVal Z (v : Rul Xo c) ≠ 0 := fun h0 => hv (Subtype.ext (eq_zero_of_genVal v.2 h0))
  have key : ∀ n : ℕ, ∀ f ∈ cuspOn U Z G, (v : Rul Xo c) ^ n * f ∈ cuspOn U Z ((n + 1) • G) := fun n f hf => by
    induction n with
    | zero => simpa using hf
    | succ n ih =>
      rw [succ_nsmul, pow_succ, mul_right_comm]
      exact mul_mem_cuspOn (even_nsmul hG _) hG ih v.2.1
  refine h (top_le_iff.1 ((growth_top (dimFlag Dw)).symm.trans_le (growth_mono _ fun k hk => ?_)))
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have h1 : Module.rank c.F (cuspOn U Z G) ≤ Module.rank c.F (cuspOn U Z ((n + 1) • G)) := by
    rw [← rank_map_mul (U := U) (G := G) (θ := (v : Rul Xo c) ^ n) (by rw [map_pow]; exact pow_ne_zero _ hv')]
    refine (Submodule.rank_mono ?_).trans (rank_map_le (genVal Z).toLinearMap _)
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨_, key n f hf, rfl⟩
  rw [top_le_iff, Cardinal.toENat_eq_top]
  exact hr.trans h1

theorem topDeg_nonneg (Z : Comp Xo c) {u : Weight Dw} (hu : ∀ τ, StrictAnti (u τ)) : 0 ≤ topDeg U Z u :=
  mul_nonneg (vZero_nonneg U Z) (Int.cast_pos.2 (vdm_pos hu)).le

theorem growth_mul_eq (hP : Proport U) (Z : Comp Xo c) {u : Weight Dw} (hu : ∀ τ, StrictAnti (u τ)) {a : ℕ}
    (ha : 1 ≤ a) : growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k) • wtOf Dw u 0)))) =
      ENNReal.ofReal ((a : ℝ) ^ dimFlag Dw * topDeg U Z u) := by
  have h1 : ∀ τ, StrictAnti ((a • u) τ) := fun τ i j hij => by
    have := hu τ hij
    simp only [Pi.smul_apply, nsmul_eq_mul]
    exact mul_lt_mul_of_pos_left this (by exact_mod_cast ha)
  have h2 := hP Z (a • u) h1
  have h3 : wtOf Dw (a • u) 0 = a • wtOf Dw u 0 := by rw [nsmul_wtOf, smul_zero]
  have h4 : topDeg U Z (a • u) = (a : ℝ) ^ dimFlag Dw * topDeg U Z u := by
    rw [topDeg, topDeg, ← Nat.cast_smul_eq_nsmul ℤ a u, vdm_smul, dimFlag]
    push_cast; ring
  rw [← h4, ← h2, growthOn, h3]
  exact congrArg _ (funext fun k => by rw [mul_nsmul])

theorem finiteDimensional_cuspOn (hP : Proport U) (Z : Comp Xo c) {u : Weight Dw} (hu : ∀ τ, StrictAnti (u τ)) :
    FiniteDimensional c.F (cuspOn U Z (wtOf Dw u 0)) :=
  finiteDimensional_of_growthOn (even_wtOf u 0) (by rw [hP Z u hu]; exact ENNReal.ofReal_ne_top)

theorem growth_hilb_le (hP : Proport U) (Z : Comp Xo c) {u : Weight Dw} (hu : ∀ τ, StrictAnti (u τ)) {a : ℕ}
    (ha : 1 ≤ a) : growth (dimFlag Dw) (fun k => hilb (genPoint Z (cuspOn U Z (wtOf Dw u 0))) (a * k)) ≤
      ENNReal.ofReal ((a : ℝ) ^ dimFlag Dw * topDeg U Z u) :=
  (growth_mono _ fun _ hk => hilb_le (even_wtOf u 0) (Nat.mul_pos ha hk)).trans_eq (growth_mul_eq hP Z hu ha)

theorem compDeg_le (hP : Proport U) (Z : Comp Xo c) {u : Weight Dw} (hu : ∀ τ, StrictAnti (u τ)) :
    (compDeg U Z (wtOf Dw u 0) : ℝ) ≤ topDeg U Z u := by
  rcases (compDeg U Z (wtOf Dw u 0)).eq_zero_or_pos with h0 | h0
  · rw [h0, Nat.cast_zero]; exact topDeg_nonneg Z hu
  · have := finiteDimensional_cuspOn hP Z hu
    have h1 := _root_.GlobalTheory.ConeDeg.degree_growth_integral.1 c.F _ _ _ _ 1 le_rfl _ ((imageDeg_pos_iff _ _).1 h0)
    have h2 := growth_hilb_le hP Z hu le_rfl
    rw [h1, Nat.cast_one, Nat.cast_one, one_pow, one_pow, one_mul, one_mul, ← ENNReal.ofReal_natCast] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (topDeg_nonneg Z hu)).1 h2

end

def normFac {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ) (G : WTZ E) (z : Σ k, Frame (U.X k).Ψ r) : ℝ :=
  lieFacZ Dw x G * (U.X z.1).nfac (modelWt U G z.1) z.2

section Fac

variable {σ : c.F →+* ℂ} (U₁ : Unf Xo c σ r) (x)

theorem homN_eq (G : WTZ E) (f : Rul Xo c) (z : Σ k, Frame (U₁.X k).Ψ r) :
    homN U₁ x G f z = normFac U₁ x G z * ‖rdU U₁ f z.1 z.2‖ := by
  show _ * (‖rdU U₁ f z.1 z.2‖ * (U₁.X z.1).nfac (modelWt U₁ G z.1) z.2) = _
  rw [normFac]; ring

theorem normFac_pos (G : WTZ E) {z : Σ k, Frame (U₁.X k).Ψ r} (hz : z.2 ∈ (U₁.X z.1).dom) : 0 < normFac U₁ x G z := by
  have hd : ∀ τ i, dmin (U₁.X z.1).Gm z.2 τ i ≠ 0 := fun τ i h0 => by
    have := (hz τ).2 i
    rw [h0] at this; simp at this
  exact mul_pos (lieFacZ_pos _ _) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _))) _)

theorem normFac_add {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2) {z : Σ k, Frame (U₁.X k).Ψ r}
    (hz : z.2 ∈ (U₁.X z.1).dom) : normFac U₁ x (G + G') z = normFac U₁ x G z * normFac U₁ x G' z := by
  have hd : ∀ τ i, dmin (U₁.X z.1).Gm z.2 τ i ≠ 0 := fun τ i h0 => by
    have := (hz τ).2 i
    rw [h0] at this; simp at this
  have key : ∀ la la' : Wt (U₁.X z.1).Ψ r, (U₁.X z.1).nfac (la + la') z.2 =
      (U₁.X z.1).nfac la z.2 * (U₁.X z.1).nfac la' z.2 := fun la la' => by
    unfold Data.nfac
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_add (norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _)))]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [normFac, normFac, normFac, modelWt_add U₁ hG hG', key, lieFacZ_add]
  ring

theorem normFac_nsmul {G : WTZ E} (hG : Even G.2) {z : Σ k, Frame (U₁.X k).Ψ r} (hz : z.2 ∈ (U₁.X z.1).dom) (n : ℕ) :
    normFac U₁ x (n • G) z = normFac U₁ x G z ^ n := by
  induction n with
  | zero =>
    have h := normFac_add x U₁ (G := 0) (G' := 0) Even.zero Even.zero hz
    rw [add_zero] at h
    rw [zero_nsmul, pow_zero]
    exact (mul_left_cancel₀ (normFac_pos x U₁ 0 hz).ne' (h.symm.trans (mul_one _).symm))
  | succ n ih => rw [succ_nsmul, normFac_add x U₁ (even_nsmul hG n) hG hz, ih, pow_succ]

end Fac

end GlobalTheory.DegTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankTorusExtensionCharactersLeRelDim
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem finrank_torusExtension_le : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (E : TorusExtension G) (g : ℕ), SmoothOfRelativeDimension g G.hom → (letI := E.addCommGroup; Module.finrank ℤ E.X) ≤ g := by
  intro k _ G _ E g hG
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  letI := E.grpB
  haveI : IsSeparated E.B.hom := E.isAbelian.proper.toIsSeparated
  have hη : IsClosedImmersion (η : 𝟙_ (Over (Sp k)) ⟶ E.B).left := isClosedImmersion_of_comp_eq_id (Y := Sp k) E.B.hom _ (Over.w _)
  have hpb : IsPullback E.i.left (toUnit (splitTorus (Sp k) E.X)).left E.q.left (η : 𝟙_ (Over (Sp k)) ⟶ E.B).left :=
    E.isKernel.map (Over.forget _)
  have hi : IsClosedImmersion E.i.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip hη
  have pt : Sp k := Classical.choice inferInstance
  have hne : Nonempty (splitTorus (Sp k) E.X).left :=
    ⟨(η : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) E.X).left ((toUnit (Over.mk (𝟙 (Sp k)))).left pt)⟩
  exact relDim_le_of_isClosedImmersion k _ G E.i hi hne g _ hG (ReciprocityTheory.ChartRestriction.G.H1.torus_dim (Sp k) E.X)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumLinePlacewiseSignatures
section
noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD GlobalTheory.VacLn

namespace GlobalTheory.HoweD

theorem vacD_ne_zero {ι : Type} [Fintype ι] {P Q R S : ι → ℕ} :
    (PiTensorProduct.tprod ℂ fun w : ι => (1 : Pol (P w) (Q w) (R w) (S w))) ≠ 0 := by
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap
    fun w => (MvPolynomial.aeval (R := ℂ) (S₁ := ℂ) (σ := Ln (P w) (Q w) (R w) (S w)) fun _ => 0).toLinearMap)) h
  simp at this

theorem vacLineD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ → ∀ (f₀ : SInf F κ) (ε : InfinitePlace F → ℤˣ),
    (∀ u u' : Matrix α β (AE F E), At (evI F) u → At (evI F) u' → ∀ c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
      (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * (C w)ᵀ) →
      ∀ f f' : SInf F κ, SD (fun t => d.rho ψ (realAd F t • u)) f₀ f → SD (fun t => d.rho ψ (realAd F t • u')) f₀ f' →
        f' = Complex.I • f) →
    ∃ z : ℂ, f₀ = z • Φ (PiTensorProduct.tprod ℂ fun _ => 1) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hStd hFr hΦ f₀ ε hyp
  have hD : DerEx := _root_.GlobalTheory.HeisDer.derEx
  obtain ⟨D, hDu⟩ := hD F E σ α β κ ψ JA JB d hStd
  obtain ⟨J, e, e', hJ, he, hJe, he1, he2, hy⟩ := GlobalTheory.T.exists_archimedeanPhaseSpace_complexStructure_signatures F E σ α β κ P Q R S τ JA JB d a b A C ε hCM hFr
  have hDx : ∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x = fderiv ℝ f x (coord d u).1 -
      2 * Real.pi * Complex.I * (trPair F κ x (coord d u).2 : ℝ) * f x := fun u hu f x => (hDu u hu f).2 x
  have hf : ∀ y x, fderiv ℝ f₀ x (J (y - (2 : ℝ) • e y)).1 - 2 * Real.pi * Complex.I *
      (trPair F κ x (J (y - (2 : ℝ) • e y)).2 : ℝ) * f₀ x =
      Complex.I * (fderiv ℝ f₀ x y.1 - 2 * Real.pi * Complex.I * (trPair F κ x y.2 : ℝ) * f₀ x) := by
    intro y x
    obtain ⟨u, u', u₁, c, hu, hu', -, hc, hc', -, h0, h', -⟩ := hy y
    have key := hyp u u' hu hu' c hc hc' (D u f₀) (D u' f₀) (hDu u hu f₀).1 (hDu u' hu' f₀).1
    have := congrArg (fun g : SInf F κ => g x) key
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at this
    rw [hDx u hu, hDx u' hu', h0, h'] at this
    exact this
  set g₀ := Φ (PiTensorProduct.tprod ℂ fun _ => 1) with hg₀
  have hg0 : g₀ ≠ 0 := fun h => vacD_ne_zero (hΦ.1 (h.trans (map_zero Φ).symm))
  have hg : ∀ y x, fderiv ℝ g₀ x (J y).1 - 2 * Real.pi * Complex.I * (trPair F κ x (J y).2 : ℝ) * g₀ x =
      Complex.I * (fderiv ℝ g₀ x y.1 - 2 * Real.pi * Complex.I * (trPair F κ x y.2 : ℝ) * g₀ x) := by
    intro y x
    obtain ⟨u, -, u₁, c, hu, -, hu₁, hc, -, hc₁, h0, -, h1⟩ := hy y
    have e0 := _root_.GlobalTheory.SDUnique.sd_unique (hDu u hu g₀).1 (hΦ.2 u hu c hc _)
    have e1 := _root_.GlobalTheory.SDUnique.sd_unique (hDu u₁ hu₁ g₀).1 (hΦ.2 u₁ hu₁ _ hc₁ _)
    rw [GlobalTheory.T.fock_vacuum_pi_tensor_heisenberg_factorwise_signature, map_smul, ← e0] at e1
    have := congrArg (fun g : SInf F κ => g x) e1
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at this
    rw [hDx u hu, hDx u₁ hu₁, h0, h1] at this
    exact this
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.VacCore.schwartz_vacuum_eq_smul (trPair F κ) (fun y h => _root_.GlobalTheory.VacLn.trPair_nondeg y h) J e e' hJ he hJe he1 he2 f₀ g₀ hg0 hg hf
  exact ⟨z, hz⟩

end GlobalTheory.HoweD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallySmoothStalkUnitSmoothGroupScheme
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem stalk_formallySmooth_of_smooth : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → π.FormallySmooth := by
  intro S G _ hG s π ε m h
  have hstr := h.str
  clear h
  revert π hstr
  have hs : G.hom.base (unitSec G s) = s := by
    rw [← Scheme.Hom.comp_apply, unitSec, sec_hom]
    rfl
  generalize unitSec G s = p at hs ⊢
  subst hs
  intro π hstr
  have e : Spec.map (CommRingCat.ofHom π) = Spec.map (G.hom.stalkMap p) :=
    (cancel_mono (S.fromSpecStalk (G.hom.base p))).1 (by
      rw [hstr, Scheme.SpecMap_stalkMap_fromSpecStalk])
  have e' : π = (G.hom.stalkMap p).hom := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  rw [e']
  exact Scheme.Hom.mem_smoothLocus.mp (G.hom.smoothLocus_eq_top.ge (Set.mem_univ p))

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentIntegralStructure
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemilinTwist

variable {W K' : Type} [CommRing W] [CommRing K'] [Algebra W K']

noncomputable def restrictFun (σ : K' →+* K')
    (h : ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) (x : W) : W :=
  Classical.choose (h x)

theorem algebraMap_restrictFun (σ : K' →+* K')
    (h : ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) (x : W) :
    algebraMap W K' (restrictFun σ h x) = σ (algebraMap W K' x) :=
  (Classical.choose_spec (h x)).symm

noncomputable def restrictHom (hinj : Function.Injective (algebraMap W K')) (σ : K' →+* K')
    (h : ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) : W →+* W where
  toFun := restrictFun σ h
  map_one' := hinj (by simp only [algebraMap_restrictFun, map_one])
  map_mul' x y := hinj (by simp only [algebraMap_restrictFun, map_mul])
  map_zero' := hinj (by simp only [algebraMap_restrictFun, map_zero])
  map_add' x y := hinj (by simp only [algebraMap_restrictFun, map_add (f := _)])

theorem algebraMap_restrictHom (hinj : Function.Injective (algebraMap W K')) (σ : K' →+* K')
    (h : ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) (x : W) :
    σ (algebraMap W K' x) = algebraMap W K' (restrictHom hinj σ h x) :=
  (algebraMap_restrictFun σ h x).symm

theorem exists_semilinear_twist : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'] (σ : K' ≃ₐ[K] K'), (∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → ∃ (τ : W →+* W) (φ : G.left ⟶ G.left), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) ∧ φ ≫ G.hom = G.hom ≫ spMap τ ∧ pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = (e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm) ≫ e.inv.left) ≫ pullback.fst G.hom (spMap (algebraMap W K')) := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ A _ _ hA G _ hG e he
  have hinj : Function.Injective (algebraMap W K') := IsFractionRing.injective W K'
  let τ : W →+* W := restrictHom hinj (σ : K' →+* K') hσ
  have hτ : ∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x) :=
    algebraMap_restrictHom hinj (σ : K' →+* K') hσ
  have hsq : spMap (σ : K' →+* K') ≫ spMap (algebraMap W K') = spMap (algebraMap W K') ≫ spMap τ := by
    rw [← Spec.map_comp, ← Spec.map_comp]; congr 1; ext x; simpa using hτ x
  have hK : spMap (algebraMap K K') = spMap (σ : K' →+* K') ≫ spMap (algebraMap K K') := by
    rw [← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm
  let s := pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _)
    (spMap (σ : K' →+* K')) (𝟙 _) (by simp)
    (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm)
  have hs1 : s ≫ pullback.fst A.hom (spMap (algebraMap K K')) = pullback.fst A.hom (spMap (algebraMap K K')) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hs2 : s ≫ pullback.snd A.hom (spMap (algebraMap K K')) =
      pullback.snd A.hom (spMap (algebraMap K K')) ≫ spMap (σ : K' →+* K') :=
    pullback.lift_snd _ _ _
  have hA1 := isGrpPullback_pullback A (spMap (algebraMap K K'))
  have hAs : IsGrpPullback ((Over.pullback (spMap (algebraMap K K'))).obj A)
      ((Over.pullback (spMap (algebraMap K K'))).obj A) (spMap (σ : K' →+* K')) s :=
    IsGrpPullback.cancel hA1 (hA1.congr hK hs1.symm) hs2
  haveI : IsMonHom e.hom := he
  have he1 := isGrpPullback_of_iso e
  haveI : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have he2 := isGrpPullback_of_iso e.symm
  have hG1 := isGrpPullback_pullback G (spMap (algebraMap W K'))
  have h1 := (((he1.comp hAs).comp he2).comp hG1).congr
    (by rw [Category.id_comp, Category.comp_id, hsq]) rfl
  have hGτ := isGrpPullback_pullback G (spMap τ)
  have hGτK := isGrpPullback_pullback ((Over.pullback (spMap τ)).obj G) (spMap (algebraMap W K'))
  obtain ⟨e', he', he'φ⟩ := grpPullback_iso h1 (hGτK.comp hGτ)
  obtain ⟨F, hF, -⟩ := GlobalTheory.AbHomExtDvr.existsUnique_hom_extension_abelian_dvr W K' G
    ((Over.pullback (spMap τ)).obj G) hG (isAbelianScheme_pullback_obj _ G hG) e'.hom he'
  refine ⟨τ, F.left ≫ pullback.fst G.hom (spMap τ), hτ, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ spMap τ) (Over.w F)
  · have hFl : ((Over.pullback (spMap (algebraMap W K'))).map F).left ≫
        pullback.fst ((Over.pullback (spMap τ)).obj G).hom (spMap (algebraMap W K')) =
        pullback.fst G.hom (spMap (algebraMap W K')) ≫ F.left := pullback.lift_fst _ _ _
    rw [hF] at hFl
    rw [← Category.assoc, ← hFl, Category.assoc, he'φ]
    simp only [Category.assoc, Iso.symm_hom]
    rfl

end GlobalTheory.SemilinTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayDescentRangeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_away_lift_descent : ∀ (k : Type) [Field k] (P : Polynomial k) (T : Finset (Localization.Away P)), ∃ F : Finset k, ∀ (R : Subring k), (F : Set k) ⊆ R → ∀ (P₁ : Polynomial R) (h : IsUnit (((algebraMap (Polynomial k) (Localization.Away P)).comp (Polynomial.mapRingHom R.subtype)) P₁)), P₁.map R.subtype = P → ∀ t ∈ T, t ∈ (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ h).range := by
  first | exact @GlobalTheory.localization_away_descent_range | exact GlobalTheory.localization_away_descent_range | (intros; apply GlobalTheory.localization_away_descent_range <;> assumption)
end

