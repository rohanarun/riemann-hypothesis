module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.OfBeforeProjector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1276
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneOfIsIntegralInt
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CongW.PlaceEmb

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

theorem norm_le_one_of_isIntegral_int {x : PadicAlgCl p} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := PadicAlgCl p)).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl p))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_int_le (σ : K →+* PadicAlgCl p) (y : 𝓞 K) : ‖σ (y : K)‖ ≤ 1 :=
  norm_le_one_of_isIntegral_int (by
    convert map_isIntegral_int σ (RingOfIntegers.isIntegral_coe y)
    exact Subsingleton.elim _ _)

def smallIdeal (σ : K →+* PadicAlgCl p) : Ideal (𝓞 K) where
  carrier := {y | ‖σ (y : K)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have : σ ((a + b : 𝓞 K) : K) = σ (a : K) + σ (b : K) := by simp
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have : σ ((c • a : 𝓞 K) : K) = σ (c : K) * σ (a : K) := by simp
    rw [this, norm_mul]
    have h1 := norm_int_le σ c
    nlinarith [norm_nonneg (σ (c : K)), norm_nonneg (σ (a : K))]

theorem mem_smallIdeal (σ : K →+* PadicAlgCl p) (y : 𝓞 K) : y ∈ smallIdeal σ ↔ ‖σ (y : K)‖ < 1 := Iff.rfl

theorem smallIdeal_isPrime (σ : K →+* PadicAlgCl p) : (smallIdeal σ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · intro a b hab
    rw [mem_smallIdeal] at hab
    rw [mem_smallIdeal, mem_smallIdeal]
    have : σ ((a * b : 𝓞 K) : K) = σ (a : K) * σ (b : K) := by simp
    rw [this, norm_mul] at hab
    by_contra hcon
    push_neg at hcon
    nlinarith [hcon.1, hcon.2]

theorem dvd_of_natCast_mem {R : Type*} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) {q M : ℕ} (hq : q.Prime)
    (h1 : (q : R) ∈ I) (h2 : (M : R) ∈ I) : q ∣ M := by
  by_contra hnd
  have hc : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).2 hnd
  obtain ⟨u, v, huv⟩ : IsCoprime (q : R) (M : R) := Nat.Coprime.cast hc
  exact hI ((Ideal.eq_top_iff_one _).2
    (huv ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem norm_p_lt_one : ‖(p : PadicAlgCl p)‖ < 1 := by
  have h : ‖algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p])‖ = ‖(p : ℚ_[p])‖ := norm_algebraMap' _ _
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h, map_natCast] at h2
  exact h2

theorem exists_embedding (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) :
    ∃ σ : K →+* PadicAlgCl p, w.asIdeal = smallIdeal σ := by
  by_contra hcon
  push_neg at hcon
  have hnle : ∀ σ : K →ₐ[ℚ] PadicAlgCl p, ¬ w.asIdeal ≤ smallIdeal (σ : K →+* PadicAlgCl p) := by
    intro σ hle
    exact hcon (σ : K →+* PadicAlgCl p) (w.isMaximal.eq_of_le (smallIdeal_isPrime _).ne_top hle)
  have σ0 : K →ₐ[ℚ] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hav : ¬ ((w.asIdeal : Set (𝓞 K)) ⊆
      ⋃ σ ∈ ((Finset.univ : Finset (K →ₐ[ℚ] PadicAlgCl p)) : Set (K →ₐ[ℚ] PadicAlgCl p)),
        (smallIdeal (σ : K →+* PadicAlgCl p) : Set (𝓞 K))) := by
    rw [Ideal.subset_union_prime σ0 σ0 (fun σ _ _ _ => smallIdeal_isPrime _)]
    rintro ⟨σ, -, hle⟩
    exact hnle σ hle
  obtain ⟨x, hxw, hx⟩ := Set.not_subset.1 hav
  have hxσ : ∀ σ : K →ₐ[ℚ] PadicAlgCl p, 1 ≤ ‖σ (x : K)‖ := by
    intro σ
    by_contra hlt
    exact hx (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ σ)) (not_le.1 hlt))
  have hN : ((Algebra.norm ℤ x).natAbs : 𝓞 K) ∈ w.asIdeal := by
    have h1 := Ideal.absNorm_mem (Ideal.span {x})
    rw [Ideal.absNorm_span_singleton] at h1
    exact (Ideal.span_singleton_le_iff_mem _).2 hxw h1
  have hpN : p ∣ (Algebra.norm ℤ x).natAbs :=
    dvd_of_natCast_mem w.asIdeal w.isPrime.ne_top Fact.out hw hN
  obtain ⟨m, hm⟩ : (p : ℤ) ∣ Algebra.norm ℤ x := Int.natCast_dvd.2 hpN
  have hprod : ((Algebra.norm ℤ x : ℤ) : PadicAlgCl p) = ∏ σ : K →ₐ[ℚ] PadicAlgCl p, σ (x : K) := by
    rw [← Algebra.norm_eq_prod_embeddings ℚ (PadicAlgCl p) (x : K), ← Algebra.coe_norm_int x]
    simp
  have h1 : 1 ≤ ‖((Algebra.norm ℤ x : ℤ) : PadicAlgCl p)‖ := by
    rw [hprod, norm_prod]
    exact Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
      le_rfl fun σ _ => hxσ σ
  have h2 : ((Algebra.norm ℤ x : ℤ) : PadicAlgCl p) = (p : PadicAlgCl p) * ((m : ℤ) : PadicAlgCl p) := by
    rw [hm]; push_cast; ring
  have h3 : ‖((m : ℤ) : PadicAlgCl p)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ m
  rw [h2, norm_mul] at h1
  have h4 := norm_p_lt_one (p := p)
  nlinarith [norm_nonneg (p : PadicAlgCl p), norm_nonneg ((m : ℤ) : PadicAlgCl p)]

end GlobalTheory.CongW.PlaceEmb

namespace GlobalTheory.CongW

open Formalism.ConjugateSelfDual

end GlobalTheory.CongW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPairRealPointsSmulAdelicVacuumDetPow
section
noncomputable section

open NumberField MeasureTheory
open scoped Classical ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDict

theorem vacuum_smul_realA : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
    (∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))) →
    ∀ g ∈ GinfC X.A, X.om (g, 1) X.vac = (∏ τ, (compAt X.θ τ (Formalism.L2.Theta.mt X.A g)).det ^ P.n τ) • X.vac := by
  intro D cc δ t0 Q P X hX hb g hg
  have hW := hX.2.weil
  have hθ := hX.2.inf
  obtain ⟨η, e1, e2, e3, e4⟩ := _root_.GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  have cart : ∀ (V : HSp D), V.gram = 1 → ∀ τ, IsCartanInv (gramAt D V τ) 1 := fun V hV τ => by
    have : gramAt D V τ = 1 := by rw [gramAt, hV, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [this]
    exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  have hmt1 : Formalism.L2.Theta.mt X.B 1 = 1 := by simp [Formalism.L2.Theta.mt]
  have hc1 : ∀ τ, compAt X.θ τ (Formalism.L2.Theta.mt X.B 1) = 1 := fun τ => by
    rw [hmt1, compAt, Matrix.map_one _ (by simp) (by simp)]
  have hA0 : ∀ τ, (gramAt D X.A τ).det ≠ 0 := fun τ => by
    rw [gramAt, hX.1.gramA, Matrix.map_one _ (map_zero _) (map_one _), Matrix.det_one]; exact one_ne_zero
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ X.A hA0 g hg
  have hy : IsDetRoot X.B 1 1 := by simp [IsDetRoot]
  rw [_root_.GlobalTheory.WeilVacChar.vacuum_character D X.ψ hW.std X.A X.B X.θ hθ X.χA X.χB X.om η ⟨e1, e4, e3, e2⟩ hW (fun _ => 1) (fun _ => 1)
    (cart X.A hX.1.gramA) (cart X.B hX.1.gramB) g hg 1 (one_mem _) (fun τ => by rw [one_mul, mul_one])
    (fun τ => by rw [one_mul, mul_one]) x 1 hx hy X.vac hX.2.vac_theta hX.2.vac_fock]
  congr 1
  let c : D.what₂.Tau → ℤ := fun τ => -((P.n τ : ℤ) + P.d)
  have hν : ∀ τ, HasInfExp D (X.χB * (η ^ X.B.rank)⁻¹) τ ((c τ : ℤ) : ℚ) := by
    intro τ
    have := GlobalTheory.VacuumCharacter.hasInfExp_twist (hb τ) (e2 τ) X.B.rank
    convert this using 1
    rw [X.rkB]
    simp only [c]
    push_cast
    ring
  rw [Circle.coe_mul, Circle.coe_inv, hxv _ c hν, map_one, Circle.coe_one, mul_one, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨p, hp, hd⟩ := GlobalTheory.VacuumCharacter.detPlus_one (n := X.A.rank) (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)
    (by simp)
  obtain ⟨d1, -⟩ := hd (compAt X.θ τ (Formalism.L2.Theta.mt X.A g⁻¹)) (compAt X.θ τ (Formalism.L2.Theta.mt X.B 1))
    (by rw [one_mul, mul_one])
  have hpd : p = P.d := by
    have : (p : ℂ) = X.B.rank := by
      rw [Matrix.trace_one, Fintype.card_fin] at hp
      linear_combination -hp / 2
    exact_mod_cast this.trans (congrArg (Nat.cast) X.rkB)
  have e1' : ((1 / 2 : ℂ) • (1 + 1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ) * 1 + (1 / 2 : ℂ) • (1 - 1)) = 1 := by
    rw [mul_one]; module
  have inv : (compAt X.θ τ (Formalism.L2.Theta.mt X.A g)).det * (compAt X.θ τ (Formalism.L2.Theta.mt X.A g⁻¹)).det = 1 := by
    rw [GlobalTheory.VacuumCharacter.det_compAt, GlobalTheory.VacuumCharacter.det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.det_one, map_one, map_one]
  have g0 := left_ne_zero_of_mul_eq_one inv
  rw [d1, hc1, e1', Matrix.det_one, one_pow, one_mul, hpd, eq_inv_of_mul_eq_one_right inv]
  simp only [c]
  rw [zpow_neg, inv_inv, zpow_add₀ g0, zpow_natCast, zpow_natCast, inv_pow]
  field_simp

end GlobalTheory.NormDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedMatrixIntegralCompLinearEquivDet
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open MeasureTheory

theorem GlobalTheory.LeviDesc.hint_comp_linear : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) (L : Matrix (Fin a) (Fin b) (w.adicCompletion E) →ₗ[w.adicCompletion E] Matrix (Fin a) (Fin b) (w.adicCompletion E)) (φ : Matrix (Fin a) (Fin b) (w.adicCompletion E) → ℂ), LinearMap.det L ≠ 0 → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (x + y) = φ x) → HasCompactSupport φ → hint (intMat a b w) (fun X => φ (L (Multiplicative.toAdd X))) = (absHalf w (LinearMap.det L) ^ 2)⁻¹ * hint (intMat a b w) (fun X => φ (Multiplicative.toAdd X)) := by
  intro E _ _ w a b L φ hL hU hc
  obtain ⟨Λ, hΛo, hΛc, hΛ⟩ := _root_.GlobalTheory.IntMatOpen.intMat_open_compact E w a b
  obtain ⟨hU', hc', hlc⟩ := _root_.GlobalTheory.LeviDesc.comp_linearAut_smooth_compact E w a b L φ hL hU hc
  letI : MeasurableSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := ⟨rfl⟩
  let μ : Measure (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  rw [hΛ, _root_.GlobalTheory.HaarSum.hint_eq_integral _ μ hμ Λ hΛo hΛc _ hU' hc', _root_.GlobalTheory.HaarSum.hint_eq_integral _ μ hμ Λ hΛo hΛc _ hU hc,
    _root_.GlobalTheory.DetScale.integral_comp_matrix _ a b L hL φ μ hμ, _root_.GlobalTheory.ModAbs.haar_eq_absHalf_sq E w _ hL]
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open _root_.CategoryTheory.Limits (pullback)
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.PPAS

variable {S S' : Scheme.{0}}

theorem one_comp_of_isGrpPullback {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) :
    (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h A'))
  let g : Over.mk (A'.hom ≫ f) ⟶ A := Over.homMk φ h.1.w
  have e2 : g ≫ (1 : A ⟶ A) = 1 := by simp
  have e3 := congrArg (fun z : Over.mk (A'.hom ≫ f) ⟶ A => z.left) e2
  simp only [Over.comp_left] at e3
  rw [← e3] at e
  exact e

end GlobalTheory.PPAS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRow0OfRowsSmul
section
noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.OneMapBase

open _root_.Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Scale

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

end Scale

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m)

theorem oneMapRow0_of_rows (cc : (T.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ph : ℂ)
    (hpins : OMPins T R κ v₀ O i)
    (hequiv : (O i).EquivAt (κ i) cc)
    (hid : OneMapRow (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (Wc D i)
      (unfBC (O i).hle (T.U ((i : ℕ) + 1)) (inC (O i).c')) (O i).dict (O i).mu (xiR D) (wtA (κ i))
      (actLev (O i).c' (O i).lev2) (O i).dδ (O i).Cl' (O i).w (O i).La (O i).Nc (O i).gam (O i).vol (O i).ep (O i).io
      (O i).thAd (O i).Plc D.what₂.embLL.toRatAlgHom.fieldRange
      (cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank) cc ph)
    (hrat : (O i).PhRat (κ i) (v₀ i (sg0 D A)) cc ph) :
    OneMapRow0 T R κ v₀ O i :=
  ⟨cc, ph, hequiv, ⟨hpins.1.ge, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ (O i).hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ (O i).hle _ _ hpins.2.act.1).2, hid⟩, hrat⟩

end GlobalTheory.OneMapBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsCompatible
section
noncomputable section

namespace GlobalTheory.PhRatCommon

section Lemmas

open NumberField
open scoped TensorProduct

open _root_.Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AdTh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ}

theorem rdU_of_isBC (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) {m : ℕ} {f' : Rul Xo c'} {as : Fin m → c'.F}
    {fs : Fin m → Rul Xo c} (h : IsBC hle f' as fs) (k : (U (σ'.comp (incF c c' hle))).Comp)
    (x : Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) :
    rdU (unfBC hle U σ') f' k x = ∑ j, σ' (as j) * rdU (U (σ'.comp (incF c c' hle))) (fs j) k x := by
  by_cases hx : x ∈ ((U (σ'.comp (incF c c' hle))).X k).dom
  · letI : Algebra c.F (CAt σ') := (σ'.comp (incF c c' hle)).toAlgebra
    have e := h (CAt σ') (fun _ => rfl) ((unfBC hle U σ').un k ⟨x, hx⟩)
    have e1 : rdU (unfBC hle U σ') f' k x = toC (evR Xo c' f' ((unfBC hle U σ').un k ⟨x, hx⟩)) := dif_pos hx
    rw [e1, e]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e2 : rdU (U (σ'.comp (incF c c' hle))) (fs j) k x =
      toC (evR Xo c (fs j) ((U (σ'.comp (incF c c' hle))).un k ⟨x, hx⟩)) := dif_pos hx
    rw [e2]
    rfl
  · have e1 : rdU (unfBC hle U σ') f' k x = 0 := dif_neg hx
    rw [e1]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    have e2 : rdU (U (σ'.comp (incF c c' hle))) (fs j) k x = 0 := dif_neg hx
    rw [e2, mul_zero]

theorem exists_rdU_eq_sum (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (f' : Rul Xo c') (hf : f' ∈ cusp Xo c' (unfBC hle U) a n) :
    ∃ (m : ℕ) (b : Fin m → c'.F) (fs : Fin m → cusp Xo c U a n), ∀ k x,
      rdU (unfBC hle U σ') f' k x = ∑ j, σ' (b j) * rdU (U (σ'.comp (incF c c' hle))) (fs j : Rul Xo c) k x := by
  obtain ⟨m, b, fs, hfs, hbc⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC E H Dw l Xo c c' hle).2 r U a n f' hf
  exact ⟨m, b, fun j => ⟨fs j, hfs j⟩, rdU_of_isBC hle U σ' hbc⟩

end Gen

theorem sum_shape {m : ℕ} {c l u x : ℂ} {a a' y p : Fin m → ℂ} (h : x = ∑ j, a j * y j) (ha : ∀ j, a' j = a j)
    (hp : ∀ j, p j = c * u * y j) : c * l * u * x = ∑ j, a' j * (l * p j) := by
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ha, hp]
  ring

end Lemmas

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.PhRatCommon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PencilLinePolynomialNatDegreeLeAndCoeffStatement
section
open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pencilLinePolynomial_natDegree_le_and_coeff : ∀ (F R : Type) [CommRing F] [CommRing R] [Algebra F R] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsMultiHomogeneous (fun _ => δ) f → ∀ (u : Fin D → Fin N → R) (a b : Fin N → R), (GlobalTheory.PencilDisc.line u a b f).natDegree ≤ δ ∧ (GlobalTheory.PencilDisc.line u a b f).coeff δ = MvPolynomial.aeval (GlobalTheory.HSChoice.join u b) f := by
  first | exact @GlobalTheory.PencilDisc.line_natDegree_le_and_coeff | exact GlobalTheory.PencilDisc.line_natDegree_le_and_coeff | (intros; apply GlobalTheory.PencilDisc.line_natDegree_le_and_coeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormComponentAddLeOfGramFrame
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt

namespace GlobalTheory.PetAdd

theorem cnorm_add_le {ι : Type} [Fintype ι] (u w : ι → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (u + w) ≤ Formalism.HermitianLatticesTheory.cnorm u + Formalism.HermitianLatticesTheory.cnorm w := by
  have key : ∀ t : ι → ℂ, Formalism.HermitianLatticesTheory.cnorm t = ‖(WithLp.equiv 2 (ι → ℂ)).symm t‖ := fun t => by
    rw [EuclideanSpace.norm_eq]; rfl
  rw [key, key, key]
  have e : (WithLp.equiv 2 (ι → ℂ)).symm (u + w) = (WithLp.equiv 2 (ι → ℂ)).symm u + (WithLp.equiv 2 (ι → ℂ)).symm w := by
    first | exact WithLp.equiv_symm_add 2 u w | rfl | simp
  rw [e]
  exact norm_add_le _ _

theorem IsGram.add_le {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    {ι : Type} [Fintype ι] [DecidableEq ι] {b : Module.Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ}
    {N : (K →+* ℂ) → V → ℝ} (h : IsGram b X N) (v : InfinitePlace K) (f g : V) :
    N v.embedding (f + g) ≤ N v.embedding f + N v.embedding g := by
  rw [← (h v).2, ← (h v).2, ← (h v).2]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
  have : Formalism.HermitianLatticesTheory.vecAt b v (f + g) = Formalism.HermitianLatticesTheory.vecAt b v f + Formalism.HermitianLatticesTheory.vecAt b v g := by
    funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
  rw [this, Matrix.mulVec_add]
  exact cnorm_add_le _ _

end GlobalTheory.PetAdd

namespace GlobalTheory.PetAdd

theorem normOn_add_le : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G : WTZ E), GoodOn U x V dict Z G → ∀ σ (f g : cuspOn U Z G), normOn U x V dict Z G σ (f + g) ≤ normOn U x V dict Z G σ f + normOn U x V dict Z G σ g := by
  intro E _ _ _ H Dw l Xo c r U x D V dict Z G h σ f g
  letI : Module c.F (cuspOn U Z G) := Submodule.module (cuspOn U Z G)
  obtain ⟨n, ⟨p, hp⟩⟩ := h.1
  have hconj : ∀ y, normOn U x V dict Z G ((starRingEnd ℂ).comp σ) y = normOn U x V dict Z G σ y :=
    fun y => GlobalTheory.CompHt.petOn_conj U x V dict Z G σ y
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · have := IsGram.add_le hp (InfinitePlace.mk σ) f g
    rwa [e] at this
  · have := IsGram.add_le hp (InfinitePlace.mk σ) f g
    have e' : (InfinitePlace.mk σ).embedding = (starRingEnd ℂ).comp σ := by
      rw [e]; ext a; simp [ComplexEmbedding.conjugate_coe_eq]
    rw [e', hconj, hconj, hconj] at this
    exact this

end GlobalTheory.PetAdd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceComponentAdeleConjugationEqComplexConj
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.RealPlaceConj

theorem piInf_cA_eq_star : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), piInf τ (cA σ z) = star (piInf τ z) := by
  intro F E _ _ _ _ _ σ hσ w τ z

  have hcomp : compInf F E w (cA σ z) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (compInf F E w z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp [cA, compInf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

  change infEmb τ (compInf F E w (cA σ z)) = star (infEmb τ (compInf F E w z))
  rw [hcomp, ← GlobalTheory.AdelicU.infEmb_sigR hσ τ]
  rfl

end GlobalTheory.RealPlaceConj
end

