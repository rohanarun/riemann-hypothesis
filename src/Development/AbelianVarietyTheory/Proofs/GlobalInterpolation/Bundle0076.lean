module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0066
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalB
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimePowSmulMemValueLatticeErase
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TendstoCoeffZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicLatticeCompletionLocalGlobal
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.LatLocGlob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}

theorem mem_latS_adele_iff (Λ : Submodule (𝓞 E) (Fin k → E)) (hΛ : Module.Finite (𝓞 E) Λ)
    (u : Fin k → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔
      ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (u i)) ∈ locLat v Λ := by
  obtain ⟨m, l, -, hl⟩ := GlobalTheory.T.exists_generators_mem_completedLattice_iff F E k Λ hΛ
  have hv : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : Fin k → E ⊗[F] v.adicCompletion F),
      w ∈ locLat v Λ ↔ ∃ t : Fin m → v.adicCompletion F,
        (∀ j, t j ∈ (v.adicCompletionIntegers F).toSubring) ∧ w = fun i => ∑ j, l j i ⊗ₜ[F] t j :=
    fun v w => hl _ _ w
  rw [hl]
  constructor
  · rintro ⟨t, ht, rfl⟩ v
    refine (hv v _).2 ⟨fun j => t j v, fun j => ht j v, ?_⟩
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => Formalism.UG.P.afsplit_prV_tmul v _ _
  · intro h
    choose t ht hu using fun v => (hv v _).1 (h v)
    let s : Fin m → FiniteAdeleRing (𝓞 F) F := fun j =>
      ⟨fun v => t v j, Filter.Eventually.of_forall fun v => ht v j⟩
    refine ⟨s, fun j v => ht v j, ?_⟩
    funext i
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun v => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, sub_eq_zero, map_sum]
    refine (congrFun (hu v) i).trans ?_
    exact Finset.sum_congr rfl fun j _ => (Formalism.UG.P.afsplit_prV_tmul v (l j i) (s j)).symm

theorem mem_of_forall_locLat (Λ : Submodule (𝓞 E) (Fin k → E)) (hΛ : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (Fin k → E)) = ⊤) (x : Fin k → E)
    (hx : ∀ v : HeightOneSpectrum (𝓞 F),
      (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ locLat v Λ) : x ∈ Λ := by
  rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin k) Λ hΛ hspan]
  show ((1⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin k) (Fin k) _) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ
  rw [inv_one, Units.val_one, one_mulVec, mem_latS_adele_iff Λ hΛ]
  exact hx

theorem mem_range_of_forall_intV (a : E)
    (ha : ∀ v : HeightOneSpectrum (𝓞 F), inclE (F := F) (v.adicCompletion F) a ∈ intV E v) :
    a ∈ (algebraMap (𝓞 E) E).range := by
  let Λ : Submodule (𝓞 E) (Fin 1 → E) := Submodule.span (𝓞 E) {fun _ => 1}
  have h1 : (fun _ => 1 : Fin 1 → E) ∈ Λ := Submodule.subset_span rfl
  have hfin : Module.Finite (𝓞 E) Λ := Module.Finite.span_of_finite _ (Set.finite_singleton _)
  have hspan : Submodule.span E (Λ : Set (Fin 1 → E)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have : x = x 0 • (fun _ => 1 : Fin 1 → E) := by
      funext i
      rw [Subsingleton.elim i 0]; simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  have := mem_of_forall_locLat (F := F) Λ hfin hspan (fun _ => a) fun v => by
    have h2 : (fun _ => inclE (F := F) (v.adicCompletion F) (1 : E)) ∈ locLat v Λ :=
      Submodule.subset_span ⟨_, h1, rfl⟩
    have h3 := (locLat v Λ).smul_mem (⟨_, ha v⟩ : intV E v) h2
    convert h3 using 1
    funext i
    show _ = inclE (F := F) (v.adicCompletion F) a * inclE (F := F) (v.adicCompletion F) (1 : E)
    rw [map_one, mul_one]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
  refine ⟨c, ?_⟩
  have := congrFun hc 0
  simpa [Algebra.smul_def] using this

theorem latS_local_global : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → (∀ u : Fin k → E ⊗[F] FiniteAdeleRing (𝓞 F) F, u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔ ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (u i)) ∈ locLat v Λ) ∧ (Submodule.span E (Λ : Set (Fin k → E)) = ⊤ → ∀ x : Fin k → E, (∀ v : HeightOneSpectrum (𝓞 F), (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ locLat v Λ) → x ∈ Λ) ∧ ∀ a : E, (∀ v : HeightOneSpectrum (𝓞 F), inclE (F := F) (v.adicCompletion F) a ∈ intV E v) → a ∈ (algebraMap (𝓞 E) E).range :=
  fun _ _ _ _ _ _ _ _ Λ hΛ =>
    ⟨mem_latS_adele_iff Λ hΛ, mem_of_forall_locLat Λ hΛ, mem_range_of_forall_intV⟩

end GlobalTheory.LatLocGlob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BandWidthLeInvSqOfRankBounds
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem bandWidth_le_inv_sq_of_rank_bounds (x e n k d La B c : ℝ) (hx : 1 < x) (hd0 : 0 ≤ d) (hd : d ≤ 1) (hn0 : 0 ≤ n)
    (hn : n ≤ 2 * x ^ (2 + 8 * e)) (hk : x ^ (9 / 2 + 10 * e) ≤ k) (hLa0 : 0 ≤ La)
    (hLa : La ≤ B * Real.log x ^ 2 * (2 * x ^ e))
    (h1 : 64 * B * x ^ (2 + 10 * e) * Real.log x ^ 2 ≤ x ^ (5 / 2 + 10 * e))
    (h2 : 4 * |c| * B * x ^ e * Real.log x ^ 3 ≤ x ^ (5 / 2 + 10 * e)) :
    4 * (2 * n * d) * x ^ e * La / k + c * Real.log x * La / k ≤ x ^ (-2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hk0 : 0 < k := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hk
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hxe : 0 < x ^ e := Real.rpow_pos_of_pos hx0 _
  have e1 : x ^ (2 + 10 * e) = x ^ (2 + 8 * e) * x ^ e * x ^ e := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
  have e2 : x ^ (5 / 2 + 10 * e) = x ^ (-2 : ℝ) * x ^ (9 / 2 + 10 * e) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hnd : n * d ≤ 2 * x ^ (2 + 8 * e) := le_trans (mul_le_of_le_one_right hn0 hd) hn
  have t1 : 4 * (2 * n * d) * x ^ e * La ≤ x ^ (5 / 2 + 10 * e) / 2 := by
    calc 4 * (2 * n * d) * x ^ e * La = 8 * (n * d) * x ^ e * La := by ring
      _ ≤ 8 * (2 * x ^ (2 + 8 * e)) * x ^ e * (B * Real.log x ^ 2 * (2 * x ^ e)) := by gcongr
      _ = 64 * B * x ^ (2 + 10 * e) * Real.log x ^ 2 / 2 := by rw [e1]; ring
      _ ≤ _ := by linarith
  have t2 : c * Real.log x * La ≤ x ^ (5 / 2 + 10 * e) / 2 := by
    calc c * Real.log x * La ≤ |c| * Real.log x * (B * Real.log x ^ 2 * (2 * x ^ e)) := by
          gcongr
          exact le_abs_self c
      _ = 4 * |c| * B * x ^ e * Real.log x ^ 3 / 2 := by ring
      _ ≤ _ := by linarith
  rw [← add_div, div_le_iff₀ hk0]
  have t3 : x ^ (5 / 2 + 10 * e) ≤ x ^ (-2 : ℝ) * k := by
    rw [e2]; gcongr
  linarith

theorem szRow_band_lambda_primes :
    SzRow (fun C D L => G.rhoB D C.GK L.sc ≤ L.sc.x ^ (-2 : ℝ) ∧ L.sc.x ^ L.sc.eps ≤ L.LaG ∧
      (∀ j : Fin 2, ((D.host.g j : ℕ) : ℝ) ≤ Real.exp (9 * L.sc.L)) ∧ (D.host.pde : ℝ) < L.sc.X' ∧
      (D.host.pde' : ℝ) < L.sc.X' ∧ ChTT_at L ∧ ChCode_at L 3 C.P.CF) := by
  intro eps he0 he1 C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hpde, -, hmid, -⟩ := hC
  have hKLa : 1 ≤ C.GK.La := hmid _ (by simp [FC.cMid])
  obtain ⟨CN, x1, h1⟩ := GlobalTheory.topCount_and_lambda_bounds eps he0 he1
  obtain ⟨x2, h2⟩ := GlobalTheory.EX.hostBounds eps C.P.Cpde he0 he1 hpde
  obtain ⟨x3, h3⟩ := GlobalTheory.scale_poly_comparison eps 41 1 he0 one_pos
  obtain ⟨x4, h4⟩ := GlobalTheory.scale_poly_comparison eps (2 * C.P.Cpde) 1 he0 one_pos
  obtain ⟨x5, h5⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (2 + 10 * eps) (5 / 2 + 10 * eps)
    (64 * (C.GK.La * CN ^ 2)) 2 (by linarith)
  obtain ⟨x6, h6⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow eps (5 / 2 + 10 * eps)
    (4 * |C.GK.rho * C.GK.CN| * (C.GK.La * CN ^ 2)) 3 (by linarith)
  refine ⟨max (max (max x1 x2) (max x3 x4)) (max (max x5 x6) 512), fun D L he hx hV => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hx1, hx2⟩, hx3, hx4⟩, ⟨hx5, hx6⟩, hx7⟩ := hx
  have hx1' := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  obtain ⟨-, -, hLa⟩ := h1 L.sc he hx1
  obtain ⟨hLa1, hLa2⟩ := hLa C.GK hKLa
  obtain ⟨-, -, -, -, -, -, -, -, hp1, hp2⟩ := h2 L.sc D.R D.host he hx2 hV.ranks hV.host
  obtain ⟨-, -, hb, -⟩ := h3 L.sc he hx3
  obtain ⟨-, -, -, -, -, -, hX⟩ := h4 L.sc he hx4
  have hy0 : 0 < L.sc.x ^ (L.sc.eps / 100) := Real.rpow_pos_of_pos hx0 _
  have hn : (D.R.n : ℝ) / L.sc.x ^ (L.sc.eps / 100) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps) := by
    rw [div_le_iff₀ hy0, mul_assoc, ← Real.rpow_add hx0]
    exact hV.ranks.n_le
  have hd : L.sc.delta1 * L.sc.x ^ (L.sc.eps / 100) ≤ 1 := by
    unfold Scale.delta1
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx1'.le (by have := L.sc.eps_pos; linarith)
  have hd0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hx0.le _
  have hnd : 2 * (D.R.n : ℝ) * L.sc.delta1 =
      2 * ((D.R.n : ℝ) / L.sc.x ^ (L.sc.eps / 100)) * (L.sc.delta1 * L.sc.x ^ (L.sc.eps / 100)) := by
    field_simp
  obtain ⟨-, -, ⟨hk1, hk2⟩, -⟩ := hV.ranks
  obtain ⟨-, hTT, -, -, hg, -⟩ := hV.host
  rw [Real.rpow_one] at hb hX
  have hp : ∀ y : ℝ, Real.log y ≤ 2 * C.P.Cpde * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2 → y < L.sc.X' := by
    intro y hy
    have a1 : y ≤ Real.exp (2 * C.P.Cpde * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) :=
      (Real.le_exp_log y).trans (Real.exp_le_exp.2 hy)
    have a2 : 1 < L.sc.x ^ (2 * C.P.Cpde) := Real.one_lt_rpow hx1' (by linarith)
    exact lt_of_le_of_lt a1 (lt_of_lt_of_le (lt_mul_of_one_lt_right (Real.exp_pos _) a2) hX)
  refine ⟨?_, hV.La_eq ▸ hLa1, fun j => ?_, hp _ hp1, hp _ hp2, hTT, ?_⟩
  · unfold G.rhoB G.Nstar
    rw [hnd]
    refine bandWidth_le_inv_sq_of_rank_bounds L.sc.x L.sc.eps _ _ _ _ (C.GK.La * CN ^ 2) _ hx1'
      (mul_nonneg hd0 hy0.le) hd (div_nonneg (Nat.cast_nonneg _) hy0.le) hn hk1
      ((Real.rpow_nonneg hx0.le _).trans hLa1) hLa2 ?_ ?_
    · rw [he]; exact h5 _ hx5
    · rw [he]; exact h6 _ hx6
  · have hk5 : (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (5 : ℝ) := by
      refine hk2.trans ?_
      have : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ L.sc.x ^ (5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [he]; linarith)
      linarith
    have hX1 : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
    have hb0 : 0 < L.sc.b := Real.exp_pos _
    have h41 : L.sc.x ^ (41 : ℕ) ≤ L.sc.b := by
      have : L.sc.x ^ (41 : ℝ) ≤ L.sc.b :=
        (le_mul_of_one_le_right (Real.rpow_nonneg hx0.le _) hX1).trans hb
      exact_mod_cast this
    have hk5' : (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (5 : ℕ) := by exact_mod_cast hk5
    have e9 : Real.exp (9 * L.sc.L) = L.sc.b ^ 9 := by
      unfold Scale.b; rw [← Real.exp_nat_mul]; norm_num
    calc ((D.host.g j : ℕ) : ℝ) ≤ 2 * ((D.R.k : ℝ) * L.sc.b) ^ 8 := (hg j).2
      _ ≤ 2 * ((2 * L.sc.x ^ (5 : ℕ)) * L.sc.b) ^ 8 := by gcongr
      _ = 512 * L.sc.x ^ 40 * L.sc.b ^ 8 := by ring
      _ ≤ L.sc.x * L.sc.x ^ 40 * L.sc.b ^ 8 := by gcongr
      _ = L.sc.x ^ 41 * L.sc.b ^ 8 := by ring
      _ ≤ L.sc.b * L.sc.b ^ 8 := by gcongr
      _ = _ := by rw [e9]; ring
  · unfold ChCode_at
    rw [hV.words]
    exact Nat.le_ceil _

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualWeylHighestWeightSpaceLineField
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

theorem rowDiv_raise_eq_zero (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) k) (hf : f ∈ dualWeyl k N N ν)
    (hwt : IsWeightedHomogeneous (rowW N N) f ν) (a b : Fin N) (hab : a < b) (j : ℕ) (hj : 1 ≤ j) :
    rowDiv k a b j f = 0 := by
  classical
  by_contra hne
  have hg : rowDiv k a b j f ∈ dualWeyl k N N ν := rowDivStable k N N ν a b j f hf
  have hZ : IsWeightedHomogeneous (GlobalTheory.LvT.KerLat.rowZ N N) f (fun i => (ν i : ℤ)) := by
    intro d hd
    funext i
    rw [GlobalTheory.LvT.KerLat.weight_rowZ, hwt hd]
  have hsh := GlobalTheory.LvT.KerLat.rowDiv_shift k (fun i => (ν i : ℤ)) a b j f hZ
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hne
  have e := hsh hm
  have dom := (GlobalTheory.DualWeyl.rowDeg_dominated_of_mem_nabla ν _ hg m (mem_support_iff.mpr hm)).1 (a.val + 1)
  have hrow : ∀ i, ((rowDeg m i : ℕ) : ℤ) = (ν i : ℤ) + (j : ℤ) * ((Pi.single a (1:ℤ) : Fin N → ℤ) i - (Pi.single b (1:ℤ) : Fin N → ℤ) i) := by
    intro i
    have := congrFun e i
    rw [GlobalTheory.LvT.KerLat.weight_rowZ, GlobalTheory.LvT.KerLat.weight_rowW] at this
    rw [this]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hcast : ((∑ i : Fin N with i.val < a.val + 1, rowDeg m i : ℕ) : ℤ) =
      ((∑ i : Fin N with i.val < a.val + 1, ν i : ℕ) : ℤ) + j := by
    push_cast
    simp only [hrow]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    have ha : (∑ i : Fin N with i.val < a.val + 1, (Pi.single a (1:ℤ) : Fin N → ℤ) i) = 1 := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro i _ hi; simp [Pi.single_apply, hi]
      · intro h; simp at h
    have hb : (∑ i : Fin N with i.val < a.val + 1, (Pi.single b (1:ℤ) : Fin N → ℤ) i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have : i ≠ b := by
        intro h; subst h
        simp at hi
        have : a.val < i.val := hab
        omega
      simp [Pi.single_apply, this]
    rw [ha, hb]; ring
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  have : ((∑ i : Fin N with i.val < a.val + 1, rowDeg m i : ℕ) : ℤ) ≤
      ((∑ i : Fin N with i.val < a.val + 1, ν i : ℕ) : ℤ) := by exact_mod_cast dom
  omega

theorem hw_line_field : ∀ (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ f ∈ dualWeyl k N N ν,
    IsWeightedHomogeneous (rowW N N) f ν → ∃ c : k, f = c • hw k le_rfl ν := by
  intro k _ N ν hν f hf hwt
  classical
  let K := AlgebraicClosure k
  let φ : k →+* K := algebraMap k K
  have hgK : map φ f ∈ dualWeyl K N N ν := dualWeylMap k K φ N N ν f hf
  have hrK : ∀ a b : Fin N, a < b → ∀ j : ℕ, 1 ≤ j → rowDiv K a b j (map φ f) = 0 := by
    intro a b hab j hj
    rw [lclosedeq_rowDiv_map, rowDiv_raise_eq_zero k N ν f hf hwt a b hab j hj, map_zero]
  obtain ⟨c, hc⟩ := hwLine K N N le_rfl ν hν (map φ f) hgK hrK
  obtain ⟨m, hm⟩ := ne_zero_iff.mp (hwNe k N N le_rfl ν)
  refine ⟨AddMonoidAlgebra.coeff f m / AddMonoidAlgebra.coeff (hw k le_rfl ν) m, ?_⟩
  have hcm := congrArg (AddMonoidAlgebra.coeff · m) hc
  rw [coeff_map, coeff_smul, ← lclosedeq_hw_map φ, coeff_map, smul_eq_mul] at hcm
  have hφ : φ (AddMonoidAlgebra.coeff (hw k le_rfl ν) m) ≠ 0 := (map_ne_zero φ).mpr hm
  have hcv : c = φ (AddMonoidAlgebra.coeff f m / AddMonoidAlgebra.coeff (hw k le_rfl ν) m) := by
    rw [map_div₀, hcm, mul_div_cancel_right₀ _ hφ]
  apply map_injective φ φ.injective
  rw [hc, hcv, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, lclosedeq_hw_map]

end GlobalTheory.Alc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConjLattice
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CMRam

open _root_.WeierstrassCurve

theorem exists_conj_lattice (σ : ℂ ≃+* ℂ) (L : PeriodPair) :
    ∃ L' : PeriodPair, L'.g₂ = σ L.g₂ ∧ L'.g₃ = σ L.g₃ := by
  first
  | exact @_root_.GlobalTheory.DiscUniformisation.main
  | exact _root_.GlobalTheory.DiscUniformisation.main
  | (apply _root_.GlobalTheory.DiscUniformisation.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DiscUniformisation.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DiscUniformisation.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DiscUniformisation.main ..)

end GlobalTheory.CMRam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLatticeVectorApproxAllFinitePlaces
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.OverCompare

theorem exists_int_approx_all (F : Type) [Field F] [NumberField F] (T : ℕ) (hT : T ≠ 0)
    (t : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (ht : ∀ v, t v ∈ v.adicCompletionIntegers F) :
    ∃ ρ : 𝓞 F, ∀ v : HeightOneSpectrum (𝓞 F), ∃ w ∈ v.adicCompletionIntegers F,
      t v = algebraMap F (v.adicCompletion F) (ρ : F) + T • w := by
  let a : FiniteAdeleRing (𝓞 F) F := ⟨t, Filter.Eventually.of_forall ht⟩
  obtain ⟨ρ, w, hw, e⟩ := Formalism.UG.P.csGlob_intAdApprox F (T : 𝓞 F) (by exact_mod_cast hT) a ht
  refine ⟨ρ, fun v => ⟨w v, hw v, ?_⟩⟩
  rw [map_natCast, ← nsmul_eq_mul] at e
  have h : a v = (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) ρ + T • w) v := by rw [← e]
  exact h

theorem exists_lattice_approx_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → ∀ (T : ℕ), T ≠ 0 → ∀ (y : ∀ v : HeightOneSpectrum (𝓞 F), Fin k → E ⊗[F] v.adicCompletion F), (∀ v, y v ∈ locLat v Λ) → ∃ x ∈ Λ, ∀ v : HeightOneSpectrum (𝓞 F), ∃ z ∈ locLat v Λ, y v = (fun i => inclE (F := F) (v.adicCompletion F) (x i)) + T • z := by
  intro F E _ _ _ _ _ k Λ hΛ T hT y hy
  obtain ⟨m, l, hl, H⟩ := GlobalTheory.T.exists_generators_mem_completedLattice_iff F E k Λ hΛ
  choose t ht hyt using fun v : HeightOneSpectrum (𝓞 F) =>
    (H (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring (y v)).1 (hy v)
  choose ρ hρ using fun j : Fin m =>
    exists_int_approx_all F T hT (fun v => t v j) (fun v => ht v j)
  refine ⟨∑ j, algebraMap (𝓞 F) (𝓞 E) (ρ j) • l j,
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hl j), fun v => ?_⟩
  choose w hw hwt using fun j => hρ j v
  refine ⟨fun i => ∑ j, l j i ⊗ₜ[F] w j,
    (H (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring _).2 ⟨w, hw, rfl⟩, ?_⟩
  rw [hyt v]
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, map_sum, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hwt j, TensorProduct.tmul_add]
  congr 1
  · have h1 : algebraMap (𝓞 F) (𝓞 E) (ρ j) • l j i = (ρ j : F) • l j i := by
      rw [Algebra.smul_def, Algebra.smul_def]; rfl
    rw [h1, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
    rfl
  · exact map_nsmul (TensorProduct.mk F E (v.adicCompletion F) (l j i)) T (w j)

end GlobalTheory.OverCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HalfLeAbsNodeSubMid
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem lowsFar_poly {y n t N l k d : ℝ} (hy : 28 ≤ y) (hn0 : 0 ≤ n) (ht0 : 0 ≤ t) (hN0 : 0 ≤ N) (hl0 : 0 ≤ l)
    (hk0 : 0 ≤ k) (hd0 : 0 ≤ d) (hn : n ≤ y) (ht : t ≤ y) (hN : N ≤ y) (hl : l ≤ y) (hk : k ≤ y) (hd : d ≤ 2 * y) :
    2 * (n * t ^ 2 * (N + t) * l ^ 2 + k * n ^ 2 * (k * (4 * d) + t + l)) + t / 2 + 3 ≤ y ^ 7 := by
  have hy0 : 0 ≤ y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have h1 : n * t ^ 2 * (N + t) * l ^ 2 ≤ y * y ^ 2 * (y + y) * y ^ 2 := by gcongr
  have h2 : k * n ^ 2 * (k * (4 * d) + t + l) ≤ y * y ^ 2 * (y * (4 * (2 * y)) + y + y) := by gcongr
  have e1 : y * y ^ 2 * (y + y) * y ^ 2 = 2 * y ^ 6 := by ring
  have e2 : y * y ^ 2 * (y * (4 * (2 * y)) + y + y) = 8 * y ^ 5 + 2 * y ^ 4 := by ring
  have p5 : y ^ 5 ≤ y ^ 6 := pow_le_pow_right₀ hy1 (by norm_num)
  have p4 : y ^ 4 ≤ y ^ 6 := pow_le_pow_right₀ hy1 (by norm_num)
  have p1 : y ^ 1 ≤ y ^ 6 := pow_le_pow_right₀ hy1 (by norm_num)
  have p7 : 28 * y ^ 6 ≤ y ^ 7 := by
    calc 28 * y ^ 6 ≤ y * y ^ 6 := by gcongr
      _ = y ^ 7 := by ring
  rw [pow_one] at p1
  linarith

theorem half_le_abs_node_sub_mid (b : ℝ) (i j : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    H ≤ |(b + i * (2 * H)) - (b + j * (2 * H) + 2 * H / 2)| := by
  rcases Nat.lt_or_ge j i with h | h
  · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    exact le_abs.2 (Or.inl (by nlinarith))
  · have : (i : ℝ) ≤ j := by exact_mod_cast h
    exact le_abs.2 (Or.inr (by nlinarith))

theorem szRow_lowsFar : SzRow (fun C D L => (∀ τ (i j : Fin D.R.m),
    2 * L.sc.b / lStar L + (D.R.t : ℝ) / 2 + 3 ≤ |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)|)) := by
  intro eps he0 he1 C _
  obtain ⟨x1, hx1⟩ := _root_.GlobalTheory.EX.rank_basic_bounds eps he0 he1
  refine ⟨402, fun cD hcD => ⟨cD * 7, fun ch hch => ⟨max x1 28, fun D L he hx V τ i j => ?_⟩⟩⟩
  have hx28 : 28 ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hx1' : 1 ≤ L.sc.x := by linarith
  obtain ⟨hf, -, hr, hkr, -, hLx, hL1, -, -, -, -, -, -, ht, hN, -, -⟩ :=
    hx1 L.sc D.R he (le_trans (le_max_left _ _) hx) V.ranks
  have up : ∀ a : ℝ, a ≤ 402 → L.sc.x ^ a ≤ L.sc.x ^ cD := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hx1' (le_trans ha hcD)
  have hxy : L.sc.x ≤ L.sc.x ^ cD := by simpa using up 1 (by norm_num)
  have hn : (D.R.n : ℝ) ≤ L.sc.x ^ cD := by
    have : (D.R.n : ℝ) ≤ D.R.f := by
      unfold Ranks.f; exact_mod_cast (by omega)
    exact this.trans (hf.trans (up _ (by norm_num)))
  have hk : (D.R.k : ℝ) ≤ L.sc.x ^ cD := by
    have : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    exact this.trans (hr.trans (up _ (by norm_num)))
  have hd : ((Delv L.sc cD : ℕ) : ℝ) ≤ 2 * L.sc.x ^ cD := by
    have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by linarith)
    unfold Delv; linarith
  have key := lowsFar_poly (y := L.sc.x ^ cD) (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hn
    (ht.trans (up _ (by norm_num))) (hN.trans (up _ (by norm_num))) (hLx.trans hxy) hk hd
  have h7 : (L.sc.x ^ cD) ^ 7 ≤ (⌈L.sc.x ^ ch⌉₊ : ℝ) := by
    refine le_trans ?_ (Nat.le_ceil _)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hx1' (by simpa using hch)
  obtain ⟨-, -, ⟨b1, hb, -⟩, -⟩ := V.hc
  have hdist := half_le_abs_node_sub_mid (b1 τ : ℝ) i.1 j.1 (⌈L.sc.x ^ ch⌉₊ : ℝ) (Nat.cast_nonneg _)
  have heq : (((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ) =
      ((b1 τ : ℝ) + i.1 * (2 * (⌈L.sc.x ^ ch⌉₊ : ℝ))) -
        ((b1 τ : ℝ) + j.1 * (2 * (⌈L.sc.x ^ ch⌉₊ : ℝ)) + 2 * (⌈L.sc.x ^ ch⌉₊ : ℝ) / 2) := by
    rw [(hb τ j).2, (hb τ i).1, (hb τ j).1]
    unfold h0v
    push_cast
    ring
  rw [heq]
  refine le_trans ?_ (key.trans (h7.trans hdist))
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hm : (1 : ℝ) ≤ D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega)
  have hS : L.Sc = (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) := by
    rw [L.Sc_eq, V.Del_eq]; push_cast; ring
  unfold lStar
  rw [hS]
  set Λ := (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 +
    (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * ((D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) + D.R.t + L.sc.L) with hΛ
  have hΛ0 : 0 ≤ Λ := by
    have : 0 ≤ L.sc.L := by linarith
    positivity
  have : 2 * L.sc.b / ((D.R.m : ℝ) * L.sc.b / Λ) ≤ 2 * Λ := by
    rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hΛ0 hb0.le]
  linarith

end GlobalTheory.EX
end

