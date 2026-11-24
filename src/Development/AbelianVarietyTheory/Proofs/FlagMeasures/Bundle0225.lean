module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0161
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0220
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0219
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothAverageLowestKType
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.StepAverage

theorem exists_smooth_average_of_isKTypeOf : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → ∀ P : ℕ, ∀ u ∈ VP B P, ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I) := by
  intro B d hD hK P u hu
  have hσ : IsURep B.σs := (tensorRep B d hD).1
  have hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v) := fun v => by
    obtain ⟨_, hds, _, _⟩ := hD v
    obtain ⟨_, _, h, _⟩ := hds
    exact h
  have hw : ∀ v, B.w v ∈ Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v) ∧ B.w v ≠ 0 := fun v => by
    obtain ⟨_, _, ⟨h1, h2⟩, _⟩ := hD v
    refine ⟨h2, fun h0 => ?_⟩
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1

  let A : Set B.Hs := {y | ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧
    HasCompactSupport F ∧ y = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I)}
  have hint : ∀ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F →
      Integrable (fun g : B.I.Ginf => F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w)) (muInf B.I) :=
    fun F hF hc => integrable_inf B hσ (B.tens B.w) hF.continuous hc
  have hzero : (0 : B.Hs) ∈ A := ⟨0, contDiff_const, HasCompactSupport.zero, by simp⟩
  have hadd : ∀ x y, x ∈ A → y ∈ A → x + y ∈ A := by
    rintro x y ⟨F, hF, hFc, rfl⟩ ⟨G, hG, hGc, rfl⟩
    refine ⟨F + G, hF.add hG, hFc.add hGc, ?_⟩
    rw [← integral_add (hint F hF hFc) (hint G hG hGc)]
    congr 1
    funext g
    simp [add_smul]
  have hsmul : ∀ (c : ℂ) x, x ∈ A → c • x ∈ A := by
    rintro c x ⟨F, hF, hFc, rfl⟩
    refine ⟨fun z => c * F z, contDiff_const.mul hF, hFc.mul_left (f := fun _ => c), ?_⟩
    rw [← integral_smul]
    congr 1
    funext g
    rw [mul_smul]

  have htens : ∀ u' : ∀ v, B.H v, (∀ v, u' v ∈ Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v)) → B.tens u' ∈ A := by
    intro u' hu'
    have hloc := fun v => GlobalTheory.exists_smooth_average_eq_of_mem_lowKSub B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v)
      (B.w v) (hU v) (hK v) (hw v).1 (hw v).2 (u' v) (hu' v)
    choose F hF hFc hFe using hloc
    obtain ⟨G, hG, hGc, hGe⟩ := tens_average B hU hσ B.w F hF hFc
    refine ⟨G, hG, hGc, ?_⟩
    rw [← hGe]
    congr 1
    funext v
    exact hFe v

  have hword : ∀ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (y : B.Hs), y ∈ A → wordAct B l y ∈ A := by
    intro l
    induction l with
    | nil => intro y hy; exact hy
    | cons X l ih =>
      intro y hy
      obtain ⟨F, hF, hFc, hFe⟩ := ih y hy
      obtain ⟨F', hF', hF'c, hd⟩ := GlobalTheory.AverageDeriv.hasDerivAt_orbit_average B F (atPlace B X.1 X.2) (B.tens B.w)
        hσ hF hFc
      refine ⟨F', hF', hF'c, ?_⟩
      show dAct B (atPlace B X.1 X.2) (wordAct B l y) = _
      rw [hFe]
      exact hd.deriv

  let S : Submodule ℂ B.Hs :=
    { carrier := A
      add_mem' := fun hx hy => hadd _ _ hx hy
      zero_mem' := hzero
      smul_mem' := fun c x hx => hsmul c x hx }
  have hle : VP B P ≤ S := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨l, u', -, hu', rfl⟩
    exact hword l _ (htens u' hu')
  exact hle hu

end GlobalTheory.StepAverage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTotallyIsotropicDualFamilyInLattice
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.IsotropicDual

section Herm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type}
  [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem h_sum_left {ι : Type} (s : Finset ι) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, v i) y = ∑ i ∈ s, H.h (v i) y := by
  let φ : V →+ E := AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)
  exact map_sum φ v s

theorem h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add (f := _), ← H.h_herm y x, ← H.h_herm y' x]

theorem h_smul_right (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

theorem h_sum_right {ι : Type} (s : Finset ι) (x : V) (v : ι → V) :
    H.h x (∑ i ∈ s, v i) = ∑ i ∈ s, H.h x (v i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [H.h_herm (∑ i ∈ s, v i) x, h_sum_left, map_sum]
  exact Finset.sum_congr rfl fun i _ => (H.h_herm (v i) x).symm

end Herm

theorem isotropic_dual : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∀ y : Fin r → V, (∀ a, y a ∈ Λ) → (∀ a b, H.h (y a) (Fr.f b) = if b = a.castSucc then 1 else 0) → ∃ y' : Fin r → V, (∀ a, y' a ∈ Λ) ∧ (∀ a b, H.h (y' a) (Fr.f b) = if b = a.castSucc then 1 else 0) ∧ ∀ a b, H.h (y' a) (y' b) = 0 := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r Fr Λ hSD hFr y hy hyf
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨htr, -, -, -, hmem, -⟩ := GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ
  have hint : ∀ a b, H.h (y a) (y b) ∈ M.L.O := fun a b => (hSD.2.2 (y a)).1 (hy a) (y b) (hy b)
  have hdiag : ∀ a, ∃ x ∈ M.L.O, x + M.L.cj x = -H.h (y a) (y a) := by
    intro a
    obtain ⟨c, hc⟩ := (M.L.cj_fix (H.h (y a) (y a))).1 (H.h_herm (y a) (y a)).symm
    have hc' : c ∈ 𝒪[F] := (hmem c).1 (hc ▸ hint a a)
    obtain ⟨x, hx, hxe⟩ := htr (-⟨c, hc'⟩)
    refine ⟨x, hx, ?_⟩
    rw [hxe, ← hc]
    simp
  choose x hxO hxe using hdiag
  obtain ⟨m, hmO, hm⟩ : ∃ m : Fin r → Fin r → E, (∀ a k, m a k ∈ M.L.O) ∧
      ∀ a b, m a b + M.L.cj (m b a) = -H.h (y a) (y b) := by
    refine ⟨fun a k => if a < k then -H.h (y a) (y k) else if a = k then x a else 0, ?_, ?_⟩
    · intro a k
      dsimp only
      split_ifs
      · exact M.L.O.neg_mem (hint a k)
      · exact hxO a
      · exact M.L.O.zero_mem
    · intro a b
      dsimp only
      rcases lt_trichotomy a b with h | rfl | h
      · rw [if_pos h, if_neg (not_lt.2 h.le), if_neg h.ne', map_zero, add_zero]
      · rw [if_neg (lt_irrefl a), if_pos rfl]
        exact hxe a
      · rw [if_neg (not_lt.2 h.le), if_neg h.ne', if_pos h, map_neg, ← H.h_herm (y b) (y a),
          zero_add]
  have he : ∀ k : Fin r, Fr.f k.castSucc ∈ Λ := fun k => hFr.1.1 k.castSucc
  have hEf : ∀ (k : Fin r) b, H.h (Fr.f k.castSucc) (Fr.f b) = 0 := fun k b =>
    hFr.2.1 _ _ (Or.inl (Fin.castSucc_lt_last k).ne)
  have hyE : ∀ a k : Fin r, H.h (y a) (Fr.f k.castSucc) = if k = a then 1 else 0 := by
    intro a k
    rw [hyf a k.castSucc]
    simp only [Fin.castSucc_inj]
  have hEy : ∀ k b : Fin r, H.h (Fr.f k.castSucc) (y b) = if k = b then 1 else 0 := by
    intro k b
    rw [H.h_herm (y b) (Fr.f k.castSucc), hyE]
    split_ifs <;> simp
  refine ⟨fun a => y a + ∑ k, m a k • Fr.f k.castSucc, fun a => ?_, fun a b => ?_, fun a b => ?_⟩
  · refine Λ.add_mem (hy a) (Λ.sum_mem fun k _ => ?_)
    exact Λ.smul_mem ⟨m a k, hmO a k⟩ (he k)
  · simp only [H.h_add_left, h_sum_left, H.h_smul_left, hEf, mul_zero, Finset.sum_const_zero,
      add_zero, hyf]
  · simp only [H.h_add_left, h_add_right, h_sum_left, h_sum_right, H.h_smul_left, h_smul_right,
      hyE, hEy, hEf, mul_zero, mul_ite, mul_one, Finset.sum_const_zero, add_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linear_combination hm a b

end GlobalTheory.IsotropicDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamPSizesRecord
section
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem sizes_record_at {D : D7} (L : SizeData₂ D) (h : SizesAt L) (Cs : ℝ) (hCs : 5 ≤ Cs)
    (hx : 16 ≤ L.sc.x) (j : Fin 2) :
    Real.exp (8 * L.sc.x ^ L.sc.eps) ≤ (D.host.g j : ℝ) ∧ L.sc.x ^ 2 ≤ (D.R.f : ℝ) ∧
      (D.R.f : ℝ) ≤ L.sc.x ^ Cs ∧ (D.R.m : ℝ) ≤ L.sc.x ^ Cs ∧ 100 ≤ D.R.r ∧
      (D.R.r : ℝ) ≤ L.sc.x ^ Cs ∧
      Real.exp (L.sc.x ^ (L.sc.ez / 6)) ≤ ((min D.host.q D.host.d : ℕ) : ℝ) := by
  obtain ⟨hN, -, hK, -, -, -, hQ, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩ := h
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hmk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hkb : (D.R.k : ℝ) ≤ L.sc.x ^ (19 / 4 : ℝ) := by
    refine hK.2.trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_)
    unfold szTh
    linarith
  have h2 : (2 : ℝ) ≤ L.sc.x ^ (1 / 4 : ℝ) := by
    have e : (2 : ℝ) = (16 : ℝ) ^ (1 / 4 : ℝ) := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [e]
    exact Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  have h2k : 2 * (D.R.k : ℝ) ≤ L.sc.x ^ Cs := by
    calc 2 * (D.R.k : ℝ) ≤ L.sc.x ^ (1 / 4 : ℝ) * L.sc.x ^ (19 / 4 : ℝ) :=
          mul_le_mul h2 hkb (by linarith) (by linarith)
      _ = L.sc.x ^ (5 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
      _ ≤ L.sc.x ^ Cs := Real.rpow_le_rpow_of_exponent_le hx1.le hCs
  have hn : L.sc.x ^ 2 ≤ (D.R.n : ℝ) := by
    refine le_trans ?_ hN.1
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hx1.le
    unfold szTh
    push_cast
    linarith
  have hf : L.sc.x ^ 2 ≤ (D.R.f : ℝ) := by
    refine hn.trans ?_
    exact_mod_cast (by unfold Ranks.f; omega : D.R.n ≤ D.R.f)
  have hfk' : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have hmk' : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hr : (D.R.r : ℝ) ≤ 2 * (D.R.k : ℝ) := by
    exact_mod_cast (by unfold Ranks.r; omega : D.R.r ≤ 2 * D.R.k)
  have hf100 : 100 ≤ D.R.f := by
    have : (100 : ℝ) ≤ D.R.f := by nlinarith
    exact_mod_cast this
  refine ⟨?_, hf, by linarith, by linarith, by unfold Ranks.r; omega, by linarith, ?_⟩
  · refine le_trans ?_ (hG j j).1
    have e : Real.exp (8 * L.sc.x ^ L.sc.eps) = L.sc.b ^ 8 := by
      unfold Scale.b Scale.L
      rw [← Real.exp_nat_mul]
      norm_num
    have hb : 0 < L.sc.b := Real.exp_pos _
    rw [e]
    exact pow_le_pow_left₀ hb.le (le_mul_of_one_le_left hb.le hk1) 8
  · have hq : (0 : ℝ) < D.host.q := by
      have := D.host.qd_big.1
      exact_mod_cast (by omega : 0 < D.host.q)
    have hd : (0 : ℝ) < D.host.d := by
      have := D.host.qd_big.2
      exact_mod_cast (by omega : 0 < D.host.d)
    rw [Nat.cast_min]
    refine le_min ((Real.le_log_iff_exp_le hq).1 hQ.1) ((Real.le_log_iff_exp_le hd).1 ?_)
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_) hQ.2.2.2.1
    have := L.sc.ez_pos
    linarith

theorem family_eventually_size_bounds : ∀ (eps : ℝ) (Fm : FamP eps) (Cs : ℝ), 5 ≤ Cs → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (j : Fin 2), Real.exp (8 * x ^ eps) ≤ ((Fm.D x i).host.g j : ℝ) ∧ x ^ 2 ≤ ((Fm.D x i).R.f : ℝ) ∧ ((Fm.D x i).R.f : ℝ) ≤ x ^ Cs ∧ ((Fm.D x i).R.m : ℝ) ≤ x ^ Cs ∧ 100 ≤ (Fm.D x i).R.r ∧ ((Fm.D x i).R.r : ℝ) ≤ x ^ Cs ∧ Real.exp (x ^ (Fm.ez / 6)) ≤ ((min (Fm.D x i).host.q (Fm.D x i).host.d : ℕ) : ℝ) := by
  intro eps Fm Cs hCs
  refine ⟨max 16 (Fm.x1 + 1), fun x hx i j => ?_⟩
  have h16 : 16 ≤ x := (le_max_left _ _).trans hx
  have hx1 : Fm.x1 < x := by linarith [(le_max_right _ _).trans hx]
  have := sizes_record_at (Fm.L x i) (Fm.sizes x hx1 i) Cs hCs (by rw [Fm.L_x x i hx1]; exact h16) j
  rw [Fm.L_x x i hx1, Fm.L_eps x i, Fm.L_ez x i] at this
  exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodPlacesOverTypePrimesSplit
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory.TypedPlacesProduct

theorem finite_over {K : Type*} [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | ((n : ℕ) : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {((n : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hn
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem finprod_over {K : Type*} [Field K] [NumberField K] {n f : ℕ} (hn : n ≠ 0) (φ : ℝ → ℝ)
    (hc : Nat.card {v : HeightOneSpectrum (𝓞 K) // ((n : ℕ) : 𝓞 K) ∈ v.asIdeal} = f)
    (hq : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal →
      Nat.card (𝓞 K ⧸ v.asIdeal) = n) :
    (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 K) | ((n : ℕ) : 𝓞 K) ∈ p.asIdeal},
      φ (Ideal.absNorm p.asIdeal : ℝ)) = φ n ^ f := by
  have hs := finite_over (K := K) hn
  have hnorm : ∀ p ∈ {p : HeightOneSpectrum (𝓞 K) | ((n : ℕ) : 𝓞 K) ∈ p.asIdeal},
      φ (Ideal.absNorm p.asIdeal : ℝ) = φ n := by
    intro p hp
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hq p hp]
  rw [finprod_mem_congr rfl hnorm, finprod_mem_eq_finite_toFinset_prod _ hs, Finset.prod_const,
    ← Nat.card_eq_card_finite_toFinset hs]
  exact congrArg _ hc

private lemma disjoint_primes_dvd_of_coprime {K : Type*} [Field K] [NumberField K] {a b : ℕ} (hab : Nat.Coprime a b) :
    Disjoint {p : HeightOneSpectrum (𝓞 K) | ((a : ℕ) : 𝓞 K) ∈ p.asIdeal}
      {p : HeightOneSpectrum (𝓞 K) | ((b : ℕ) : 𝓞 K) ∈ p.asIdeal} := by
  rw [Set.disjoint_left]
  intro p ha hb
  obtain ⟨u, w, huw⟩ := (Nat.isCoprime_iff_coprime.mpr hab).map (Int.castRingHom (𝓞 K))
  have h1 : (1 : 𝓞 K) ∈ p.asIdeal := by
    rw [← huw]
    simp only [eq_intCast, Int.cast_natCast]
    exact p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ ha) (p.asIdeal.mul_mem_left _ hb)
  exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem finprod_typed_places : ∀ (D : D7) (φ : ℝ → ℝ), (∀ i, StandardLattice.SplitsF D (D.host.g i)) → (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}, φ (Ideal.absNorm p.asIdeal : ℝ)) = φ (D.host.g 0) ^ D.R.f * φ (D.host.g 1) ^ D.R.f := by
  intro D φ hs
  have hp := D.host.g_prime
  have hne : D.host.g 0 ≠ D.host.g 1 := D.host.g_ne
  have hcop : Nat.Coprime (D.host.g 0) (D.host.g 1) := (Nat.coprime_primes (hp 0) (hp 1)).mpr hne
  rw [Set.setOf_or, finprod_mem_union (disjoint_primes_dvd_of_coprime hcop) (finite_over (hp 0).ne_zero)
    (finite_over (hp 1).ne_zero), finprod_over (hp 0).ne_zero φ (hs 0).1 (hs 0).2,
    finprod_over (hp 1).ne_zero φ (hs 1).1 (hs 1).2]

end GlobalTheory.TypedPlacesProduct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapBigOfComparison
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.GapAtRealPlaces

theorem gapBig_of_comparison (h : PI.ScGapBig.ScGapBig) (D : Formalism.BasicNotions.D7) :
    Formalism.L2.SG.SplitPrimeNormLemmas.GapBigOfGapHyp D := by
  intro hm hG τ

  have hr : PI.ScGapBig.rk48 D.R.k D.R.rS = D.R.r := by
    simp only [PI.ScGapBig.rk48, Formalism.BasicNotions.Ranks.r]
    omega

  have hgaps : ∀ (j : Fin (2 * D.R.rS + 2)) (hj : j.val + 1 < 2 * D.R.rS + 2),
      16 * (PI.ScGapBig.rk48 D.R.k D.R.rS : ℝ) ^ 19 ≤
        ((D.hc τ).b (Fin.cast hm.symm ⟨j.val + 1, hj⟩) : ℝ) - ((D.hc τ).b (Fin.cast hm.symm j) : ℝ) := by
    intro j hj
    have hlt : (Fin.cast hm.symm j).val + 1 < D.R.m := by
      rw [Fin.val_cast]
      omega
    have key := hG.2 τ (Fin.cast hm.symm j) hlt
    have hidx : (⟨(Fin.cast hm.symm j).val + 1, hlt⟩ : Fin D.R.m) = Fin.cast hm.symm ⟨j.val + 1, hj⟩ :=
      Fin.ext rfl
    rw [hidx] at key
    rw [hr]
    exact_mod_cast key
  obtain ⟨t, hto, ht5, ht1801, hgap⟩ :=
    h D.R.k D.R.rS (fun j => ((D.hc τ).b (Fin.cast hm.symm j) : ℝ)) (hr ▸ hG.1) hgaps
  exact ⟨t, hto, ht5, ht1801, hgap⟩

theorem gapBigOfGapHyp : ∀ D : D7, GapBigOfGapHyp D := by
  intro D
  exact gapBig_of_comparison scGapBig D

end GlobalTheory.GapAtRealPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDataWithTermSingleOrbitPrimeTo
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver GlobalTheory.HL
open scoped Pointwise Classical

namespace GlobalTheory.HL.PrimeToOrbit

theorem coord_one_orbit {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ)
    (S : GlobalTheory.HL.Frames L r k) (hgg : S.gg = false) (hvG : vE L S.ϖ S.G = 0)
    (hDu : ∀ l, S.D l ≠ 0 → S.D l ∈ L.O ∧ ∃ y ∈ L.O, S.D l * y = 1)
    {δ δ' : S.Datum} {Λ Λ' : Submodule L.O S.V} (hT : S.IsTerm δ Λ) (hT' : S.IsTerm δ' Λ') :
    ∃ h ∈ S.H0, h • δ = δ' := by
  have ha : S.a = 0 := by simp [GlobalTheory.HL.Frames.a, GlobalTheory.HL.Frames.vth, hgg, hvG]
  obtain ⟨-, -, hall⟩ := GlobalTheory.HL.GoodClass.one_class L r k S hgg hDu
  have hint : ∀ d Λ, S.IsTerm d Λ → S.IsIntCls (S.Fr d Λ) := fun d Λ h =>
    (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.1
  have hdd : ∀ d d' Λ, S.IsTerm d Λ → S.IsTerm d' Λ → d' = d := fun d d' Λ h h' =>
    (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.2 d' h'
  have hact := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S
  have hcom := GlobalTheory.HL.ComplAct.main L r k S
  have hcls := GlobalTheory.HL.FrameClass.frame_classes L r k S
  obtain ⟨s, hs, e⟩ := hall _ (hint _ _ hT)
  obtain ⟨s', hs', e'⟩ := hall _ (hint _ _ hT')
  have h1 := hact δ _ hT _ (S.St.inv_mem hs)
  have h1' := hact δ' _ hT' _ (S.St.inv_mem hs')
  have hFr₁ : S.Fr δ (s⁻¹ • Λ) = S.frameCls S.f S.f' := by
    rw [h1.2.2.2.2.1, e, smul_smul, inv_mul_cancel, one_smul]
  have hFr₁' : S.Fr δ' (s'⁻¹ • Λ') = S.frameCls S.f S.f' := by
    rw [h1'.2.2.2.2.1, e', smul_smul, inv_mul_cancel, one_smul]
  have hM : S.M δ (s⁻¹ • Λ) = S.M δ' (s'⁻¹ • Λ') := by
    have h3 : (S.fr δ (s⁻¹ • Λ), S.fr' δ (s⁻¹ • Λ)) ∈ S.Fr δ' (s'⁻¹ • Λ') := by
      rw [hFr₁', ← hFr₁]; exact (hcls _ _).1
    exact ((hcls _ _).2.1 _ h3).2
  obtain ⟨h, hh, e₁⟩ := GlobalTheory.HL.StdPlace.term_orbit L r k S ha h1.1 h1'.1 hM
  have h4 := (hcom δ' _ h1'.1 h hh).1
  rw [e₁] at h4
  refine ⟨h⁻¹, S.H0.inv_mem hh, ?_⟩
  have h5 : h • δ' = δ := hdd _ _ _ h1.1 h4
  rw [← h5, smul_smul, inv_mul_cancel, one_smul]

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → P.PrimeTo → ∀ (d d' : Datum P) (t t' : Term V M r), IsTermOver P d t → IsTermOver P d' t' → Datum.Rel d d' := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hdim hrel hpt d d' t t' ht ht'
  have := hM.loc
  have := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hdim hrel
  obtain ⟨-, -, hgg, hvG, -⟩ : _ ∧ _ ∧ (S.gg = false ∧ vE M.L S.ϖ S.G = 0 ∧ True) := by
    obtain ⟨a1, a2, a3⟩ := GlobalTheory.HL.CoordHeight.height_eq M hM H r k P S c
    obtain ⟨b1, b2, -⟩ := a3 hpt
    exact ⟨a1, a2, b1, b2, trivial⟩
  obtain ⟨-, -, -, -, hD, -⟩ := GlobalTheory.FrameBasic.main M.L r k S
  have hDu : ∀ l, S.D l ≠ 0 → S.D l ∈ M.L.O ∧ ∃ y ∈ M.L.O, S.D l * y = 1 := by
    intro l hl
    by_cases h0 : l = 0
    · have e : S.D l = 1 := by
        subst h0
        unfold GlobalTheory.HL.Frames.D GlobalTheory.HL.lead
        exact Matrix.det_isEmpty (n := Fin 0)
      rw [e]
      exact ⟨M.L.O.one_mem, 1, M.L.O.one_mem, mul_one 1⟩
    · have hmem : (l : ℕ) ∈ P.ends := by
        unfold LocNG.FPair.ends
        simp only [Finset.mem_filter, Finset.mem_range]
        rw [GlobalTheory.HL.CoordHeight.Dm_eq c]
        exact ⟨l.2, Nat.one_le_iff_ne_zero.mpr fun h => h0 (Fin.ext h), hD l hl⟩
      have := hpt.2.2 _ hmem
      rwa [GlobalTheory.HL.CoordHeight.Dm_eq c] at this
  have hT := ((GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c).1 d t ht).1
  have hT' := ((GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c).1 d' t' ht').1
  exact ((GlobalTheory.HL.CoordDatum.transport M hM H r k P S c).2.2.1 d d').2
    (coord_one_orbit M.L r k S hgg hvG hDu hT hT')

end GlobalTheory.HL.PrimeToOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeWithDensityDetNormSqStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftQuotientCovolume_withDensity_detNormSq : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ), 1 ≤ j → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → ∀ F : ℝ → ENNReal, Measurable F → covol (autGL E j Λ) ((haarGL E j).withDensity fun x => F (detNorm E j x)) {x | 0 < detNorm E j x} = covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} * ∫⁻ t in Set.Ioi (0 : ℝ), F t / ENNReal.ofReal t := by
  intro E _ _ hE j hj Λ hΛ F hF
  first
  | exact GlobalTheory.DetSlab.covol_withDensity_detNorm E hE j hj Λ hΛ F hF
  | exact GlobalTheory.DetSlab.covol_withDensity_detNorm E hE j hj Λ hΛ.toIsLattice F hF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanLEqOfRealMeanCReStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanL_tsum_ofReal_eq_ofReal_re_meanC : ∀ (G : Type) [MeasurableSpace G] (μ : Measure G) (𝓕 : Set G) (ι : Type) [Countable ι] (f : ι → G → ℝ), (∀ i, Measurable (f i)) → (∀ i h, 0 ≤ f i h) → μ 𝓕 < ⊤ → ∫⁻ h in 𝓕, ∑' i, ‖((f i h : ℝ) : ℂ)‖ₑ ∂μ < ⊤ → meanL μ 𝓕 (fun h => ∑' i, ENNReal.ofReal (f i h)) = ENNReal.ofReal (meanC μ 𝓕 (fun h => ∑' i, ((f i h : ℝ) : ℂ))).re := by
  first | exact @GlobalTheory.meanL_eq_ofReal_meanC_re | exact GlobalTheory.meanL_eq_ofReal_meanC_re | (intros; apply GlobalTheory.meanL_eq_ofReal_meanC_re <;> assumption)
end

