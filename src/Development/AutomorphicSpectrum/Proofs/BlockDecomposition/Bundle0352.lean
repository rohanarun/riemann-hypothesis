module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import GroundTheory.AutomorphicForms.SmoothRep
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0335
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorsCommuteOnFixed
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeOpMul

open GroundTheory.Automorphic GlobalTheory.CompanionTheory.HeckeMult Zls

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_orbit_const {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : GlobalTheory.PRep.IsSmooth π)
    {K : Subgroup (GL (Fin N) k)} (hK : K ≤ KO k (Fin N)) {x y : V} (hy : ∀ g ∈ K, π g y = y)
    (hxy : ∀ l : Module.Dual ℂ V, (∀ g ∈ K, l ∘ₗ π g = l) → l x = l y)
    (f : Module.Dual ℂ V) (hf : ∀ g ∈ K, f (π g x) = f x) : f x = f y := by
  have hsm : GroundTheory.Automorphic.IsSmooth π := fun v => hπ v
  have hmem : x - y ∈ coinvariantsKer π K := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    have := hxy (φ ∘ₗ (coinvariantsKer π K).mkQ) (fun g hg => by
      ext u
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
      congr 1
      exact (Submodule.Quotient.eq _).2 (sub_mem_coinvariantsKer hg u))
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply] at this
    rw [Submodule.Quotient.mk_sub, map_sub, this, sub_self]
  obtain ⟨U, hU, hUz⟩ := exists_nhds_cosetSum_eq_zero hsm hmem
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : NonarchimedeanAddGroup k := ⟨fun W hW => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hW
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin N → Fin N → k))
  haveI : TotallyDisconnectedSpace (GL (Fin N) k) :=
    ⟨(isTotallyDisconnected_of_image (f := fun g : GL (Fin N) k => g.val)
      GlobalTheory.SplitFlip.isEmbedding_val_GL.continuous.continuousOn
      GlobalTheory.SplitFlip.isEmbedding_val_GL.injective (isTotallyDisconnected_of_totallyDisconnectedSpace _))⟩
  obtain ⟨M, -, -, hMU, hnorm, hfin⟩ :=
    exists_normal_subgroup (K := KO k (Fin N)) GlobalTheory.SplitFlip.isCompact_KO GlobalTheory.SplitFlip.isOpen_KO hU
  haveI : (M.subgroupOf (KO k (Fin N))).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have h2 : (M.subgroupOf (KO k (Fin N))).comap (Subgroup.inclusion hK) = M.subgroupOf K := by
    ext g
    simp [Subgroup.mem_subgroupOf]
  haveI : (M.subgroupOf K).FiniteIndex := by
    rw [← h2]
    refine ⟨?_⟩
    rw [Subgroup.index_comap]
    exact (inferInstance : (((M.subgroupOf (KO k (Fin N))).subgroupOf
      (Subgroup.inclusion hK).range).FiniteIndex)).index_ne_zero
  haveI : Finite (K ⧸ M.subgroupOf K) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (K ⧸ M.subgroupOf K) := Fintype.ofFinite _
  have h0 := hUz M hMU (fun g hg n hn => hnorm g (hK hg) n hn) inferInstance
  rw [map_sub, cosetSum_of_mem π (v := y) hy, sub_eq_zero, cosetSum_apply] at h0
  have h1 := congrArg f h0
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_smul] at h1
  have h3 : ∀ q : K ⧸ M.subgroupOf K, f (π ((Quotient.out q : K) : GL (Fin N) k) x) = f x :=
    fun q => hf _ (Quotient.out q).2
  simp only [h3, Finset.sum_const, Finset.card_univ, smul_eq_mul, nsmul_eq_mul] at h1
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero) h1

abbrev idl (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) : Ideal 𝒪[k] := Ideal.span {unif k ^ m}

theorem isUnit_of_sub_one_mem {m : ℕ} (hm : 1 ≤ m) (s : 𝒪[k]) (hs : s - 1 ∈ idl k m) : IsUnit s := by
  by_contra hu
  have hmax : s ∈ IsLocalRing.maximalIdeal 𝒪[k] := hu
  have hpow : unif k ^ m ∈ IsLocalRing.maximalIdeal 𝒪[k] :=
    Ideal.pow_mem_of_mem _ (show unif k ∈ IsLocalRing.maximalIdeal 𝒪[k] from irreducible_unif.not_isUnit)
      m (by omega)
  have hle : idl k m ≤ IsLocalRing.maximalIdeal 𝒪[k] := (Ideal.span_singleton_le_iff_mem _).mpr hpow
  have h1m : (1 : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    have := Ideal.sub_mem _ hmax (hle hs)
    simpa using this
  exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal 𝒪[k]).ne_top h1m

theorem exists_mem_Km {N m : ℕ} (hm : 1 ≤ m) (A : Matrix (Fin N) (Fin N) 𝒪[k])
    (hA : CongOne (idl k m) A) :
    ∃ g ∈ Km k N m, g.val = A.map (algebraMap 𝒪[k] k) := by
  have hred : A.map (Ideal.Quotient.mk (idl k m)) = 1 := by
    ext i j
    have h := (Ideal.Quotient.eq (I := idl k m)).2 (hA i j)
    rw [Matrix.map_apply, h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : IsUnit A.det := by
    refine isUnit_of_sub_one_mem hm _ ?_
    refine (Ideal.Quotient.eq (I := idl k m)).1 ?_
    have := RingHom.map_det (Ideal.Quotient.mk (idl k m)) A
    rw [this, map_one]
    have e : (Ideal.Quotient.mk (idl k m)).mapMatrix A = 1 := hred
    rw [e, Matrix.det_one]
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (Matrix.GeneralLinearGroup.mk'' A hdet),
    ⟨Matrix.GeneralLinearGroup.mk'' A hdet, ?_, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  exact Units.ext hred

theorem exists_cong_of_mem_Km {N m : ℕ} {g : GL (Fin N) k} (hg : g ∈ Km k N m) :
    ∃ A : Matrix (Fin N) (Fin N) 𝒪[k], CongOne (idl k m) A ∧ g.val = A.map (algebraMap 𝒪[k] k) := by
  obtain ⟨h, hh, rfl⟩ := hg
  refine ⟨h.val, fun i j => ?_, rfl⟩
  have h1 : (Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (idl k m)) h).val = 1 := by
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hh
    rw [hh]; rfl
  have h2 := congrFun (congrFun h1 i) j
  refine (Ideal.Quotient.eq (I := idl k m)).1 ?_
  refine Eq.trans h2 ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem diagPow_val (N : ℕ) (a : Fin N → ℤ) :
    (diagPow k N a).val = Matrix.diagonal (fun i => (algebraMap 𝒪[k] k (unif k)) ^ (a i)) := by
  ext i j
  simp [diagPow, unifU, Matrix.diagonal_apply]

theorem diagPow_add (N : ℕ) (a b : Fin N → ℤ) :
    diagPow k N (a + b) = diagPow k N a * diagPow k N b := by
  have h0 : algebraMap 𝒪[k] k (unif k) ≠ 0 := (unifU k).ne_zero
  apply Units.ext
  rw [Units.val_mul, diagPow_val, diagPow_val, diagPow_val, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  simp [zpow_add₀ h0]

theorem exists_split {N m : ℕ} (hm : 1 ≤ m) {a b : Fin N → ℤ} (ha : Antitone a) (hb : Antitone b)
    {g : GL (Fin N) k} (hg : g ∈ Km k N m) :
    ∃ p ∈ Km k N m, ∃ l ∈ Km k N m, ∃ q ∈ Km k N m, ∃ r ∈ Km k N m,
      g = p * l ∧ diagPow k N a * p = q * diagPow k N a ∧ l * diagPow k N b = diagPow k N b * r := by
  have h0 : algebraMap 𝒪[k] k (unif k) ≠ 0 := (unifU k).ne_zero
  obtain ⟨A, hA, hgA⟩ := exists_cong_of_mem_Km hg
  obtain ⟨U, L, hU, hL, hUt, hLt, rfl⟩ := exists_upper_lower _ (isUnit_of_sub_one_mem hm) N A hA
  obtain ⟨Vq, hVq, hVe⟩ := conj_upper (K := k) (unif k) h0 a ha U hU hUt
  obtain ⟨Wr, hWr, hWe⟩ := conj_lower (K := k) (unif k) h0 b hb L hL hLt
  obtain ⟨p, hp, hpv⟩ := exists_mem_Km hm U hU
  obtain ⟨l, hl, hlv⟩ := exists_mem_Km hm L hL
  obtain ⟨q, hq, hqv⟩ := exists_mem_Km hm Vq hVq
  obtain ⟨r, hr, hrv⟩ := exists_mem_Km hm Wr hWr
  refine ⟨p, hp, l, hl, q, hq, r, hr, Units.ext ?_, Units.ext ?_, Units.ext ?_⟩
  · rw [hgA, Units.val_mul, hpv, hlv, Matrix.map_mul]
  · rw [Units.val_mul, Units.val_mul, hpv, hqv, diagPow_val, hVe]
  · rw [Units.val_mul, Units.val_mul, hlv, hrv, diagPow_val, hWe]

theorem Km_le_KO (N m : ℕ) : Km k N m ≤ KO k (Fin N) := by
  rintro _ ⟨h, -, rfl⟩
  exact ⟨h, rfl⟩

theorem isHeckeOp_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.PRep.IsSmooth π → ∀ m : ℕ, 1 ≤ m → ∀ (a b : Fin N → ℤ), Antitone a → Antitone b → ∀ (T T' : Module.End ℂ (fixed π (Zls.Km k N m))), Zls.IsHeckeOp π m (Zls.diagPow k N a) T → Zls.IsHeckeOp π m (Zls.diagPow k N b) T' → Zls.IsHeckeOp π m (Zls.diagPow k N (a + b)) (T * T') := by
  intro k _ _ _ _ N V _ _ π hπ m hm a b ha hb T T' hT hT' v l hl
  have hfix : ∀ (w : fixed π (Km k N m)), ∀ g ∈ Km k N m, π g (w : V) = w := by
    intro w g hg
    have := w.2 ⟨g, hg⟩
    simpa using this
  have hlg : ∀ g ∈ Km k N m, ∀ u, l (π g u) = l u := fun g hg u =>
    congrArg (fun t : Module.Dual ℂ V => t u) (hl g hg)
  have key := eq_of_orbit_const π hπ (Km_le_KO N m) (x := π (diagPow k N b) (v : V))
    (y := ((T' v : fixed π (Km k N m)) : V)) (hfix _)
    (fun l' hl' => hT' v l' hl') (l ∘ₗ π (diagPow k N a)) (by
      intro g hg
      obtain ⟨p, hp, l0, hl0, q, hq, r, hr, rfl, e1, e2⟩ := exists_split hm ha hb hg
      simp only [LinearMap.comp_apply]
      calc l (π (diagPow k N a) (π (p * l0) (π (diagPow k N b) (v : V))))
          = l (π (diagPow k N a * p * (l0 * diagPow k N b)) (v : V)) := by
            simp only [map_mul, Module.End.mul_apply]
        _ = l (π q (π (diagPow k N a) (π (diagPow k N b) (π r (v : V))))) := by
            rw [e1, e2]
            simp only [map_mul, Module.End.mul_apply]
        _ = l (π (diagPow k N a) (π (diagPow k N b) (v : V))) := by
            rw [hlg q hq, hfix v r hr])
  simp only [LinearMap.comp_apply] at key
  rw [diagPow_add, map_mul, Module.End.mul_apply, key]
  exact hT (T' v) l hl

end GlobalTheory.CompanionTheory.HeckeOpMul

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundFacts
section
noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.HbBasis

open PositivityTheory.RgTw (Mat hb)
open PositivityTheory.RgBcC
open PositivityTheory.RgBcC.LfSt

variable {n : ℕ}

theorem sum_single_one : ∑ a : Fin n, (Matrix.single a a (1 : ℂ) : Mat n) = 1 := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.single_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [Matrix.one_apply_ne h]
    refine Finset.sum_eq_zero fun x _ => if_neg fun hx => h (hx.1.symm.trans hx.2)

theorem sqrt_two_inv_sq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 :=
  GlobalTheory.CompanionTheory.TopClass.sqrt_two_inv_sq

theorem hb_mul_self (a b : Fin n) :
    (hb (a, b) : Mat n) * hb (a, b) = (1 / 2 : ℂ) • (Matrix.single a a 1 + Matrix.single b b 1) := by
  have hs := sqrt_two_inv_sq
  by_cases h : a = b
  · subst h
    have : (hb (a, a) : Mat n) = Matrix.single a a 1 := by simp [hb]
    rw [this, Matrix.single_mul_single_same, ← two_smul ℂ, smul_smul]
    norm_num
  · have hne : b ≠ a := fun e => h e.symm
    by_cases h' : a < b
    · have : (hb (a, b) : Mat n) = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) • (Matrix.single a b 1 + Matrix.single b a 1) := by
        simp [hb, h, h']
      rw [this, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne _ _ _ _ hne, Matrix.single_mul_single_of_ne _ _ _ _ h]
      simp [add_comm]
    · have : (hb (a, b) : Mat n) =
          (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I) • (Matrix.single a b 1 - Matrix.single b a 1) := by
        simp [hb, h, h']
      have hc : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I) = -(1 / 2) := by
        calc _ = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (Complex.I * Complex.I) := by ring
          _ = _ := by rw [hs, Complex.I_mul_I]; ring
      rw [this, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne _ _ _ _ hne, Matrix.single_mul_single_of_ne _ _ _ _ h]
      simp only [mul_one, sub_zero, zero_sub, neg_smul, smul_neg, smul_sub, smul_add]
      abel

theorem sum_hb_mul_self : ∑ p, (hb p : Mat n) * hb p = (n : ℂ) • 1 := by
  rw [Fintype.sum_prod_type]
  simp only [hb_mul_self, ← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, sum_single_one]
  rw [← Nat.cast_smul_eq_nsmul ℂ n (1 : Mat n), ← two_smul ℂ, smul_smul, smul_smul]
  norm_num

theorem coords_one (p : Fin n × Fin n) : ((coords (1 : Mat n) p : ℝ) : ℂ) = (hb p : Mat n).trace := by
  have := GlobalTheory.CompanionTheory.ConeLin.re_trace (1 : Mat n) (by simp) p
  simpa [coords] using this

theorem hOf_coords {H : Mat n} (hH : H.IsHermitian) : hOf (coords H) = H :=
  GlobalTheory.CompanionTheory.ConeLin.hOf_re H hH

theorem coords_hOf (v : Fin n × Fin n → ℝ) : coords (hOf v) = v := by
  funext q
  have : (hOf v * hb q).trace = (v q : ℂ) := by
    classical
    simp [hOf, Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul,
      GlobalTheory.CompanionTheory.TopClass.trace_hb_mul_hb]
  simp [coords, this]

theorem hOf_isHermitian (v : Fin n × Fin n → ℝ) : (hOf v).IsHermitian :=
  GlobalTheory.CompanionTheory.ConeLin.hOf_herm v

theorem sum_trace_smul_hb : ∑ p, (hb p : Mat n).trace • hb p = 1 := by
  have h := hOf_coords (H := (1 : Mat n)) Matrix.isHermitian_one
  simpa only [hOf, coords_one] using h

theorem oPt_mem_cone : oPt n ∈ cone n := by
  show (hOf (coords (1 : Mat n))).PosDef
  rw [hOf_coords Matrix.isHermitian_one]
  exact Matrix.PosDef.one

theorem hbFacts : HbFacts := fun _ =>
  ⟨GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose, GlobalTheory.CompanionTheory.TopClass.trace_hb_mul_hb, fun _ hH => hOf_coords hH,
    coords_hOf, hOf_isHermitian, sum_hb_mul_self, sum_trace_smul_hb, oPt_mem_cone⟩

end GlobalTheory.CompanionTheory.HbBasis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactKm
section
open Filter Topology ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.KmTop

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_Km_iff (N m : ℕ) (g : GL (Fin N) k) :
    g ∈ Zls.Km k N m ↔ g ∈ KO k (Fin N) ∧
      ∀ i j, ((Zls.unifU k : k) ^ m)⁻¹ * (g.val i j - (1 : Matrix (Fin N) (Fin N) k) i j) ∈ 𝒪[k] := by
  have ha : ((Zls.unifU k : k) ^ m) = algebraMap 𝒪[k] k (Zls.unif k ^ m) := by
    simp [Zls.unifU]
  have ha0 : ((Zls.unifU k : k) ^ m) ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, fun i j => ?_⟩
    have h1 : Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}) (u.val i j) =
        Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}) ((1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j) := by
      have h2 := congrArg (fun w => w.val i j) (MonoidHom.mem_ker.1 hu)
      simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at h2
      rw [h2, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1)
    have h3 : (Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) u).val i j -
        (1 : Matrix (Fin N) (Fin N) k) i j = algebraMap 𝒪[k] k (c * Zls.unif k ^ m) := by
      rw [hc, map_sub]
      simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [h3, map_mul, ← ha, mul_comm (algebraMap 𝒪[k] k c), inv_mul_cancel_left₀ ha0]
    exact c.2
  · rintro ⟨⟨u, rfl⟩, h⟩
    refine ⟨u, MonoidHom.mem_ker.2 ?_, rfl⟩
    refine Units.ext ?_
    ext i j
    have h1 := h i j
    let c : 𝒪[k] := ⟨_, h1⟩
    have h2 : algebraMap 𝒪[k] k (u.val i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j) =
        algebraMap 𝒪[k] k (c * Zls.unif k ^ m) := by
      rw [map_mul, ← ha, map_sub]
      show _ = ((Zls.unifU k : k) ^ m)⁻¹ * _ * _
      rw [mul_comm, mul_inv_cancel_left₀ ha0]
      simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h3 := IsFractionRing.injective 𝒪[k] k h2
    have h4 : Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}) (u.val i j) =
        Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}) ((1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j) :=
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨c, h3.symm⟩)
    simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one]
    rw [h4, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem continuous_entry (N m : ℕ) (i j : Fin N) :
    Continuous fun g : GL (Fin N) k =>
      ((Zls.unifU k : k) ^ m)⁻¹ * (g.val i j - (1 : Matrix (Fin N) (Fin N) k) i j) := by
  have h : Continuous fun g : GL (Fin N) k => g.val i j :=
    (continuous_id.matrix_elem i j).comp Units.continuous_val
  exact continuous_const.mul (h.sub continuous_const)

theorem coe_Km_eq (N m : ℕ) : (Zls.Km k N m : Set (GL (Fin N) k)) =
    (KO k (Fin N) : Set (GL (Fin N) k)) ∩ ⋂ i, ⋂ j, (fun g : GL (Fin N) k =>
      ((Zls.unifU k : k) ^ m)⁻¹ * (g.val i j - (1 : Matrix (Fin N) (Fin N) k) i j)) ⁻¹' (𝒪[k] : Set k) := by
  ext g
  simp only [SetLike.mem_coe, mem_Km_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]

theorem isOpen_Km (N m : ℕ) : IsOpen (Zls.Km k N m : Set (GL (Fin N) k)) := by
  rw [coe_Km_eq]
  exact GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    GlobalTheory.SplitWeil.Model.isOpen_int.preimage (continuous_entry N m i j))

theorem isCompact_Km (N m : ℕ) : IsCompact (Zls.Km k N m : Set (GL (Fin N) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  rw [coe_Km_eq]
  refine GlobalTheory.SplitFlip.isCompact_KO.inter_right (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
  exact (GlobalTheory.SplitWeil.Model.isCompact_int.isClosed).preimage (continuous_entry N m i j)

end GlobalTheory.CompanionTheory.KmTop
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityNeZeroSubquotient
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JmSub

theorem exists_subQuot_of_jm_ne_zero :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin N) k) V), Zc.jm x hd π ≠ 0 →
      ∃ S T : Subrepresentation (GlobalTheory.SmGL.jac (stdBlocks (fun a => (x a).1) hd) π),
        Nonempty ((subQuot S T).Equiv (piTensor fun a => (x a).rep)) := by
  intro k _ _ _ _ h N x hd V _ _ π hjm
  obtain ⟨r, hr, hpos⟩ : ∃ r, GlobalTheory.SmGL.OccursTimes (GlobalTheory.SmGL.piTensor fun a => (x a).rep)
      (GlobalTheory.SmGL.jac (GlobalTheory.SmGL.stdBlocks (fun a => (x a).1) hd) π) r ∧ 0 < r := by
    by_contra hcon
    apply hjm
    unfold Zc.jm GlobalTheory.SmGL.jhMult
    refine le_antisymm (iSup_le fun r => iSup_le fun hr' => ?_) zero_le
    have hr0 : r = 0 := by
      by_contra hne
      exact hcon ⟨r, hr', Nat.pos_of_ne_zero hne⟩
    simp [hr0]
  obtain ⟨S, T, -, -, hST⟩ := hr
  exact ⟨S ⟨0, hpos⟩, T ⟨0, hpos⟩, hST ⟨0, hpos⟩⟩

end GlobalTheory.CompanionTheory.JmSub
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastBlockCentralScalarModulusOne
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.ZjScalar

theorem sum_card_mul_modExp {h : ℕ} (d : Fin h → ℕ) :
    ∑ a, (d a : ℤ) * modExp (fun a => Fin (d a)) a = 0 := by
  simp only [modExp, Fintype.card_fin, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_filter]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : b < a
  · simp [hab, mul_comm]
  · simp [hab]

theorem prod_zpow_eq {ι : Type} (s : Finset ι) (x : ℝ) (hx : x ≠ 0) (f : ι → ℤ) :
    ∏ a ∈ s, x ^ f a = x ^ ∑ a ∈ s, f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem zj_last {h : ℕ} (d : Fin h → ℕ) (t : kˣ) (j : Fin h) (hj : j.val + 1 = h) (a : Fin h) :
    Zl.JC.zj d t j a = Matrix.GeneralLinearGroup.scalar (Fin (d a)) t := by
  have : a ≤ j := by
    have := a.2
    exact Fin.le_def.2 (by omega)
  simp [Zl.JC.zj, this]

theorem nabs_det_zj_last {h : ℕ} (d : Fin h → ℕ) (t : kˣ) (j : Fin h) (hj : j.val + 1 = h) (a : Fin h) :
    nabs k (Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a)) = nabs k t ^ (d a) := by
  rw [zj_last d t j hj a]
  have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) = t ^ (d a) := by
    ext
    simp [Matrix.GeneralLinearGroup.scalar]
  rw [this]
  simp [nabs]

theorem zj_last_scalar_modulus (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h)
    (hj : j.val + 1 = h) :
    leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) = Matrix.GeneralLinearGroup.scalar (Fin N) t ∧
      modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) = 1 := by
  constructor
  · apply Units.ext
    ext p q
    obtain ⟨⟨a, x⟩, rfl⟩ := (stdBlocks d hd).surjective p
    obtain ⟨⟨b, y⟩, rfl⟩ := (stdBlocks d hd).surjective q
    by_cases hab : a = b
    · subst hab
      rw [leviEmb_apply_same, zj_last d t j hj a]
      by_cases hxy : x = y
      · subst hxy
        simp [Matrix.GeneralLinearGroup.scalar]
      · have : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨a, y⟩ := fun e => hxy (by simpa using (stdBlocks d hd).injective e)
        simp [Matrix.GeneralLinearGroup.scalar, hxy, this]
    · have : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨b, y⟩ := fun e =>
        hab (congrArg Sigma.fst ((stdBlocks d hd).injective e))
      rw [leviEmb_apply_ne k _ _ hab]
      simp [Matrix.GeneralLinearGroup.scalar, this]
  · have hx : nabs k t ≠ 0 := (nabs_pos' k t).ne'
    simp only [modulus, nabs_det_zj_last d t j hj]
    have : ∀ a, (nabs k t ^ d a) ^ modExp (fun a => Fin (d a)) a =
        nabs k t ^ ((d a : ℤ) * modExp (fun a => Fin (d a)) a) := fun a => by
      rw [zpow_mul, zpow_natCast]
    simp only [this]
    rw [prod_zpow_eq _ _ hx, sum_card_mul_modExp, zpow_zero]

end GlobalTheory.CompanionTheory.ZjScalar
end

