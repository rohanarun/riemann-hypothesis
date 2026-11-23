module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0647
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerOComponents
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.PeriodComp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem apply_smul (x : HomE E a b) (s : 𝓞 E) (y : Sp E a) : x (s • y) = s • x y := x.map_smul_of_tower s y

theorem exists_common (S : Submonoid (𝓞 E)) {N : Submodule (𝓞 E) (Sp E a)} (hN : N.FG) (N' : Submodule (𝓞 E) (Sp E b))
    (x : HomE E a b) (h : ∀ y ∈ N, ∃ s ∈ S, s • x y ∈ N') : ∃ s ∈ S, s • x ∈ homO N N' := by
  classical
  obtain ⟨T, hT⟩ := hN
  have hgen : ∀ y ∈ T, ∃ s ∈ S, s • x y ∈ N' := fun y hy =>
    h y (hT ▸ Submodule.subset_span (Finset.mem_coe.mpr hy))
  choose! f hfS hf using hgen
  refine ⟨∏ y ∈ T, f y, prod_mem fun y hy => hfS y hy, ?_⟩
  intro y hy
  rw [← hT] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rw [LinearMap.smul_apply, ← Finset.mul_prod_erase T f (Finset.mem_coe.mp hy), mul_comm, mul_smul]
    exact N'.smul_mem _ (hf y (Finset.mem_coe.mp hy))
  | zero => rw [map_zero]; exact N'.zero_mem
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact N'.add_mem hy hz
  | smul r y _ hy => rw [GlobalTheory.ThetaMove.PeriodComp.apply_smul]; exact N'.smul_mem r hy

theorem smul_mem_perO {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {r : E} (hr : r ∈ AA) {x : HomE E a b} (hx : x ∈ homO N N') : r • x ∈ perO AA N N' :=
  Submodule.subset_span ⟨r, hr, x, hx, rfl⟩

theorem mono (AA : Submodule (𝓞 E) E) (Q : HeightOneSpectrum (𝓞 E)) (N₁ N₂ : Submodule (𝓞 E) (Sp E a))
    (N₁' N₂' : Submodule (𝓞 E) (Sp E b)) (hN : N₂.FG) (h : localization₂ Q.asIdeal N₂ ≤ localization₂ Q.asIdeal N₁)
    (h' : localization₂ Q.asIdeal N₁' ≤ localization₂ Q.asIdeal N₂') :
    localization₂ Q.asIdeal (perO AA N₁ N₁') ≤ localization₂ Q.asIdeal (perO AA N₂ N₂') := by
  have hgen : perO AA N₁ N₁' ≤ localization₂ Q.asIdeal (perO AA N₂ N₂') := by
    apply Submodule.span_le.mpr
    rintro _ ⟨r, hr, x, hx, rfl⟩
    have hmult : ∀ y ∈ N₂, ∃ s ∈ Q.asIdeal.primeCompl, s • x y ∈ N₂' := by
      intro y hy
      obtain ⟨u, hu, huy⟩ := h (mem_localization_of_mem Q hy)
      have hxy : x (u • y) ∈ N₁' := hx _ huy
      rw [GlobalTheory.ThetaMove.PeriodComp.apply_smul] at hxy
      obtain ⟨v, hv, hvxy⟩ := h' (mem_localization_of_mem Q hxy)
      exact ⟨v * u, mul_mem hv hu, by rw [mul_smul]; exact hvxy⟩
    obtain ⟨t, ht, htx⟩ := GlobalTheory.ThetaMove.PeriodComp.exists_common Q.asIdeal.primeCompl hN N₂' x hmult
    exact ⟨t, ht, by rw [smul_comm]; exact GlobalTheory.ThetaMove.PeriodComp.smul_mem_perO hr htx⟩
  calc localization₂ Q.asIdeal (perO AA N₁ N₁') ≤ localization₂ Q.asIdeal (localization₂ Q.asIdeal (perO AA N₂ N₂')) :=
        localization_mono Q hgen
    _ = localization₂ Q.asIdeal (perO AA N₂ N₂') := localization_localization₂ Q _

theorem eq_homAt (AA : Submodule (𝓞 E) E) (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (hN : N.FG)
    (hA : localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) :
    localization₂ P.asIdeal (perO AA N N') = homAt {P} N N' := by
  apply le_antisymm
  · have hgen : perO AA N N' ≤ homAt {P} N N' := by
      apply Submodule.span_le.mpr
      rintro _ ⟨r, hr, x, hx, rfl⟩
      intro P' hP' y hy
      rw [Finset.mem_singleton] at hP'
      subst hP'
      obtain ⟨u, hu, huy⟩ := hy
      have hr1 : r ∈ localization₂ P'.asIdeal (1 : Submodule (𝓞 E) E) := by
        rw [← hA]; exact mem_localization_of_mem P' hr
      obtain ⟨v, hv, hvr⟩ := hr1
      obtain ⟨w, hw⟩ := Submodule.mem_one.mp hvr
      have hxy : u • x y ∈ N' := by
        rw [← GlobalTheory.ThetaMove.PeriodComp.apply_smul]; exact hx _ huy
      refine ⟨v * u, mul_mem hv hu, ?_⟩
      rw [LinearMap.smul_apply, mul_smul, smul_comm u r, ← smul_assoc v r, ← hw, algebraMap_smul]
      exact N'.smul_mem w hxy
    intro z hz
    obtain ⟨s, hs, hsz⟩ := hz
    have h1 := hgen hsz
    intro P' hP' y hy
    obtain ⟨t, ht, hty⟩ := h1 P' hP' y hy
    rw [Finset.mem_singleton] at hP'
    subst hP'
    refine ⟨t * s, mul_mem ht hs, ?_⟩
    rw [mul_smul, ← LinearMap.smul_apply]
    exact hty
  · intro x hx
    have h1 : (1 : E) ∈ localization₂ P.asIdeal AA := by
      rw [hA]; exact mem_localization_of_mem P (Submodule.mem_one.mpr ⟨1, map_one _⟩)
    obtain ⟨v, hv, hv1⟩ := h1
    have hmult : ∀ y ∈ N, ∃ s ∈ P.asIdeal.primeCompl, s • x y ∈ N' := fun y hy =>
      hx P (Finset.mem_singleton_self P) y (mem_localization_of_mem P hy)
    obtain ⟨t, ht, htx⟩ := GlobalTheory.ThetaMove.PeriodComp.exists_common P.asIdeal.primeCompl hN N' x hmult
    refine ⟨v * t, mul_mem hv ht, ?_⟩
    have h2 := GlobalTheory.ThetaMove.PeriodComp.smul_mem_perO hv1 htx
    rwa [smul_one_smul, ← mul_smul] at h2

private theorem exists_nsmul_mem_of_isLattice (N' : Submodule (𝓞 E) (Sp E b)) (hN' : Submodule.IsFullLattice E N') (v : Sp E b) :
    ∃ n : ℕ, 0 < n ∧ (n : 𝓞 E) • v ∈ N' := by
  have hv : v ∈ Submodule.span E (N' : Set (Sp E b)) := by
    let _ : Submodule.IsFullLattice E N' := hN'
    rw [Submodule.IsFullLattice.span_eq_top (A := E) (M := N')]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem w hw => exact ⟨1, one_pos, by rw [Nat.cast_one, one_smul]; exact hw⟩
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact N'.zero_mem⟩
  | add v w _ _ hv hw =>
    obtain ⟨m, hm, hmv⟩ := hv
    obtain ⟨k, hk, hkw⟩ := hw
    refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
    rw [smul_add, Nat.cast_mul]
    refine N'.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N'.smul_mem _ hmv
    · rw [mul_smul]; exact N'.smul_mem _ hkw
  | smul c v _ hv =>
    obtain ⟨m, hm, hmv⟩ := hv
    obtain ⟨y, hy0, hyint⟩ := exists_integral_multiples ℤ ℚ ({c} : Finset E)
    have h1 : IsIntegral ℤ ((y : E) * c) := by
      simpa [zsmul_eq_mul] using hyint c (Finset.mem_singleton_self c)
    have hint : IsIntegral ℤ ((y.natAbs : E) * c) := by
      rcases Int.natAbs_eq y with h | h
      · rw [h] at h1; simpa using h1
      · rw [h] at h1; simpa using h1.neg
    refine ⟨y.natAbs * m, Nat.mul_pos (Int.natAbs_pos.mpr hy0) hm, ?_⟩
    have key : ((y.natAbs * m : ℕ) : 𝓞 E) • (c • v) =
        (⟨(y.natAbs : E) * c, hint⟩ : 𝓞 E) • ((m : 𝓞 E) • v) := by
      ext i
      rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply]
      simp only [smul_eq_mul, Algebra.smul_def, map_natCast]
      push_cast
      have hα : ∀ z : ↥(integralClosure ℤ E), algebraMap (↥(integralClosure ℤ E)) E z = (z : E) :=
        fun _ => rfl
      simp only [hα]
      ring
    rw [key]
    exact N'.smul_mem _ hmv

theorem full (AA : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (hN : N.FG)
    (hN' : Submodule.IsFullLattice E N') (hA : AA ≠ ⊥) : Full (perO AA N N') := by
  obtain ⟨r, hrA, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
  intro x
  let S : Submonoid (𝓞 E) :=
    { carrier := {s | ∃ n : ℕ, 0 < n ∧ (n : 𝓞 E) = s}
      mul_mem' := by
        rintro _ _ ⟨m, hm, rfl⟩ ⟨k, hk, rfl⟩
        exact ⟨m * k, Nat.mul_pos hm hk, by push_cast; rfl⟩
      one_mem' := ⟨1, one_pos, Nat.cast_one⟩ }
  have hmult : ∀ y ∈ N, ∃ s ∈ S, s • (r⁻¹ • x) y ∈ N' := fun y _ => by
    obtain ⟨n, hn, h⟩ := exists_nsmul_mem_of_isLattice N' hN' ((r⁻¹ • x) y)
    exact ⟨n, ⟨n, hn, rfl⟩, h⟩
  obtain ⟨s, hsS, hs⟩ := GlobalTheory.ThetaMove.PeriodComp.exists_common S hN N' (r⁻¹ • x) hmult
  obtain ⟨n, hn, rfl⟩ := hsS
  refine ⟨n, hn, ?_⟩
  have h2 := GlobalTheory.ThetaMove.PeriodComp.smul_mem_perO hrA hs
  rwa [smul_comm r, smul_inv_smul₀ hr0] at h2

theorem perO_components : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (AA : Submodule (𝓞 E) E), (∀ (Q : HeightOneSpectrum (𝓞 E)) (N₁ N₂ : Submodule (𝓞 E) (Sp E a)) (N₁' N₂' : Submodule (𝓞 E) (Sp E b)), N₂.FG → localization₂ Q.asIdeal N₂ ≤ localization₂ Q.asIdeal N₁ → localization₂ Q.asIdeal N₁' ≤ localization₂ Q.asIdeal N₂' → localization₂ Q.asIdeal (perO AA N₁ N₁') ≤ localization₂ Q.asIdeal (perO AA N₂ N₂')) ∧ (∀ (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)), N.FG → localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E) → localization₂ P.asIdeal (perO AA N N') = homAt {P} N N') ∧ ∀ (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)), N.FG → Submodule.IsFullLattice E N' → AA ≠ ⊥ → Full (perO AA N N') := by
  intro E _ _ _ a b AA
  exact ⟨fun Q N₁ N₂ N₁' N₂' hN h h' => GlobalTheory.ThetaMove.PeriodComp.mono AA Q N₁ N₂ N₁' N₂' hN h h',
    fun P N N' hN hA => GlobalTheory.ThetaMove.PeriodComp.eq_homAt AA P N N' hN hA,
    fun N N' hN hN' hA => GlobalTheory.ThetaMove.PeriodComp.full AA N N' hN hN' hA⟩

end GlobalTheory.ThetaMove.PeriodComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticFormIntegralOfSelfDualPeriodLattices
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem int_mul_mem_lamOf (a : 𝓞 D.host.K) {w : ℂ} (hw : w ∈ TaylorLogMetric.lamOf D cc δ) :
    D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ TaylorLogMetric.lamOf D cc δ := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩
    push_cast
    rw [map_mul]
    ring
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [mul_neg]; exact AddSubgroup.neg_mem _ ha

theorem int_smul_mem_La (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (a : 𝓞 D.host.K) {x : TaylorLogMetric.VC D N N'} (hx : x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') :
    D.host.φ₀ (((a : D.host.K) : D.host.E)) • x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L' := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, B, hB, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨_, int_mul_mem_lamOf a hw, B, hB, smul_smul _ _ _⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [smul_neg]; exact AddSubgroup.neg_mem _ ha

theorem qIntAll_of_latAll : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), B.LatAll → B.QIntAll := by
  intro D cc δ B h N N' L L' hA x hx
  have hsd := (h.1 N N' L L' hA).1
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hw := int_smul_mem_La L L' a hx
  rw [ha] at hw
  have hw' : StandardLatticesGL3.w0 D • x ∈ dualLat (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.La D B.tor L L') := by
    rw [hsd]; exact hw
  obtain ⟨m, hm⟩ := hw' x hx
  have him : (TaylorLogMetric.Hf D B.tor x x).im = 0 := by
    have : starRingEnd ℂ (TaylorLogMetric.Hf D B.tor x x) = TaylorLogMetric.Hf D B.tor x x := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [TaylorLogMetric.Hf, map_div₀, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj, mul_comm]
    exact Complex.conj_eq_iff_im.1 this
  have h1 : (StandardLatticesGL3.w0 D).re = 1 / 2 := by simp [StandardLatticesGL3.w0]
  have h2 : (StandardLatticesGL3.w0 D).im = Real.sqrt D.host.d / 2 := by simp [StandardLatticesGL3.w0]
  have h3 : formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N' x x = TaylorLogMetric.Hf D B.tor x x := rfl
  refine ⟨m, ?_⟩
  rw [← hm, altE, LinearMap.map_smul₂, h3, smul_eq_mul, Complex.mul_im, h1, h2, him]
  ring

end GlobalTheory.ThetaMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexEqOfSelfDualAlternating
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.DualCount

theorem relIndex_le_of_selfDual (H : Type) [AddCommGroup H] (ω : H → H → ℝ)
    (Λ₁ Λ₂ : AddSubgroup H) (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z)
    (hanti : ∀ x y, ω x y = -ω y x)
    (h₁ : ∀ x, x ∈ Λ₁ ↔ ∀ y ∈ Λ₁, ∃ n : ℤ, ω x y = n)
    (h₂ : ∀ x, x ∈ Λ₂ ↔ ∀ y ∈ Λ₂, ∃ n : ℤ, ω x y = n)
    (hfin : Λ₁.relIndex Λ₂ ≠ 0) : Λ₂.relIndex Λ₁ ≤ Λ₁.relIndex Λ₂ := by
  classical
  have hadd' : ∀ x y z, ω x (y + z) = ω x y + ω x z := by
    intro x y z
    rw [hanti x (y + z), hadd, hanti x y, hanti x z]; ring
  have hsub : ∀ x y z, ω (x - y) z = ω x z - ω y z := by
    intro x y z
    have := hadd (x - y) y z
    rw [sub_add_cancel] at this
    linarith
  have hint : ∀ r : ℝ, ((r : ℝ) : UnitAddCircle) = 0 ↔ ∃ n : ℤ, r = n := by
    intro r
    rw [AddCircle.coe_eq_zero_iff]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, by simpa using hn.symm⟩
    · rintro ⟨n, hn⟩; exact ⟨n, by simpa using hn.symm⟩
  let φ : H → (Λ₂ →+ UnitAddCircle) := fun x =>
    AddMonoidHom.mk' (fun y => ((ω x y : ℝ) : UnitAddCircle)) (by
      intro a b
      simp only [AddSubgroup.coe_add, hadd', AddCircle.coe_add])
  have hφ : ∀ x : Λ₁, Λ₁.addSubgroupOf Λ₂ ≤ (φ x).ker := by
    intro x y hy
    rw [AddMonoidHom.mem_ker]
    exact (hint _).2 ((h₁ x).1 x.2 y (AddSubgroup.mem_addSubgroupOf.1 hy))
  let ψ : Λ₁ → (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂ →+ UnitAddCircle) := fun x =>
    QuotientAddGroup.lift _ (φ x) (hφ x)
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let χ : Λ₁ → AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) Circle := fun x =>
    (AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom (ψ x)
  have hχ : ∀ a b : Λ₁, χ a = χ b → ((a : H) - b) ∈ Λ₂ := by
    intro a b hab
    rw [h₂]
    intro y hy
    have h := DFunLike.congr_fun hab (QuotientAddGroup.mk ⟨y, hy⟩)
    have h' : AddCircle.toCircle (((ω a y : ℝ)) : UnitAddCircle)
        = AddCircle.toCircle (((ω b y : ℝ)) : UnitAddCircle) := h
    have h'' := AddCircle.injective_toCircle (T := 1) one_ne_zero h'
    rw [← hint, hsub, AddCircle.coe_sub, h'', sub_self]
  haveI hG : Finite (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Nat.finite_of_card_ne_zero hfin
  haveI : Fintype (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Fintype.ofFinite _
  let f : (Λ₁ ⧸ Λ₂.addSubgroupOf Λ₁) → AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ℂ := fun q =>
    AddChar.circleEquivComplex (χ q.out)
  have hf : Function.Injective f := by
    intro p q hpq
    have h := hχ _ _ (AddChar.circleEquivComplex.injective hpq)
    rw [← QuotientAddGroup.out_eq' p, ← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_iff_sub_mem,
      AddSubgroup.mem_addSubgroupOf]
    exact h
  have hle := Nat.card_le_card_of_injective f hf
  have hc : Nat.card (AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ℂ)
      = Nat.card (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  rw [hc] at hle
  exact hle

theorem relIndex_eq_of_selfDual : ∀ (H : Type) [AddCommGroup H] (ω : H → H → ℝ)
    (Λ₁ Λ₂ : AddSubgroup H), (∀ x y z, ω (x + y) z = ω x z + ω y z) → (∀ x y, ω x y = -ω y x) →
    (∀ x, x ∈ Λ₁ ↔ ∀ y ∈ Λ₁, ∃ n : ℤ, ω x y = n) → (∀ x, x ∈ Λ₂ ↔ ∀ y ∈ Λ₂, ∃ n : ℤ, ω x y = n) →
    Λ₁.relIndex Λ₂ ≠ 0 → Λ₂.relIndex Λ₁ ≠ 0 → Λ₁.relIndex Λ₂ = Λ₂.relIndex Λ₁ := by
  intro H _ ω Λ₁ Λ₂ hadd hanti h₁ h₂ f₁ f₂
  exact le_antisymm (relIndex_le_of_selfDual H ω Λ₂ Λ₁ hadd hanti h₂ h₁ f₂)
    (relIndex_le_of_selfDual H ω Λ₁ Λ₂ hadd hanti h₁ h₂ f₁)

end GlobalTheory.MomT.DualCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexEqProdLocP
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove

theorem relIndex_eq_prod_locP (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module (𝓞 E) W]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (M₁ M₂ : Submodule (𝓞 E) W) (h₁ : Full M₁) (h₂ : Full M₂) (hD : Dom S M₁ M₂) :
    M₂.toAddSubgroup.relIndex M₁.toAddSubgroup =
      ∏ P ∈ S, (localization₂ P.asIdeal M₂).toAddSubgroup.relIndex (localization₂ P.asIdeal M₁).toAddSubgroup := by
  classical
  let Q : S → Type := fun P => (localization₂ P.1.asIdeal M₁).toAddSubgroup ⧸
    (localization₂ P.1.asIdeal M₂).toAddSubgroup.addSubgroupOf (localization₂ P.1.asIdeal M₁).toAddSubgroup
  let g : ∀ P : S, M₁.toAddSubgroup →+ Q P := fun P =>
    (QuotientAddGroup.mk' _).comp (AddSubgroup.inclusion (H := M₁.toAddSubgroup) (K := (localization₂ P.1.asIdeal M₁).toAddSubgroup)
      fun x hx => mem_localization_of_mem P.1 hx)
  have hg : ∀ (P : S) (x : M₁.toAddSubgroup) (y : (localization₂ P.1.asIdeal M₁).toAddSubgroup),
      g P x = (QuotientAddGroup.mk y : Q P) ↔ (x : W) - y ∈ localization₂ P.1.asIdeal M₂ := by
    intro P x y
    exact QuotientAddGroup.eq_iff_sub_mem
  let f : M₁.toAddSubgroup →+ ∀ P : S, Q P := AddMonoidHom.pi g
  have hker : f.ker = M₂.toAddSubgroup.addSubgroupOf M₁.toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, funext_iff]
    constructor
    · intro h
      refine mem_of_locP fun P => ?_
      by_cases hP : P ∈ S
      · simpa using (hg ⟨P, hP⟩ x 0).1 (h ⟨P, hP⟩)
      · exact hD.2 P hP (mem_localization_of_mem P x.2)
    · intro h P
      exact (hg P x 0).2 (by simpa using mem_localization_of_mem P.1 h)
  have hsurj : Function.Surjective f := by
    intro y
    choose x hx using fun P : S => QuotientAddGroup.mk_surjective (y P)
    choose t ht ht' using fun P : S => (h₁.inf h₂).approx {P.1} (x P : W)
    have htM : ∀ P : S, t P ∈ M₁ := fun P => mem_of_locP fun R => by
      by_cases hR : R = P.1
      · subst hR
        have := (localization₂ P.1.asIdeal M₁).add_mem
          (localization_mono P.1 inf_le_left (ht P P.1 (Finset.mem_singleton_self _))) (x P).2
        simpa using this
      · exact localization_mono R inf_le_left (ht' P R (by simpa using hR))
    refine ⟨∑ P : S, ⟨t P, htM P⟩, funext fun P => ?_⟩
    rw [← hx P]
    refine (hg P _ _).2 ?_
    change M₁.toAddSubgroup.subtype (∑ P : S, ⟨t P, htM P⟩) - (x P : W) ∈ _
    rw [map_sum M₁.toAddSubgroup.subtype, ← Finset.add_sum_erase _ _ (Finset.mem_univ P), add_sub_right_comm]
    refine Submodule.add_mem _ (localization_mono P.1 inf_le_right (ht P P.1 (Finset.mem_singleton_self _)))
      (Submodule.sum_mem _ fun R hR => localization_mono P.1 inf_le_right (ht' R P.1 ?_))
    rw [Finset.mem_singleton]
    exact fun e => (Finset.ne_of_mem_erase hR) (Subtype.ext e.symm)
  rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top,
    Nat.card_pi, ← Finset.prod_coe_sort S]
  rfl

end GlobalTheory.ThetaMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RhoVrBrAtEqBrStd
section
noncomputable section

namespace GlobalTheory.BranchBlock

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem isBlock_of_mulVec' {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1) {A' : Matrix (Fin N) (Fin N) E}
    {A : Matrix (Fin n) (Fin n) E} {c : E} (h1 : ∀ x, iniH hN (A' *ᵥ x) = A *ᵥ iniH hN x)
    (h2 : ∀ x, (A' *ᵥ x) (Br.iL hN) = c * x (Br.iL hN)) : BranchFormula.IsBlock hN A' A c := by
  have hne : ∀ a : Fin n, Br.iC hN a ≠ Br.iL hN := fun a h => absurd (congrArg Fin.val h) a.2.ne
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · have h := congrFun (h1 (Pi.single (Br.iC hN b) 1)) a
    have e : iniH hN (Pi.single (Br.iC hN b) (1 : E)) = Pi.single b 1 := funext fun i => by
      simp only [iniH, Pi.single_apply, (Br.iC_inj hN).eq_iff]
    rw [e, mulVec_single_one, mulVec_single_one] at h
    exact h
  · have h := congrFun (h1 (Pi.single (Br.iL hN) 1)) a
    have e : iniH hN (Pi.single (Br.iL hN) (1 : E)) = 0 := funext fun i => Pi.single_eq_of_ne (hne i) _
    rw [e, mulVec_single_one, mulVec_zero] at h
    exact h
  · have h := h2 (Pi.single (Br.iC hN a) 1)
    rw [mulVec_single_one, Pi.single_eq_of_ne (hne a).symm, mul_zero] at h
    exact h
  · have h := h2 (Pi.single (Br.iL hN) 1)
    rw [mulVec_single_one, Pi.single_eq_same, mul_one] at h
    exact h

theorem rhoVr_brAt_eq_brStd : ∀ {E K ι : Type} [Field E] [Field K] [CharZero K] [Fintype ι] (emb : ι → E →+* K) {N n : ℕ}
    (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n), (∀ τ, Br.Interlace hN (lam τ) (sg τ)) →
    (∀ τ, Br.SameShift (lam τ) (sg τ)) → ∀ (t : E) (B' : GL (Fin n) E) (B : GL (Fin N) E),
    (∀ x, iniH hN ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) = (B' : Matrix (Fin n) (Fin n) E) *ᵥ iniH hN x) →
    (∀ x, t * ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) (Br.iL hN) = x (Br.iL hN)) →
    ∀ G : Formalism.L2.DIV.VV K lam, rhoVr emb sg B'⁻¹ (Br.brAt hN lam sg (fun τ => emb τ t) G) =
      Br.brStd hN lam sg (rhoVr emb lam B⁻¹ G) := by
  intro E K ι _ _ _ _ emb N n hN lam sg hI hS t B' B h1 h2 G
  have ht : t ≠ 0 := by
    intro h0
    have h := h2 (Pi.single (Br.iL hN) 1)
    rw [h0, zero_mul, Pi.single_eq_same] at h
    exact zero_ne_one h
  have hBA : ∀ x, (B : Matrix (Fin N) (Fin N) E) *ᵥ (((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x) = x := by
    intro x
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hAB : ∀ y, ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ((B' : Matrix (Fin n) (Fin n) E) *ᵥ y) = y := by
    intro y
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hblk : BranchFormula.IsBlock hN ((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)
      ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) t := by
    refine isBlock_of_mulVec' hN (fun x => ?_) (fun x => ?_)
    · have h := h1 (((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x)
      rw [hBA] at h
      rw [h, hAB]
    · have h := h2 (((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x)
      rw [hBA] at h
      exact h.symm
  have e1 : ∀ {m : ℕ} (g : GL (Fin m) E) (τ : ι) (a b : Fin m),
      ((invTrK (embGL emb g) τ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) a b =
        emb τ (((g⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) b a) := fun g τ a b => rfl
  have key := BranchFormula.brAt_eq_pullback hN hI hS (invTrK (embGL emb B')) (invTrK (embGL emb B))
    (fun τ => emb τ t) (fun τ => (map_ne_zero _).2 ht) (fun τ => by
      refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩ <;> simp only [e1]
      · rw [hblk.1]
      · rw [(hblk.2.1 a).2, map_zero]
      · rw [(hblk.2.1 a).1, map_zero]
      · rw [hblk.2.2]) G
  show rhoK sg (invTrK (embGL emb B'⁻¹)) _ = Br.brStd hN lam sg (rhoK lam (invTrK (embGL emb B⁻¹)) G)
  rw [map_inv (embGL emb), map_inv (embGL emb), map_inv invTrK, map_inv invTrK]
  exact key.symm

end GlobalTheory.BranchBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitOfConjPNe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove

theorem split_of_conj_ne₂ : ∀ (X : Fields) (P : HeightOneSpectrum (𝓞 X.E)) (v : HeightOneSpectrum (𝓞 X.F)),
    X.Ok → conjPrime₂ P ≠ P → P.asIdeal.under (𝓞 X.F) = v.asIdeal →
    Ideal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) v.asIdeal = P.asIdeal * (conjPrime₂ P).asIdeal ∧
    ∀ Q : HeightOneSpectrum (𝓞 X.E), Q.asIdeal.under (𝓞 X.F) = v.asIdeal ↔ (Q = P ∨ Q = conjPrime₂ P) := by
  intro X P v hX hP hv
  obtain rfl : P.under (𝓞 X.F) = v := HeightOneSpectrum.ext hv
  have key := GlobalTheory.MuConj.mem_above_iff hX.star_F hX.rankE P hP
  refine ⟨GlobalTheory.Mem.GoodPlace.map_eq_mul hX.rankE hP.symm ((key _).2 (Or.inr rfl)), fun Q => ?_⟩
  rw [← key Q]
  exact ⟨fun h => HeightOneSpectrum.ext h, fun h => congrArg HeightOneSpectrum.asIdeal h⟩

end GlobalTheory.ThetaMove
end

