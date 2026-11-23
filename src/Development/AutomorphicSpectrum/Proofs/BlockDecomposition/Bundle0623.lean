module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0003
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0347
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0393
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0586
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionTwo
section
noncomputable section

namespace GlobalTheory.CompanionTheory.ValuationCompleteness

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr Filter _root_.Topology
open scoped TensorProduct

section Abstract

variable {K A : Type} [NormedField K] [CommRing A] [Algebra K A] {d : ℕ}
  (b : Module.Basis (Fin d) K A) (S : Subring A)

theorem mem_lev_iff (hS : ∀ x, x ∈ S ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {ϖ : K} (h0 : ϖ ≠ 0)
    (hϖ : algebraMap K A ϖ ∈ S) (a : S) (k : ℕ) :
    a ∈ lev (⟨_, hϖ⟩ : S) k ↔ ∀ i, ‖b.repr (a : A) i‖ ≤ ‖ϖ‖ ^ k := by
  have hpow : ∀ c : A, c * (algebraMap K A ϖ) ^ k = ϖ ^ k • c := by
    intro c
    rw [← map_pow, Algebra.smul_def, mul_comm]
  have hcoe : ∀ c : S, ((c * (⟨_, hϖ⟩ : S) ^ k : S) : A) = ϖ ^ k • (c : A) := by
    intro c
    rw [← hpow]
    rfl
  constructor
  · intro ha i
    rw [lev, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, hc⟩ := ha
    have hc' : (a : A) = ϖ ^ k • (c : A) := by
      rw [← hc, hcoe]
    rw [hc', map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_pow]
    have hci := (hS c).1 c.2 i
    calc ‖ϖ‖ ^ k * ‖b.repr (c : A) i‖ ≤ ‖ϖ‖ ^ k * 1 := by gcongr
      _ = ‖ϖ‖ ^ k := mul_one _
  · intro ha
    rw [lev, Ideal.mem_span_singleton']
    have hpos : 0 < ‖ϖ‖ ^ k := pow_pos (norm_pos_iff.mpr h0) k
    have hcS : (ϖ ^ k)⁻¹ • (a : A) ∈ S := by
      rw [hS]
      intro i
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_inv, norm_pow,
        inv_mul_le_iff₀ hpos, mul_one]
      exact ha i
    refine ⟨⟨_, hcS⟩, ?_⟩
    apply Subtype.ext
    rw [hcoe]
    change ϖ ^ k • ((ϖ ^ k)⁻¹ • (a : A)) = (a : A)
    rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero k h0), one_smul]

theorem separated (hS : ∀ x, x ∈ S ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {ϖ : K} (h0 : ϖ ≠ 0) (h1 : ‖ϖ‖ < 1)
    (hϖ : algebraMap K A ϖ ∈ S) (a : S) (h : ∀ k, a ∈ lev (⟨_, hϖ⟩ : S) k) : a = 0 := by
  have hi : ∀ i, b.repr (a : A) i = 0 := by
    intro i
    have hle : ∀ k : ℕ, ‖b.repr (a : A) i‖ ≤ ‖ϖ‖ ^ k :=
      fun k => (mem_lev_iff b S hS h0 hϖ a k).1 (h k) i
    have ht : Tendsto (fun k : ℕ => ‖ϖ‖ ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h1
    exact norm_le_zero_iff.mp (ge_of_tendsto' ht hle)
  have hr : b.repr (a : A) = 0 := by
    ext i
    exact hi i
  have ha : (a : A) = 0 := (LinearEquiv.map_eq_zero_iff b.repr).mp hr
  exact_mod_cast ha

variable [CompleteSpace K] [IsUltrametricDist K]

theorem complete (hS : ∀ x, x ∈ S ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {ϖ : K} (h0 : ϖ ≠ 0) (h1 : ‖ϖ‖ < 1)
    (hϖ : algebraMap K A ϖ ∈ S) (f : ℕ → S) (hf : ∀ k, f (k + 1) - f k ∈ lev (⟨_, hϖ⟩ : S) k) :
    ∃ a, ∀ k, a - f k ∈ lev (⟨_, hϖ⟩ : S) k := by
  set x : ℕ → Fin d → K := fun k i => b.repr (f k : A) i with hx
  have hstep : ∀ k i, ‖x (k + 1) i - x k i‖ ≤ ‖ϖ‖ ^ k := by
    intro k i
    have := (mem_lev_iff b S hS h0 hϖ _ k).1 (hf k) i
    simpa [hx, map_sub] using this
  have hn0 : 0 ≤ ‖ϖ‖ := norm_nonneg _
  have hle1 : ‖ϖ‖ ≤ 1 := le_of_lt h1
  have hfar : ∀ i k m, k ≤ m → ‖x m i - x k i‖ ≤ ‖ϖ‖ ^ k := by
    intro i k m hkm
    induction m, hkm using Nat.le_induction with
    | base => simp
    | succ m hkm ih =>
      have e : x (m + 1) i - x k i = (x (m + 1) i - x m i) + (x m i - x k i) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      exact (hstep m i).trans (pow_le_pow_of_le_one hn0 hle1 hkm)
  have hcau : ∀ i, CauchySeq (fun k => x k i) := by
    intro i
    refine cauchySeq_of_le_geometric ‖ϖ‖ 1 h1 (fun n => ?_)
    rw [dist_eq_norm, ← norm_neg, neg_sub, one_mul]
    exact hstep n i
  choose c hc using fun i => cauchySeq_tendsto_of_complete (hcau i)
  have hbd : ∀ i k, ‖c i - x k i‖ ≤ ‖ϖ‖ ^ k := by
    intro i k
    have ht : Tendsto (fun m => ‖x m i - x k i‖) atTop (𝓝 ‖c i - x k i‖) :=
      ((hc i).sub_const _).norm
    refine le_of_tendsto ht ?_
    filter_upwards [eventually_ge_atTop k] with m hm
    exact hfar i k m hm
  set aA : A := b.equivFun.symm c with haA
  have hrep : ∀ i, b.repr aA i = c i := by
    intro i
    rw [← b.equivFun_apply, haA, LinearEquiv.apply_symm_apply]
  have hmem : aA ∈ S := by
    rw [hS]
    intro i
    rw [hrep]
    have e : c i = (c i - x 0 i) + x 0 i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · simpa using hbd i 0
    · exact (hS _).1 (f 0).2 i
  refine ⟨⟨aA, hmem⟩, fun k => ?_⟩
  rw [mem_lev_iff b S hS h0 hϖ]
  intro i
  have e : ((⟨aA, hmem⟩ - f k : S) : A) = aA - (f k : A) := rfl
  rw [e, map_sub, Finsupp.sub_apply, hrep]
  exact hbd i k

end Abstract

theorem q2 : Q2 := by
  intro F E _ _ _ _ _ σ d bs v S σS ϖ hQ hϖ
  obtain ⟨-, -, hSR, -, h0, h1, -, -⟩ := hQ
  have hS : ∀ x, x ∈ S ↔ ∀ i, ‖(Algebra.TensorProduct.basis (Fv F v) bs).repr x i‖ ≤ 1 := by
    intro x
    rw [← SetLike.mem_coe, hSR]
    exact forall_congr' fun i =>
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).trans
        Valued.toNormedField.norm_le_one_iff.symm
  exact ⟨fun a ha => separated _ S hS h0 h1 hϖ a ha, fun f hf => complete _ S hS h0 h1 hϖ f hf⟩

end GlobalTheory.CompanionTheory.ValuationCompleteness

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerNewform
section
noncomputable section

open Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GLnLocal (integralGL mem_integralGL_iff)
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.RankinSelberg

open Ad3 Ad3.R

def lowT {F : Type} [Field F] (a d : Fˣ) (z : F) : GL (Fin 2) F :=
  ⟨!![(a : F), 0; z, (d : F)], !![((a⁻¹ : Fˣ) : F), 0; -z * ((a⁻¹ : Fˣ) : F) * ((d⁻¹ : Fˣ) : F), ((d⁻¹ : Fˣ) : F)],
    by
      have ha := a.ne_zero
      have hd := d.ne_zero
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring,
    by
      have ha := a.ne_zero
      have hd := d.ne_zero
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring⟩

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem lowT_mem {a d : Fˣ} {z : F} (ha : (a : F) ∈ 𝒪[F]) (ha' : ((a⁻¹ : Fˣ) : F) ∈ 𝒪[F])
    (hd : (d : F) ∈ 𝒪[F]) (hd' : ((d⁻¹ : Fˣ) : F) ∈ 𝒪[F]) (hz : z ∈ 𝒪[F]) :
    lowT a d z ∈ integralGL F 2 := by
  have e1 : (lowT a d z : Matrix (Fin 2) (Fin 2) F) = !![(a : F), 0; z, (d : F)] := rfl
  have e2 : ((lowT a d z)⁻¹ : GL (Fin 2) F).val =
      !![((a⁻¹ : Fˣ) : F), 0; -z * ((a⁻¹ : Fˣ) : F) * ((d⁻¹ : Fˣ) : F), ((d⁻¹ : Fˣ) : F)] := rfl
  rw [mem_integralGL_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [e1]
    fin_cases i <;> fin_cases j
    · exact ha
    · exact zero_mem _
    · exact hz
    · exact hd
  · rw [e2]
    fin_cases i <;> fin_cases j
    · exact ha'
    · exact zero_mem _
    · exact mul_mem (mul_mem (neg_mem hz) ha') hd'
    · exact hd'

private theorem mem_integers_iff_ord_nonneg' {x : F} (hx : x ≠ 0) : x ∈ 𝒪[F] ↔ 0 ≤ ord x := by
  rw [← normalizedValuation_le_one_iff, normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  omega

theorem le_ord_sub_one {n : ℕ} (hn : 1 ≤ n) {u : Fˣ} (hu : u ∈ unitFiltrationUnits F (n - 1))
    (h1 : (u : F) - 1 ≠ 0) : (n : ℤ) - 1 ≤ ord ((u : F) - 1) := by
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨a, ha⟩ := exists_sub_one_eq_mul hϖ (⟨v, hv⟩ : unitFiltration F (n - 1))
  have hF : ((unitsIncl F v : Fˣ) : F) - 1 = (ϖ : F) ^ (n - 1) * (a : F) := by
    rw [coe_unitsIncl]
    have := congrArg Subtype.val ha
    exact_mod_cast this
  have hϖ0 : (ϖ : F) ≠ 0 := by
    intro h
    apply hϖ.ne_zero
    exact Subtype.ext h
  have ha0 : (a : F) ≠ 0 := by
    intro h
    apply h1
    rw [hF, h, mul_zero]
  have hpow : ∀ k : ℕ, ord ((ϖ : F) ^ k) = k := by
    intro k
    induction k with
    | zero => simp [GroundTheory.LocalField.ord]
    | succ k ih =>
      rw [pow_succ, ord_mul (pow_ne_zero _ hϖ0) hϖ0, ih, ord_uniformizer hϖ]
      push_cast
      ring
  have ha' : 0 ≤ ord (a : F) := (mem_integers_iff_ord_nonneg' ha0).mp a.2
  rw [hF, ord_mul (pow_ne_zero _ hϖ0) ha0, hpow]
  push_cast [Nat.cast_sub hn]
  linarith

theorem unit_mem_integers {u : Fˣ} (hu : ord (u : F) = 0) : (u : F) ∈ 𝒪[F] := by
  exact (mem_integers_iff_ord_nonneg' u.ne_zero).mpr hu.ge

theorem ne_zero_of_ord {y : F} (hy : ord y = -1) : y ≠ 0 := by
  rintro rfl
  simp [GroundTheory.LocalField.ord] at hy

theorem entry_mem {n : ℕ} (hn : 1 ≤ n) {u : Fˣ} (hu : u ∈ unitFiltrationUnits F (n - 1))
    (h1 : (u : F) - 1 ≠ 0) {y : F} (hy : ord y = -1) :
    (((unifUnit F)⁻¹ ^ n : Fˣ) : F) * (((u : F) - 1) * y⁻¹) ∈ 𝒪[F] ∧ ((u : F) - 1) * y⁻¹ ∈ 𝒪[F] := by
  have hy0 := ne_zero_of_ord hy
  have h0 : ((u : F) - 1) * y⁻¹ ≠ 0 := mul_ne_zero h1 (inv_ne_zero hy0)
  have hyi : ord y⁻¹ = 1 := by
    have := ord_units_inv (Units.mk0 y hy0)
    simpa [hy] using this
  have hz : (n : ℤ) ≤ ord (((u : F) - 1) * y⁻¹) := by
    rw [ord_mul h1 (inv_ne_zero hy0), hyi]
    linarith [le_ord_sub_one hn hu h1]
  have hpi : ord (((unifUnit F)⁻¹ ^ n : Fˣ) : F) = -n := by
    rw [← zpow_natCast, ord_units_zpow, ord_units_inv, ord_unifUnit]
    ring
  have hn0 : (0 : ℤ) ≤ n := by positivity
  constructor
  · rw [mem_integers_iff_ord_nonneg' (mul_ne_zero (Units.ne_zero _) h0), ord_mul (Units.ne_zero _) h0, hpi]
    linarith
  · rw [mem_integers_iff_ord_nonneg' h0]
    linarith

theorem lower_torus_conjugate_unipotent {u : Fˣ} {y : F} (hy : y ≠ 0) :
    lowT u 1 (((u : F) - 1) * y⁻¹) * uni2 y = uni2 y * lowT 1 u (((u : F) - 1) * y⁻¹) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowT, Ad3.uni2, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem unipotent_conj_moves_char : Ad3.R.U2 := by
  unfold Ad3.R.U2 Ad3.R.ForF
  intro F _ _ _ _ _ _ ψ _ ω _ hc y hy
  set n := quasiCharConductor ω with hn_def
  have hn : 1 ≤ n := hc
  have hnot : ¬ (unitFiltrationUnits F (n - 1) ≤ ω.ker) := by
    intro hle
    have : n ≤ n - 1 := Nat.sInf_le hle
    omega
  obtain ⟨u, hu, hωu⟩ := SetLike.not_le_iff_exists.mp hnot
  rw [MonoidHom.mem_ker] at hωu
  have h1 : (u : F) - 1 ≠ 0 := by
    intro h
    apply hωu
    have : u = 1 := Units.ext (sub_eq_zero.mp h)
    rw [this, map_one]
  have hord : ord (u : F) = 0 := by
    obtain ⟨v, -, hv⟩ := Subgroup.mem_map.mp hu
    rw [← hv, coe_unitsIncl]
    exact ord_unit v
  have hu1 : (u : F) ∈ 𝒪[F] := unit_mem_integers hord
  have hu2 : ((u⁻¹ : Fˣ) : F) ∈ 𝒪[F] := unit_mem_integers (by rw [ord_units_inv, hord, neg_zero])
  have h11 : ((1 : Fˣ) : F) ∈ 𝒪[F] := by
    rw [Units.val_one]
    exact one_mem _
  have h12 : (((1 : Fˣ)⁻¹ : Fˣ) : F) ∈ 𝒪[F] := by
    rw [inv_one, Units.val_one]
    exact one_mem _
  have he := entry_mem hn hu h1 hy
  refine ⟨lowT u 1 (((u : F) - 1) * y⁻¹), 1, lowT 1 u (((u : F) - 1) * y⁻¹), u, ?_, ?_,
    lower_torus_conjugate_unipotent (ne_zero_of_ord hy), ?_⟩
  · unfold Ad3.R.GammaZeroLevelMembership
    exact ⟨lowT_mem hu1 hu2 h11 h12 he.2, he.1, rfl⟩
  · unfold Ad3.R.GammaZeroLevelMembership
    exact ⟨lowT_mem h11 h12 hu1 hu2 he.2, he.1, rfl⟩
  · rw [map_one]
    exact fun h => hωu h.symm

end GlobalTheory.CompanionTheory.RankinSelberg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursProductInterleave
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.WordProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem row_ne_zero {n p N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsSmooth π) (zz : Fin n → IrrGL (k := k)) (σ : Fin p ↪o Fin n)
    (c : Fin n → ℕ) (hc : ∀ a, c (σ a) = (zz (σ a)).1) (hc0 : ∀ j, j ∉ Set.range σ → c j = 0)
    (hz : ∑ a, (zz (σ a)).1 = N) (f : (Σ j, Fin (c j)) ≃ Fin N) (h : jm (fun a => zz (σ a)) hz π ≠ 0) :
    jhMult (piTensor fun j => (clOf (zz j) (c j)).rep.ρ) (GlobalTheory.SmGL.jac f π) ≠ 0 :=
  GlobalTheory.T.jacquet_multiplicity_order_embedding π hπ zz σ c hc hc0 hz f h

theorem col_equiv (a : IrrGL (k := k)) {α : Type} [Fintype α] [LinearOrder α] (b : α → ℕ) (i₀ : α)
    (hb : b i₀ = a.1) (hb0 : ∀ i, i ≠ i₀ → b i = 0) (g : (Σ i, Fin (b i)) ≃ Fin a.1) :
    Nonempty ((multiProd g fun i => (clOf a (b i)).rep.ρ).Equiv a.rep) :=
  GlobalTheory.T.multi_product_single_factor_equiv a b i₀ hb hb0 g


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem interleave_embed {T : Type 1} {u v w : List T} (h : Zc.Comb.Interleave u v w) :
    ∃ (r : Fin w.length → Fin 2) (σ₀ : Fin u.length ↪o Fin w.length) (σ₁ : Fin v.length ↪o Fin w.length),
      (∀ j, r j = 0 ↔ j ∈ Set.range σ₀) ∧ (∀ j, r j = 1 ↔ j ∈ Set.range σ₁) ∧
        (∀ a, w.get (σ₀ a) = u.get a) ∧ (∀ a, w.get (σ₁ a) = v.get a) :=
  _root_.GlobalTheory.CompanionTheory.WordProd.Intl.interleave_embeddings h

theorem jm_congr' {h N : ℕ} {x x' : Fin h → IrrGL (k := k)} (e : x = x') (hd : ∑ a, (x a).1 = N)
    (hd' : ∑ a, (x' a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    jm x hd π = jm x' hd' π := by
  subst e; rfl

theorem sum_ite_range {n p : ℕ} (σ : Fin p ↪o Fin n) (P : Fin n → Prop) [DecidablePred P]
    (hP : ∀ j, P j ↔ j ∈ Set.range σ) (F : Fin n → ℕ) :
    ∑ j, (if P j then F j else 0) = ∑ a, F (σ a) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun a _ => σ a) (fun a _ => by simp [hP]) (fun a _ b _ h => σ.injective h)
    (fun j hj => ?_) (fun a _ => rfl)
  obtain ⟨a, rfl⟩ := (hP j).1 (Finset.mem_filter.1 hj).2
  exact ⟨a, Finset.mem_univ _, rfl⟩

theorem jhMult_jac_multiProd_ne_zero {α β n : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    [Fintype n] [DecidableEq n] {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
    (E : (Σ i, m i) ≃ n) (E' : (Σ j, m' j) ≃ n)
    {X : α → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)) (hs : ∀ i, IsSmooth (ρ i))
    (hl : ∀ i, HasFiniteLength (ρ i)) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (Levi k m') Y) (hτ : τ.IsIrreducible) (hτs : IsSmooth τ)
    (b₀ : SizeMatrix m m') (s₀ : ∀ i j, IrrCl (GL (Fin (b₀.1 i j)) k))
    (hrow : ∀ (f : ∀ i, (Σ j, Fin (b₀.1 i j)) ≃ m i) i,
      jhMult (piTensor fun j => (s₀ i j).rep.ρ) (GlobalTheory.SmGL.jac (f i) (ρ i)) ≠ 0)
    (hcol : ∀ g : ∀ j, (Σ i, Fin (b₀.1 i j)) ≃ m' j,
      jhMult τ (piTensor fun j => multiProd (g j) fun i => (s₀ i j).rep.ρ) ≠ 0) :
    jhMult τ (GlobalTheory.SmGL.jac E' (multiProd E ρ)) ≠ 0 := by
  classical
  haveI : Fintype (SizeMatrix m m') := Fintype.ofFinite _
  have hG := GlobalTheory.CompanionTheory.GeoLink.geometricLemma k
  let f : ∀ (b : SizeMatrix m m') i, (Σ j, Fin (b.1 i j)) ≃ m i := fun b => b.nonempty_rows.some
  let g : ∀ (b : SizeMatrix m m') j, (Σ i, Fin (b.1 i j)) ≃ m' j := fun b => b.nonempty_cols.some
  rw [multiProd, hG.1.jhMult_eq E E' (isSmooth_piTensor hs) f g hτ]
  intro h0
  refine absurd ((Finset.sum_eq_zero_iff.1 h0) b₀ (Finset.mem_univ _)) ?_
  obtain ⟨T, hTout, hT⟩ := hG.2 α β m m' (fun i j => Fin (b₀.1 i j)) (f b₀) (g b₀) X ρ hs hl
  rw [show jhMult τ (cellFunctor (f b₀) (g b₀) (piTensor ρ)) = _ from hT ⟨Y, τ, hτs, hτ⟩]
  have hmem : s₀ ∈ T := by
    by_contra hn
    obtain ⟨i, hi⟩ := hTout s₀ hn
    exact hrow (f b₀) i hi
  intro hsum
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => hrow (f b₀) i) (hcol (g b₀))
    ((Finset.sum_eq_zero_iff.1 hsum) s₀ hmem)

theorem wd_prod₂_of_interleave_fin (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (X : Fin 2 → IrrGL (k := k))
    (u v w : List (IrrGL (k := k))) (hxu : Wd (X 0).rep u) (hyv : Wd (X 1).rep v) (hw : Zc.Comb.Interleave u v w) :
    Wd (prod₂ (X 0).rep (X 1).rep) w := by
  classical
  obtain ⟨hdu, hju⟩ := hxu
  obtain ⟨hdv, hjv⟩ := hyv
  have hE := interleave_embed (T := IrrGL (k := k)) hw
  obtain ⟨r, σ₀, σ₁, hE⟩ := hE
  obtain ⟨hr0, hr1, hw0, hw1⟩ := hE
  let n := w.length
  let m : Fin 2 → Type := fun i => Fin (X i).1
  let m' : Fin n → Type := fun j => Fin (w.get j).1
  have hdeg0 : ∑ a, (w.get (σ₀ a)).1 = (X 0).1 := by
    rw [← hdu]; exact Finset.sum_congr rfl fun a _ => by rw [hw0]
  have hdeg1 : ∑ a, (w.get (σ₁ a)).1 = (X 1).1 := by
    rw [← hdv]; exact Finset.sum_congr rfl fun a _ => by rw [hw1]
  have hrow : ∀ i : Fin 2, ∑ j, (if r j = i then (w.get j).1 else 0) = (X i).1 := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · exact (sum_ite_range σ₀ _ hr0 _).trans hdeg0
    · exact (sum_ite_range σ₁ _ hr1 _).trans hdeg1
  have hsplit : ∀ j, (w.get j).1 =
      (if r j = 0 then (w.get j).1 else 0) + (if r j = 1 then (w.get j).1 else 0) := by
    intro j
    rcases Fin.exists_fin_two.1 ⟨r j, rfl⟩ with h | h <;> simp [h]
  have hd' : ∑ j, (w.get j).1 = (X 0).1 + (X 1).1 := by
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) (hrow 0) (hrow 1)
  have hd : ∑ a, (X a).1 = (X 0).1 + (X 1).1 := Fin.sum_univ_two _
  let b₀ : SizeMatrix m m' := ⟨fun i j => if r j = i then (w.get j).1 else 0, fun i => by
    simpa [m] using hrow i, fun j => by
    rcases Fin.exists_fin_two.1 ⟨r j, rfl⟩ with h | h <;> simp [m', h]⟩
  let ρ : ∀ i, Representation ℂ (GL (m i) k) (X i).2.rep.V := fun i => (X i).rep
  have hs : ∀ i, IsSmooth (ρ i) := fun i => (X i).2.rep.smooth
  have hl : ∀ i, HasFiniteLength (ρ i) := fun i => hasFiniteLength_of_isIrreducible (X i).2.rep.irr
  let τ := piTensor fun j : Fin n => (w.get j).rep
  have hτ : τ.IsIrreducible := GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA w.get
  have hτs : IsSmooth τ := isSmooth_piTensor fun j => (w.get j).2.rep.smooth
  let s₀ : ∀ i j, IrrCl (GL (Fin (b₀.1 i j)) k) := fun i j => clOf (w.get j) (b₀.1 i j)
  have hrowf : ∀ (f : ∀ i, (Σ j, Fin (b₀.1 i j)) ≃ m i) i,
      jhMult (piTensor fun j => (s₀ i j).rep.ρ) (GlobalTheory.SmGL.jac (f i) (ρ i)) ≠ 0 := by
    intro f
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · refine row_ne_zero (X 0).rep (hs 0) w.get σ₀ (fun j => b₀.1 0 j) (fun a => ?_) (fun j hj => ?_) hdeg0
        (f 0) ?_
      · simp [b₀, (hr0 (σ₀ a)).2 ⟨a, rfl⟩]
      · simp [b₀, mt (hr0 j).1 hj]
      · rw [jm_congr' (funext hw0) hdeg0 hdu]; exact hju
    · refine row_ne_zero (X 1).rep (hs 1) w.get σ₁ (fun j => b₀.1 1 j) (fun a => ?_) (fun j hj => ?_) hdeg1
        (f 1) ?_
      · simp [b₀, (hr1 (σ₁ a)).2 ⟨a, rfl⟩]
      · simp [b₀, mt (hr1 j).1 hj]
      · rw [jm_congr' (funext hw1) hdeg1 hdv]; exact hjv
  have hcolf : ∀ g : ∀ j, (Σ i, Fin (b₀.1 i j)) ≃ m' j,
      jhMult τ (piTensor fun j => multiProd (g j) fun i => (s₀ i j).rep.ρ) ≠ 0 := by
    intro g
    have hcol : ∀ j, Nonempty ((multiProd (g j) fun i => (s₀ i j).rep.ρ).Equiv (w.get j).rep) := fun j =>
      col_equiv (w.get j) (fun i => b₀.1 i j) (r j) (by simp [b₀]) (fun i hi => by simp [b₀, Ne.symm hi])
        (g j)
    rw [jhMult_congr_right τ (piTensorEquiv fun j => (hcol j).some), jhMult_self hτ]
    exact one_ne_zero
  refine ⟨hd', ?_⟩
  have hφ : Nonempty ((prod₂ (X 0).rep (X 1).rep).Equiv (prodIrr X hd)) :=
    nonempty_prod₂_equiv_prodIrr_rep X hd
  let E' := stdBlocks (fun a => (w.get a).1) hd'
  have e1 : jm w.get hd' (prod₂ (X 0).rep (X 1).rep) = jhMult τ (GlobalTheory.SmGL.jac E' (prodIrr X hd)) :=
    jhMult_congr_right τ (GlobalTheory.SmGL.Exponents.jacEquiv E' hφ.some)
  rw [e1]
  exact jhMult_jac_multiProd_ne_zero (stdBlocks (fun a => (X a).1) hd) E' ρ hs hl τ hτ hτs b₀ s₀ hrowf hcolf

theorem wd_prod₂_of_interleave (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x y : IrrGL (k := k))
    (u v w : List (IrrGL (k := k))) (_hu : ∀ c ∈ u, c.IsCusp) (_hv : ∀ c ∈ v, c.IsCusp) (hxu : Wd x.rep u)
    (hyv : Wd y.rep v) (hw : Zc.Comb.Interleave u v w) : Wd (prod₂ x.rep y.rep) w := by
  obtain ⟨X, rfl, rfl⟩ : ∃ X : Fin 2 → IrrGL (k := k), X 0 = x ∧ X 1 = y := ⟨![x, y], rfl, rfl⟩
  exact wd_prod₂_of_interleave_fin hA X u v w hxu hyv hw

end GlobalTheory.CompanionTheory.WordProd

end
end

