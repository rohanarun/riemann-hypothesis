module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0531
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0514
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingHomMulSubEqZero
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SmallRatCell

open RestrictedProduct InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F]

theorem exists_nat_mem (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ v ∈ S, ((N : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hpos : 0 < ∏ v ∈ S, Ideal.absNorm v.asIdeal :=
    Finset.prod_pos fun v _ => Nat.pos_of_ne_zero (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  refine ⟨2 * ∏ v ∈ S, Ideal.absNorm v.asIdeal, by omega, fun v hv => ?_⟩
  obtain ⟨c, hc⟩ : Ideal.absNorm v.asIdeal ∣ 2 * ∏ v ∈ S, Ideal.absNorm v.asIdeal :=
    (Finset.dvd_prod_of_mem _ hv).mul_left 2
  rw [hc]
  push_cast
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

def tau (N k : ℕ) : ℚ := (N : ℚ) ^ k / (1 + ((N : ℚ) ^ k) ^ 2)

theorem tau_pos {N : ℕ} (hN : 2 ≤ N) (k : ℕ) : 0 < tau N k := by
  have : (0 : ℚ) < N := by exact_mod_cast (by omega : 0 < N)
  unfold tau
  positivity

theorem tendsto_tau_fin (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (hN : ((N : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    Tendsto (fun k => algebraMap F (v.adicCompletion F) ((tau N k : ℚ) : F)) atTop (𝓝 0) := by
  have hv : Valued.v (N : v.adicCompletion F) < 1 := by
    have e : (N : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) (N : 𝓞 F) :=
      (map_natCast _ N).symm
    rw [e]
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (N : 𝓞 F)
    have h2 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (N : 𝓞 F)).2 hN
    exact h1 ▸ h2
  have ht := Valued.tendsto_zero_pow_of_v_lt_one hv
  have h2 : Tendsto (fun k : ℕ => 1 + ((N : v.adicCompletion F) ^ k) ^ 2) atTop (𝓝 1) := by
    simpa using (ht.pow 2).const_add 1
  have h3 := ht.div h2 one_ne_zero
  rw [zero_div] at h3
  refine h3.congr fun k => ?_
  simp [tau, map_div₀, map_add (f := _), map_pow, map_natCast]

theorem tendsto_tau_inf (w : InfinitePlace F) {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (fun k => algebraMap F w.Completion ((tau N k : ℚ) : F)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : ∀ k, ‖algebraMap F w.Completion ((tau N k : ℚ) : F)‖ = (tau N k : ℝ) := fun k => by
    rw [← (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]
    have h := map_ratCast ((extensionEmbedding w).comp (algebraMap F w.Completion)) (tau N k)
    rw [RingHom.comp_apply] at h
    rw [h, Complex.norm_ratCast, abs_of_pos (by exact_mod_cast tau_pos hN k)]
  simp only [hnorm]
  have hb : ∀ k, (tau N k : ℝ) ≤ (1 / 2 : ℝ) ^ k := fun k => by
    have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hx : (2 : ℝ) ^ k ≤ (N : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) h2 k
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    have hxp : (0 : ℝ) < (N : ℝ) ^ k := by linarith
    simp only [tau]
    push_cast
    rw [one_div, inv_pow, div_le_iff₀ (by positivity)]
    have : (2 : ℝ) ^ k * (N : ℝ) ^ k ≤ 1 + ((N : ℝ) ^ k) ^ 2 := by nlinarith
    rw [← div_eq_inv_mul, le_div_iff₀ hp]
    linarith
  refine squeeze_zero (fun k => by exact_mod_cast (tau_pos hN k).le) hb ?_
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)


open Classical in
def finS (S : Finset (HeightOneSpectrum (𝓞 F))) (q : F) :
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] :=
  ⟨fun v => if v ∈ S then algebraMap F (v.adicCompletion F) q else 0, by
    rw [Filter.eventually_principal]
    intro v hv
    have hv' : v ∉ S := by simpa using hv
    simp only [if_neg hv']
    exact zero_mem _⟩

theorem cofinite_le (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ 𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
  rw [le_principal_iff, mem_cofinite, compl_compl]
  exact S.finite_toSet

def sAd (S : Finset (HeightOneSpectrum (𝓞 F))) (q : F) : AF F :=
  (fun w => algebraMap F w.Completion q,
    RestrictedProduct.inclusion _ _ (cofinite_le S) (finS S q))

theorem tendsto_sAd (S : Finset (HeightOneSpectrum (𝓞 F))) (q : ℕ → F)
    (hi : ∀ w : InfinitePlace F, Tendsto (fun k => algebraMap F w.Completion (q k)) atTop (𝓝 0))
    (hf : ∀ v ∈ S, Tendsto (fun k => algebraMap F (v.adicCompletion F) (q k)) atTop (𝓝 0)) :
    Tendsto (fun k => sAd S (q k)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k => finS S (q k)) atTop (𝓝 0) := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isInducing.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    by_cases hv : v ∈ S
    · refine (hf v hv).congr fun k => ?_
      exact (if_pos hv).symm
    · refine tendsto_const_nhds.congr fun k => ?_
      show (0 : v.adicCompletion F) = _
      exact (if_neg hv).symm
  have h2 := ((RestrictedProduct.continuous_inclusion (cofinite_le S)).tendsto 0).comp h1
  refine Tendsto.prodMk_nhds (tendsto_pi_nhds.2 hi) h2

theorem one_tmul_algebraMap {A E : Type} [CommRing A] [Algebra F A] [Field E] [Algebra F E] (q : F) :
    (1 : A) ⊗ₜ[F] algebraMap F E q = algebraMap F A q ⊗ₜ[F] (1 : E) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

theorem ring_hom_mul_sub_eq_zero {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x e y : A) (c : B)
    (hc : f e = c) (h : f x * c = f y) : f (x * e - y) = 0 := by
  rw [map_sub, map_mul, hc, h, sub_self]


open Classical in
theorem tensor_key {E : Type} [Field E] [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : AF F ⊗[F] E) (hi : ∀ w, compInf F E w e = 1)
    (hf : ∀ v, compFin F E v e = if v ∈ S then 1 else 0) (q : F) :
    ((1 : AF F) ⊗ₜ[F] algebraMap F E q) * e = sAd S q ⊗ₜ[F] (1 : E) := by
  rw [← sub_eq_zero]
  refine GlobalTheory.CompanionTheory.AdeleComp.tensor_eq_zero _ (fun w => ?_) (fun v => ?_)
  · refine ring_hom_mul_sub_eq_zero (compInf F E w) _ _ _ _ (hi w) ?_
    rw [mul_one]
    exact one_tmul_algebraMap (A := w.Completion) _
  · refine ring_hom_mul_sub_eq_zero (compFin F E v) _ _ _ _ (hf v) ?_
    by_cases hv : v ∈ S
    · rw [if_pos hv, mul_one]
      have h : evFin F v (sAd S q) = algebraMap F (v.adicCompletion F) q := if_pos hv
      show (1 : v.adicCompletion F) ⊗ₜ[F] _ = evFin F v (sAd S q) ⊗ₜ[F] (1 : E)
      rw [h]
      exact one_tmul_algebraMap _
    · rw [if_neg hv, mul_zero]
      have h : evFin F v (sAd S q) = 0 := if_neg hv
      show 0 = evFin F v (sAd S q) ⊗ₜ[F] (1 : E)
      rw [h, TensorProduct.zero_tmul]

theorem incA_mul_idem (D : D7) (S : Finset (Pl D)) (e : AE D) (he : IsIdem S e) (q : ℚ) :
    incA D ((q : ℚ) : D.host.E) * e = sAd S ((q : ℚ) : D.host.F) • (1 : AE D) := by
  have hq : ((q : ℚ) : D.host.E) = algebraMap D.host.F D.host.E ((q : ℚ) : D.host.F) :=
    (map_ratCast (algebraMap D.host.F D.host.E) q).symm
  have hs : sAd S ((q : ℚ) : D.host.F) • (1 : AE D) =
      sAd S ((q : ℚ) : D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    show _ • ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hs, hq]
  exact tensor_key S e he.1 he.2 _

theorem smallRat : PositivityTheory.Rg.Rsw.L.IdemEx → PositivityTheory.Rg.Rsw.Cell.SmallRat := by
  intro _ D S e he V hV M
  obtain ⟨N, hN, hmem⟩ := exists_nat_mem S
  have ht : Tendsto (fun k => sAd S ((tau N k : ℚ) : D.host.F)) atTop (𝓝 0) :=
    tendsto_sAd S _ (fun w => tendsto_tau_inf w hN) (fun v hv => tendsto_tau_fin v (hmem v hv))
  have hz : Tendsto (fun k => incA D ((tau N k : ℚ) : D.host.E) * e) atTop (𝓝 0) := by
    have h := ht.smul_const (1 : AE D)
    rw [zero_smul] at h
    exact h.congr fun k => (incA_mul_idem D S e he _).symm
  have hall : ∀ᶠ k in atTop, ∀ j : Fin M,
      ((j.1 + 1 : ℕ) : AE D) * (incA D ((tau N k : ℚ) : D.host.E) * e) ∈ V := by
    rw [Filter.eventually_all]
    intro j
    have h := hz.const_mul ((j.1 + 1 : ℕ) : AE D)
    rw [mul_zero] at h
    exact h hV
  obtain ⟨k, hk⟩ := hall.exists
  refine ⟨fun j => ((j.1 + 1 : ℕ) : ℚ) * tau N k, fun i j hij => ?_, fun j => ?_⟩
  · have h := mul_right_cancel₀ (tau_pos hN k).ne' hij
    have h2 : i.1 + 1 = j.1 + 1 := by exact_mod_cast h
    exact Fin.ext (by omega)
  · have h := hk j
    have e1 : incA D (((((j.1 + 1 : ℕ) : ℚ) * tau N k : ℚ)) : D.host.E) =
        ((j.1 + 1 : ℕ) : AE D) * incA D ((tau N k : ℚ) : D.host.E) := by
      rw [Rat.cast_mul, map_mul, Rat.cast_natCast, map_natCast]
    show incA D (((((j.1 + 1 : ℕ) : ℚ) * tau N k : ℚ)) : D.host.E) * e ∈ V
    rw [e1, mul_assoc]
    exact h

end GlobalTheory.CompanionTheory.SmallRatCell

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingleGluing
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.OneStepProof

open GlobalTheory.CompanionTheory.EGlue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem subset_hull (S : Set (Sm E N)) : S ⊆ (hull S : Submodule ℂ (Sm E N)) := by
  intro φ hφ
  refine (Submodule.mem_sInf).2 ?_
  rintro U ⟨hS, -⟩
  exact hS hφ

theorem hull_le {S : Set (Sm E N)} {U : Submodule ℂ (Sm E N)} (hS : S ⊆ U) (hU : _root_.GlobalTheory.CuspRep.IsStable U) : hull S ≤ U :=
  sInf_le ⟨hS, hU⟩

theorem hull_ne_bot {S : Set (Sm E N)} {φ : Sm E N} (hφ : φ ∈ S) (h0 : φ ≠ 0) : hull S ≠ ⊥ := by
  intro h
  have h1 : φ ∈ (hull S : Submodule ℂ (Sm E N)) := subset_hull S hφ
  rw [h] at h1
  exact h0 ((Submodule.mem_bot ℂ).1 h1)

theorem exists_ne_of_hull {S : Set (Sm E N)} (hst : _root_.GlobalTheory.CuspRep.IsStable (hull S)) (T : Sm E N →ₗ[ℂ] Sm E N)
    (he : ∀ o, ∀ χ ∈ hull S, T (act o χ) = act o (T χ)) {ψ : Sm E N} (hψ : ψ ∈ hull S) (hT : T ψ ≠ 0) :
    ∃ φ ∈ S, T φ ≠ 0 := by
  by_contra hcon
  have hz : ∀ φ ∈ S, T φ = 0 := by
    intro φ hφ
    by_contra h
    exact hcon ⟨φ, hφ, h⟩
  have hK : _root_.GlobalTheory.CuspRep.IsStable (hull S ⊓ LinearMap.ker T) := by
    intro o χ hχ
    refine Submodule.mem_inf.2 ⟨hst o χ hχ.1, ?_⟩
    have h0 : T χ = 0 := LinearMap.mem_ker.1 hχ.2
    rw [LinearMap.mem_ker, he o χ hχ.1, h0, map_zero]
  have hS : S ⊆ (hull S ⊓ LinearMap.ker T : Submodule ℂ (Sm E N)) := fun φ hφ =>
    Submodule.mem_inf.2 ⟨subset_hull S hφ, LinearMap.mem_ker.2 (hz φ hφ)⟩
  exact hT (LinearMap.mem_ker.1 (Submodule.mem_inf.1 (hull_le hS hK hψ)).2)

theorem sm_ne_zero {φ : Sm E N} {x : GA E N} (h : φ.1 x ≠ 0) : φ ≠ 0 := by
  rintro rfl
  exact h rfl

theorem oneStep_of_parts : PairSlices → PairRestrict → PairFD → SliceType → PairStep₁ → PairStep₂ → HullGen → CapEquiv →
    OneStep := by
  intro hSl hRe hFD hST hP₁ hP₂ hHG hCE
  intro E _ _ _ a b ι _ K₁ K₂ W₁ W₂ Θ₁ Θ₂ Ω₁ Ω₂ f m₁ m₂ hW₁ hW₂ hF₁ hF₂ hf hT hs₁ hs₂ hA₁ hA₂ hN₁ hN₂ hC₁ hC₂ hI₁ hI₂
    hD₁ hD₂ hP
  obtain ⟨fd₁, fd₂⟩ := hFD E a b ι _ _ f hP
  have ty₁ : ∀ φ ∈ slices₁ f, TypeB K₁ W₁ φ := by
    rintro φ ⟨i, m, h⟩
    exact (hST E a b K₁ K₂ W₁ W₂ (f i) (hT i)).1 φ m h
  have ty₂ : ∀ φ ∈ slices₂ f, TypeB K₂ W₂ φ := by
    rintro φ ⟨i, m, h⟩
    exact (hST E a b K₁ K₂ W₁ W₂ (f i) (hT i)).2 φ m h
  obtain ⟨st₁, fg₁⟩ := hHG E a K₁ W₁ _ ty₁ fd₁
  obtain ⟨st₂, fg₂⟩ := hHG E b K₂ W₂ _ ty₂ fd₂

  have hU₁ : hull (slices₁ f) ≠ ⊥ := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hf
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hi
    obtain ⟨φ, hφ⟩ := hs₁ i x.2
    refine hull_ne_bot (φ := φ) ⟨i, x.2, hφ⟩ (sm_ne_zero (x := x.1) ?_)
    rw [hφ]
    exact hx
  obtain ⟨t₁, T₁, r₁, g₁, l₁, e₁, i₁, ψ, hψ, hTψ⟩ :=
    hF₁ _ st₁ hA₁ fg₁ hN₁ hC₁ (fun τ => ⟨m₁ τ, hI₁ τ, hD₁ τ⟩) hU₁
  obtain ⟨φ, ⟨i₀, y, hφ⟩, hTφ⟩ := exists_ne_of_hull st₁ T₁ e₁ hψ hTψ
  obtain ⟨G₁ne, G₁p, G₁t, G₁h⟩ := hP₁ E a b ι K₁ K₂ W₁ W₂ _ t₁.space _ T₁ f hW₁ hW₂ st₁ e₁ i₁ hP hT
    ⟨i₀, y, φ, hφ, hTφ⟩

  have hsl : ∀ i m, sl₂ (ap₁ T₁ (f i)) m ∈ hull (slices₂ f) ∧
      (sl₂ (ap₁ T₁ (f i)) m).1 = fun x => ap₁ T₁ (f i) (m, x) :=
    fun i m => (hSl E a b _ _ _ (G₁p i)).2 m
  have hss : slices₂ (fun i => ap₁ T₁ (f i)) ⊆ (hull (slices₂ f) : Submodule ℂ (Sm E b)) := by
    rintro χ ⟨i, m, h⟩
    have hχ : χ = sl₂ (ap₁ T₁ (f i)) m := Subtype.ext (h.trans (hsl i m).2.symm)
    rw [hχ]
    exact (hsl i m).1
  have hle : hull (slices₂ fun i => ap₁ T₁ (f i)) ≤ hull (slices₂ f) := hull_le hss st₂
  have ty₂' : ∀ χ ∈ slices₂ (fun i => ap₁ T₁ (f i)), TypeB K₂ W₂ χ := by
    rintro χ ⟨i, m, h⟩
    exact (hST E a b K₁ K₂ W₁ W₂ _ (G₁t i)).2 χ m h
  obtain ⟨st₂', fg₂'⟩ := hHG E b K₂ W₂ _ ty₂' (hFD E a b ι _ _ _ G₁p).2
  have G₁p' : ∀ i, ap₁ T₁ (f i) ∈ pairSpace t₁.space (hull (slices₂ fun i => ap₁ T₁ (f i))) := fun i =>
    hRe E a b _ _ _ _ (G₁p i) fun m χ h => subset_hull _ ⟨i, m, h⟩
  have hU₂ : hull (slices₂ fun i => ap₁ T₁ (f i)) ≠ ⊥ := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 G₁ne
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hi
    refine hull_ne_bot (φ := sl₂ (ap₁ T₁ (f i)) x.1) ⟨i, x.1, (hsl i x.1).2⟩ (sm_ne_zero (x := x.2) ?_)
    rw [(hsl i x.1).2]
    exact hx

  obtain ⟨t₂, T₂, r₂, g₂, l₂, e₂, i₂, ψ', hψ', hTψ'⟩ :=
    hF₂ _ st₂' (fun χ hχ => hA₂ χ (hle hχ)) fg₂' (fun χ hχ => hN₂ χ (hle hχ))
      (by
        obtain ⟨z, hz, h⟩ := hC₂
        exact ⟨z, hz, fun χ hχ => h χ (hle hχ)⟩)
      (fun τ => ⟨m₂ τ, ⟨(hI₂ τ).1, fun u χ hχ => (hI₂ τ).2 u χ (hle hχ)⟩, hD₂ τ⟩) hU₂
  obtain ⟨χ, ⟨i₃, y₃, hχ⟩, hTχ⟩ := exists_ne_of_hull st₂' T₂ e₂ hψ' hTψ'
  obtain ⟨Gne, Gp, Gt, Gh⟩ := hP₂ E a b ι K₁ K₂ W₁ W₂ _ _ t₂.space T₂ (fun i => ap₁ T₁ (f i)) hW₁ hW₂ st₂' e₂ i₂ G₁p' G₁t
    ⟨i₃, y₃, χ, hχ, hTχ⟩
  exact ⟨t₁, t₂, fun i => ap₂ T₂ (ap₁ T₁ (f i)), T₁ ψ, T₂ ψ', r₁, r₂, g₁, g₂, l₁, l₂, Gne, Gp, Gt,
    fun h c e => Gh h c (G₁h h c e), i₁ ψ hψ, hTψ,
    hCE E a _ T₁ ψ m₁ st₁ e₁ hψ (fun τ u => (hI₁ τ).2 u ψ hψ),
    i₂ ψ' hψ', hTψ',
    hCE E b _ T₂ ψ' m₂ st₂' e₂ hψ' (fun τ u => (hI₂ τ).2 u ψ' (hle hψ'))⟩

end GlobalTheory.CompanionTheory.EGlue.OneStepProof

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceType
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.SliceTypePf

theorem restrict_left {A B : Type} [One B] (W₁ : Submodule ℂ (A → ℂ)) (W₂ : Submodule ℂ (B → ℂ)) (f : A × B → ℂ)
    (hf : f ∈ Submodule.span ℂ {f : A × B → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :
    (fun k : A => f (k, 1)) ∈ W₁ := by
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨w₁, h₁, w₂, -, rfl⟩ := h
    have : (fun k : A => w₁ k * w₂ 1) = w₂ 1 • w₁ := by
      funext k
      simp [mul_comm]
    simpa [this] using W₁.smul_mem _ h₁
  | zero => exact W₁.zero_mem
  | add f g _ _ hf hg => exact W₁.add_mem hf hg
  | smul c f _ hf => exact W₁.smul_mem c hf

theorem restrict_right {A B : Type} [One A] (W₁ : Submodule ℂ (A → ℂ)) (W₂ : Submodule ℂ (B → ℂ)) (f : A × B → ℂ)
    (hf : f ∈ Submodule.span ℂ {f : A × B → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :
    (fun k : B => f (1, k)) ∈ W₂ := by
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨w₁, -, w₂, h₂, rfl⟩ := h
    have : (fun k : B => w₁ 1 * w₂ k) = w₁ 1 • w₂ := by
      funext k
      simp
    simpa [this] using W₂.smul_mem _ h₂
  | zero => exact W₂.zero_mem
  | add f g _ _ hf hg => exact W₂.add_mem hf hg
  | smul c f _ hf => exact W₂.smul_mem c hf

theorem main : GlobalTheory.CompanionTheory.EGlue.SliceType := by
  intro E _ _ _ a b K₁ K₂ W₁ W₂ F hF
  obtain ⟨hl, hk⟩ := hF
  refine ⟨?_, ?_⟩
  · rintro φ m₂ hφ
    refine ⟨?_, ?_⟩
    · intro u hu g
      have := hl u hu 1 K₂.one_mem (g, m₂)
      simpa [hφ, Prod.mk_mul_mk] using this
    · intro g
      have := restrict_left W₁ W₂ _ (hk (g, m₂))
      simpa [hφ, Prod.mk_mul_mk] using this
  · rintro φ m₁ hφ
    refine ⟨?_, ?_⟩
    · intro u hu g
      have := hl 1 K₁.one_mem u hu (m₁, g)
      simpa [hφ, Prod.mk_mul_mk] using this
    · intro g
      have := restrict_right W₁ W₂ _ (hk (m₁, g))
      simpa [hφ, Prod.mk_mul_mk] using this

end GlobalTheory.CompanionTheory.EGlue.SliceTypePf

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackChartFormula
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.PullDens


open Filter _root_.Topology in
theorem locDens_pullback_eq : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → ∀ (c : GlobalTheory.AlgChart q σ D) (j : Fin A.n) (u : Fin D → ℂ),
      u ∈ (A.chart j).target → F ((A.chart j).symm u) ∈ c.e.source →
      AnalyticAt ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u ∧
      locDens A (fun _ => φ.locPot.pullback F hF) j u =
        ‖LinearMap.det (fderiv ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u :
          (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 * c.chernDens φ (F ((A.chart j).symm u)) := by
  intro k _ X q σ D T _ A F hF hH B φ h c j u hu hsrc
  have hcont : ContinuousAt (F ∘ (A.chart j).symm) u :=
    hF.continuousAt.comp ((A.chart j).continuousAt_symm hu)
  have hN : ∀ᶠ w in 𝓝 u, F ((A.chart j).symm w) ∈ c.e.source :=
    hcont.eventually (c.e.open_source.mem_nhds hsrc)
  have hG : AnalyticAt ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u := by
    refine analyticAt_pi_iff.2 fun a => ?_
    refine (hH c.U (c.x a) j u ⟨hu, c.source_subset hsrc⟩).congr ?_
    filter_upwards [hN] with w hw
    exact (c.finChart_eq_ev hw a).symm
  refine ⟨hG, ?_⟩
  set G := c.finChart ∘ F ∘ (A.chart j).symm with hGdef
  set y₀ := F ((A.chart j).symm u) with hy₀
  have hGu : G u = c.finChart y₀ := rfl
  have hsy : c.finChart.symm (G u) = y₀ := c.finChart.left_inv hsrc
  have hz : G u ∈ c.finChart.target := c.finChart.map_source hsrc
  have hma := h.maDens_eq c hz
  rw [hsy] at hma
  have hr : c.e y₀ = GlobalTheory.FinChart.toV D (G u) := rfl
  have hd := h.contDiffAt c hsrc (mem_pick φ.isLB y₀)
  rw [hr] at hd
  have hψ : ContDiffAt ℝ 2 (fun w => φ.locPot.φ y₀ (c.finChart.symm w)) (G u) :=
    (hd.comp (G u) (GlobalTheory.FinChart.toV D).contDiff.contDiffAt).div_const 2
  have hcomp := ReciprocityTheory.AnForm.A.maDens_comp (fun _ w => φ.locPot.φ y₀ (c.finChart.symm w)) G u hG
    (fun _ => hψ)
  rw [ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq, hma] at hcomp
  rw [mul_comm, ← hcomp]
  unfold locDens
  refine maDens_congr_hessC _ _ _ fun _ => hessCGerm _ _ _ ?_
  filter_upwards [hN] with w hw
  simp only [LocPot.pullback, Function.comp_apply, hGdef]
  rw [c.finChart.left_inv hw]

end GlobalTheory.CompanionTheory.MixZ.PullDens
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerDividesFrobeniusDifference
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem dvd_pow_qOf_sub_self : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), (Ideal.span {π}).IsMaximal →
    Finite (↥(OL K) ⧸ Ideal.span {π}) → ∀ c : ↥(OL K), π ∣ c ^ qOf π - c := by
  intro l _ K π hmax hfin c
  set_option synthInstance.maxHeartbeats 200000 in
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem,
      map_sub (Ideal.Quotient.mk _), map_pow (Ideal.Quotient.mk _), sub_eq_zero]
  letI := Ideal.Quotient.field (Ideal.span {π})
  letI := Fintype.ofFinite (↥(OL K) ⧸ Ideal.span {π})
  rw [qOf, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card _

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

