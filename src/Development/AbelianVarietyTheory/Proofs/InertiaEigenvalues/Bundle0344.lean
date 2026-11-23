module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0267
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsPrincipalIdealRingOfIsLocalization
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import GroundTheory.LocalFields.Bundle0013
public import GroundTheory.LocalFields.Different
public import GroundTheory.LocalFields.Integers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0321

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralCocycleOfGeneratorAndFixing
section
noncomputable section

namespace GlobalTheory.ExpImage.IntCoc

open _root_.Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage Filter Topology
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

theorem oB_mem {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (α : Om l) :
    oB P α ∈ FilB P 0 := by
  have hα : IsIntegral ℚ_[l] α := Algebra.IsIntegral.isIntegral α
  obtain ⟨K, hK⟩ : ∃ K : FinExt l, α ∈ K.1 :=
    ⟨⟨IntermediateField.adjoin ℚ_[l] {α}, IntermediateField.adjoin.finiteDimensional hα⟩,
      IntermediateField.mem_adjoin_simple_self _ α⟩
  have h := ((P.PD K).Fil 0).smul_mem (⟨α, hK⟩ : ↥K.1) (P.PD K).one_mem
  rw [Algebra.smul_def, mul_one, IsScalarTower.algebraMap_apply ↥K.1 (Om l) P.R.BdR] at h
  exact (T.fil _ _ _).2 ((T.fil K _ _).1 h)

theorem act_qB (P : LocPrime l) (g : GQ l) (c : ℚ_[l]) : P.actQdR g (qB P c) = qB P c :=
  AlgEquiv.commutes _ c

def tw (LT : LocTheory) (e : ℕ) (σ : GQ l) : ℚ_[l] :=
  (((LT l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l])

def coc (LT : LocTheory) (e : ℕ) (x b : (LT l).R.BdR) (σ : GQ l) : (LT l).R.BdR :=
  qB (LT l) ((logChi LT σ : ℤ_[l]) : ℚ_[l]) * x +
    (qB (LT l) (tw LT e σ) * (LT l).actQdR σ b - b)

variable (LT : LocTheory)

theorem norm_chi (σ : GQ l) : ‖((LT l).χQ σ : ℚ_[l])‖ = 1 :=
  (cyc_basic l _ (LT l).χQ_cyc).1 σ

theorem logChi_coe (σ : GQ l) :
    ((logChi LT σ : ℤ_[l]) : ℚ_[l]) = logZl l ((LT l).χQ σ : ℚ_[l]) := by
  exact congrArg Subtype.val (dif_pos ((GlobalTheory.PadicLogUnits.logZl_hom l).2.2.1 _ (norm_chi LT σ)))

theorem logChi_mul (σ τ : GQ l) : ((logChi LT (σ * τ) : ℤ_[l]) : ℚ_[l]) =
    ((logChi LT σ : ℤ_[l]) : ℚ_[l]) + ((logChi LT τ : ℤ_[l]) : ℚ_[l]) := by
  rw [logChi_coe, logChi_coe, logChi_coe, map_mul, Units.val_mul,
    (GlobalTheory.PadicLogUnits.logZl_hom l).1 _ _ (norm_chi LT σ) (norm_chi LT τ)]

theorem logZl_one : logZl l 1 = 0 := by
  have h := (GlobalTheory.PadicLogUnits.logZl_hom l).1 1 1 norm_one norm_one
  rw [mul_one] at h
  exact left_eq_add.1 h

theorem continuous_logChi : Continuous fun σ : GQ l => ((logChi LT σ : ℤ_[l]) : ℚ_[l]) := by
  simp only [logChi_coe]
  exact (GlobalTheory.PadicLogUnits.logZl_hom l).2.1.comp_continuous (cyc_basic l _ (LT l).χQ_cyc).2.1
    (norm_chi LT)

theorem tw_eq (e : ℕ) (σ : GQ l) : tw LT e σ = (((LT l).χQ σ : ℚ_[l]) ^ e)⁻¹ := by
  simp [tw]

theorem norm_tw (e : ℕ) (σ : GQ l) : ‖tw LT e σ‖ = 1 := by
  simp [tw_eq, norm_chi]

theorem tw_mul (e : ℕ) (σ τ : GQ l) : tw LT e (σ * τ) = tw LT e σ * tw LT e τ := by
  rw [tw, tw, tw, map_mul, mul_zpow, Units.val_mul]

theorem continuous_tw (e : ℕ) : Continuous (tw (l := l) LT e) := by
  have : tw (l := l) LT e = fun σ => (((LT l).χQ σ : ℚ_[l]) ^ e)⁻¹ := funext (tw_eq LT e)
  rw [this]
  exact ((cyc_basic l _ (LT l).χQ_cyc).2.1.pow e).inv₀ fun σ => pow_ne_zero _ (Units.ne_zero _)

theorem tw_act (e : ℕ) (σ : GQ l) (α : Om l) (h : σ α = α) :
    qB (LT l) (tw LT e σ) * (LT l).actQdR σ (oB (LT l) α * tD (LT l) ^ e) =
      oB (LT l) α * tD (LT l) ^ e := by
  have h1 : qB (LT l) (tw LT e σ) * qB (LT l) ((LT l).χQ σ : ℚ_[l]) ^ e = 1 := by
    rw [← map_pow, ← map_mul, tw_eq, inv_mul_cancel₀ (pow_ne_zero _ (Units.ne_zero _)), map_one]
  rw [map_mul, map_pow, act_tD, (LT l).actQdR_Om, h, mul_pow]
  linear_combination (oB (LT l) α * tD (LT l) ^ e) * h1

theorem coc_mul (e : ℕ) (x b : (LT l).R.BdR) (σ τ : GQ l)
    (h : qB (LT l) (tw LT e σ) * (LT l).actQdR σ x = x) :
    coc LT e x b (σ * τ) =
      coc LT e x b σ + qB (LT l) (tw LT e σ) * (LT l).actQdR σ (coc LT e x b τ) := by
  simp only [coc, logChi_mul, tw_mul, map_add (f := _), map_mul, map_sub, act_qB, AlgEquiv.mul_apply]
  linear_combination (-qB (LT l) ((logChi LT τ : ℤ_[l]) : ℚ_[l])) * h

theorem small_mul {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {M n k : ℕ} {c : ℚ_[l]}
    {x : P.R.BdR} (hc : ‖c‖ ≤ (l : ℝ) ^ (-(k : ℤ))) (hx : (l : P.R.BdR) ^ k * x ∈ Lat AI M n) :
    qB P c * x ∈ Lat AI M n := by
  have h0 : ((l : ℚ_[l]) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have h1 : ‖c / (l : ℚ_[l]) ^ k‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.2 h0), Padic.norm_p_pow]
    exact hc
  have := qB_mul_mem_Lat AI T ⟨_, h1⟩ hx
  rwa [← mul_assoc, ← map_natCast (qB P), ← map_pow, ← map_mul, div_mul_cancel₀ _ h0] at this

theorem ev_small {f : GQ l → ℚ_[l]} (hf : Continuous f) (h1 : f 1 = 0) (k : ℕ) :
    ∀ᶠ τ in 𝓝 (1 : GQ l), ‖f τ‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  refine hf.norm.continuousAt.eventually_le_const ?_
  show ‖f 1‖ < _
  rw [h1, norm_zero]
  exact zpow_pos hl _

theorem coc_small {AI : LocAinf l (LT l)} (T : LocTied l (LT l) AI) (e M n : ℕ)
    {x b : (LT l).R.BdR} (hx : x ∈ FilB (LT l) 0) (hb : b ∈ FilB (LT l) 0) :
    ∀ᶠ τ in 𝓝 (1 : GQ l), coc LT e x b τ ∈ Lat AI M n := by
  obtain ⟨⟨k, hk⟩, -⟩ := _root_.GlobalTheory.ExpImage.bounded_and_eventually_sub_mem_Lat l _ AI T x hx M n
  obtain ⟨⟨k', hk'⟩, h3⟩ := _root_.GlobalTheory.ExpImage.bounded_and_eventually_sub_mem_Lat l _ AI T b hb M n
  have h1 := ev_small (continuous_logChi (l := l) LT)
    (by rw [logChi_coe, map_one, Units.val_one, logZl_one]) k
  have h2 := ev_small (f := fun τ : GQ l => tw LT e τ - 1) ((continuous_tw LT e).sub continuous_const)
    (by simp [tw]) k'
  filter_upwards [h1, h2, h3] with τ a1 a2 a3
  have := add_mem (small_mul T a1 hk) (add_mem (small_mul T a2 hk')
    (qB_mul_mem_Lat AI T ⟨_, (norm_tw LT e τ).le⟩ a3))
  convert this using 1
  simp only [coc, map_sub, map_one]
  ring

theorem coc_near {AI : LocAinf l (LT l)} (T : LocTied l (LT l) AI) (e M n : ℕ)
    {x b : (LT l).R.BdR} (hx : x ∈ FilB (LT l) 0) (hb : b ∈ FilB (LT l) 0) (σ : GQ l)
    (h : qB (LT l) (tw LT e σ) * (LT l).actQdR σ x = x) :
    ∀ᶠ τ in 𝓝 σ, coc LT e x b τ - coc LT e x b σ ∈ Lat AI M n := by
  have ht : Tendsto (fun τ : GQ l => σ⁻¹ * τ) (𝓝 σ) (𝓝 1) := by
    have := (continuous_const_mul σ⁻¹).tendsto σ
    rwa [inv_mul_cancel] at this
  filter_upwards [ht.eventually (coc_small LT T e M n hx hb)] with τ hτ
  have h1 := coc_mul LT e x b σ (σ⁻¹ * τ) h
  rw [mul_inv_cancel_left] at h1
  rw [h1, add_sub_cancel_left]
  exact qB_mul_mem_Lat AI T ⟨_, (norm_tw LT e σ).le⟩ (act_mem_Lat AI σ hτ)

theorem fil_mul (e : ℕ) {M : ℤ} {x b : (LT l).R.BdR} {σ τ : GQ l}
    (h : qB (LT l) (tw LT e σ) * (LT l).actQdR σ x = x) {y z : ℚ_[l]}
    (hy : qB (LT l) y - coc LT e x b σ ∈ FilB (LT l) M)
    (hz : qB (LT l) z - coc LT e x b τ ∈ FilB (LT l) M) :
    qB (LT l) (y + tw LT e σ * z) - coc LT e x b (σ * τ) ∈ FilB (LT l) M := by
  have := add_mem hy (qB_mul_mem (tw LT e σ) (act_mem σ hz))
  convert this using 1
  rw [coc_mul LT e x b σ τ h, map_add (f := _), map_mul, map_sub, act_qB]
  ring

theorem nearZ_mul (e M : ℕ) {x b : (LT l).R.BdR} {σ τ : GQ l}
    (h : qB (LT l) (tw LT e σ) * (LT l).actQdR σ x = x)
    (hy : NearZ (LT l) M (coc LT e x b σ)) (hz : NearZ (LT l) M (coc LT e x b τ)) :
    NearZ (LT l) M (coc LT e x b (σ * τ)) := by
  obtain ⟨y, hy⟩ := hy
  obtain ⟨z, hz⟩ := hz
  let u : ℤ_[l] := ⟨tw LT e σ, (norm_tw LT e σ).le⟩
  refine ⟨y + u * z, ?_⟩
  rw [PadicInt.coe_add, PadicInt.coe_mul]
  exact fil_mul LT e h hy hz

theorem exists_pow_lt {ε : ℝ} (hε : 0 < ε) : ∃ n : ℕ, (l : ℝ) ^ (-(n : ℤ)) < ε := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl)
  exact ⟨n, by rwa [zpow_neg, zpow_natCast, ← inv_pow]⟩

theorem eq_zero_of_fil {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {M : ℕ}
    (hM : 1 ≤ M) {c : ℚ_[l]} (hc : qB P c ∈ FilB P (M : ℤ)) : c = 0 := by
  by_contra h
  obtain ⟨n, hn⟩ := exists_pow_lt (l := l) (norm_pos_iff.2 h)
  exact absurd (GlobalTheory.T.norm_le_of_qB_mem_Lat_alt l P AI T M n hM c (FilB_le_Lat AI hc)) (not_le.2 hn)

end GlobalTheory.ExpImage.IntCoc

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage Filter Topology IntCoc

theorem integral_cocycle_of_gen : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), IsGen (LT l).χQ K s g → ∀ α ∈ Ks K s, ∀ b ∈ FilB (LT l) 0, (∀ h ∈ Hinf K, NearZ (LT l) (e + 1) ((LT l).actQdR h b - b)) → NearZ (LT l) (e + 1) (qB (LT l) ((logChi LT g : ℤ_[l]) : ℚ_[l]) * (oB (LT l) α * tD (LT l) ^ e) + (qB (LT l) (((LT l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (LT l).actQdR g b - b)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (α) := by
  intro LT l _ AI T K s hs e g hg α hα b hb hH hgz
  set x := oB (LT l) α * tD (LT l) ^ e with hxdef
  have hM : 1 ≤ e + 1 := Nat.le_add_left 1 e
  have hx : x ∈ FilB (LT l) 0 :=
    FilB_zero_mul (oB_mem T α) (FilB_anti (by positivity) (FilB_pow tD_mem e))
  have hfix : ∀ σ ∈ Gj K s, qB (LT l) (tw LT e σ) * (LT l).actQdR σ x = x :=
    fun σ hσ => tw_act LT e σ α (hσ ⟨α, hα⟩)
  have hχ : IsCyc (LT l).χQ := (LT l).χQ_cyc
  have hact : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  have hH1 : ∀ h ∈ Hinf K, (LT l).χQ h = 1 := fun h hh =>
    ((cyc_basic l _ hχ).2.2 K h (Hinf_le_fix hh)).2.1 hh
  have hHG : ∀ h ∈ Hinf K, h ∈ Gj K s := fun h hh =>
    (((cyc_basic l _ hχ).2.2 K h (Hinf_le_fix hh)).1 s).2 (by
      rw [hH1 h hh, Units.val_one, sub_self, norm_zero]; positivity)
  have hHz : ∀ h ∈ Hinf K, NearZ (LT l) (e + 1) (coc LT e x b h) := fun h hh => by
    have := hH h hh
    convert this using 1
    simp [coc, tw, logChi_coe, hH1 h hh, logZl_one]
  have hpow : ∀ a : ℕ, NearZ (LT l) (e + 1) (coc LT e x b (g ^ a)) := fun a => by
    induction a with
    | zero => rw [pow_zero]; exact hHz 1 (one_mem _)
    | succ a ih => rw [pow_succ']; exact nearZ_mul LT e _ (hfix g hg.1) hgz ih
  have hall : ∀ σ ∈ Gj K s, NearZ (LT l) (e + 1) (coc LT e x b σ) := fun σ hσ => by
    refine GlobalTheory.T.padicInt_add_fil_closed_in_deRhamPeriodRing l _ AI T _ hM _ fun n => ?_
    have hcl := ((gen_dense l _ _ hact hχ K s hs).2 g hg).2.2 hσ
    obtain ⟨τ, ⟨h, hh, a, rfl⟩, hτ⟩ := ((mem_closure_iff_frequently.1 hcl).and_eventually
      (coc_near LT T e (e + 1) n hx hb σ (hfix σ hσ))).exists
    obtain ⟨z, hz⟩ := nearZ_mul LT e _ (hfix h (hHG h hh)) (hHz h hh) (hpow a)
    refine ⟨z, ?_⟩
    have := add_mem (FilB_le_Lat AI (n := n) hz) hτ
    rwa [sub_add_sub_cancel] at this
  choose! z hz using hall
  refine ⟨fun σ => (z σ : ℚ_[l]), fun σ _ => (z σ).2, ⟨?_, fun _ _ => Set.mem_univ _, ?_⟩, b, hb, ?_⟩
  · intro σ hσ
    rw [ContinuousWithinAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt (l := l) hε
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
      (coc_near LT T e (e + 1) n hx hb σ (hfix σ hσ))] with τ hτ h1
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (GlobalTheory.T.norm_le_of_qB_mem_Lat_alt l _ AI T _ n hM _ ?_) hn
    have := sub_mem (add_mem (FilB_le_Lat AI (n := n) (hz τ hτ)) h1) (FilB_le_Lat AI (hz σ hσ))
    convert this using 1
    rw [map_sub]
    ring
  · intro σ hσ τ hτ
    rw [← sub_eq_zero]
    refine eq_zero_of_fil T hM ?_
    have := sub_mem (hz _ (mul_mem hσ hτ)) (fil_mul LT e (hfix σ hσ) (hz σ hσ) (hz τ hτ))
    rwa [sub_sub_sub_cancel_right, ← map_sub] at this
  · intro σ hσ
    have := hz σ hσ
    rw [coc, ← sub_sub, Nat.cast_add_one] at this
    exact this

end GlobalTheory.ExpImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpanStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDeRham_of_isCrystalline_span : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → IsDR (P.PD K) ρ ∧ ∀ y ∈ DdR (P.PD K) ρ, ∃ (m : ℕ) (c : Fin m → ↥K.1) (d : Fin m → V ⊗[ℚ_[l]] P.R.B), (∀ i, d i ∈ Dcris (P.PD K) ρ) ∧ y = ∑ i, mulVdR (K := ↥K.1) (BdR := P.R.BdR) (V := V) (LL := ↥LL.1) (c i) (ιV (P.PD K) (LL := ↥LL.1) (V := V) (d i)) := by
  first | exact @GlobalTheory.Per.CrisDR.isDR_of_isCrys | exact GlobalTheory.Per.CrisDR.isDR_of_isCrys | (intros; apply GlobalTheory.Per.CrisDR.isDR_of_isCrys <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDomainClosedDiscGaugeCompletionOfEquivNormStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_closedDiscGaugeCompletion_of_equiv_norm : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (u : A) (ρ : ℝ≥0), ∀ (N : A → ℝ) (c : ℝ), 0 < c → (∀ x y, N (x * y) = N x * N y) → (∀ x y, N (x + y) ≤ max (N x) (N y)) → N (l : A) = (l : ℝ)⁻¹ → (∀ x, N x ≤ ‖toDisc l u ρ x‖) → (∀ x, c * ‖toDisc l u ρ x‖ ≤ N x) → IsDomain (Disc l u ρ) ∧ ∀ x y : Disc l u ρ, c ^ 2 * (‖x‖ * ‖y‖) ≤ ‖x * y‖ := by
  first | exact @GlobalTheory.BSP.DiscDomain.isDomain_disc | exact GlobalTheory.BSP.DiscDomain.isDomain_disc | (intros; apply GlobalTheory.BSP.DiscDomain.isDomain_disc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFCocIff
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.ResSel

namespace GlobalTheory.ResDual

def CupCob {Γ k M M' : Type} [Group Γ] [TopologicalSpace Γ] [CommRing k] [AddCommGroup M] [Module k M] [AddCommGroup M']
    [Module k M'] (χ : Γ → k) (ρ' : Representation k Γ M') (P : M →ₗ[k] M' →ₗ[k] k) (x : Γ → M) (y : Γ → M') : Prop :=
  ∃ f : Γ → k, IsLocallyConstant f ∧ ∀ g h, P (x g) (ρ' g (y h)) = χ g * f h - f (g * h) + f g

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (v : PlE D.host) (hv : v ∈ placesOver D.host.E (X.l i))

def IsFCoc {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) (y : ↥(DecV N v) → Fin r → X.O0 i) : Prop :=
  (fun g a => (bkP.br i v hv).toLL (y ((bkP.br i v hv).e.symm g) a)) ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv ρ)

variable {bkP i v hv}

theorem isFCoc_iff {r : ℕ} {ρ : GE N →* GL (Fin r) (X.O0 i)} {y : ↥(DecV N v) → Fin r → X.O0 i} :
    IsFCoc bkP i v hv ρ y ↔ ∃ c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv ρ),
      ∀ g a, c ((bkP.br i v hv).e g) a = (bkP.br i v hv).toLL (y g a) := by
  constructor
  · intro h
    exact ⟨_, h, fun g a => by simp only [MulEquiv.symm_apply_apply]⟩
  · rintro ⟨c, hc, h⟩
    have : (fun g a => (bkP.br i v hv).toLL (y ((bkP.br i v hv).e.symm g) a)) = c := by
      funext g a
      rw [← h, MulEquiv.apply_symm_apply]
    unfold IsFCoc
    rw [this]
    exact hc

theorem IsFCoc.continuous {r : ℕ} {ρ : GE N →* GL (Fin r) (X.O0 i)} {y : ↥(DecV N v) → Fin r → X.O0 i}
    (h : IsFCoc bkP i v hv ρ y) : Continuous y := by
  obtain ⟨c, hc, e⟩ := isFCoc_iff.1 h
  refine continuous_pi fun a => ?_
  have h1 : Continuous fun g => (bkP.br i v hv).toLL (y g a) := by
    simp_rw [← e]
    exact (continuous_apply a).comp (hc.1.1.comp (bkP.br i v hv).e_cont)
  have h2 : Continuous fun g => (bkP.br i v hv).eO (y g a) := continuous_induced_rng.2 h1
  simpa [Function.comp_def] using (bkP.br i v hv).eO_symm_cont.comp h2

theorem IsFCoc.cocycle {r : ℕ} {ρ : GE N →* GL (Fin r) (X.O0 i)} {y : ↥(DecV N v) → Fin r → X.O0 i}
    (h : IsFCoc bkP i v hv ρ y) (g g' : ↥(DecV N v)) :
    y (g * g') = y g + ((ρ g : GL (Fin r) (X.O0 i)) : Matrix (Fin r) (Fin r) (X.O0 i)).mulVec (y g') := by
  have e := h.1.2 ((bkP.br i v hv).e g) ((bkP.br i v hv).e g')
  funext a
  have inj : Function.Injective (bkP.br i v hv).toLL := Subtype.val_injective.comp (bkP.br i v hv).eO.injective
  apply inj
  have e2 := congrFun e a
  simp only [← map_mul, MulEquiv.symm_apply_apply, Pi.add_apply] at e2
  rw [e2, Pi.add_apply, map_add (f := _)]
  congr 1
  simp [LocBridge.rep, Matrix.mulVec, dotProduct, Matrix.toLinAlgEquiv'_apply]

end GlobalTheory.ResDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPrincipalIdealRingWittPowerSeriesAwayPrime
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isPrincipalIdealRing_away_l : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    IsPrincipalIdealRing (Localization.Away (l : bk.S)) := by
  intro l _ K bk
  have h : (l : bk.S) = C ((l : ℕ) : Wq l bk.a) := (map_natCast C l).symm
  rw [h]
  exact GlobalTheory.ChartRing.isPrincipalIdealRing_away_C (WittVector.irreducible l (k := Fq l bk.a)) _

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpSumKernelCoboundaryCharLeSixMul
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_kernel_le_six_mul :
    ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E r : ℕ) (x : L) (a : (L ≃ₐ[F] L) → ℤ), p.Prime → 0 < E → OrdIs L p E → AxIn F L p → (∀ σ : L ≃ₐ[F] L, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) → (∃ σ, ¬ (p : ℤ) ^ r ∣ a σ) → ∃ J : Subgroup (L ≃ₐ[F] L), (∀ σ, σ ∈ J ↔ (p : ℤ) ^ r ∣ a σ) ∧ jumpSum (wild F L) ⊤ J ≤ 6 * E := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E r x a hp hE hord hax hx hne
  have hadd : ∀ σ τ : L ≃ₐ[F] L, (p : ℤ) ^ r ∣ a (σ * τ) - a σ - a τ := fun σ τ =>
    _root_.GlobalTheory.PMon.Ram.coboundary_int_additive_mod F L p E r ⊤ x a hp hE hord (fun σ _ => hx σ) σ (Subgroup.mem_top _) τ (Subgroup.mem_top _)
  obtain ⟨J, hJn, σ₁, c, hJ, hc, hpc⟩ := GlobalTheory.T.character_mod_prime_pow_kernel_generator (L ≃ₐ[F] L) p r a hp hadd hne
  refine ⟨J, hJ, ?_⟩

  have hp0 : (p : L) ≠ 0 := by
    intro h0
    have h1 : ((p : 𝒪[L]) : L) = 0 := by simpa using h0
    have h2 : (p : 𝒪[L]) = 0 := Subtype.ext (by simpa using h1)
    unfold OrdIs at hord
    rw [h2, AddValuation.map_zero] at hord
    exact ENat.top_ne_coe E hord
  set M := IntermediateField.fixedField J with hM
  haveI : IsGalois F M := IsGalois.of_fixedField_normal_subgroup J
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.PMon.Ram.exists_integer_fixedField_trace_eq F L p r x a J σ₁ c hp0 hax hx (fun σ hσ => (hJ σ).1 hσ) hc
  obtain ⟨e, hordF, hEe, -⟩ := _root_.GlobalTheory.PMon.Ram.ordIs_of_ordIs_ext F L p E hord
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at hEe; omega
    · exact h

  have hdM : differentExponent F M < (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) * (3 * e) := by
    by_contra hle
    push_neg at hle
    obtain ⟨w, hw, hwt⟩ := _root_.GlobalTheory.PMon.Ram.exists_mem_maximalIdeal_pow_eq_trace_of_le_differentExponent F M (3 * e) hle z
    exact _root_.GlobalTheory.PMon.Ram.sq_mul_not_mem_maxIdeal_pow F p e c hp he hordF hpc w hw (hwt.trans hz)
  have htow := differentExponent_tower F M L
  have hram := ramificationIndex_tower F M L
  have hjs : jumpSum (wild F L) ⊤ J + 2 * differentExponent M L ≤ 2 * differentExponent F L := _root_.GlobalTheory.PMon.Ram.jumpSum_add_two_mul_differentExponent_fixedField_le F L J
  have key : jumpSum (wild F L) ⊤ J ≤ 2 * ((_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) * differentExponent F M) := by omega
  have hML : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) * differentExponent F M ≤ (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) * ((_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) * (3 * e)) :=
    Nat.mul_le_mul_left _ hdM.le
  have : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) * ((_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) * (3 * e)) * 2 = 6 * E := by
    dsimp only [ramificationIndex] at hram
    rw [hEe, hram]; ring
  nlinarith

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixPhiEquationToFamilyEquation
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem GlobalTheory.BSP.matrix_phi_eq_family : ∀ (R C : Type) [CommRing R] [CommRing C] (i : R →+* C) (φ : C → C) (e e' : R), Associated e e' → ∀ (d d' a a' b : ℕ) (P : Matrix (Fin d') (Fin d') R) (Q Q' : Matrix (Fin d) (Fin d) R), Q * Q' = e' ^ b • (1 : Matrix (Fin d) (Fin d) R) → ∀ Δ : Matrix (Fin d') (Fin d) C, i e' ^ a • (P.map i * Δ.map φ) = i e ^ a' • (Δ * Q.map i) → ∃ (h : ℕ) (c : Fin d' × Fin d → Fin d' × Fin d → R), ∀ j : Fin d' × Fin d, i e ^ h * Δ j.1 j.2 = ∑ k : Fin d' × Fin d, φ (Δ k.1 k.2) * i (c k j) := by
  intro R C _ _ i φ e e' he d d' a a' b P Q Q' hQ Δ hΔ
  obtain ⟨u, hu⟩ := he
  have hQm : Q.map i * Q'.map i = (i e') ^ b • (1 : Matrix (Fin d) (Fin d) C) := by
    rw [← Matrix.map_mul, hQ]
    ext x y
    by_cases hxy : x = y <;> simp [Matrix.one_apply, hxy]
  have key : (i e' ^ a • (P.map i * Δ.map φ)) * Q'.map i
      = (i e ^ a' • (Δ * Q.map i)) * Q'.map i := by rw [hΔ]
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc Δ, hQm, Matrix.mul_smul, Matrix.mul_one] at key
  refine ⟨a' + b, fun k j => ((u⁻¹ : Rˣ) : R) ^ b * e' ^ a * P j.1 k.1 * Q' k.2 j.2, ?_⟩
  intro j
  have hj := congrFun (congrFun key j.1) j.2
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, Finset.sum_mul] at hj
  rw [Finset.sum_comm] at hj
  have hu' : i e' = i e * i (u : R) := by rw [← hu, map_mul]
  have hinv : i ((u⁻¹ : Rˣ) : R) * i (u : R) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have goalR : ∑ k : Fin d' × Fin d, φ (Δ k.1 k.2) * i (((u⁻¹ : Rˣ) : R) ^ b * e' ^ a * P j.1 k.1 * Q' k.2 j.2)
      = i ((u⁻¹ : Rˣ) : R) ^ b * (i e' ^ a * ∑ k1 : Fin d', ∑ k2 : Fin d, i (P j.1 k1) * φ (Δ k1 k2) * i (Q' k2 j.2)) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k1 _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k2 _ => ?_
    simp only [map_mul, map_pow]; ring
  rw [goalR, hj, hu', mul_pow]
  calc i e ^ (a' + b) * Δ j.1 j.2
      = (i ((u⁻¹ : Rˣ) : R) * i (u : R)) ^ b * (i e ^ (a' + b) * Δ j.1 j.2) := by rw [hinv, one_pow, one_mul]
    _ = _ := by ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoGaloisInvariantsTorsionCoeffOfSelmerSetupStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noGaloisInvariantsTorsionCoeff_of_selmerSetup : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → NoInv i s κ := by
  first | exact @GlobalTheory.NoGlobalInv.noInv | exact GlobalTheory.NoGlobalInv.noInv | (intros; apply GlobalTheory.NoGlobalInv.noInv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OnePlaceAdmissibleOfGapConstantLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineIneq

theorem one_place_admissible_of_gap_constant_le : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.LiftingTheory.adm22 D HW F := by
  intro D HW F l _ K LL
  exact (GlobalTheory.Per.FontaineBound.fontaineLe_of_tied l (D.loc l) (D.locA l) (D.locT l) K LL).1

end GlobalTheory.FontaineIneq
end

