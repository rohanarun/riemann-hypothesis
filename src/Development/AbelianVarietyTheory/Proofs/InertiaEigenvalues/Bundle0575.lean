module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LineOfSingleJump
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0564
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0547
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0563
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0555
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0566
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0346
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0567
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0556

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineTwistCrystallineCharacterJumpsShift
section
noncomputable section

namespace GlobalTheory.TwistRepCrys

open _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem finrank_fildR_of_equiv {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (e : V ≃ₗ[LL] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    finrank LL (FildR PD ρ τ a) = finrank LL (FildR PD ρ' τ a) := by
  rw [GlobalTheory.HTW.FildR_eq_comap PD ρ ρ' e.toLinearMap e.injective he τ a]
  exact (LinearEquiv.ofSubmodule'
    (AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)) (FildR PD ρ' τ a)).finrank_eq

theorem multV_of_equiv {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (e : V ≃ₗ[LL] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    multV PD ρ τ a = multV PD ρ' τ a := by
  rw [multV, multV, finrank_fildR_of_equiv PD e he, finrank_fildR_of_equiv PD e he]

theorem multV_of_le_one (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL)
    [FiniteDimensional LL (DdRE PD ρ τ)] (h1 : finrank LL (DdRE PD ρ τ) ≤ 1) {b : ℤ}
    (hb : IsJumpV PD ρ τ b) (a : ℤ) : multV PD ρ τ a = if a = b then 1 else 0 := by
  haveI : ∀ a, FiniteDimensional LL (FildR PD ρ τ a) := fun a =>
    Submodule.finiteDimensional_of_le (S₂ := DdRE PD ρ τ) inf_le_left
  have anti : Antitone (FildR PD ρ τ) := fun a a' haa =>
    inf_le_inf_left _ (GlobalTheory.Cmp.SmallJumps.filV_anti PD haa)
  have mono : ∀ a a', a ≤ a' → finrank LL (FildR PD ρ τ a') ≤ finrank LL (FildR PD ρ τ a) :=
    fun a a' h => Submodule.finrank_mono (anti h)
  have le1 : ∀ a, finrank LL (FildR PD ρ τ a) ≤ 1 := fun a =>
    (Submodule.finrank_mono (inf_le_left : FildR PD ρ τ a ≤ DdRE PD ρ τ)).trans h1
  have lt : finrank LL (FildR PD ρ τ (b + 1)) < finrank LL (FildR PD ρ τ b) :=
    Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (anti (by omega)) hb)
  have := le1 a
  have := le1 b
  rw [multV]
  rcases lt_trichotomy a b with h | h | h
  · have := mono (a + 1) b (by omega)
    have := mono a (a + 1) (by omega)
    rw [if_neg h.ne]
    omega
  · subst h
    rw [if_pos rfl]
    omega
  · have := mono (b + 1) a (by omega)
    have := mono a (a + 1) (by omega)
    rw [if_neg h.ne']
    omega

def transport (e : V ≃ₗ[LL] V') (ρ' : Representation LL G V') : Representation LL G V where
  toFun g := e.symm.toLinearMap ∘ₗ ρ' g ∘ₗ e.toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

omit [Module Qp V] [IsScalarTower Qp LL V] [Module Qp V'] [IsScalarTower Qp LL V'] in
theorem transport_apply (e : V ≃ₗ[LL] V') (ρ' : Representation LL G V') (g : G) (x : V) :
    e (transport e ρ' g x) = ρ' g (e x) := by
  simp [transport]

end Generic

theorem isCrys_and_multV_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (χ : ↥(GK K) →* (↥LL.1)ˣ), IsTwistRep χ ρ ρ' → IsCrys (P.PD K) (charRep χ) → IsCrys (P.PD K) ρ → IsCrys (P.PD K) ρ' ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a b : ℤ), IsJumpV (P.PD K) (charRep χ) τ b → multV (P.PD K) ρ' τ (a + b) = multV (P.PD K) ρ τ a := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' χ ⟨e, he⟩ cχ cρ
  let f : (Fin 1 → ↥LL.1) ≃ₗ[↥LL.1] ↥LL.1 := LinearEquiv.funUnique (Fin 1) ↥LL.1 ↥LL.1
  let ν := transport f (charRep χ)
  have hν : ∀ g x, ν g x = ((χ g : (↥LL.1)ˣ) : ↥LL.1) • x := fun g x => by
    apply f.injective
    rw [transport_apply, map_smul]
    rfl
  have hρ : ∀ g x, transport e ρ' g x = ((χ g : (↥LL.1)ˣ) : ↥LL.1) • ρ g x := fun g x => by
    apply e.injective
    rw [transport_apply, he, map_smul]
  have cν : IsCrys (P.PD K) ν :=
    GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD K) f.symm (fun g x => by
      apply f.injective
      rw [transport_apply, f.apply_symm_apply, f.apply_symm_apply]) cχ
  refine ⟨GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD K) e (transport_apply e ρ')
    ((GlobalTheory.TwistCrys.isCrys_iff_of_twist GlobalTheory.MemLoc.fontaineBcris l P AI T K LL V ρ _ ν _ hν hρ cν).1 cρ),
    fun τ a b hb => ?_⟩
  obtain ⟨hfin, hle, -⟩ := (_root_.GlobalTheory.Per.Components.components_finrank l P AI T K LL ↥LL.1 (charRep χ)).1 τ
  rw [finrank_self] at hle
  rw [← multV_of_equiv (P.PD K) e (transport_apply e ρ')]
  refine GlobalTheory.TwistJump.multV_twist_char l P AI T K LL V ρ _ ν _ hν hρ
    (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T K LL _ ν cν).1 τ b (fun c => ?_) a
  rw [multV_of_equiv (P.PD K) f (transport_apply f (charRep χ))]
  exact multV_of_le_one (P.PD K) (charRep χ) τ hle hb c

end GlobalTheory.TwistRepCrys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBetaOfDiscCocycleStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_beta_of_disc_cocycle_alt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (κ : ↥(GK K) → Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (φε : ↥(GK K) → Matrix (Fin d) (Fin d) (Ainf l)) (H : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → IsUnit H → (∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) bk.S), (∀ a b, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) a b) ∧ ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → ∀ a b, bk.iS bk.E ^ m ∣ (κ g * (Λ.map bk.iS).map G - Λ.map bk.iS) a b) → (∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → G (bk.iS (frobS l bk.a bk.E)) ^ N • (H.map i * (φε g).map bk.iA) = bk.iS (frobS l bk.a bk.E) ^ N • (κ g * (H.map i).map G)) → ∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), (∀ a b, bk.E ∣ (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) a b) ∧ ∀ (g : ↥(GK K)) a b, bk.ev bk.E ^ m ∣ (φε g * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev) a b := by
  first | (exact @GlobalTheory.BKLim.exists_beta_of_disc_cocycle) | (exact GlobalTheory.BKLim.exists_beta_of_disc_cocycle) | (intros; apply GlobalTheory.BKLim.exists_beta_of_disc_cocycle  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedOfPhiEquationDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_root_radii (l : ℕ) (hl : 2 ≤ l) (ρ₀ : ℝ≥0) (h0 : 0 < ρ₀) (h1 : ρ₀ < 1) :
    ∃ r : ℕ → ℝ≥0, r 0 = ρ₀ ∧ (∀ n, r (n + 1) ^ l = r n) ∧ (∀ n, ρ₀ ≤ r n) ∧ (∀ n, r n < 1) ∧
      ∀ ρ₁ : ℝ≥0, ρ₁ < 1 → ∃ n, ρ₁ ≤ r n := by
  have hl0 : l ≠ 0 := by omega
  let r : ℕ → ℝ≥0 := fun n => ρ₀ ^ (((l ^ n : ℕ) : ℝ)⁻¹)
  have hp : ∀ n, r n ^ (l ^ n) = ρ₀ := fun n => NNReal.rpow_inv_natCast_pow _ (pow_ne_zero _ hl0)
  have hlt : ∀ n, r n < 1 := fun n => by
    by_contra h
    have := one_le_pow₀ (not_lt.1 h) (n := l ^ n)
    rw [hp] at this
    exact absurd h1 (not_lt.2 this)
  refine ⟨r, by simpa using hp 0, fun n => ?_, fun n => ?_, hlt, fun ρ₁ h => ?_⟩
  · refine (pow_left_inj₀ zero_le zero_le (pow_ne_zero n hl0)).1 ?_
    rw [← pow_mul, ← pow_succ', hp, hp]
  · rw [← hp n]
    exact pow_le_of_le_one zero_le (hlt n).le (pow_ne_zero _ hl0)
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h0 h
    refine ⟨n, le_of_lt (lt_of_pow_lt_pow_left₀ (l ^ n) zero_le ?_)⟩
    rw [hp]
    exact (pow_le_pow_of_le_one zero_le h.le (Nat.lt_pow_self (by omega)).le).trans_lt hn

theorem norm_l_pow_mul_disc (l : ℕ) [Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (k : ℕ)
    (y : Disc l u ρ) : ‖((l : ℕ) : Disc l u ρ) ^ k * y‖ = ‖y‖ / (l : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A u ρ).2.1, ih, div_div, pow_succ]

theorem exists_bounded_of_phi_equation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ (φ : A →+* A), φ (s X) = s X ^ l → ∀ (Φ : Disc l (s X) bk.ρ₀ →+* Disc l (s X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) φ Φ → ∀ (κ : Type) (c : κ → κ → A), (∀ i (n : ℕ), {j | c i j ∉ (bk.J ^ n).map s}.Finite) → ∀ (h : ℕ) (V : κ → Disc l (s X) bk.ρ₀), Filter.Tendsto V Filter.cofinite (nhds 0) → (∀ j, HasSum (fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j)) (toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j)) → ∃ (k : ℕ) (v : κ → A), (∀ j, toDisc l (s X) bk.ρ₀ (v j) = (l : Disc l (s X) bk.ρ₀) ^ k * V j) ∧ ∀ n : ℕ, {j | v j ∉ (bk.J ^ n).map s}.Finite := by
  intro l hl K bk A _ s ι tb φ hφ Φ hΦ κ c hc h V hV hs
  obtain ⟨-, -, ⟨h0, h1, -⟩, -⟩ := _root_.GlobalTheory.BSP.flat_disc l K bk
  have hl2 := hl.out.two_le
  obtain ⟨r, r0, rs, rle, rlt, rlim⟩ := exists_root_radii l hl2 bk.ρ₀ h0 h1
  have rpos : ∀ n, 0 < r n := fun n => h0.trans_le (rle n)
  have hR : ∀ n, ∃ R : Disc l (s X) (r n) →+* Disc l (s X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R := fun n =>
    GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l A A (RingHom.id A) (s X) (s X) (r n) bk.ρ₀ 1 h0 (by simp) (by simpa using rle n)
  choose R hR using hR
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ j, ‖V j‖ ≤ C := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto_cofinite hV)
    exact ⟨max C 0, le_max_right _ _, fun j => (hC _ ⟨j, rfl⟩).trans (le_max_left _ _)⟩
  set m := bk.Ep.natDegree * h with hm
  have h0' : (0 : ℝ) < bk.ρ₀ := h0
  have key : ∀ n, ∃ U : κ → Disc l (s X) (r n), Filter.Tendsto U Filter.cofinite (nhds 0) ∧
      (∀ j, R n (U j) = V j) ∧ ∀ j, ‖U j‖ ≤ C * ((r n : ℝ) / bk.ρ₀) ^ m := by
    intro n
    induction n with
    | zero =>
      have gen : ∀ (ρ : ℝ≥0) (R₀ : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀), ρ = bk.ρ₀ →
          IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R₀ → ∃ U : κ → Disc l (s X) ρ, Filter.Tendsto U Filter.cofinite (nhds 0) ∧
          (∀ j, R₀ (U j) = V j) ∧ ∀ j, ‖U j‖ ≤ C * ((ρ : ℝ) / bk.ρ₀) ^ m := by
        rintro ρ R₀ rfl hR₀
        refine ⟨V, hV, fun j => ?_, fun j => ?_⟩
        · rw [hR₀.unique (isDiscMap_id l (s X) bk.ρ₀)]; rfl
        · rw [div_self h0'.ne', one_pow, mul_one]; exact hC j
      exact gen _ _ r0 (hR 0)
    | succ n ih =>
      obtain ⟨U, hU, hRU, hn⟩ := ih
      obtain ⟨U', hU', hRU', hn'⟩ := GlobalTheory.T.exists_phiContraction_disc_step l K bk A s ι tb φ hφ Φ hΦ κ c hc h V hs (r n) (r (n + 1))
        (rle n) (rlt n) (rs n) (R n) (R (n + 1)) (hR n) (hR (n + 1)) U _ (by positivity) hU hRU hn
      refine ⟨U', hU', hRU', fun j => ?_⟩
      have hp : (0 : ℝ) < r (n + 1) := rpos _
      have hle : (r n : ℝ) ≤ r (n + 1) * r (n + 1) := by
        have : r n ≤ r (n + 1) ^ 2 := by
          rw [← rs n]; exact pow_le_pow_of_le_one zero_le (rlt _).le hl2
        rw [← sq]; exact_mod_cast this
      refine le_of_mul_le_mul_left ((hn' j).trans ?_) (pow_pos hp m)
      rw [mul_left_comm, ← mul_pow, ← mul_div_assoc]
      gcongr
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C * (1 / (bk.ρ₀ : ℝ)) ^ m)
    (show (1 : ℝ) < l by exact_mod_cast hl.out.one_lt)
  have hlk : (0 : ℝ) < (l : ℝ) ^ k := pow_pos (Nat.cast_pos.2 hl.out.pos) k
  have hv : ∀ j, ∃ a, toDisc l (s X) bk.ρ₀ a = (l : Disc l (s X) bk.ρ₀) ^ k * V j := fun j =>
    GlobalTheory.T.exists_base_eq_of_closedDisc_extends_norm_le_one l K bk A s ι tb bk.ρ₀ h0 h1 _ fun ρ₁ hρ₁ => by
      obtain ⟨n, hn⟩ := rlim ρ₁ hρ₁
      obtain ⟨U, -, hRU, hU⟩ := key n
      refine ⟨r n, R n, (l : Disc l (s X) (r n)) ^ k * U j, hn, rle n, rlt n, hR n, ?_, ?_⟩
      · rw [map_mul, map_pow, map_natCast, hRU]
      · rw [norm_l_pow_mul_disc, div_le_one hlk]
        refine (hU j).trans (le_trans ?_ hk.le)
        have : (r n : ℝ) ≤ 1 := (rlt n).le
        gcongr
  choose v hv using hv
  refine ⟨k, v, hv, fun n => ?_⟩
  obtain ⟨ε, hε, hJ⟩ := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk A s ι tb bk.ρ₀ h0 h1).2.1 n
  have ht : Filter.Tendsto (fun j => (l : Disc l (s X) bk.ρ₀) ^ k * V j) Filter.cofinite (nhds 0) := by
    simpa using hV.const_mul ((l : Disc l (s X) bk.ρ₀) ^ k)
  have he := Filter.eventually_cofinite.1 (ht.eventually (Metric.closedBall_mem_nhds 0 hε))
  refine he.subset fun j hj hj' => hj (hJ _ ?_)
  rw [hv]
  simpa using hj'

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescentSolutionLiftModPrismIdealStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_solution_lift_mod_prism_ideal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ z : Fin d → C.A, (∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ 1) → ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ 1) ∧ (fun i => p.f (z' i)) = (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) := by
  first | exact @GlobalTheory.BSP.lift_solution | exact GlobalTheory.BSP.lift_solution | (intros; apply GlobalTheory.BSP.lift_solution <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisModPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.EtBasis

theorem zW_dvd {l : ℕ} [Fact l.Prime] {n : ℕ} {x : ℤ_[l]} (h : (l : ℤ_[l]) ^ n ∣ x) :
    (l : WCb l) ^ n ∣ algebraMap ℤ_[l] (WCb l) x := by
  simpa [map_pow, map_natCast] using map_dvd (algebraMap ℤ_[l] (WCb l)) h

theorem flatKer {l : ℕ} [Fact l.Prime] {d d' n : ℕ} (Pi : Matrix (Fin d) (Fin d') ℤ_[l])
    (f : Matrix (Fin d') (Fin d') ℤ_[l])
    (hker : ∀ v : Fin d' → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ (Pi *ᵥ v) i) ↔ ∃ w, v = f *ᵥ w)
    (u : Fin d' → WCb l) (hu : ∀ i, (l : WCb l) ^ n ∣ (zW Pi *ᵥ u) i) : ∃ w, u = zW f *ᵥ w := by
  classical
  haveI : Module.IsTorsionFree ℤ_[l] (WCb l) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact (WittVector.map_injective _ (ZMod.castHom_injective (Cb l))).comp (WittVector.equiv l).symm.injective
  choose y hy using hu
  let x : ((Fin d' ⊕ Fin d) → ℤ_[l]) →ₗ[ℤ_[l]] WCb l := Fintype.linearCombination ℤ_[l] (Sum.elim u y)
  let B : Matrix (Fin d' ⊕ Fin d) (Fin d) ℤ_[l] :=
    Matrix.fromRows Piᵀ (Matrix.diagonal fun _ => -((l : ℤ_[l]) ^ n))
  let F : (Fin d → ℤ_[l]) →ₗ[ℤ_[l]] ((Fin d' ⊕ Fin d) → ℤ_[l]) := Matrix.toLin' B
  have hxF : x ∘ₗ F = 0 := by
    ext i : 2
    have := hy i
    simp [x, F, B, Fintype.linearCombination_apply, Fintype.sum_sum_type, Matrix.mulVec, dotProduct,
      Algebra.smul_def, Matrix.diagonal_apply] at this ⊢
    rw [this]
    simp [apply_ite (algebraMap ℤ_[l] (WCb l)), ite_mul]
  obtain ⟨k, a, yy, hx, haF⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxF
  let A : Fin k → (Fin d' ⊕ Fin d) → ℤ_[l] := fun m p => a (fun q => if p = q then 1 else 0) m
  have hyy : ∀ v : Fin k →₀ ℤ_[l], yy v = ∑ m, v m • yy (Finsupp.single m 1) := by
    intro v
    have : yy = Finsupp.linearCombination ℤ_[l] (fun m => yy (Finsupp.single m 1)) := by
      refine Finsupp.lhom_ext fun m r => ?_
      rw [Finsupp.linearCombination_single, ← map_smul, Finsupp.smul_single_one]
    conv_lhs => rw [this]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    simp
  have hA : ∀ m i, (Pi *ᵥ fun j => A m (Sum.inl j)) i = (l : ℤ_[l]) ^ n * A m (Sum.inr i) := by
    intro m i
    have h0 := congrArg (fun v => v m) (LinearMap.congr_fun haF (_root_.Pi.single i 1))
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Finsupp.coe_zero, _root_.Pi.zero_apply] at h0
    rw [LinearMap.pi_apply_eq_sum_univ] at h0
    simp [A, F, B, Fintype.sum_sum_type, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, _root_.Pi.single_apply] at h0 ⊢
    linear_combination h0
  have hu' : ∀ j, u j = ∑ m, A m (Sum.inl j) • yy (Finsupp.single m 1) := by
    intro j
    have h1 : u j = x (fun q => if Sum.inl j = q then 1 else 0) := by
      simp [x, Fintype.linearCombination_apply, Fintype.sum_sum_type]
    rw [h1, hx, LinearMap.comp_apply, hyy]
  choose w hw using fun m => (hker (fun j => A m (Sum.inl j))).1 (fun i => ⟨A m (Sum.inr i), hA m i⟩)
  refine ⟨fun t => ∑ m, w m t • yy (Finsupp.single m 1), funext fun j => ?_⟩
  rw [hu' j]
  have h2 : ∀ m, A m (Sum.inl j) = ∑ t, f j t * w m t := fun m => congrFun (hw m) j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h2, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.mul_sum, Finset.sum_mul, Algebra.smul_def, Matrix.map_apply,
    map_sum, map_mul, mul_assoc]
  exact Finset.sum_comm

theorem kerW {l : ℕ} [Fact l.Prime] {d d' n : ℕ} (Pi : Matrix (Fin d) (Fin d') ℤ_[l])
    (f : Matrix (Fin d') (Fin d') ℤ_[l])
    (hker : ∀ v : Fin d' → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ (Pi *ᵥ v) i) ↔ ∃ w, v = f *ᵥ w)
    (u : Fin d' → WCb l) : (∀ i, (l : WCb l) ^ n ∣ (zW Pi *ᵥ u) i) ↔ ∃ w, u = zW f *ᵥ w := by
  refine ⟨flatKer Pi f hker u, ?_⟩
  rintro ⟨w, rfl⟩ i
  have hPf : ∀ i j, (l : ℤ_[l]) ^ n ∣ (Pi * f) i j := by
    intro i j
    have := (hker (f *ᵥ _root_.Pi.single j 1)).2 ⟨_, rfl⟩ i
    rw [Matrix.mul_apply]
    simpa [Matrix.mulVec, dotProduct, _root_.Pi.single_apply] using this
  have hm : zW Pi * zW f = zW (Pi * f) := (Matrix.map_mul).symm
  rw [Matrix.mulVec_mulVec, hm]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (zW_dvd (hPf i j)) _

end GlobalTheory.BKLim.EtBasis


open GlobalTheory.BKLim.EtBasis in
theorem GlobalTheory.BKLim.etBasis_modPow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d d' n : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (ρ' : ↥(GK K) →* GL (Fin d') ℤ_[l]) (F' : Pre bk N d' fun g => (ρ' g).val) (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])), 1 ≤ n → Onto (fun g => (ρ g).val) (fun g => (ρ' g).val) Pi n → ∃ (Tn : Matrix (Fin d) (Fin d) (WCb l)) (R : Matrix (Fin d) (Fin d') (WCb l)) (R' : Matrix (Fin d') (Fin d) (WCb l)), IsUnit Tn ∧ (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - Tn * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T * R' - Tn) i j) := by
  intro l _ K bk τ hτ N d d' n ρ ρ' F' Pi hn hOnto
  obtain ⟨f, ρ'', hdet, hfeq, hker⟩ := _root_.GlobalTheory.KerLat.exists_kernel_lattice l (↥(GK K)) d d' n ρ ρ' Pi hOnto
  obtain ⟨T'', P, hT'', hP, hfT⟩ := _root_.GlobalTheory.EtBasis.main l K bk τ hτ N d' (fun g => (ρ' g).val)
    (fun g => (ρ'' g).val) F' f hdet (fun g => (ρ'' g).isUnit) hfeq
  have hTd := (Matrix.isUnit_iff_isUnit_det _).1 F'.unit
  have hT''d := (Matrix.isUnit_iff_isUnit_det _).1 hT''
  apply _root_.GlobalTheory.SmithQuot.main l K bk d d' n (zW Pi * F'.T) P hn hP
  · obtain ⟨S, hS⟩ := hOnto.surj
    refine ⟨F'.T⁻¹ * zW S, fun i j => ?_⟩
    have : zW Pi * F'.T * (F'.T⁻¹ * zW S) - 1 = zW (Pi * S - 1) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc F'.T, Matrix.mul_nonsing_inv _ hTd, Matrix.one_mul]
      show _ = (algebraMap ℤ_[l] (WCb l)).mapMatrix (Pi * S - 1)
      rw [map_sub, map_one, RingHom.mapMatrix_apply, Matrix.map_mul]
    rw [this]
    exact zW_dvd (hS i j)
  · intro v
    rw [← Matrix.mulVec_mulVec, kerW Pi f hker]
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨T''⁻¹ *ᵥ w, ?_⟩
      have h1 : zW f = F'.T * P * T''⁻¹ := by
        rw [← hfT, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT''d, Matrix.mul_one]
      calc v = F'.T⁻¹ *ᵥ (F'.T *ᵥ v) := by
            rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mulVec]
        _ = P *ᵥ (T''⁻¹ *ᵥ w) := by
            rw [hw, h1]
            simp only [Matrix.mulVec_mulVec]
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mul]
    · rintro ⟨w, rfl⟩
      exact ⟨T'' *ᵥ w, by simp only [Matrix.mulVec_mulVec, hfT]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisDescentDatumAndStableStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisDescentDatum_and_stable : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), (∀ g : Gl l, sQ l g ∈ ϖ.GfieldInf a → ∀ v : ME P, I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v) → (∀ (g : Gl l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ → ∀ v : ME P, v.1 ∈ P.M → ∃ v' : ME P, v'.1 ∈ P.M ∧ I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v') → (∃ Δ : Descent P, IsGalDesc (sQ l) I Δ) ∧ (Ident.Stable (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ g : Gl l, ∀ v ∈ LA (thetaW a LL) ϖ P, I.act (sQ l g) g v ∈ LA (thetaW a LL) ϖ P) := by
  first | exact @GlobalTheory.BKGal.GalDescent.exists_galDesc_and_stable | exact GlobalTheory.BKGal.GalDescent.exists_galDesc_and_stable | (intros; apply GlobalTheory.BKGal.GalDescent.exists_galDesc_and_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulUnramifiedEqWittBcris
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.TeichmullerPowerUnit

theorem exists_pow_mul_u_eq_aB : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (c : ↥(MaximalUnramifiedExtension l)), (c : Om l) ∈ K.1 → ∃ (n : ℕ) (w : Wq l bk.a), (l : Per.Bcris l) ^ n * C.u c = Per.aB l (wA l bk.a w) := by
  intro l _ K bk C c hc
  obtain ⟨n, w, hw⟩ := _root_.GlobalTheory.UnrWitt.exists_pow_mul_eq_theta l K bk (c : Om l) hc c.2
  have ho := _root_.GlobalTheory.SeedSec.o_eq_aDp_wA l bk.a C w ((l : Om l) ^ n * (c : Om l)) hw
  refine ⟨n, w, ?_⟩
  apply GlobalTheory.Published.FontaineBcris.iotaInj _root_.GlobalTheory.MemLoc.fontaineBcris C
  have hB : C.ι (Per.aB l (wA l bk.a w)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (wA l bk.a w)) :=
    GlobalTheory.MemLoc.ULaws.iota_aB C (wA l bk.a w)
  rw [hB, ← ho, map_mul, map_pow, map_natCast, C.ι_u, map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast]

end GlobalTheory.TeichmullerPowerUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtIn
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTransfer

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def ExtIn (Y : Model Xo c β) (S : Set Y.X) (T : CDVR) (io : c.F →+* T.Fr) (x : Sp T.Fr ⟶ Xo.X) : Prop :=
  ∃ (y' : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c), z ≫ pullback.fst _ _ = x ∧ z ≫ pullback.snd _ _ = spMap io ∧
    z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' ∧ Set.range y' ⊆ S

end GlobalTheory.GoodTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixesCrystallineImageDescentDatumStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_fixes_crystalline_image_descentDatum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T), IsCrisCmp I jB → ∀ C : Conn P, C.nabla = P.nabla → Ident.Taylor (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) C → IsHoriz (thetaW a LL) ϖ (sQ l) P jB := by
  first | exact @GlobalTheory.HorizXi.galois_fixes_xi | exact GlobalTheory.HorizXi.galois_fixes_xi | (intros; apply GlobalTheory.HorizXi.galois_fixes_xi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRegroupAntitonePartitionsByDegreeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_regroup_antitonePartitions_by_degree : ∀ {m : ℕ} (G : (Fin m → ℕ) → ℂ),
    (Summable fun l : {l : Fin m → ℕ // Antitone l} => ‖G l.1‖) →
    Summable (fun d => ‖∑ l ∈ GlobalTheory.JSW.antiParts m d, G l‖) ∧
    ∀ s, HasSum (fun d => ∑ l ∈ GlobalTheory.JSW.antiParts m d, G l) s →
      HasSum (fun l : {l : Fin m → ℕ // Antitone l} => G l.1) s := by
  first | exact @GlobalTheory.JSW.regroup_antiParts | exact GlobalTheory.JSW.regroup_antiParts | (intros; apply GlobalTheory.JSW.regroup_antiParts <;> assumption)
end

