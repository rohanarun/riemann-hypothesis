module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LineOfSingleJump
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsJumpMultiset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockCharactersCrystallineOfRules
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0449
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComponentEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.ReindexedFiltrationComparison
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0237
public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.MemIntegralClosureIffMemBall
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.ExistsDen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.IsEquivAdicAbvNormAbv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0656
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0657
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
section
noncomputable section

namespace GlobalTheory.TopSteps.CrysRules

open GlobalTheory.AdmLoc _root_.Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct Module
open GlobalTheory.TwistJump GlobalTheory.Cmp.JumpDict GlobalTheory.Cmp.SmallJumps

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

theorem multV_of_only_zero {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (h : ∀ a, IsJumpV PD ρ τ a → a = 0) (a : ℤ) :
    multV PD ρ τ a = if a = 0 then (finrank LL (DdRE PD ρ τ) : ℤ) else 0 := by
  have hs : ∀ a : ℤ, a ≠ 0 → FildR PD ρ τ (a + 1) = FildR PD ρ τ a := fun a ha => by
    by_contra hne
    exact ha (h a hne)
  split_ifs with ha
  · subst ha
    have h0 : ∀ b ≤ (0 : ℤ), FildR PD ρ τ b = FildR PD ρ τ 0 := fun b hb => by
      induction b, hb using Int.leInductionDown with
      | base => rfl
      | pred n hn ih => rw [← hs (n - 1) (by omega), sub_add_cancel, ih]
    have h1 : ∀ b ≥ (1 : ℤ), FildR PD ρ τ b = FildR PD ρ τ 1 := fun b hb => by
      induction b, hb using Int.leInduction with
      | base => rfl
      | succ n hn ih => rw [hs n (by omega), ih]
    have e0 : FildR PD ρ τ 0 = DdRE PD ρ τ := by
      refine le_antisymm inf_le_left fun x hx => ?_
      obtain ⟨b, hb⟩ := filV_exh PD (LL := LL) x
      rw [← h0 (min b 0) (min_le_right _ _)]
      exact ⟨hx, filV_anti PD (min_le_left b 0) hb⟩
    have e1 : FildR PD ρ τ (0 + 1) = ⊥ := by
      rw [eq_bot_iff, zero_add]
      intro x hx
      refine filV_sep PD (LL := LL) x fun b => ?_
      rw [← h1 (max b 1) (le_max_right _ _)] at hx
      exact filV_anti PD (le_max_left b 1) hx.2
    rw [multV, e0, e1]
    simp
  · rw [multV, hs a ha, sub_self]

theorem ddRE_ne_bot [Algebra.IsSeparable Qp K] (hs : ∃ s ∈ PD.Fil (-1), PD.ι PD.t * s = 1)
    (ν : Representation LL G LL) (χ : G → LL) (hν : ∀ g x, ν g x = χ g • x)
    {m : ℕ} (k : Fin m → ℤ) (β : Fin m → BdR) (d : Fin m → LL ⊗[Qp] BdR)
    (hd : ∀ i, d i ∈ DdR PD ν ∧ d i ∈ FilV PD (LL := LL) (V := LL) (k i))
    (h1 : (1 : LL ⊗[Qp] BdR) =
      ∑ i, AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL) (LinearMap.mulLeft Qp (β i)) (d i))
    (τ : K →ₐ[Qp] LL) : DdRE PD ν τ ≠ ⊥ := by
  intro h0
  have hm := GlobalTheory.BlockJumps.multV_twist PD hs (1 : Representation LL G LL) 0 (fun g x => by simp) τ 0
  have hb : FildR PD (1 : Representation LL G LL) τ 0 = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hz : ∀ i, act LL (AlgHom.id LL LL) (d i) y = 0 := fun i => by
      have := act_maps PD (AlgHom.id LL LL) 1 ν τ (hd i).2 (fun g y hy => by
        have hi : actVdR PD ν g (d i) = d i := by
          have := (Submodule.mem_iInf _).1 (hd i).1 g
          simpa [sub_eq_zero] using this
        rw [actVdR_twist PD 1 ν g (χ g) (fun x => by simp [hν]), actVdR_act, hy, ← LinearMap.smul_apply,
          ← map_smul, ← actVdR_char PD ν g (χ g) (hν g), hi]) y hy
      have h2 := this.1
      rw [h0] at h2
      exact h2
    have : y = act LL (AlgHom.id LL LL) (1 : LL ⊗[Qp] BdR) y := by rw [map_one]; rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Submodule.mem_bot, this, h1, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mulLeft, map_mul, Module.End.mul_apply, hz, map_zero]
  rw [multV, hb] at hm
  simp at hm
  omega

end Generic

section Tied

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (K LL : FinExt l)
include T

theorem exists_inverse_fontaineElement_mem_fil_neg_one : ∃ s ∈ (P.PD K).Fil (-1), (P.PD K).ι (P.PD K).t * s = 1 := by
  obtain ⟨s, hs, h⟩ := GlobalTheory.ThetaTie.exists_inverse_fontaineElement_mem_fil_neg_one T
  refine ⟨s, ?_, by rw [P.PD_ι, P.period_datum_t_eq, h]⟩
  rw [← SetLike.mem_coe, P.PD_Fil K (Formalism.MainNotions.LocalSituation.botExt l)]
  exact hs

theorem isDR {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (h : IsCrys (P.PD K) ρ) :
    IsDR (P.PD K) ρ := by
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ
  refine (GlobalTheory.DRFil.isDR_of_isCrys (P.PD K) (fun m c hc b hb => GlobalTheory.T.injective_tensor_Bcris_to_BdR l P AI T K m c hc b ?_) ρ h2 h).1
  simpa only [P.PD_ι] using hb

theorem multV_shift {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    (ρ ρ' : Representation ↥LL.1 ↥(GK K) V) (θ : ↥(GK K) →* (↥LL.1)ˣ)
    (hρ : ∀ g x, ρ' g x = (θ g : ↥LL.1) • ρ g x) (hθ : IsCrys (P.PD K) (charRep θ))
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ)
    (h : ∀ a, multV (P.PD K) (charRep θ) τ a = (({b} : Multiset ℤ).count a : ℤ)) (a : ℤ) :
    multV (P.PD K) ρ' τ (a + b) = multV (P.PD K) ρ τ a := by
  haveI := (P.PD K).finK
  obtain ⟨m, k, β, d, hd, h1⟩ := GlobalTheory.T.deRham_comparison_isFiltered l P AI T K LL ↥LL.1 (charRep θ) (isDR T K LL _ hθ) 0 1
    ⟨1 ⊗ₜ ⟨1, (P.PD K).one_mem⟩, rfl⟩
  have key := finrank_twist (P.PD K) (AlgHom.id ↥LL.1 ↥LL.1) ρ ρ' (charRep θ) (fun g => (θ g : ↥LL.1))
    (fun _ _ => rfl) hρ k β d hd h1 τ b (fun a => by
      rw [h, Multiset.count_singleton]; split_ifs <;> rfl)
  rw [multV, multV, add_right_comm, key, key]

theorem isCrys_iff {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ ρ' : Representation ↥LL.1 ↥(GK K) V) (θ : ↥(GK K) →* (↥LL.1)ˣ)
    (hρ : ∀ g x, ρ' g x = (θ g : ↥LL.1) • ρ g x) (hθ : IsCrys (P.PD K) (charRep θ)) :
    IsCrys (P.PD K) ρ ↔ IsCrys (P.PD K) ρ' := by
  obtain ⟨hq, ht, hd⟩ := GlobalTheory.RegularRing.quot_tensor_dual_crys l P AI (GlobalTheory.Per.IsStd.of_tied T)
  exact GlobalTheory.TwistCrys.isCrys_twist_iff (P.PD K) (ht K LL) (hq K LL) (hd K LL) ρ ρ' (charRep θ)
    (fun g => (θ g : ↥LL.1)) LinearMap.id 1 rfl (fun _ _ => rfl) hρ hθ

variable {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1))

theorem crysWith_cyc (θ : ↥(GK K) →* (↥LL.1)ˣ) (e : ℕ) (hθ : θ = cycLL (P.PD K) ↥LL.1 ^ (-(e : ℤ))) :
    CrysWith (P.PD K) emb (charRep θ) (fun _ => {(e : ℤ)}) := by
  haveI := (P.PD K).finK
  haveI := LL.2
  subst hθ
  refine ⟨GlobalTheory.BlockCrys.isCrys_cyc_zpow (P.PD K) _, fun i τ _ a => ?_⟩
  rw [GlobalTheory.BlockJumps.multV_twist (P.PD K) (exists_inverse_fontaineElement_mem_fil_neg_one T K) _ e (fun g x => ?_) τ a, Multiset.count_singleton]
  · split_ifs <;> rfl
  · simp [charRep, cycLL]

theorem crysWith_inv (θ : ↥(GK K) →* (↥LL.1)ˣ) (a : ZMod n → ℤ)
    (h : CrysWith (P.PD K) emb (charRep θ) (fun i => {a i})) :
    CrysWith (P.PD K) emb (charRep θ⁻¹) (fun i => {-a i}) := by
  have h1 := crysWith_cyc T K LL emb 1 0 (by simp)
  have hρ : ∀ g x, charRep (1 : ↥(GK K) →* (↥LL.1)ˣ) g x = (θ g : ↥LL.1) • charRep θ⁻¹ g x := fun g x => by
    simp [charRep]
  refine ⟨(isCrys_iff T K LL _ _ θ hρ h.1).2 h1.1, fun i τ hτ c => ?_⟩
  rw [← multV_shift T K LL _ _ θ hρ h.1 τ (a i) (h.2 i τ hτ) c, h1.2 i τ hτ, Multiset.count_singleton,
    Multiset.count_singleton]
  congr 1
  exact if_congr (by omega) rfl rfl

theorem isCrysChar_inv (θ : ↥(GK K) →* (↥(OL LL))ˣ) (a : ZMod n → ℤ) (h : IsCrysChar (P.PD K) emb θ a) :
    IsCrysChar (P.PD K) emb θ⁻¹ (fun i => -a i) := by
  refine ⟨(h.1.comp continuous_inv).congr fun g => by
    rw [Function.comp_apply, map_inv, MonoidHom.inv_apply], ?_⟩
  have e : chiLL ↥LL.1 θ⁻¹ = (chiLL ↥LL.1 θ)⁻¹ := by
    refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.inv_apply, ← map_inv]
    exact congrArg (Units.map _) (map_inv θ g).symm
  rw [e]
  exact crysWith_inv T K LL emb _ a h.2

theorem multV_char_zero (hc : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1)
    (θ : ↥(GK K) →* (↥LL.1)ˣ) (hθ : IsCrys (P.PD K) (charRep θ)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (h : ∀ a, IsJumpV (P.PD K) (charRep θ) τ a → a = 0) (a : ℤ) :
    multV (P.PD K) (charRep θ) τ a = (({0} : Multiset ℤ).count a : ℤ) := by
  classical
  haveI := (P.PD K).finK
  have hdr := isDR T K LL _ hθ
  haveI := (_root_.GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL ↥LL.1 (charRep θ)).1
  obtain ⟨m, k, β, d, hd, h1⟩ := GlobalTheory.T.deRham_comparison_isFiltered l P AI T K LL ↥LL.1 (charRep θ) hdr 0 1
    ⟨1 ⊗ₜ ⟨1, (P.PD K).one_mem⟩, rfl⟩
  set_option synthInstance.maxHeartbeats 200000 in
  have hpos : ∀ τ', 1 ≤ finrank ↥LL.1 (DdRE (P.PD K) (charRep θ) τ') := fun τ' => by
    haveI : FiniteDimensional ↥LL.1 (DdRE (P.PD K) (charRep θ) τ') :=
      Submodule.finiteDimensional_of_le (S₂ := DdR (P.PD K) (charRep θ)) inf_le_left
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact ddRE_ne_bot (P.PD K) (exists_inverse_fontaineElement_mem_fil_neg_one T K) (charRep θ) (fun g => (θ g : ↥LL.1)) (fun _ _ => rfl) k β d
      (fun i => ⟨(hd i).1, (hd i).2.1⟩) h1 τ'
  rw [Nat.card_eq_fintype_card] at hc
  have hsum := (GlobalTheory.DeRhamSplit.finrank_split (P.PD K) hc (charRep θ)).1
  rw [hdr, finrank_self, mul_one, ← hc, ← Finset.card_univ, Finset.card_eq_sum_ones] at hsum
  have hone := (Finset.sum_eq_sum_iff_of_le fun τ' _ => hpos τ').1 hsum τ (Finset.mem_univ _)
  rw [multV_of_only_zero (P.PD K) _ τ h, ← hone, Multiset.count_singleton]
  split_ifs <;> rfl


omit T in
theorem card_emb {lam : ↥(OL LL)} (h : Standing P K LL emb lam) :
    Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := by
  have e : K0 K = K.1 := inf_eq_left.2 h.2.1.1
  rw [← Nat.card_congr ((IntermediateField.equivOfEq e).arrowCongr (AlgEquiv.refl : ↥LL.1 ≃ₐ[ℚ_[l]] ↥LL.1)),
    ← Nat.card_congr (Equiv.ofBijective _ h.2.2.2.1), Nat.card_zmod, h.2.2.1]

end Tied

theorem crysCalc {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (hT : Nonempty (LocTied l P AI))
    (S : TopSit P) : S.CrysCalc := by
  obtain ⟨T⟩ := hT
  refine ⟨fun A A' A'' U U' e he h h' => ⟨?_, fun i τ hτ a => ?_⟩,
    fun A U θ a h hθ => ⟨⟨?_, fun i τ hτ c => ?_⟩, isCrysChar_inv T _ _ _ θ a hθ⟩, ?_, fun μ hc hμ => ?_⟩
  · refine GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv _ e.symm (fun g x => ?_)
      (GlobalTheory.Cmp.WachMonoidal.isCrys_prod _ h.1 h'.1)
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
    rfl
  · haveI := (_root_.GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T S.K S.LL _ A.ρ).1
    haveI := (_root_.GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T S.K S.LL _ A'.ρ).1
    rw [GlobalTheory.HTW.SumJumps.multV_add _ e he, h.2 i τ hτ, h'.2 i τ hτ, Multiset.count_add, Nat.cast_add]
  · exact (isCrys_iff T _ _ _ _ (chiLL ↥S.LL.1 θ) (fun _ _ => rfl) hθ.2.1).1 h.1
  · obtain ⟨c, rfl⟩ : ∃ c', c = c' + a i := ⟨c - a i, by ring⟩
    rw [multV_shift T _ _ A.ρ _ (chiLL ↥S.LL.1 θ) (fun _ _ => rfl) hθ.2.1 τ (a i) (hθ.2.2 i τ hτ) c, h.2 i τ hτ,
      Multiset.count_map_eq_count' _ _ (add_left_injective (a i))]
  · have hε := S.hyp.2.1.2.2.2
    have e : chiLL ↥S.LL.1 S.Γ.ε = cycLL (P.PD S.K) ↥S.LL.1 := by
      ext g : 2
      exact hε g
    refine ⟨(GlobalTheory.Survey.SlowDecayFunctions.continuous_cyc P S.K S.LL).congr fun g => (hε g).symm, ?_⟩
    have := crysWith_inv T _ _ S.emb _ (fun _ => ((1 : ℕ) : ℤ))
      (crysWith_cyc T S.K S.LL S.emb (cycLL (P.PD S.K) ↥S.LL.1)⁻¹ 1 (by simp))
    rw [inv_inv, ← e] at this
    exact this
  · obtain ⟨h1, h2⟩ := _root_.GlobalTheory.UnramifiedRep.isCrys_and_jump_eq_zero l P AI T S.K S.LL (charLat ℚ_[l] Subtype.val_injective μ hc)
      (fun g hg x => by
        change (chiLL ↥S.LL.1 μ g : ↥S.LL.1) • x = x
        simp [hμ g hg])
    exact ⟨hc, h1, fun i τ _ a => multV_char_zero T _ _ (card_emb _ _ _ S.hyp.1) _ h1 τ (h2 τ) a⟩

end GlobalTheory.TopSteps.CrysRules
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupActsResiduesFrobeniusPower
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

noncomputable section

namespace GlobalTheory.DecFrobPow

theorem frob_pow_apply {F R : Type} [Field F] [Fintype F] [CommRing R] [Algebra F R] (n : ℕ) (x : R) :
    ((FiniteField.frobeniusAlgHom F R) ^ n) x = x ^ (Fintype.card F ^ n) := by
  rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]

theorem exists_pow_of_algHom {k F : Type} [Field k] [Field F] [Fintype F] [Algebra F k]
    (τ : k →ₐ[F] k) {a : ℕ} (ha : 0 < a) :
    ∃ j : ℕ, ∀ x : k, x ^ (Fintype.card F ^ a) = x → τ x = x ^ (Fintype.card F ^ j) := by
  set q := Fintype.card F with hq
  let S : Subalgebra F k := AlgHom.equalizer ((FiniteField.frobeniusAlgHom F k) ^ a) (AlgHom.id F k)
  have hS : ∀ x, x ∈ S ↔ x ^ (q ^ a) = x := by
    intro x
    show ((FiniteField.frobeniusAlgHom F k) ^ a) x = (AlgHom.id F k) x ↔ _
    rw [frob_pow_apply]; rfl
  let L : IntermediateField F k := S.toIntermediateField (fun x hx => by
    rw [hS] at hx ⊢; rw [inv_pow, hx])
  have hL : ∀ x, x ∈ L ↔ x ^ (q ^ a) = x := hS
  have hq1 : 1 < q := Fintype.one_lt_card
  have hfin : (L : Set k).Finite := by
    have hP : (X ^ q ^ a - X : k[X]) ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero k ha.ne' hq1
    refine (Polynomial.finite_setOfPred_isRoot hP).subset fun x hx => ?_
    have := (hL x).mp hx
    simp [Polynomial.IsRoot, this]
  haveI : Finite L := hfin.to_subtype
  let σ : L →ₐ[F] L := (τ.comp L.val).codRestrict L.toSubalgebra fun x => by
    show τ (x : k) ∈ L
    rw [hL, ← map_pow, (hL x).mp x.2]
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow F L).2 σ
  refine ⟨n, fun x hx => ?_⟩
  have h1 := congrArg (fun f : L →ₐ[F] L => ((f ⟨x, (hL x).mpr hx⟩ : L) : k)) hn
  simp only [frob_pow_apply] at h1
  have h2 : ((σ ⟨x, (hL x).mpr hx⟩ : L) : k) = τ x := rfl
  rw [← h2, ← h1, SubmonoidClass.coe_pow]

end GlobalTheory.DecFrobPow

namespace GlobalTheory.DecFrobPow

theorem exists_place {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (A : ValuationSubring Ω) {p : ℕ} (hp : p.Prime) (hpA : A.valuation (p : Ω) < 1) :
    ∃ wK : HeightOneSpectrum (𝓞 K), IsPlaceOver A wK := by
  let g : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A (x.2.algebraMap (B := Ω))
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap g
  have hmem : ∀ x : 𝓞 K, x ∈ P ↔ A.valuation (algebraMap K Ω (x : K)) < 1 := fun x =>
    A.valuation_lt_one_iff (g x)
  have hne : P ≠ ⊥ := by
    intro h0
    have hpP : ((p : ℕ) : 𝓞 K) ∈ P := by
      rw [hmem]; simpa using hpA
    rw [h0, Ideal.mem_bot] at hpP
    exact hp.ne_zero (by exact_mod_cast hpP)
  exact ⟨⟨P, Ideal.comap_isPrime g _, hne⟩, fun x => (hmem x).symm⟩

theorem exists_pow_cong_of_mem {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (A : ValuationSubring Ω) {p : ℕ} (hp : p.Prime) (hpA : A.valuation (p : Ω) < 1) :
    ∃ c : ℕ, 0 < c ∧ ∀ z : K, A.valuation (algebraMap K Ω z) ≤ 1 →
      A.valuation ((algebraMap K Ω z) ^ (p ^ c) - algebraMap K Ω z) < 1 := by
  obtain ⟨wK, hwK⟩ := exists_place (K := K) A hp hpA
  obtain ⟨φ, hφD, hφ⟩ := exists_isFrob (F := K) hwK
  obtain ⟨p', c, hp', hc, hN, hp'A⟩ := GlobalTheory.FrobTeich.exists_prime_pow_normV A wK hwK
  have hchar : ∀ r : ℕ, r.Prime → A.valuation (r : Ω) < 1 → CharP (IsLocalRing.ResidueField A) r := by
    intro r hr hrA
    refine (CharP.charP_iff_prime_eq_zero hr).2 ?_
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      A.valuation_lt_one_iff]
    simpa using hrA
  have hpp : p' = p := by
    haveI := hchar p hp hpA
    haveI := hchar p' hp' hp'A
    exact CharP.eq (IsLocalRing.ResidueField A) ‹CharP _ p'› ‹CharP _ p›
  subst hpp
  refine ⟨c, hc, fun z hz => ?_⟩
  have h1 := hφ _ hz
  rw [hN, φ.commutes] at h1
  rw [← Valuation.map_neg, neg_sub]
  exact h1

end GlobalTheory.DecFrobPow

namespace GlobalTheory.DecFrobPow

theorem pow_pow_eq_self {R : Type} [Monoid R] {r : R} {M : ℕ} (h : r ^ M = r) (b : ℕ) :
    r ^ (M ^ b) = r := by
  induction b with
  | zero => simp
  | succ b ih => rw [pow_succ, pow_mul, ih, h]

theorem exists_field_cong_pow : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (_h : IsPlaceOver A w),
    ∀ d ∈ Dec (F := E) A, ∀ y : Ω, ∃ K : IntermediateField E Ω, FiniteDimensional E K ∧ y ∈ K ∧
      ∃ j : ℕ, ∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (d z - z ^ (normV w ^ j)) < 1 := by
  intro E Ω _ _ _ _ _ A w h d hd y
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  set K := IntermediateField.adjoin E ({y} : Set Ω) with hK
  haveI hKfin : FiniteDimensional E K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  haveI : FiniteDimensional ℚ K := Module.Finite.trans E K
  haveI : NumberField K := ⟨⟩
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) K⟩
  refine ⟨K, hKfin, IntermediateField.mem_adjoin_simple_self E y, ?_⟩
  obtain ⟨p, b, hp, hb, hq, hpA⟩ := GlobalTheory.FrobTeich.exists_prime_pow_normV A w h
  obtain ⟨c, hc, hcK⟩ := exists_pow_cong_of_mem (K := K) A hp hpA
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  letI : Field (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 E ⧸ w.asIdeal) = normV w := Fintype.card_eq_nat_card
  let gE : 𝓞 E →+* A := ((algebraMap E Ω).comp (algebraMap (𝓞 E) E)).codRestrict A fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A (x.2.algebraMap (B := Ω))
  let ι : 𝓞 E ⧸ w.asIdeal →+* IsLocalRing.ResidueField A :=
    Ideal.Quotient.lift w.asIdeal ((IsLocalRing.residue A).comp gE) (fun x hx => by
      show IsLocalRing.residue A (gE x) = 0
      rw [IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
      exact (h x).mpr hx)
  letI : Algebra (𝓞 E ⧸ w.asIdeal) (IsLocalRing.ResidueField A) := ι.toAlgebra
  let D : A.decompositionSubgroup E := ⟨d, hd⟩
  let τ0 : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField A :=
    MulSemiringAction.toRingHom (A.decompositionSubgroup E) (IsLocalRing.ResidueField A) D
  have hτ0 : ∀ a : A, τ0 (IsLocalRing.residue A a) = IsLocalRing.residue A (D • a) := fun a =>
    (IsLocalRing.ResidueField.residue_smul (g := D) (r := a)).symm
  have hval : ∀ a : A, ((D • a : A) : Ω) = d a := fun a => rfl
  let τ : IsLocalRing.ResidueField A →ₐ[𝓞 E ⧸ w.asIdeal] IsLocalRing.ResidueField A :=
    { τ0 with
      commutes' := fun c => by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
        show τ0 (ι (Ideal.Quotient.mk _ x)) = ι (Ideal.Quotient.mk _ x)
        have e1 : ι (Ideal.Quotient.mk _ x) = IsLocalRing.residue A (gE x) := Ideal.Quotient.lift_mk _ _ _
        rw [e1, hτ0]
        congr 1
        apply Subtype.ext
        rw [hval]
        exact d.commutes _ }
  obtain ⟨j, hj⟩ := exists_pow_of_algHom τ hc
  rw [hcard] at hj
  refine ⟨j, fun z hzK hz => ?_⟩
  let a : A := ⟨z, (A.valuation_le_one_iff z).mp hz⟩
  have h1 : A.valuation (z ^ (p ^ c) - z) < 1 := hcK ⟨z, hzK⟩ hz
  have h2 : IsLocalRing.residue A a ^ (p ^ c) = IsLocalRing.residue A a := by
    rw [← sub_eq_zero, ← map_pow, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      A.valuation_lt_one_iff]
    exact h1
  have h3 : IsLocalRing.residue A a ^ (normV w ^ c) = IsLocalRing.residue A a := by
    rw [hq, ← pow_mul, mul_comm, pow_mul]
    exact pow_pow_eq_self h2 b
  have h4 := hj _ h3
  have h5 : τ (IsLocalRing.residue A a) = IsLocalRing.residue A (D • a) := hτ0 a
  rw [h5, ← sub_eq_zero, ← map_pow, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    A.valuation_lt_one_iff] at h4
  exact h4

end GlobalTheory.DecFrobPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompositionGroupEquivPadicGalois
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DecGalois

theorem exists_continuousMulEquiv : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∃ i : ↥(A.decompositionSubgroup F) ≃ₜ*
      (PadicAlgCl p ≃ₐ[↥(IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x)))] PadicAlgCl p),
      ∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x) := by
  intro p _ F Ω _ _ _ _ _ A j hj
  let K : Formalism.BasicNotions.Loc.FinExt p :=
    ⟨IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x)),
      GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
  have hK := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hj K rfl
  obtain ⟨hf, hf'⟩ := GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[p] (PadicAlgCl p) K.1
  let e2 : ↥(A.decompositionSubgroup F) ≃* (PadicAlgCl p ≃ₐ[↥K.1] PadicAlgCl p) :=
    e.trans (IntermediateField.fixingSubgroupEquiv K.1)
  refine ⟨{ e2 with continuous_toFun := hf.comp he, continuous_invFun := he'.comp hf' }, fun g x => ?_⟩
  exact hec g x

end GlobalTheory.DecGalois
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeTateBasisOfCrystallineOverKsStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hodgeTateBasis_of_crystalline_over_Ks : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O), IsCrysOn S S.W.GKs T → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∀ m : ℕ, s ≤ m → (Jset S T).Finite ∧ HTBasis (D.locA l).actC (D.loc l).χQ (Gj K m) M (Jset S T) := by
  first | exact @GlobalTheory.HTBasisEx.exists_htBasis | exact GlobalTheory.HTBasisEx.exists_htBasis | (intros; apply GlobalTheory.HTBasisEx.exists_htBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocTheoryTied
section
open Formalism Formalism.BasicNotions
namespace GlobalTheory.MemLoc

theorem exists_locTheory_tied : ∃ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)),
    Nonempty (∀ (l : ℕ) [Fact l.Prime], LocTied l (L l) (A l)) := by
  choose P A h using exists_locPrime_tied
  exact ⟨fun l _ => P l, fun l _ => A l, ⟨fun l _ => (h l).some⟩⟩
end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSmallerParahoricLevelModFirstBlocksStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_smaller_parahoricLevel_mod_firstBlocks : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → (∀ PP ∈ L.Pg, ∀ PP' ∈ Q', PP ≠ PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP' PP) → ∀ g ∈ (levEnv V β L).Q, ∃ g' ∈ (levEnv V β { L with Q := Q', xq := xq }).Q, g⁻¹ * g' ∈ (levEnv V β L).J := by
  first | exact @GlobalTheory.SmallerParahoric.exists_mem_smaller | exact GlobalTheory.SmallerParahoric.exists_mem_smaller | (intros; apply GlobalTheory.SmallerParahoric.exists_mem_smaller <;> assumption)
end

