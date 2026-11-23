module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevOp

variable {D : D7} {V : HSp D} {P : Pl D.host.E}

theorem mem_hyp {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {k : GA D V} :
    k ∈ GlobalTheory.Hk3.hyp V P ↔ k ∈ KsphC V ∅ ∧ SuppF V f k := by
  refine ⟨fun ⟨h, e', f', h', hs⟩ => ⟨h, ?_⟩, fun h => ⟨h.1, e, f, hP, h.2⟩⟩
  obtain ⟨-, rfl⟩ := ((_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e f hP).2.2.2.1 e' f' h'
  exact hs

theorem comm_of_supp {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {a b : GA D V} (ha : SuppF V f a)
    (hb : SuppF V (1 - f) b) : Commute a b :=
  have h1 := (_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e f hP
  ((_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).1 f h1.1 h1.2.1).2.2 (1 - f) a b (by rw [mul_sub, mul_one, h1.1, sub_self]) ha hb

theorem full_iff {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {J : Set (GA D V)} {χ : GA D V → ℂ}
    (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) (hχ : ∀ g ∈ J, SuppF V f g → χ g = 1)
    (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (d : List ℤ) (B : Finset (GA D V)) :
    Hecke₂ V J χ SF P d B ↔ OffS D SF P ∧ SphOp V P d B := by
  have hK : {k | k ∈ J ∧ SuppF V f k} = {k | k ∈ KsphC V ∅ ∧ SuppF V f k} :=
    Set.ext fun k => and_congr_left fun hk => hJ k hk
  constructor
  · rintro ⟨e', f', ϖ, α, hS, hP', h1, h2, hd, -, -, hα, hD, hR, hc⟩
    obtain ⟨rfl, rfl⟩ := ((_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
    exact ⟨hS, _, _, ϖ, α, fun v hv => absurd hv (Finset.notMem_empty v), hP, h1, h2, hd, fun _ _ => Iff.rfl,
      fun _ _ _ => rfl, hα, hD, hR, hK ▸ hc⟩
  · rintro ⟨hS, e', f', ϖ, α, -, hP', h1, h2, hd, -, -, hα, hD, hR, hc⟩
    obtain ⟨rfl, rfl⟩ := ((_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
    exact ⟨_, _, ϖ, α, hS, hP, h1, h2, hd, hJ, hχ, hα, hD, hR, hK ▸ hc⟩

theorem offS_empty : OffS D ∅ P := fun v hv => absurd hv (Finset.notMem_empty v)

theorem rep_cases (d : List ℤ) : GlobalTheory.Hk3.rep V P d = ∅ ∨ SphOp V P d (GlobalTheory.Hk3.rep V P d) := by
  unfold GlobalTheory.Hk3.rep
  split_ifs with h
  · exact Or.inr h.choose_spec
  · exact Or.inl rfl

theorem heckeLin_translate {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {J : Subgroup (GA D V)}
    (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) {d : List ℤ} {R : Finset (GA D V)} (hR : SphOp V P d R)
    {F : GA D V → ℂ} (hF : ∀ k ∈ GlobalTheory.Hk3.hyp V P, ∀ h, F (h * k) = F h) {k₁ k₂ : GA D V} (hk₁ : k₁ ∈ J)
    (s₁ : SuppF V f k₁) (s₂ : SuppF V (1 - f) k₂) (h : GA D V) :
    heckeLin V R F (h * (k₁ * k₂)) = heckeLin V R (fun x => F (x * (k₁ * k₂))) h := by
  obtain ⟨L, hL⟩ := GlobalTheory.HeckeKeep.exists_loc V f
  have hJ' : ∀ g, SuppF V f g → (g ∈ ((J ⊓ L : Subgroup (GA D V)) : Set (GA D V)) ↔ g ∈ KsphC V ∅) := fun g hg =>
    ⟨fun h => (hJ g hg).1 h.1, fun h => ⟨(hJ g hg).2 h, (hL g).2 hg⟩⟩
  have hop := (full_iff hP (χ := fun _ => 1) hJ' (fun _ _ _ => rfl) ∅ d R).2 ⟨offS_empty, hR⟩
  have hsupp : ∀ γ ∈ R, SuppF V f γ := by
    obtain ⟨e', f', ϖ, α, -, hP', -, -, -, -, -, -, -, hR, -⟩ := hR
    obtain ⟨-, rfl⟩ := ((_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
    exact hR
  have key := GlobalTheory.SphericalOps.level_heckeLin (J := J ⊓ L) (F := fun x => F (x * k₂)) (fun _ _ _ _ => (one_mul _).symm)
    (fun e' f' _ hP' k hk => by
      obtain ⟨-, rfl⟩ := ((_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
      exact ⟨k, hk, 1, one_mem _, (hL k).1 hk.2, GlobalTheory.HeckeKeep.suppF_one _, (mul_one k).symm⟩) hop
    (fun k hk g => by
      have s := (hL k).1 hk.2
      show F (g * k * k₂) = 1 * F (g * k₂)
      rw [one_mul, mul_assoc, (comm_of_supp hP s s₂).eq, ← mul_assoc,
        hF k ((mem_hyp hP).2 ⟨(hJ k s).1 hk.1, s⟩)]) k₁ ⟨hk₁, (hL _).2 s₁⟩ h
  rw [one_mul, heckeLin_apply, heckeLin_apply] at key
  rw [heckeLin_apply, heckeLin_apply]
  refine Eq.trans (Finset.sum_congr rfl fun a ha => ?_) (key.trans (Finset.sum_congr rfl fun a _ => ?_))
  · rw [← mul_assoc, mul_assoc _ k₂, ← (comm_of_supp hP (hsupp a ha) s₂).eq, ← mul_assoc]
  · show _ = F (h * a * (k₁ * k₂))
    rw [(comm_of_supp hP s₁ s₂).eq, ← mul_assoc, hF k₁ ((mem_hyp hP).2 ⟨(hJ _ s₁).1 hk₁, s₁⟩)]

theorem hk_apply (c : List ℤ →₀ ℂ) (F : GA D V → ℂ) (h : GA D V) :
    hk V P c F h = ∑ d ∈ c.support, c d * heckeLin V (GlobalTheory.Hk3.rep V P d) F h := by
  unfold hk Finsupp.sum
  rw [LinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem hk_translate {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {J : Subgroup (GA D V)}
    (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) (c : List ℤ →₀ ℂ)
    {F : GA D V → ℂ} (hF : ∀ k ∈ GlobalTheory.Hk3.hyp V P, ∀ h, F (h * k) = F h) {k₁ k₂ : GA D V} (hk₁ : k₁ ∈ J)
    (s₁ : SuppF V f k₁) (s₂ : SuppF V (1 - f) k₂) (h : GA D V) :
    hk V P c F (h * (k₁ * k₂)) = hk V P c (fun x => F (x * (k₁ * k₂))) h := by
  rw [hk_apply, hk_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  rcases rep_cases (V := V) (P := P) d with h0 | h0
  · rw [h0, heckeLin_apply, heckeLin_apply, Finset.sum_empty, Finset.sum_empty]
  · exact heckeLin_translate hP hJ h0 hF hk₁ s₁ s₂ h

theorem postOn_hk {S : D.what₂.Tau → SPar} (M : DSModel V S) (c : List ℤ →₀ ℂ) (U : MMap M) :
    postOn M (hk V P c) U = ∑ d ∈ c.support, c d • heckeOn M (GlobalTheory.Hk3.rep V P d) U := by
  ext v g
  rw [postOn_apply, hk_apply, MultilinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem level_operators : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank), IsBaseFrame V β Λ N → ∀ P : Pl D.host.E, ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → (∀ k ∈ GlobalTheory.Hk3.hyp V P, k ∈ levG V β L ∧ levChi V β L k = 1) ∧ (∀ SF d B, Hecke₂ V (levS V β L) (levChi V β L) SF P d B ↔ OffS D SF P ∧ SphOp V P d B) ∧ (∀ c Φ, HasType V β L Φ → HasType V β L (hk V P c Φ)) ∧ (∀ c (g0 : G0 L.Pg L.r) Φ, (∀ k ∈ GlobalTheory.Hk3.hyp V P, ∀ h, Φ (h * k) = Φ h) → actG0 V β L g0 (hk V P c Φ) = hk V P c (actG0 V β L g0 Φ)) ∧ ∀ (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) c, IsInfFam θ → ∀ U ∈ Mult θ M (levS V β L) (levChi V β L), postOn M (hk V P c) U ∈ Mult θ M (levS V β L) (levChi V β L) := by
  intro D V β Λ N L hB P hN hPP
  obtain ⟨e, f, hP⟩ := (_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.1 P
  obtain ⟨hJ, hχ, hs⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N L hB).2 P e f hP hN hPP
  obtain ⟨hJ', -, hs'⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N (flagL L) hB).2 P e f hP hN hPP
  have h1 : ∀ k ∈ GlobalTheory.Hk3.hyp V P, k ∈ levG V β L ∧ levChi V β L k = 1 := fun k hk => by
    obtain ⟨a, b⟩ := (mem_hyp hP).1 hk
    exact ⟨(hJ k b).2 a, hχ k ((hJ k b).2 a) b⟩
  have hinv : ∀ Φ, HasType V β L Φ → ∀ k ∈ GlobalTheory.Hk3.hyp V P, ∀ h, Φ (h * k) = Φ h := fun Φ hΦ k hk h => by
    rw [hΦ k (h1 k hk).1, (h1 k hk).2, one_mul]
  refine ⟨h1, full_iff hP hJ hχ, fun c Φ hΦ κ hκ h => ?_, fun c g0 Φ hΦ => ?_, fun S θ M c hθ U hU => ?_⟩
  · obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hs κ hκ
    have e1 : (fun x => Φ (x * (k₁ * k₂))) = levChi V β L (k₁ * k₂) • Φ := funext fun x => hΦ _ hκ x
    rw [hk_translate hP hJ c (hinv Φ hΦ) hk₁ s₁ s₂, e1, LinearMap.map_smul]
    rfl
  · unfold actG0
    split_ifs with hex
    · have hl := hex.choose_spec
      generalize hex.choose = κ at hl ⊢
      have hκ : κ ∈ levG V β (flagL L) := ⟨hl.1, hl.2.1, Subgroup.mem_top _⟩
      obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hs' κ hκ
      have e1 : (fun x => (levChi V β (flagL L) (k₁ * k₂))⁻¹ * Φ (x * (k₁ * k₂))) =
        (levChi V β (flagL L) (k₁ * k₂))⁻¹ • fun x => Φ (x * (k₁ * k₂)) := rfl
      rw [e1, LinearMap.map_smul]
      funext h
      rw [hk_translate hP hJ' c hΦ hk₁ s₁ s₂]
      rfl
    · rw [LinearMap.map_zero]
  · rw [postOn_hk]
    refine sum_mem fun d _ => Submodule.smul_mem _ _ ?_
    rcases rep_cases (V := V) (P := P) d with h0 | h0
    · have : heckeOn M (GlobalTheory.Hk3.rep V P d) U = 0 := by
        ext v g
        rw [h0, heckeOn, postOn_apply, heckeLin_apply, Finset.sum_empty]
        rfl
      rw [this]
      exact zero_mem _
    · have hop := (full_iff hP (J := levS V β L) hJ hχ ∅ d _).2 ⟨offS_empty, h0⟩
      rw [GlobalTheory.MultMem.mem_mult_iff] at hU ⊢
      refine GlobalTheory.SphericalOps.isMultMap_heckeOn hU (fun k hk => ?_) fun v κ hκ h => ?_
      · obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, -, -, hc⟩ := hop
        exact (hc.1 k hk).1
      · obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hs κ hκ
        have e1 : (fun x => U v (x * (k₁ * k₂))) = levChi V β L (k₁ * k₂) • U v := funext fun x => hU.lev v _ hκ x
        rw [heckeLin_translate hP hJ h0 (hinv _ (hU.lev v)) hk₁ s₁ s₂, e1, LinearMap.map_smul]
        rfl

end GlobalTheory.LevOp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalLatticeVacuumMemSpanFixed
section
open Matrix

namespace GlobalTheory.Hk3

theorem locVac_mem_span_vac : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ w : M, GlobalTheory.Hk3.LocVac ρ w → w ∈ Submodule.span ℂ {s} := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac hspan w hw
  classical
  have hind := locVac_span_classes_indep L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac
  obtain ⟨hU, -, hSint, hTint, hS, hT, hδ, -, hpsi_ne, hρ0, hρ, -, -, -⟩ := hP
  have hσ := hU.1
  have hA : ∀ x y : Matrix (Fin n') (Fin n) L, σ (locH σ δ JS JT x y) = - locH σ δ JS JT y x :=
    locH_conj σ hσ δ hδ.2 JS JT hS hT
  have hψinv : ∀ a, ψ a * ψ (-a) = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hΛ : intMatSub (L := L) n n' = HoweDuality.intMat L n' n := AddSubgroup.ext fun _ => Iff.rfl
  have hshift : ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ (x + u) s = ψ (-((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2)) • ρ x s := by
    intro x u hu
    have h1 : ρ x s = ψ ((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2) • ρ (x + u) s := by
      have := congrArg (fun f => f s) (hρ x u)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rwa [hvac u hu] at this
    rw [h1, smul_smul, mul_comm, hψinv, one_smul]
  have heig : ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ u (ρ x s) = ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) • ρ x s := by
    intro x u hu
    have := congrArg (fun f => f s) (hρ u x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, add_comm u x, hshift x u hu, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hA u x, hA x u]; ring
  set Λ := HoweDuality.intMat L n' n with hΛdef
  set V : Matrix (Fin n') (Fin n) L ⧸ Λ → Submodule ℂ M := fun c => Submodule.span ℂ {ρ c.out s} with hVdef
  have hVind : iSupIndep V := by
    refine hind.mono fun c => Submodule.span_le.mpr ?_
    rintro _ rfl
    exact Submodule.subset_span ⟨c.out, QuotientAddGroup.out_eq' c, rfl⟩
  have hmemV : ∀ x, ρ x s ∈ V (QuotientAddGroup.mk x) := by
    intro x
    have hm : -(QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ Λ).out + x ∈ intMatSub (L := L) n n' := by
      rw [hΛ]
      exact QuotientAddGroup.eq.mp (by rw [QuotientAddGroup.out_eq'])
    have := hshift (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ Λ).out _ hm
    rw [add_neg_cancel_left] at this
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hwV : w ∈ ⨆ c, V c := by
    have hle : Submodule.span ℂ (Set.range fun x => ρ x s) ≤ ⨆ c, V c :=
      Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact Submodule.mem_iSup_of_mem _ (hmemV x))
    exact hle (hspan ▸ Submodule.mem_top)
  obtain ⟨f, hf, hfw⟩ := (Submodule.mem_iSup_iff_exists_finsupp V w).mp hwV
  set χ : Matrix (Fin n') (Fin n) L ⧸ Λ → Matrix (Fin n') (Fin n) L → ℂ :=
    fun c u => ψ (locH σ δ JS JT u c.out + σ (locH σ δ JS JT u c.out)) with hχ
  have heigV : ∀ c, ∀ u ∈ intMatSub (L := L) n n', ∀ v ∈ V c, ρ u v = χ c u • v := by
    intro c u hu v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, heig _ u hu, smul_comm]
  have hzero : ∀ c, c ≠ 0 → f c = 0 := by
    intro c hc
    obtain ⟨u, hu, hχu⟩ : ∃ u ∈ intMatSub (L := L) n n', χ c u ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have hint := intMat_of_psi hU hδ.1 hSint hTint ψ hpsi_ne c.out hcon
      apply hc
      rw [hΛ] at hint
      rw [← QuotientAddGroup.out_eq' c, QuotientAddGroup.eq_zero_iff]
      exact hint
    have hsum : (f.support.sum fun d => (χ d u - 1) • f d) = 0 := by
      have e1 : ρ u w = f.support.sum fun d => χ d u • f d := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hfw, Finsupp.sum, map_sum]
        exact Finset.sum_congr rfl fun d _ => heigV d u hu _ (hf d)
      have e2 : w = f.support.sum fun d => f d := by rw [← hfw, Finsupp.sum]
      simp only [sub_smul, one_smul, Finset.sum_sub_distrib, ← e1, ← e2, hw u hu, sub_self]
    by_cases hcs : c ∈ f.support
    · rw [← Finset.add_sum_erase _ _ hcs, add_eq_zero_iff_eq_neg] at hsum
      have hmem1 : (χ c u - 1) • f c ∈ V c := Submodule.smul_mem _ _ (hf c)
      have hmem2 : (χ c u - 1) • f c ∈ ⨆ (j) (_ : j ≠ c), V j := by
        rw [hsum]
        refine Submodule.neg_mem _ (Submodule.sum_mem _ fun d hd => ?_)
        have hdc : d ≠ c := Finset.ne_of_mem_erase hd
        exact Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem hdc (Submodule.smul_mem _ _ (hf d)))
      have hz : (χ c u - 1) • f c = 0 := by
        have := (iSupIndep_def.mp hVind c)
        rw [Submodule.disjoint_def] at this
        exact this _ hmem1 hmem2
      exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hχu)
    · exact Finsupp.notMem_support_iff.mp hcs
  have hw0 : w = f 0 := by
    rw [← hfw, Finsupp.sum, Finset.sum_eq_single (0 : Matrix (Fin n') (Fin n) L ⧸ Λ)]
    · intro d _ hd; exact hzero d hd
    · intro h0; exact Finsupp.notMem_support_iff.mp h0
  have hout : ρ (0 : Matrix (Fin n') (Fin n) L ⧸ Λ).out s = s := by
    apply hvac
    have : (0 : Matrix (Fin n') (Fin n) L ⧸ Λ).out ∈ Λ := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq']
    exact this
  have := hf 0
  change f 0 ∈ Submodule.span ℂ {ρ (0 : Matrix (Fin n') (Fin n) L ⧸ Λ).out s} at this
  rw [hout] at this
  rw [hw0]; exact this

end GlobalTheory.Hk3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexLeOfIntegralKernel
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem exists_pow_mul_int {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (z : L) :
    ∃ n : ℕ, Valued.v (ϖ ^ n * z) ≤ 1 := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  have hv : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v z = WithZero.exp m := ⟨_, (WithZero.exp_log hv).symm⟩
  refine ⟨m.toNat, ?_⟩
  rw [map_mul, map_pow, hϖ, hm, ← WithZero.exp_nsmul, ← WithZero.exp_add,
    ← WithZero.exp_zero, WithZero.exp_le_exp, nsmul_eq_mul]
  have := Int.self_le_toNat m
  omega

theorem pow_mul_int_mono {ϖ : L} (hϖ : Valued.v ϖ ≤ 1) {z : L} {n m : ℕ} (hnm : n ≤ m)
    (h : Valued.v (ϖ ^ n * z) ≤ 1) : Valued.v (ϖ ^ m * z) ≤ 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [pow_add, mul_comm (ϖ ^ n), mul_assoc, map_mul, map_pow]
  exact mul_le_one' (pow_le_one' hϖ k) h

theorem exists_pow_smul_int {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {a b : ℕ}
    (x : Matrix (Fin a) (Fin b) L) : ∃ K : ℕ, ∀ i j, Valued.v (ϖ ^ K * x i j) ≤ 1 := by
  choose n hn using fun p : Fin a × Fin b => exists_pow_mul_int hϖ (x p.1 p.2)
  have hϖ1 : Valued.v ϖ ≤ 1 := by rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  refine ⟨∑ p, n p, fun i j => pow_mul_int_mono hϖ1 ?_ (hn (i, j))⟩
  exact Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j))

theorem finite_range_latIdx {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) {a b : ℕ}
    (x : Matrix (Fin a) (Fin b) L) :
    (Set.range fun u : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a)).Finite := by
  obtain ⟨-, -, -, hϖ, -, h2q, hc⟩ := hU
  set V := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) with hV
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ1 : V ϖ ≤ 1 := by rw [hV, hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  have hc' : Nat.card (V.valuationSubring ⧸ IsLocalRing.maximalIdeal V.valuationSubring) = q ^ 2 := hc
  haveI : Finite (V.valuationSubring ⧸ IsLocalRing.maximalIdeal V.valuationSubring) :=
    Nat.finite_of_card_ne_zero (by rw [hc']; exact pow_ne_zero _ (by omega))
  let ϖO : V.valuationSubring := ⟨ϖ, hϖ1⟩
  have hmax : IsLocalRing.maximalIdeal V.valuationSubring ≤ Ideal.span {ϖO} := by
    intro z hz
    rw [Valuation.mem_maximalIdeal_iff] at hz
    rw [Ideal.mem_span_singleton']
    by_cases hz0 : (z : L) = 0
    · exact ⟨0, by ext; simp [hz0]⟩
    have hϖ0 : ϖ ≠ 0 := by
      intro e; rw [e, map_zero] at hϖ'; exact WithZero.zero_ne_coe hϖ'
    have hz' : Valued.v (z : L) < 1 := hz
    have hle : Valued.v (z : L) ≤ Valued.v ϖ := by
      have hv : Valued.v (z : L) ≠ 0 := (Valuation.ne_zero_iff _).2 hz0
      rw [hϖ', ← WithZero.exp_log hv, WithZero.exp_le_exp]
      rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hz'
      omega
    have hq1 : Valued.v ((z : L) / ϖ) ≤ 1 := by
      rw [map_div₀, div_le_one₀ (by rw [hϖ']; exact WithZero.exp_pos)]
      exact hle
    refine ⟨⟨(z : L) / ϖ, hq1⟩, ?_⟩
    ext
    simp [ϖO, div_mul_cancel₀ _ hϖ0]
  haveI : Finite (V.valuationSubring ⧸ Ideal.span {ϖO}) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective hmax)
  obtain ⟨K, hK⟩ := exists_pow_smul_int hϖ' x
  haveI hfinK : Finite (V.valuationSubring ⧸ Ideal.span {ϖO} ^ K) :=
    Ideal.finite_quotient_pow (Submodule.fg_span_singleton _) K
  let g : (Fin b → V.valuationSubring ⧸ Ideal.span {ϖO} ^ K) → (Fin a → L) ⧸ intVec L a :=
    fun c => QuotientAddGroup.mk (Matrix.mulVec x fun j => (((c j).out : V.valuationSubring) : L))
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨u, rfl⟩
  have hu : ∀ j, Valued.v ((u : Fin b → L) j) ≤ 1 := (mem_intVec _).1 u.2
  refine ⟨fun j => Ideal.Quotient.mk _ ⟨(u : Fin b → L) j, hu j⟩, ?_⟩
  have hd : ∀ j, ∃ t : V.valuationSubring,
      (((Ideal.Quotient.mk (Ideal.span {ϖO} ^ K) ⟨(u : Fin b → L) j, hu j⟩).out : V.valuationSubring) : L) =
        (u : Fin b → L) j + ϖ ^ K * t := by
    intro j
    have hm := Ideal.Quotient.mk_out (I := Ideal.span {ϖO} ^ K)
      (⟨(u : Fin b → L) j, hu j⟩ : V.valuationSubring)
    have hm' := Ideal.Quotient.eq.1 hm
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 ((Ideal.span_singleton_pow ϖO K).le hm')
    refine ⟨t, ?_⟩
    have := congrArg (fun w : V.valuationSubring => (w : L)) ht
    push_cast at this
    simp only [ϖO] at this
    linear_combination -this
  choose t ht using hd
  refine (QuotientAddGroup.eq.2 ?_).symm
  intro i
  simp only [Pi.add_apply, Pi.neg_apply, Matrix.mulVec, dotProduct, ht, mul_add, Finset.sum_add_distrib,
    neg_add_cancel_left]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [show x i j * (ϖ ^ K * (t j : L)) = (ϖ ^ K * x i j) * (t j : L) by ring]
  exact Subring.mul_mem _ (hK i j) (t j).2

theorem latIdx_le_of_ker : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q a b : ℕ) (x y : Matrix (Fin a) (Fin b) L),
    Formalism.UG.IsUnramInv ϖ σ q →
    (∀ u : Fin b → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (Matrix.mulVec x u) i ∈ Formalism.UG.intL L) →
      ∀ i, (Matrix.mulVec y u) i ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweDuality.latIdx y ≤ GlobalTheory.Hk3.HoweDuality.latIdx x := by
  intro L _ _ ϖ σ q a b x y hU hN
  classical
  have hfin := finite_range_latIdx hU x
  set Sx := Set.range fun u : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a) with hSx
  set Sy := Set.range fun u : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec y (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a) with hSy
  let h : (Fin a → L) ⧸ intVec L a → (Fin a → L) ⧸ intVec L a := fun c =>
    if hc : ∃ u : intVec L b, (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a) = c
    then QuotientAddGroup.mk (Matrix.mulVec y (hc.choose : Fin b → L)) else 0
  have hsub : Sy ⊆ h '' Sx := by
    rintro _ ⟨u, rfl⟩
    refine ⟨_, ⟨u, rfl⟩, ?_⟩
    have hc : ∃ u' : intVec L b, (QuotientAddGroup.mk (Matrix.mulVec x (u' : Fin b → L)) : (Fin a → L) ⧸ intVec L a) =
        QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) := ⟨u, rfl⟩
    simp only [h, dif_pos hc]
    have he := hc.choose_spec
    set u' := hc.choose
    rw [QuotientAddGroup.eq] at he ⊢
    have hd := hN ((u : Fin b → L) - (u' : Fin b → L)) (fun i => Subring.sub_mem _ (u.2 i) (u'.2 i))
      (fun i => by
        have := he i
        rw [Matrix.mulVec_sub]
        simpa [neg_add_eq_sub] using this)
    intro i
    have := hd i
    rw [Matrix.mulVec_sub] at this
    simpa [neg_add_eq_sub] using this
  unfold latIdx
  rw [← hSx, ← hSy, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact (Set.ncard_le_ncard hsub (hfin.image h)).trans (Set.ncard_image_le hfin)

end GlobalTheory.Hk3.HoweDuality

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemISupTypePartsOfGoodBaseForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwParts

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL]

theorem mk_bC_mem_range (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j : Fin D.R.m)
    (k : Fin ((R.toCx3 F).dW false j)) :
    Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.toRealDat.bC F.lv2 false j (sg0 D A3.A) k) ∈
      LinearMap.range ((R.toCx3 F).w0C false j) := by
  have hpos : (0 : ℝ) < Real.sqrt (RealDat.nP F.lv2 false) := Real.sqrt_pos.mpr (RealDat.nP_pos (F := F.lv2) false)
  refine ⟨Pi.single k ((((Real.sqrt (RealDat.nP F.lv2 false))⁻¹ : ℝ) : ℂ)), ?_⟩
  simp only [CxData.w0C, CxData.wC, lin, LinearMap.comp_apply, Fintype.linearCombination_apply_single]
  rw [LinearMap.map_smul]
  show Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW j (sg0 D A3.A)).H) (_ • _) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW j (sg0 D A3.A)).H) (Tw.mk _ _)
  erw [Tw.out_smul, cj_ofReal]
  show ((((Real.sqrt (RealDat.nP F.lv2 false))⁻¹ : ℝ) : ℂ)) • ((((Real.sqrt (RealDat.nP F.lv2 false)) : ℝ) : ℂ) • R.toRealDat.bC F.lv2 false j (sg0 D A3.A) k) = R.toRealDat.bC F.lv2 false j (sg0 D A3.A) k
  rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one, one_smul]

end GlobalTheory.TwParts

open GlobalTheory.TwParts in
theorem GlobalTheory.TwParts.mem_iSup_Wp3_of_mem_WS : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), (R.toCx3 F).PartsW false → ∀ j (w : (R.HW j (sg0 D A3.A)).H), w ∈ R.toRealDat.WS F.lv2 false j (sg0 D A3.A) → w ∈ ⨆ p, R.Wp3 j p := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hP j w hw
  obtain ⟨-, hsup⟩ := hP j
  refine Submodule.span_le.mpr ?_ hw
  rintro _ ⟨k, rfl⟩
  have hk := mk_bC_mem_range R F j k
  rw [← hsup] at hk
  have hk' : Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.toRealDat.bC F.lv2 false j (sg0 D A3.A) k) ∈
      ⨆ p, (R.toCx3 F).Wp j p := by
    have hle : (⨆ p, (R.toCx3 F).Wp j p ⊓ LinearMap.range ((R.toCx3 F).w0C false j)) ≤ ⨆ p, (R.toCx3 F).Wp j p :=
      iSup_mono fun p => inf_le_left
    exact hle hk
  refine Submodule.iSup_induction (fun p => (R.toCx3 F).Wp j p) (motive := fun x => Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW j (sg0 D A3.A)).H) x ∈ ⨆ p, R.Wp3 j p) hk' ?_ ?_ ?_
  · intro p x hx
    exact Submodule.mem_iSup_of_mem p hx
  · exact Submodule.zero_mem _
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy
end

