module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMulAddEqOneOfNotMem
section
noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.MainNotions.G _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

section Deco

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}



omit [StarRing E] in
theorem exists_coprime_mem (p : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ Q ∈ S, ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal) : ∃ a : ℕ, a.Coprime p ∧ ∀ Q ∈ S, ((a : ℕ) : 𝓞 E) ∈ Q.asIdeal := by
  classical
  have h1 : ∀ Q : S, ∃ a : ℕ, a.Coprime p ∧ ((a : ℕ) : 𝓞 E) ∈ Q.1.asIdeal := by
    intro Q
    haveI := Q.1.isMaximal
    haveI : Finite (𝓞 E ⧸ Q.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ Q.1.ne_bot
    letI := Ideal.Quotient.field Q.1.asIdeal
    have hp : (ringChar (𝓞 E ⧸ Q.1.asIdeal)).Prime := CharP.prime_ringChar _
    refine ⟨_, (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hS Q.1 Q.2 ?_, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact (ringChar.spec _ _).2 h
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact (ringChar.spec _ _).2 dvd_rfl
  choose a ha ha' using h1
  refine ⟨∏ Q, a Q, Nat.Coprime.prod_left fun Q _ => ha Q, fun Q hQ => ?_⟩
  exact Ideal.mem_of_dvd _ (Nat.cast_dvd_cast (Finset.dvd_prod_of_mem a (Finset.mem_univ ⟨Q, hQ⟩))) (ha' ⟨Q, hQ⟩)

end Deco

section Coef

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K)

theorem natCast_notMem_of_coprime {a p : ℕ} (h : a.Coprime p) (w : HeightOneSpectrum (𝓞 K))
    (hw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal) : ((a : ℕ) : 𝓞 K) ∉ w.asIdeal := by
  intro ha
  obtain ⟨x, y, e⟩ := (Nat.Coprime.cast (R := 𝓞 K) h)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ ha) (w.asIdeal.mul_mem_left _ hw)))

omit [Fintype ι] in
theorem nsmul_mem_tauLat (τ : ι) {L L' : Submodule (𝓞 E) (Fin n → E)} {a : ℕ} (h : ∀ x ∈ L, a • x ∈ L')
    {y : Fin n → K} (hy : y ∈ tauLat emb τ L) : a • y ∈ tauLat emb τ L' := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    refine Submodule.subset_span ⟨a • x, h x hx, ?_⟩
    funext i
    simp
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ c hy

omit [Fintype ι] in
theorem localization_dualFr_tauLat_le (τ : ι) {L L' : Submodule (𝓞 E) (Fin n → E)} {a : ℕ} (h : ∀ x ∈ L, a • x ∈ L')
    (w : HeightOneSpectrum (𝓞 K)) (ha : ((a : ℕ) : 𝓞 K) ∉ w.asIdeal) :
    localization₂ w.asIdeal (dualFr (tauLat emb τ L')) ≤ localization₂ w.asIdeal (dualFr (tauLat emb τ L)) := by
  refine GlobalTheory.TransLoc.localization_le_of_smul_mem w ha fun φ hφ x hx => ?_
  have := hφ _ (nsmul_mem_tauLat emb τ h hx)
  rw [dotProduct_smul] at this
  rw [smul_dotProduct, Nat.cast_smul_eq_nsmul]
  exact this

theorem localization_nabK_delK_congr (lam : ι → DomWeight n) {M M' : ι → Submodule (𝓞 K) (Fin n → K)}
    (hM : ∀ τ, Submodule.IsFullLattice K (M τ)) (hM' : ∀ τ, Submodule.IsFullLattice K (M' τ)) (w : HeightOneSpectrum (𝓞 K))
    (h : ∀ τ, localization₂ w.asIdeal (M τ) = localization₂ w.asIdeal (M' τ)) :
    localization₂ w.asIdeal (nabK lam M) = localization₂ w.asIdeal (nabK lam M') ∧
      localization₂ w.asIdeal (delK lam M) = localization₂ w.asIdeal (delK lam M') := by
  choose B hB using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (hM τ) w
  have hB' : ∀ τ, IsBasisAt w (M' τ) (B τ) := fun τ => (h τ).symm.trans (hB τ)
  have h1 := GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι n lam M hM w B hB
  have h2 := GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι n lam M' hM' w B hB'
  have key : ∀ (T : Submodule (𝓞 K) (Pol K ι n)) (x : VV K lam),
      x ∈ localization₂ w.asIdeal (T.comap ((VV K lam).subtype.restrictScalars (𝓞 K))) ↔ x.1 ∈ localization₂ w.asIdeal T := by
    intro T x
    exact Iff.rfl
  constructor
  · ext x
    unfold nabK
    rw [key, key, h1.1, h2.1]
  · ext x
    unfold delK
    rw [key, key, h1.2, h2.2]

theorem localization_nabAtr_delAtr_congr (lam : ι → DomWeight n) {L L' : Submodule (𝓞 E) (Fin n → E)}
    (hL : Submodule.IsFullLattice E L) (hL' : Submodule.IsFullLattice E L') {a : ℕ} (h : ∀ x ∈ L, a • x ∈ L')
    (h' : ∀ x ∈ L', a • x ∈ L) (w : HeightOneSpectrum (𝓞 K)) (ha : ((a : ℕ) : 𝓞 K) ∉ w.asIdeal) :
    localization₂ w.asIdeal (nabAtr emb lam L) = localization₂ w.asIdeal (nabAtr emb lam L') ∧
      localization₂ w.asIdeal (delAtr emb lam L) = localization₂ w.asIdeal (delAtr emb lam L') :=
  localization_nabK_delK_congr lam
    (fun τ => GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.TauLat.tauLatLattice E K ι n emb τ L hL))
    (fun τ => GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.TauLat.tauLatLattice E K ι n emb τ L' hL')) w
    fun τ => le_antisymm (localization_dualFr_tauLat_le emb τ h' w ha) (localization_dualFr_tauLat_le emb τ h w ha)

end Coef

variable {p : ℕ} {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem use₃ (lam : X.Tau → DomWeight n) (hT : ∀ Q ∈ ST, ((p : ℕ) : 𝓞 X.E) ∉ Q.asIdeal)
    (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal) :
    localization₂ w.asIdeal (nabAtr X.emb lam d.1.Lsh) = localization₂ w.asIdeal (nabAtr X.emb lam d.1.N) ∧
      localization₂ w.asIdeal (delAtr X.emb lam d.1.Lsh) = localization₂ w.asIdeal (delAtr X.emb lam d.1.N) := by
  obtain ⟨a, hap, ha⟩ := exists_coprime_mem p ST hT
  letI : Submodule.IsFullLattice X.E d.1.N := Formalism.L2.Ker.full_of_sd ⟨d.2.lat, d.2.uni⟩
  letI := d.2.Lsh_lattice
  have hLsh : Submodule.IsFullLattice X.E d.1.Lsh := Submodule.IsFullLattice.of_le X.E d.2.N_le_Lsh
  refine localization_nabAtr_delAtr_congr X.emb lam hLsh inferInstance (a := a) (fun x hx => ?_)
    (fun x hx => Submodule.smul_of_tower_mem _ a (d.2.N_le_Lsh hx)) w (natCast_notMem_of_coprime hap w hw)
  rw [← Nat.cast_smul_eq_nsmul (𝓞 X.E)]
  exact d.2.smul_Lsh_mem_N (fun P => by rw [map_natCast]; exact ha P.1 P.2) hx

end GlobalTheory.GO
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalCombinationOfFixedLocalTranslates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphAvg

section Abstract

variable {G : Type} [Group G]

open GlobalTheory.SphLabelOps

theorem finiteIndex_stab {K : Subgroup G} {g : G} {R : Finset G} (hR : Reps K g R) :
    (MulAction.stabilizer K (QuotientGroup.mk g : G ⧸ K)).FiniteIndex := by
  have hfin : (MulAction.orbit K (QuotientGroup.mk g : G ⧸ K)).Finite := by
    refine (R.finite_toSet.image (fun γ => (QuotientGroup.mk γ : G ⧸ K))).subset ?_
    rintro _ ⟨k, rfl⟩
    obtain ⟨γ, ⟨hγ, e⟩, -⟩ := hR.2 ((k : G) * g) ⟨k, k.2, 1, one_mem _, by simp⟩
    refine ⟨γ, hγ, ?_⟩
    show (QuotientGroup.mk γ : G ⧸ K) = (k : G) • (QuotientGroup.mk g : G ⧸ K)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
    exact e
  refine ⟨?_⟩
  rw [MulAction.index_stabilizer]
  exact ((Set.ncard_pos hfin).2 ⟨_, MulAction.mem_orbit_self _⟩).ne'

theorem mem_of_stab {K : Subgroup G} {g : G} {n : K} (hn : n ∈ MulAction.stabilizer K (QuotientGroup.mk g : G ⧸ K)) :
    g⁻¹ * (n : G) * g ∈ K := by
  have h : ((n : G) • (QuotientGroup.mk g : G ⧸ K)) = QuotientGroup.mk g := hn
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at h
  have := inv_mem h
  convert this using 1
  group

theorem card_pos {K : Subgroup G} {g : G} {R : Finset G} (hR : Reps K g R) : 0 < R.card := by
  obtain ⟨γ, ⟨hγ, -⟩, -⟩ := hR.2 g ⟨1, one_mem _, 1, one_mem _, by simp⟩
  exact Finset.card_pos.2 ⟨γ, hγ⟩

theorem fixed_comb {K : Subgroup G} {ι : Type} (s : Finset ι) (g : ι → G) (R : ι → Finset G)
    (hR : ∀ i ∈ s, Reps K (g i) (R i)) (a : ι → ℂ) {M : Type} [AddCommGroup M] [Module ℂ M]
    (π : G →* Module.End ℂ M) (u : M) (hu : ∀ k ∈ K, π k u = u)
    (hw : ∀ k ∈ K, π k (∑ i ∈ s, a i • π (g i) u) = ∑ i ∈ s, a i • π (g i) u) :
    ∑ i ∈ s, a i • π (g i) u = ∑ i ∈ s, (a i / ((R i).card : ℂ)) • ∑ γ ∈ R i, π γ u := by
  classical
  have fix : ∀ x, ∀ l ∈ K, π (x * l) u = π x u := fun x l hl => by
    rw [map_mul, Module.End.mul_apply, hu l hl]
  let St : ι → Subgroup K := fun i => MulAction.stabilizer K (QuotientGroup.mk (g i) : G ⧸ K)
  have hSt : (⨅ i ∈ s, St i).FiniteIndex := Subgroup.finiteIndex_iInf' St fun i hi => finiteIndex_stab (hR i hi)
  let N : Subgroup K := (⨅ i ∈ s, St i).normalCore
  haveI : N.FiniteIndex := Subgroup.finiteIndex_normalCore _
  haveI : Fintype (K ⧸ N) := Fintype.ofFinite _
  have hN : ∀ i ∈ s, ∀ n ∈ N, ∀ x : G, π (x * (n : G) * g i) u = π (x * g i) u := by
    intro i hi n hn x
    have h1 : n ∈ St i := (iInf₂_le i hi : (⨅ i ∈ s, St i) ≤ St i) (Subgroup.normalCore_le _ hn)
    have := fix (x * g i) _ (mem_of_stab h1)
    rw [← this]
    congr 1
    group
  let T : ι → M := fun i => ∑ q : K ⧸ N, π ((q.out : G) * g i) u

  have hT : ∀ i ∈ s, ∀ k₁ ∈ K, ∑ q : K ⧸ N, π ((q.out : G) * k₁ * g i) u = T i := by
    intro i hi k₁ hk₁
    have e := Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk (⟨k₁, hk₁⟩ : K) : K ⧸ N))
      (fun q => π (((q * QuotientGroup.mk (⟨k₁, hk₁⟩ : K) : K ⧸ N).out : G) * g i) u)
      (fun q => π ((q.out : G) * g i) u) (fun q => rfl)
    refine Eq.trans ?_ e
    refine Finset.sum_congr rfl fun q _ => ?_
    have hq : (q.out * ⟨k₁, hk₁⟩)⁻¹ * (q * QuotientGroup.mk (⟨k₁, hk₁⟩ : K) : K ⧸ N).out ∈ N := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
    have := hN i hi _ hq ((q.out : G) * k₁)
    rw [← this]
    congr 2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev]
    group
  have hC : ∀ i ∈ s, ((R i).card : ℂ) • T i = (Fintype.card (K ⧸ N) : ℂ) • ∑ γ ∈ R i, π γ u := by
    intro i hi
    have e1 : ∑ γ ∈ R i, ∑ q : K ⧸ N, π ((q.out : G) * γ) u = ∑ γ ∈ R i, T i := by
      refine Finset.sum_congr rfl fun γ hγ => ?_
      obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := (hR i hi).1 γ hγ
      rw [← hT i hi k₁ h₁]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← fix ((q.out : G) * k₁ * g i) k₂ h₂]
      congr 1
      group
    have e2 : ∑ γ ∈ R i, ∑ q : K ⧸ N, π ((q.out : G) * γ) u = ∑ q : K ⧸ N, ∑ γ ∈ R i, π γ u := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun q _ => (hR i hi).sum_eq (hR i hi) q.out.2 (fun x => π x u) fix
    rw [e1, Finset.sum_const, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
      ← Nat.cast_smul_eq_nsmul ℂ] at e2
    exact e2
  have hQ : (Fintype.card (K ⧸ N) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have main : (Fintype.card (K ⧸ N) : ℂ) • ∑ i ∈ s, a i • π (g i) u = ∑ i ∈ s, a i • T i := by
    have e : ∀ q : K ⧸ N, π (q.out : G) (∑ i ∈ s, a i • π (g i) u) = ∑ i ∈ s, a i • π ((q.out : G) * g i) u := by
      intro q
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, map_mul, Module.End.mul_apply]
    calc (Fintype.card (K ⧸ N) : ℂ) • ∑ i ∈ s, a i • π (g i) u
        = ∑ q : K ⧸ N, π (q.out : G) (∑ i ∈ s, a i • π (g i) u) := by
          rw [Nat.cast_smul_eq_nsmul ℂ, ← Finset.card_univ, ← Finset.sum_const]
          exact Finset.sum_congr rfl fun q _ => (hw _ q.out.2).symm
      _ = ∑ i ∈ s, a i • T i := by
          simp only [e, T, Finset.smul_sum]
          exact Finset.sum_comm
  refine smul_right_injective M hQ ?_
  simp only
  rw [main, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [smul_comm, ← hC i hi, smul_smul, div_mul_cancel₀ _ (Nat.cast_ne_zero.2 (card_pos (hR i hi)).ne')]

end Abstract

end GlobalTheory.SphAvg

namespace GlobalTheory.SphAvg

open GlobalTheory.SphLabelOps GlobalTheory.IdemSupport

theorem fixed_comb_eq_opOf : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ e f, IsPrimeIdem P e f → ∀ a : GA D V →₀ ℂ, (∀ g ∈ a.support, SuppF V f g) → ∃ c : List ℤ →₀ ℂ, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ GlobalTheory.Hk3.hyp V P, π k u = u) → (∀ k ∈ GlobalTheory.Hk3.hyp V P, π k (a.sum fun g z => z • π g u) = a.sum fun g z => z • π g u) → (a.sum fun g z => z • π g u) = opOf π P c u := by
  classical
  intro D V P e f h a ha
  obtain ⟨K, hK⟩ := exists_hyp V P
  obtain ⟨-, ϖ, -, h1, h2⟩ := exists_real_unif D P
  have he := (GlobalTheory.HeckeDual.idem_of_isPrimeIdem h).1
  have hd : ∀ g, ∃ d, SuppF V f g → Reps K g (rep V P d) := by
    intro g
    by_cases hg : SuppF V f g
    · obtain ⟨d, hd, hD⟩ := exists_divAt V he (tie_of_isPrimeIdem h) h1 h2 g
      exact ⟨d, fun _ => reps_of_sphOp hK h h1 h2 hg hD (sphOp_rep (isLab_of_divAt h h1 h2 hd hg hD))⟩
    · exact ⟨[], fun h' => absurd h' hg⟩
  choose d hd using hd
  refine ⟨∑ g ∈ a.support, Finsupp.single (d g) (a g / ((rep V P (d g)).card : ℂ)), ?_⟩
  intro M _ _ π u hu hw
  have hu' : ∀ k ∈ K, π k u = u := fun k hk => hu k (by rw [hK]; exact hk)
  have hw' : ∀ k ∈ K, π k (∑ g ∈ a.support, a g • π (id g) u) = ∑ g ∈ a.support, a g • π (id g) u :=
    fun k hk => hw k (by rw [hK]; exact hk)
  rw [Finsupp.sum]
  refine (fixed_comb a.support id (fun g => rep V P (d g)) (fun g hg => hd g (ha g hg)) a π u hu' hw').trans ?_
  rw [opOf, ← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by rw [add_smul]), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finsupp.sum_single_index (by simp), LinearMap.smul_apply, LinearMap.sum_apply]

end GlobalTheory.SphAvg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeGLChartOfUnitaryGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitPrimeChart

theorem entries_of_stab {R K : Type} [CommRing R] [CommRing K] {n : ℕ} {Λ : (Fin n → R) → Prop} {O : R → Prop}
    {OK : Subring K} {ε : R} (φ : R →+* K) (s : K → R) (hs : ∀ t, φ (s t) = t) (hε : φ ε = 1)
    (hO : ∀ x, O x → φ x ∈ OK) (hO' : ∀ t ∈ OK, O (s t))
    {A B C : Matrix (Fin n) (Fin n) R}
    (h1 : ∀ z : Fin n → R, (∀ i, O (z i)) → Λ (ε • B *ᵥ z))
    (h2 : ∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ ε • y = ε • B *ᵥ z)
    (hA : ∀ y, Λ y → Λ (A *ᵥ y)) (hCB : C.map φ * B.map φ = 1) :
    ∀ i j, (C.map φ * A.map φ * B.map φ) i j ∈ OK := by
  intro i j
  have mv : ∀ (M : Matrix (Fin n) (Fin n) R) x, φ ∘ (M *ᵥ x) = M.map φ *ᵥ (φ ∘ x) := fun M x =>
    funext fun i => RingHom.map_mulVec φ M x i
  have sm : ∀ x : Fin n → R, φ ∘ (ε • x) = φ ∘ x := fun x => funext fun i => by simp [hε]
  let z : Fin n → R := fun k => s ((Pi.single j (1 : K) : Fin n → K) k)
  have hz : ∀ k, O (z k) := fun k => hO' _ (by
    by_cases hk : k = j
    · subst hk; simp [one_mem]
    · simp [hk, zero_mem])
  have hz' : φ ∘ z = Pi.single j 1 := funext fun k => hs _
  obtain ⟨z', hz1, hz2⟩ := h2 _ (hA _ (h1 z hz))
  have e1 : A.map φ *ᵥ (B.map φ *ᵥ Pi.single j 1) = B.map φ *ᵥ (φ ∘ z') := by
    have := congrArg (φ ∘ ·) hz2
    simp only [sm] at this
    rw [mv, sm, mv, hz', mv] at this
    exact this
  have e2 : (C.map φ * A.map φ * B.map φ) i j = (φ ∘ z') i := by
    have : (C.map φ * A.map φ * B.map φ) *ᵥ Pi.single j 1 = φ ∘ z' := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec]
    have := congrFun this i
    rw [Matrix.mulVec_single_one] at this
    simpa using this
  rw [e2]
  exact hO _ (hz1 i)

theorem conj_mul_eq_one {K : Type} [CommRing K] {n : ℕ} {X Y Z W : Matrix (Fin n) (Fin n) K} (h1 : Y * X = 1)
    (h2 : X * Y = 1) (h3 : Z * W = 1) : X * Z * Y * (X * W * Y) = 1 := by
  calc X * Z * Y * (X * W * Y) = X * (Z * ((Y * X) * (W * Y))) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.one_mul, ← Matrix.mul_assoc Z, h3, Matrix.one_mul, h2]

theorem conj_conj {K : Type} [CommRing K] {n : ℕ} {X Y Z : Matrix (Fin n) (Fin n) K} (h1 : Y * X = 1) :
    Y * (X * Z * Y) * X = Z := by
  calc Y * (X * Z * Y) * X = (Y * X) * Z * (Y * X) := by simp only [Matrix.mul_assoc]
    _ = Z := by rw [h1, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.SplitPrimeChart

namespace GlobalTheory.SplitPrimeChart

open Formalism.L2.NTheta


set_option maxHeartbeats 1000000 in
theorem exists_chart : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∃ ρ : GA D V →* GL (Fin V.rank) (P.adicCompletion D.host.E), (∀ M : GL (Fin V.rank) (P.adicCompletion D.host.E), ∃ g, Formalism.L2.Theta.SuppAt e V g ∧ ρ g = M) ∧ (∀ k ∈ KsphC V ∅, ρ k ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P)) ∧ ∀ (g : GA D V) (a : Fin V.rank → ℤ), ∀ k₁ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P), ∀ k₂ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P), ((ρ g : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) = (k₁ : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) * Formalism.UG.diagPow D.host.E P (algebraMap D.host.E (P.adicCompletion D.host.E) (ϖ : D.host.E)) a * (k₂ : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) → DivAt V e (ϖ : D.host.E) (List.ofFn a) g := by
  intro D V P e he ϖ h1 h2
  have hee' : e * e = e := he.1.1
  have ht := GlobalTheory.SphLabelOps.tie_of_isPrimeIdem (P := P) (f := e + cA D e) (Or.inl ⟨he, rfl⟩)
  obtain ⟨φ, s, hs, hε, hφ, hO, hO', hinc⟩ := GlobalTheory.SphLabelOps.exists_component hee' ht
  obtain ⟨B, b1, b2⟩ := GlobalTheory.SphLabelOps.exists_basis V hee' ht
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, hee']
  obtain ⟨C, c1, c2⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B hee fun y hy => (b2 y hy).imp fun _ h => h.2
  have mp : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
      finPart D e • (X * Y) = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) → X.map φ * Y.map φ = 1 := by
    intro X Y hXY
    rw [← Matrix.map_mul, ← Matrix.map_one φ (map_zero φ) (map_one φ)]
    refine Matrix.ext fun i j => ?_
    have := congrArg φ (congrFun (congrFun hXY i) j)
    rwa [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hε, one_mul,
      one_mul] at this
  let b : GL (Fin V.rank) (P.adicCompletion D.host.E) := ⟨B.map φ, C.map φ, mp _ _ c1, mp _ _ c2⟩
  let ρ : GA D V →* GL (Fin V.rank) (P.adicCompletion D.host.E) :=
    (MulAut.conj b⁻¹).toMonoidHom.comp ((Formalism.UG.bc φ).comp (finHom V))
  have hρ : ∀ g, ((ρ g : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _) =
      C.map φ * (finMat D.sp.cm.sig V.gram g).map φ * B.map φ := fun g => by
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Units.val_mul]
    rfl
  refine ⟨ρ, fun M => ?_, fun k hk => ?_, fun g a k₁ hk₁ k₂ hk₂ hg => ?_⟩
  · have hsM : ∀ N : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E), (N.map s).map φ = N :=
      fun N => Matrix.ext fun i j => hs _
    have hm : finPart D e • ((B * (M : Matrix _ _ _).map s * C) * (B * ((M⁻¹ : GL _ _) : Matrix _ _ _).map s * C)) =
        finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.smul_apply, smul_eq_mul]
      apply hφ
      have : ((B * (M : Matrix _ _ _).map s * C) * (B * ((M⁻¹ : GL _ _) : Matrix _ _ _).map s * C)).map φ =
          (1 : Matrix (Fin V.rank) (Fin V.rank) _).map φ := by
        simp only [Matrix.map_mul]
        rw [Matrix.map_one φ (map_zero φ) (map_one φ), hsM, hsM]
        exact conj_mul_eq_one (mp _ _ c2) (mp _ _ c1) (Units.mul_inv M)
      exact congrFun (congrFun this i) j
    obtain ⟨g, hgs, hg⟩ := GlobalTheory.SplitLift.split_lift V e he.1 _ _ hm
    refine ⟨g, hgs, Units.ext ?_⟩
    have hgm : (finMat D.sp.cm.sig V.gram g).map φ = (B * (M : Matrix _ _ _).map s * C).map φ :=
      Matrix.ext fun i j => by
        have := congrArg φ (congrFun (congrFun hg i) j)
        rwa [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hε, one_mul,
          one_mul] at this
    rw [hρ, hgm, Matrix.map_mul, Matrix.map_mul, hsM]
    exact conj_conj (mp _ _ c2)
  · have hint : ∀ g ∈ KsphC V ∅, ∀ i j,
        ((ρ g : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _) i j ∈
          Formalism.UG.Ov D.host.E P := by
      intro g hg i j
      rw [hρ]
      exact entries_of_stab (Λ := fun y => y ∈ LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b1
        (fun y hy => b2 y hy) (fun y hy => (hg.2.1 y).1 hy) (mp _ _ c2) i j
    have hk' : k⁻¹ ∈ KsphC V ∅ :=
      (GlobalTheory.SphLabelOps.mem_stabG _).1 (inv_mem ((GlobalTheory.SphLabelOps.mem_stabG k).2 hk))
    refine Formalism.UG.P.cartan_mem_of_entries _ _ (hint k hk) ?_
    rw [← map_inv]
    exact hint _ hk'
  · rw [GlobalTheory.DivDual.divAt_iff]
    refine ⟨List.length_ofFn, GlobalTheory.SphLabelOps.dv_of_cartan φ s hs hε hφ hO hO' (B := B) b1 b2
      (Formalism.UG.P.cartan_entries_of_mem _ _ hk₁) (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₁))
      (Formalism.UG.P.cartan_entries_of_mem _ _ hk₂) (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₂)) ?_⟩
    have e1 : (Matrix.diagonal fun i : Fin V.rank =>
        φ (finPart D (incA D ((ϖ : D.host.E) ^ ((List.ofFn a).getD i.1 0))))) =
        Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) a := by
      unfold Formalism.UG.diagPow
      congr 1
      funext i
      rw [hinc, map_zpow₀]
      simp
    rw [e1, ← hg, hρ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mp _ _ c1, Matrix.one_mul]

end GlobalTheory.SplitPrimeChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAutomorphismOrbitMemFiniteExtensionPadic
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

namespace GlobalTheory

theorem orbit_finite_mem_finite_ext : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (J : Type) (z : J → ℂ),
    (Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (z j)).Finite →
      ∃ L : IntermediateField ℚ_[l] (Qbar l), FiniteDimensional ℚ_[l] L ∧ ∀ j, ι.symm (z j) ∈ L := by
  intro l _ ι J z hfin
  classical
  set O := Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (z j) with hO
  haveI : Finite O := hfin.to_subtype
  set w : J → Qbar l := fun j => ι.symm (z j) with hw
  let K : Finset J → IntermediateField ℚ_[l] (Qbar l) := fun s =>
    IntermediateField.adjoin ℚ_[l] (w '' (s : Set J))
  have hKfin : ∀ s, FiniteDimensional ℚ_[l] (K s) := fun s => by
    haveI : Finite (w '' (s : Set J)) := (s.finite_toSet.image w).to_subtype
    exact IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hbound : ∀ s, Module.finrank ℚ_[l] (K s) ≤ Nat.card O := by
    intro s
    haveI := hKfin s
    rw [← AlgHom.card ℚ_[l] (K s) (Qbar l), ← Nat.card_eq_fintype_card]
    let g : (K s →ₐ[ℚ_[l]] Qbar l) → O := fun φ =>
      ⟨fun j => ι (φ.liftNormal (Qbar l) (w j)),
        ι.symm.trans ((AlgEquiv.ofBijective (φ.liftNormal (Qbar l))
          (Algebra.IsAlgebraic.algHom_bijective _)).toRingEquiv.trans ι), rfl⟩
    apply Nat.card_le_card_of_injective g
    intro φ ψ h
    apply IntermediateField.adjoin_algHom_ext
    rintro x ⟨j, hj, rfl⟩
    have h1 := ι.injective (congrFun (congrArg Subtype.val h) j)
    have e1 := AlgHom.liftNormal_commutes φ (Qbar l) ⟨w j, IntermediateField.subset_adjoin _ _ ⟨j, hj, rfl⟩⟩
    have e2 := AlgHom.liftNormal_commutes ψ (Qbar l) ⟨w j, IntermediateField.subset_adjoin _ _ ⟨j, hj, rfl⟩⟩
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at e1 e2
    exact e1.symm.trans (h1.trans e2)
  set R := Set.range fun s : Finset J => Module.finrank ℚ_[l] (K s) with hR
  have hne : R.Nonempty := ⟨_, ∅, rfl⟩
  have hbdd : BddAbove R := ⟨Nat.card O, by rintro _ ⟨s, rfl⟩; exact hbound s⟩
  obtain ⟨s0, hs0⟩ := Nat.sSup_mem hne hbdd
  haveI := hKfin s0
  refine ⟨K s0, inferInstance, fun j => ?_⟩
  have hle : K s0 ≤ K (insert j s0) :=
    IntermediateField.adjoin.mono _ _ _ (Set.image_mono (by simp))
  haveI := hKfin (insert j s0)
  have heq : K s0 = K (insert j s0) := by
    apply IntermediateField.eq_of_le_of_finrank_le hle
    rw [show Module.finrank ℚ_[l] (K s0) = sSup R from hs0]
    exact le_csSup hbdd ⟨insert j s0, rfl⟩
  rw [heq]
  exact IntermediateField.subset_adjoin _ _ ⟨j, by simp, rfl⟩

end GlobalTheory
end

