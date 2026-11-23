module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.TwTrLin

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_fixed_iff (ρ : Representation ℂ G V) (H : Subgroup G) (v : V) :
    v ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  show (∀ h : H, ρ (h : G) v = ((1 : H →* ℂˣ) h : ℂ) • v) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  exact ⟨fun H h hh => H ⟨h, hh⟩, fun H h => H h h.2⟩

theorem finite_out_support [TopologicalSpace G] [IsTopologicalGroup G] {K' : Subgroup G}
    (hK' : IsOpen (K' : Set G)) {f : G → ℂ} (hf : HasCompactSupport f) :
    {q : G ⧸ K' | f q.out ≠ 0}.Finite := by
  haveI : DiscreteTopology (G ⧸ K') := QuotientGroup.discreteTopology hK'
  have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ K') '' tsupport f) :=
    hf.image QuotientGroup.continuous_mk
  refine hc.finite_of_discrete.subset ?_
  intro q hq
  exact ⟨q.out, subset_tsupport _ hq, QuotientGroup.out_eq' q⟩

theorem term_fin (ρ : Representation ℂ G V) (K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V)
    (h : {q : G ⧸ K' | f q.out ≠ 0}.Finite) :
    Function.HasFiniteSupport fun q : G ⧸ K' => f q.out • (ρ q.out ∘ₗ A) :=
  h.subset (Function.support_smul_subset_left (fun q : G ⧸ K' => f q.out) fun q => ρ q.out ∘ₗ A)

theorem levOp_add (ρ : Representation ℂ G V) (K K' : Subgroup G) (f f' : G → ℂ) (A : V →ₗ[ℂ] V)
    (h : {q : G ⧸ K' | f q.out ≠ 0}.Finite) (h' : {q : G ⧸ K' | f' q.out ≠ 0}.Finite) :
    levOp ρ K K' (f + f') A = levOp ρ K K' f A + levOp ρ K K' f' A := by
  unfold levOp
  rw [← smul_add, ← finsum_add_distrib (term_fin ρ K' f A h) (term_fin ρ K' f' A h')]
  congr 1
  exact finsum_congr fun q => by simp [add_smul]

theorem levOp_smul_fun (ρ : Representation ℂ G V) (K K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V) (c : ℂ) :
    levOp ρ K K' (c • f) A = c • levOp ρ K K' f A := by
  unfold levOp
  rw [smul_comm c, smul_finsum c]
  congr 1
  exact finsum_congr fun q => by simp [mul_smul]

theorem levOp_smul_op (ρ : Representation ℂ G V) (K K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V) (c : ℂ) :
    levOp ρ K K' f (c • A) = c • levOp ρ K K' f A := by
  unfold levOp
  rw [smul_comm c, smul_finsum c]
  congr 1
  exact finsum_congr fun q => by rw [LinearMap.comp_smul, smul_comm]

end GlobalTheory.TwTrLin

namespace GlobalTheory.TwTrLin

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem A_fixed (ρ : Representation ℂ G V) (θ : G →* G) (hθ : ∀ g, θ (θ g) = g) (K' : Subgroup G)
    (hK'θ : ∀ k ∈ K', θ k ∈ K') (A : V →ₗ[ℂ] V) (hA : ∀ g, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A) {v : V}
    (hv : v ∈ fixed ρ K') : A v ∈ fixed ρ K' := by
  rw [mem_fixed_iff] at hv ⊢
  intro k hk
  have := LinearMap.congr_fun (hA (θ k)) v
  simp only [LinearMap.comp_apply, hθ] at this
  rw [← this, hv _ (hK'θ k hk)]

theorem levOp_mapsTo (ρ : Representation ℂ G V) (K K' : Subgroup G) (A : V →ₗ[ℂ] V) (f : G → ℂ)
    (hfin : {q : G ⧸ K' | f q.out ≠ 0}.Finite)
    (hl : ∀ k ∈ K', ∀ x, f (k * x) = f x) (hr : ∀ k ∈ K', ∀ x, f (x * k) = f x)
    (hA : ∀ v ∈ fixed ρ K', A v ∈ fixed ρ K') :
    ∀ v ∈ fixed ρ K', levOp ρ K K' f A v ∈ fixed ρ K' := by
  intro v hv
  have hw := hA v hv
  have hw' := (mem_fixed_iff ρ K' (A v)).1 hw
  let F : G ⧸ K' → V := fun q => f q.out • ρ q.out (A v)
  have hF : ∀ x : G, F (QuotientGroup.mk x) = f x • ρ x (A v) := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K' x
    simp only [F, hh, hr _ h.2, map_mul, Module.End.mul_apply, hw' _ h.2]
  have hFfin : Function.HasFiniteSupport F :=
    hfin.subset (Function.support_smul_subset_left (fun q : G ⧸ K' => f q.out) fun q => ρ q.out (A v))
  have hL : levOp ρ K K' f A v = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ∑ᶠ q, F q := by
    unfold levOp
    rw [LinearMap.smul_apply, ← LinearMap.applyₗ_apply_apply (R := ℂ) v,
      map_finsum _ (term_fin ρ K' f A hfin)]
    rfl
  rw [hL, mem_fixed_iff]
  intro k hk
  rw [map_smul, map_finsum _ hFfin]
  congr 1
  have hk' : ∀ q, ρ k (F q) = F (k • q) := by
    intro q
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [MulAction.Quotient.smul_mk, hF, smul_eq_mul, hl _ hk]
    simp only [F, map_smul, map_mul, Module.End.mul_apply]
  simp_rw [hk']
  exact finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (G ⧸ K'))

end GlobalTheory.TwTrLin

namespace GlobalTheory.TwTrLin

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem twTr_eq (ρ : Representation ℂ G V) (K K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V)
    (h : ∀ v ∈ fixed ρ K', levOp ρ K K' f A v ∈ fixed ρ K') :
    twTr ρ K K' f A = LinearMap.trace ℂ (fixed ρ K') ((levOp ρ K K' f A).restrict h) := dif_pos h

theorem trace_restrict_congr {W : Submodule ℂ V} {L L' : V →ₗ[ℂ] V} (e : L = L') (h : ∀ v ∈ W, L v ∈ W)
    (h' : ∀ v ∈ W, L' v ∈ W) : LinearMap.trace ℂ W (L.restrict h) = LinearMap.trace ℂ W (L'.restrict h') := by
  subst e; rfl

theorem restrict_add' {W : Submodule ℂ V} (L₁ L₂ : V →ₗ[ℂ] V) (h₁ : ∀ v ∈ W, L₁ v ∈ W) (h₂ : ∀ v ∈ W, L₂ v ∈ W)
    (h : ∀ v ∈ W, (L₁ + L₂) v ∈ W) : (L₁ + L₂).restrict h = L₁.restrict h₁ + L₂.restrict h₂ := by
  ext x; simp [LinearMap.restrict_apply]

theorem restrict_smul' {W : Submodule ℂ V} (L : V →ₗ[ℂ] V) (c : ℂ) (h₁ : ∀ v ∈ W, L v ∈ W)
    (h : ∀ v ∈ W, (c • L) v ∈ W) : (c • L).restrict h = c • L.restrict h₁ := by
  ext x; simp [LinearMap.restrict_apply]

theorem trace_id_eq_finrank (W : Type) [AddCommGroup W] [Module ℂ W] :
    LinearMap.trace ℂ W LinearMap.id = (Module.finrank ℂ W : ℂ) := by
  by_cases hW : Module.Finite ℂ W
  · exact LinearMap.trace_id ℂ W
  · rw [Module.finrank_of_not_finite hW]
    unfold LinearMap.trace
    rw [dite_eq_right]
    · simp
    · rintro ⟨s, ⟨b⟩⟩
      exact hW (Module.Finite.of_basis b)

theorem relIndex_ne_zero_of_isOpen [TopologicalSpace G] [IsTopologicalGroup G] {K K' : Subgroup G}
    (hKc : IsCompact (K : Set G)) (hK'o : IsOpen (K' : Set G)) : K'.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  haveI : Finite (K ⧸ K'.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hK'o.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem levOp_unit (ρ : Representation ℂ G V) (K K' : Subgroup G) :
    ∃ x₀ ∈ K', levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ρ x₀ := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K' (1 : G)
  refine ⟨h, h.2, ?_⟩
  unfold levOp
  have hout : ∀ q : G ⧸ K', q ≠ (QuotientGroup.mk 1 : G ⧸ K') → q.out ∉ K' := by
    intro q hq hm
    apply hq
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 (by simpa using K'.inv_mem hm)
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K')
    (fun q hq => by rw [Set.indicator_of_notMem (hout q hq), zero_smul])]
  rw [hh, one_mul, Set.indicator_of_mem h.2]
  simp

end GlobalTheory.TwTrLin

namespace GlobalTheory.TwTrLin

theorem twTr_linear : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), ∀ (θ : G →* G), (∀ g, θ (θ g) = g) → ∀ A : V →ₗ[ℂ] V, (∀ g, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A) → ∀ K' : Subgroup G, IsLevel θ K K' → (∀ f f' (c : ℂ), IsHecke K' f → IsHecke K' f' → twTr ρ K K' (f + f') A = twTr ρ K K' f A + twTr ρ K K' f' A ∧ twTr ρ K K' (c • f) A = c * twTr ρ K K' f A ∧ twTr ρ K K' f (c • A) = c * twTr ρ K K' f A) ∧ (fixed ρ K' = ⊥ → ∀ f, twTr ρ K K' f A = 0) ∧ twTr ρ K K' ((K' : Set G).indicator 1) LinearMap.id = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * (Module.finrank ℂ (fixed ρ K') : ℂ) ∧ K'.relIndex K ≠ 0 := by
  intro G _ _ _ K _ hKc V _ _ ρ θ hθ A hA K' hlev
  obtain ⟨hK'o, _, hK'θ⟩ := hlev
  have hAf : ∀ v ∈ fixed ρ K', A v ∈ fixed ρ K' := fun v hv => A_fixed ρ θ hθ K' hK'θ A hA hv
  have hmaps : ∀ f, IsHecke K' f → ∀ v ∈ fixed ρ K', levOp ρ K K' f A v ∈ fixed ρ K' := fun f hf =>
    levOp_mapsTo ρ K K' A f (finite_out_support hK'o hf.1) (fun k hk x => (hf.2 k hk x).1)
      (fun k hk x => (hf.2 k hk x).2) hAf
  refine ⟨?_, ?_, ?_, relIndex_ne_zero_of_isOpen hKc hK'o⟩
  · intro f f' c hf hf'
    have h1 := hmaps f hf
    have h2 := hmaps f' hf'
    have e1 := levOp_add ρ K K' f f' A (finite_out_support hK'o hf.1) (finite_out_support hK'o hf'.1)
    have e2 := levOp_smul_fun ρ K K' f A c
    have e3 := levOp_smul_op ρ K K' f A c
    have h12 : ∀ v ∈ fixed ρ K', levOp ρ K K' (f + f') A v ∈ fixed ρ K' := by
      intro v hv; rw [e1]; exact add_mem (h1 v hv) (h2 v hv)
    have hs : ∀ v ∈ fixed ρ K', (c • levOp ρ K K' f A) v ∈ fixed ρ K' := fun v hv =>
      Submodule.smul_mem _ c (h1 v hv)
    have hc : ∀ v ∈ fixed ρ K', levOp ρ K K' (c • f) A v ∈ fixed ρ K' := by
      intro v hv; rw [e2]; exact hs v hv
    have hc' : ∀ v ∈ fixed ρ K', levOp ρ K K' f (c • A) v ∈ fixed ρ K' := by
      intro v hv; rw [e3]; exact hs v hv
    refine ⟨?_, ?_, ?_⟩
    · rw [twTr_eq _ _ _ _ _ h12, twTr_eq _ _ _ _ _ h1, twTr_eq _ _ _ _ _ h2,
        trace_restrict_congr e1 h12 (fun v hv => add_mem (h1 v hv) (h2 v hv)), restrict_add' _ _ h1 h2, map_add]
    · rw [twTr_eq _ _ _ _ _ hc, twTr_eq _ _ _ _ _ h1, trace_restrict_congr e2 hc hs, restrict_smul' _ c h1,
        map_smul, smul_eq_mul]
    · rw [twTr_eq _ _ _ _ _ hc', twTr_eq _ _ _ _ _ h1, trace_restrict_congr e3 hc' hs, restrict_smul' _ c h1,
        map_smul, smul_eq_mul]
  · intro h0 f
    unfold twTr
    split_ifs with h
    · haveI : Subsingleton (fixed ρ K') := by
        have key : ∀ v : V, v ∈ fixed ρ K' → v = 0 := fun v hv => by
          rw [h0] at hv
          exact (Submodule.mem_bot ℂ).1 hv
        exact ⟨fun a b => Subtype.ext ((key _ a.2).trans (key _ b.2).symm)⟩
      rw [show (levOp ρ K K' f A).restrict h = 0 from LinearMap.ext fun x => Subsingleton.elim _ _, map_zero]
    · rfl
  · obtain ⟨x₀, hx₀, hL⟩ := levOp_unit ρ K K'
    have hfx : ∀ v ∈ fixed ρ K', ρ x₀ v = v := fun v hv => (mem_fixed_iff ρ K' v).1 hv x₀ hx₀
    have hm : ∀ v ∈ fixed ρ K', levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id v ∈ fixed ρ K' := by
      intro v hv
      rw [hL, LinearMap.smul_apply, hfx v hv]
      exact Submodule.smul_mem _ _ hv
    rw [twTr_eq _ _ _ _ _ hm]
    have hr : (levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id).restrict hm =
        ((K'.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id := by
      ext x
      simp [LinearMap.restrict_apply, hL, hfx x.1 x.2]
    rw [hr, map_smul, trace_id_eq_finrank, smul_eq_mul]

end GlobalTheory.TwTrLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise

namespace GlobalTheory.LocFinU

theorem relIndex_ne_zero_of_subset_cpt {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U P : Subgroup G) (hU : IsOpen (U : Set G)) (Ω : Set G) (hΩ : IsCompact Ω) (hP : (P : Set G) ⊆ Ω) :
    U.relIndex P ≠ 0 := by
  obtain ⟨s, hs⟩ := hΩ.elim_finite_subcover (fun g : Ω => (g : G) • (U : Set G)) (fun g => hU.smul _)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, ⟨1, U.one_mem, mul_one x⟩⟩)
  have hmem : ∀ q : P ⧸ U.subgroupOf P, ∃ i : s, ((Quotient.out q : P) : G) ∈ ((i : Ω) : G) • (U : Set G) := by
    intro q
    have := hs (hP (Quotient.out q).2)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, h⟩ := this
    exact ⟨⟨i, hi⟩, h⟩
  choose f hf using hmem
  have hinj : Function.Injective f := by
    intro q q' h
    have h1 := hf q
    have h2 := hf q'
    rw [h] at h1
    obtain ⟨u, hu, hu'⟩ := h1
    obtain ⟨u', hu2, hu2'⟩ := h2
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    change QuotientGroup.mk _ = QuotientGroup.mk _
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hu', ← hu2']
    simp only [smul_eq_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    exact U.mul_mem (U.inv_mem hu) hu2
  haveI : Finite (P ⧸ U.subgroupOf P) := Finite.of_injective f hinj
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.LocFinU

namespace GlobalTheory.LocFinU

theorem continuous_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) : Continuous (cj w) := by
  unfold cj
  split_ifs with h
  · exact h.choose_spec.1
  · exact continuous_id

theorem isClosed_UL {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) :
    IsClosed (UL n w : Set (GLw n w)) := by
  unfold UL
  split_ifs
  · exact isClosed_univ
  · have hc : Continuous fun g : GLw n w => cT (cj w) (g : Matrix (Fin n) (Fin n) _) * 1 * (g : Matrix (Fin n) (Fin n) _) :=
      ((Units.continuous_val.matrix_map (continuous_cj w)).matrix_transpose.matrix_mul continuous_const).matrix_mul
        Units.continuous_val
    exact isClosed_eq hc continuous_const

theorem isCompact_KL {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) :
    IsCompact (KL n w : Set (UL n w)) := by
  rw [Subtype.isCompact_iff]
  have hK : IsCompact (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w)
  have : (Subtype.val '' (KL n w : Set (UL n w))) = (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ∩ (UL n w : Set (GLw n w)) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨g, h2⟩, h1, rfl⟩
  rw [this]
  exact hK.inter_right (isClosed_UL n w)

end GlobalTheory.LocFinU

namespace GlobalTheory.LocFinU

theorem cptPart_subset_of_comm {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (T : Subgroup G) (hc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) :
    (cptPart T : Set G) ⊆ {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))} := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    refine ⟨T.one_mem, ?_⟩
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.coe_bot, closure_singleton]
    exact isCompact_singleton
  | mul x y _ _ hx hy =>
    refine ⟨T.mul_mem hx.1 hy.1, ?_⟩
    have hxy : Commute x y := hc x hx.1 y hy.1
    have hcp : IsCompact (closure (Subgroup.zpowers x : Set G) * closure (Subgroup.zpowers y : Set G)) :=
      hx.2.mul hy.2
    refine hcp.of_isClosed_subset isClosed_closure (closure_minimal ?_ hcp.isClosed)
    rintro _ ⟨k, rfl⟩
    exact ⟨x ^ k, subset_closure ⟨k, rfl⟩, y ^ k, subset_closure ⟨k, rfl⟩, (hxy.mul_zpow k).symm⟩
  | inv x _ hx =>
    refine ⟨T.inv_mem hx.1, ?_⟩
    rw [Subgroup.zpowers_inv]
    exact hx.2

end GlobalTheory.LocFinU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (IsFiniteQC)
open GlobalTheory.VB

namespace GlobalTheory.CurveDegreesCompare


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits in
theorem _root_.GlobalTheory.CurveDegreesCompare.residueDegree_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueDegree x = g.residueDegree (f x) * f.residueDegree x := by
  letI := (g.residueFieldMap (f x)).hom.toAlgebra
  letI := (f.residueFieldMap x).hom.toAlgebra
  letI : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  haveI : IsScalarTower (Z.residueField (g (f x))) (Y.residueField (f x))
      (X.residueField x) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((f ≫ g).residueFieldMap x).hom = _
    rw [Scheme.residueFieldMap_comp]
    rfl
  change Module.finrank (Z.residueField (g (f x))) (X.residueField x) =
    Module.finrank (Z.residueField (g (f x))) (Y.residueField (f x)) *
      Module.finrank (Y.residueField (f x)) (X.residueField x)
  exact (Module.finrank_mul_finrank _ _ _).symm


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits in
theorem _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsOpenImmersion f] (x : X) : f.residueDegree x = 1 := by
  letI := (f.residueFieldMap x).hom.toAlgebra
  have hbij : Function.Bijective (algebraMap (Y.residueField (f x)) (X.residueField x)) :=
    ConcreteCategory.bijective_of_isIso (f.residueFieldMap x)
  let e : Y.residueField (f x) ≃ₗ[Y.residueField (f x)] X.residueField x :=
    (AlgEquiv.ofBijective (Algebra.ofId _ _) hbij).toLinearEquiv
  change Module.finrank (Y.residueField (f x)) (X.residueField x) = 1
  rw [← e.finrank_eq, Module.finrank_self]

section Clauses

variable (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C]

variable {C}

end Clauses

end GlobalTheory.CurveDegreesCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightDerivativeMultiplicityMapValueEq
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.MultDer

theorem smoothVec_zero {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : SmoothVec L π 0 := by
  intro k Xs _
  simp only [map_zero]
  exact contDiff_const

theorem smoothVec_of_mem {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {w : M.H τ} (hw : w ∈ M.sm τ) : SmoothVec (lieAt V τ) (M.rep τ) w := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact smoothVec_zero _ _
  | add x y _ _ hx hy =>
    intro k Xs h
    simp only [map_add (f := _)]
    exact (hx k Xs h).add (hy k Xs h)
  | smul c x _ hx =>
    intro k Xs h
    simp only [map_smul]
    exact (hx k Xs h).const_smul c

theorem rder_eq : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsInfFam θ → IsMultMap θ M J χ T → ∀ (v : M.Vec) (τ : D.what₂.Tau), SmoothVec (lieAt V τ) (M.rep τ) (v τ : M.H τ) ∧ ∀ X ∈ lieAt V τ, ∃ u : M.sm τ, (u : M.H τ) = dRep (M.rep τ) X (v τ : M.H τ) ∧ Rder θ V τ X (T v) = T (Function.update v τ u) := by
  intro D θ V S M J χ T _ hT v τ
  have hs := smoothVec_of_mem M τ (v τ).2
  refine ⟨hs, fun X hX => ?_⟩
  have hH := GlobalTheory.SmoothAutCheck.gramAt_herm V τ
  have hU := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have hπ := (GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.1
  obtain ⟨h1, -, h3⟩ := _root_.GlobalTheory.SmVecCalc.smooth_calculus _ _ _ _ hH hU hπ _ hs
  refine ⟨⟨_, Submodule.subset_span (h3 X hX).1⟩, rfl, ?_⟩
  funext x
  obtain ⟨ℓ, hℓ, hℓT⟩ := hT.cont τ v x
  have hd := _root_.GlobalTheory.SobOrbit.hasDerivAt_sobCont_orbit _ _ _ _ hH hU hπ _ hs ℓ hℓ X hX
  rw [← hℓT]
  have e : (fun t : ℝ => T v (x * oneP θ V τ X t)) =
      fun t : ℝ => ℓ (M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ)) := by
    funext t
    have hg := GlobalTheory.SmoothAutCheck.exp_mem_UH hU hX t
    let w : M.sm τ := ⟨_, Submodule.subset_span (h1 _ hg)⟩
    have h4 := congrFun (hT.equiv τ _ hg v w rfl) x
    exact ((hℓT w).trans h4).symm
  show deriv (fun t : ℝ => T v (x * oneP θ V τ X t)) 0 = _
  rw [e]
  exact hd.deriv

end GlobalTheory.HolRead.MultDer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySubsingletonEtaleOverPolynomiStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_subsingleton_etale_over_polynomial_algClosed : ∀ (q : ℕ) [NeZero q] (K E : Type) [Field K] [IsAlgClosed K] [CommRing E] [Algebra (Polynomial K) E] [Algebra.Etale (Polynomial K) E], IsUnit (q : K) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp E) n i) := by
  first | (exact @GlobalTheory.EtAlgCD.etale_polynomial_cd_le_one) | (exact GlobalTheory.EtAlgCD.etale_polynomial_cd_le_one) | (intros; apply GlobalTheory.EtAlgCD.etale_polynomial_cd_le_one <;> assumption)
end

