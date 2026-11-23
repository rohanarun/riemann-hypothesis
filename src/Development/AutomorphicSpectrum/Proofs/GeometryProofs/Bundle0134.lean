module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0064
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0069
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0070
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0071
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0129
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0072
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0130
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0124
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSncModelOfPatches
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem ratEval_mem {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {N : ℕ} {x : Fin (N + 1) → Ω}
    {c : Fin (N + 1)} {p : Cpt ξ} (hc : InChart ξ x c p) (g : MRing (fun _ : Unit => Fin (N + 1))) :
    ratEval x c g ∈ regAt ξ p := by
  induction g using MvPolynomial.induction_on with
  | C a => simpa using intCast_mem (regAt ξ p) a
  | add a b ha hb => simpa using (regAt ξ p).add_mem ha hb
  | mul_X a i ha =>
    simpa using (regAt ξ p).mul_mem ha (hc.2 i.2)

theorem not_unitAt_of_mem_span {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {N : ℕ}
    {x : Fin (N + 1) → Ω} {B : Set (Cpt ξ)} (hξ : IsCptGen ξ) {c : Fin (N + 1)} {p : Cpt ξ} (hp : p ∈ B)
    (hc : InChart ξ x c p) {g : MRing (fun _ : Unit => Fin (N + 1))} (hg : g ∈ Ideal.span (bdGens ξ x B)) :
    ¬ unitAt ξ p (ratEval x c g) := by
  induction hg using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨d, -, h⟩ := hG
    exact h c p hp hc
  | zero => simpa [unitAt] using fun h : (0 : Ω) ≠ 0 => absurd rfl h
  | add a b _ _ ha hb =>
    have := not_unitAt_add hξ (ratEval_mem hc a) (ratEval_mem hc b) ha hb
    simpa using this
  | smul a b _ hb =>
    intro h
    have e : ratEval x c (a • b) = ratEval x c a * ratEval x c b := by simp
    rw [e] at h
    exact hb (unitAt_of_mul_right h (ratEval_mem hc a) (ratEval_mem hc b))

theorem patch_invAdj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {Pt Bd : Set (Subring Ω)} {e : ℕ} {A : Subalgebra ℚ Ω}
    {z : Fin e → A} {n : ℕ} (hA : IsSncPatch Pt Bd e A z n) {g : Ω} (hg : g ∈ A) (h0 : g ≠ 0) :
    ∃ z' : Fin e → invAdj A g, IsSncPatch Pt Bd e (invAdj A g) z' n ∧ ∀ i, (z' i : Ω) = z i := by
  let z' : Fin e → invAdj A g := fun i => ⟨z i, le_invAdj A g (z i).2⟩
  have hd := _root_.GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.differentials_basis_invAdj Ω A g hg h0 e z z' (fun _ => rfl) hA.li hA.span
  refine ⟨z', ⟨?_, _root_.GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.smooth_invAdj Ω A g hg h0 hA.smooth, hA.le, hd.1, hd.2, ?_⟩, fun _ => rfl⟩
  · obtain ⟨S, hS⟩ := hA.fg
    classical
    refine ⟨insert g⁻¹ S, ?_⟩
    rw [Finset.coe_insert]
    apply le_antisymm
    · refine Algebra.adjoin_mono (Set.insert_subset_insert ?_)
      rw [← hS]
      exact Algebra.subset_adjoin
    · refine Algebra.adjoin_le (Set.insert_subset (Algebra.subset_adjoin (Set.mem_insert _ _)) ?_)
      rw [← hS]
      exact Algebra.adjoin_mono (Set.subset_insert _ _)
  · intro q hq
    obtain ⟨R, hR, hloc, hbd⟩ := hA.pts (primeUnder A g q) (Ideal.comap_isPrime _ _)
    refine ⟨R, hR, isLocAt_invAdj hg h0 hq hloc, hbd.trans ?_⟩
    exact exists_congr fun i => and_congr_right fun _ => Iff.rfl

theorem chartQ_fg {Ω : Type} [Field Ω] [Algebra ℚ Ω] {N : ℕ} (x : Fin (N + 1) → Ω) (c : Fin (N + 1)) :
    (chartQ x c).FG :=
  ⟨(Set.finite_range (fun j => x j / x c)).toFinset, by simp⟩

theorem not_mem_primeUnder {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : Subalgebra ℚ Ω} {g : Ω} (hg : g ∈ A) (h0 : g ≠ 0)
    {q : Ideal (invAdj A g)} (hq : q.IsPrime) : (⟨g, hg⟩ : A) ∉ primeUnder A g q :=
  not_mem_of_isPrime hg h0 hq

variable {Ω : Type} [Field Ω] [CharZero Ω] {X : Scheme.{0}} {ξ : Sp Ω ⟶ X}

theorem exists_patch {N : ℕ} {x : Fin (N + 1) → Ω} {e : ℕ} {B : Set (Cpt ξ)} (hT : CoordTie ℤ ξ x)
    (hP : ∀ p, Char0 ξ p → ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A),
      IsSncPatch (Pts ξ) (regAt ξ '' B) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ p))
    (c : Fin (N + 1)) (p : Cpt ξ) (hp : Char0 ξ p) (hc : InChart ξ x c p) :
    ∃ h ∈ chartQ x c, unitAt ξ p h ∧ ∃ (z : Fin e → invAdj (chartQ x c) h) (n : ℕ),
      IsSncPatch (Pts ξ) (regAt ξ '' B) e (invAdj (chartQ x c) h) z n := by
  obtain ⟨A, z, n, q, hA, hq, hl⟩ := hP p hp
  obtain ⟨I, hI, hu, hIl⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_prime_chartQ Ω X ξ _ x c hT p hp hc
  obtain ⟨g, h, hg, hh, he⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SncBase.CommonLoc.exists_common_loc Ω A (chartQ x c) q I (regAt ξ p) hA.fg (chartQ_fg x c) hq hI hl hIl
  have hg0 : (g : Ω) ≠ 0 := fun h0 => hg (by
    have : g = 0 := Subtype.ext h0
    rw [this]; exact q.zero_mem)
  obtain ⟨z', hz', -⟩ := patch_invAdj hA g.2 hg0
  refine ⟨h, h.2, (hu h).1 hh, ?_⟩
  rw [← he]
  exact ⟨z', n, hz'⟩

theorem primePoint {κ : Type} {x : κ → Ω} {c : κ} (hT : CoordTie ℤ ξ x) (hx : x c ≠ 0) {h : Ω}
    (hh : h ∈ chartQ x c) (h0 : h ≠ 0) (q : Ideal (invAdj (chartQ x c) h)) (hq : q.IsPrime) :
    ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ unitAt ξ p h ∧
      (∀ s : invAdj (chartQ x c) h, s ∉ q ↔ unitAt ξ p (s : Ω)) ∧
      IsLocAt (invAdj (chartQ x c) h) q (regAt ξ p) := by
  obtain ⟨p, hp, hc, hu, hl⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.chartPrime_point Ω X ξ κ x c hT hx (primeUnder _ h q) (Ideal.comap_isPrime _ _)
  have hhu : unitAt ξ p h := (hu ⟨h, hh⟩).1 (not_mem_primeUnder hh h0 hq)
  refine ⟨p, hp, hc, hhu, ?_, isLocAt_invAdj hh h0 hq hl⟩
  intro s
  obtain ⟨k, hk⟩ := exists_mul_pow_mem hh h0 s.2
  have hreg : (s : Ω) ∈ regAt ξ p := invAdj_le hp (fun _ => chartQ_le hp hc) hhu s.2
  rw [not_congr (mem_iff_mul_pow hh h0 hq s k ⟨_, hk⟩ rfl), hu]
  exact ⟨fun u => unitAt_of_mul_left u hreg (unitAt_pow hhu k).2.1, fun u => unitAt_mul u (unitAt_pow hhu k)⟩

theorem pointPrime {κ : Type} {x : κ → Ω} {c : κ} (hT : CoordTie ℤ ξ x) {h : Ω} (hh : h ∈ chartQ x c)
    (p : Cpt ξ) (hp : Char0 ξ p) (hc : InChart ξ x c p) (hu : unitAt ξ p h) :
    ∃ q : Ideal (invAdj (chartQ x c) h), q.IsPrime ∧
      (∀ s : invAdj (chartQ x c) h, s ∉ q ↔ unitAt ξ p (s : Ω)) ∧
      IsLocAt (invAdj (chartQ x c) h) q (regAt ξ p) := by
  haveI hloc : IsLocalRing (regAt ξ p) := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hT.gen p).1
  have hmem : ∀ s : invAdj (chartQ x c) h, (s : Ω) ∈ regAt ξ p :=
    fun s => invAdj_le hp (fun _ => chartQ_le hp hc) hu s.2
  let f : invAdj (chartQ x c) h →+* regAt ξ p :=
    ((invAdj (chartQ x c) h).val : invAdj (chartQ x c) h →+* Ω).codRestrict (regAt ξ p) hmem
  have hq : (Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p))).IsPrime := inferInstance
  have hs : ∀ s : invAdj (chartQ x c) h,
      s ∉ Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p)) ↔ unitAt ξ p (s : Ω) := by
    intro s
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    constructor
    · intro hu'
      obtain ⟨b, hb⟩ := hu'.exists_right_inv
      have e1 : (s : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
      have h0 : (s : Ω) ≠ 0 := fun h0 => by simp [h0] at e1
      refine ⟨h0, hmem s, ?_⟩
      rw [inv_eq_of_mul_eq_one_right e1]
      exact b.2
    · rintro ⟨h0, -, hinv⟩
      exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  obtain ⟨I, -, hI, hIl⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_prime_chartQ Ω X ξ κ x c hT p hp hc
  have e : primeUnder (chartQ x c) h (Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p))) = I := by
    ext a
    exact not_iff_not.1 ((hs ⟨a, le_invAdj _ h a.2⟩).trans (hI a).symm)
  exact ⟨_, hq, hs, isLocAt_invAdj hh hu.1 hq (e ▸ hIl)⟩

theorem patchClause {κ : Type} {x : κ → Ω} {e : ℕ} {B : Set (Cpt ξ)} (hT : CoordTie ℤ ξ x)
    {S : Subalgebra ℚ Ω} {z : Fin e → S} {n : ℕ} (hS : IsSncPatch (Pts ξ) (regAt ξ '' B) e S z n)
    (q : Ideal S) (hq : q.IsPrime) (p : Cpt ξ) (hl : IsLocAt S q (regAt ξ p)) :
    p ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q := by
  obtain ⟨R, -, hRl, hbd⟩ := hS.pts q hq
  have hR : R = regAt ξ p := Subring.ext fun a => (hRl a).trans (hl a).symm
  subst hR
  rw [← hbd]
  constructor
  · exact fun hp => ⟨p, hp, rfl⟩
  · rintro ⟨p', hp', e'⟩
    have := _root_.GlobalTheory.CompanionTheory.Ar.SncBase.eq_of_regAt_eq_of_coordTie X Ω ξ ℤ κ x hT p' p e'
    exact this ▸ hp'

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

namespace GlobalTheory.CompanionTheory.Ar.SncBase


open Mdl in
theorem exists_isSncModel_of_patches : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ) (B : Set (Cpt ξ)), CoordTie ℤ ξ x → (∀ p ∈ B, Char0 ξ p) → (∀ p, Char0 ξ p → ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A), IsSncPatch (Pts ξ) (regAt ξ '' B) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ p)) → ∃ bd : Ideal (MRing (fun _ : Unit => Fin (N + 1))), Cmp.IsSncModel (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) e bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) z w → (w ∈ mcPts bd ↔ ∃ h : genPt ξ ⤳ centre z, (⟨centre z, h⟩ : Cpt ξ) ∈ B) := by
  open Mdl in
  intro Ω _ _ X ξ N x e B hT hB hP
  have hcov := fun c p hp hc => exists_patch (B := B) hT hP c p hp hc
  have hsep : ∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → p ∉ B →
      ∃ G ∈ bdGens ξ x B, unitAt ξ p (ratEval x c G) := by
    intro c p hp hc hnB
    obtain ⟨h, hh, hu, z, n, hz⟩ := hcov c p hp hc
    have hcl : ∀ q : Cpt ξ, Char0 ξ q → InChart ξ x c q → unitAt ξ q h →
        (q ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ ¬ unitAt ξ q (z i : Ω)) := by
      intro q hq hcq huq
      obtain ⟨Q, hQ, hs, hl⟩ := pointPrime hT hh q hq hcq huq
      rw [patchClause hT hz Q hQ q hl]
      refine exists_congr fun i => and_congr_right fun _ => ?_
      rw [← hs (z i), not_not]
    obtain ⟨a, ha, hau, hnon⟩ := GlobalTheory.T.snc_patch_boundary_units Ω X ξ _ x c B h e n z p hT.gen hB hh hu.1 hcl hp hc hu hnB
    exact _root_.GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.Sep.exists_bdGens_unitAt Ω X ξ N x c B p a hB hp hc ha hau hnon
  refine ⟨Ideal.span (bdGens ξ x B), ?_, _root_.GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.mem_mcPts_span_bdGens_iff Ω X ξ N x B hT.gen hsep⟩
  refine _root_.GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.isSncModel_of_chart_patches Ω X ξ N x e B _ hcov ?_ ?_ ?_
  · intro c hx I hI
    obtain ⟨p, a, b, d, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.chartPrime_point Ω X ξ _ x c hT hx I hI
    exact ⟨p, a, b, d⟩
  · intro c h hx hh h0 q hq
    obtain ⟨p, hp, hc, -, hs, hl⟩ := primePoint hT hx hh h0 q hq
    exact ⟨p, hp, hc, hs, fun z n hz => patchClause hT hz q hq p hl⟩
  · intro c p hp hc
    constructor
    · intro hpB g hg
      exact not_unitAt_of_mem_span hT.gen hpB hc hg
    · intro hall
      by_contra hn
      obtain ⟨G, hG, hu⟩ := hsep c p hp hc hn
      exact hall G (Ideal.subset_span hG) hu

end GlobalTheory.CompanionTheory.Ar.SncBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStableEigenTangents
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk

section Linear

variable {ι O : Type} [Fintype ι] [CommRing O]
variable {R N : Type} [CommRing R] [AddCommGroup N] [Module R N]

theorem mem_eig (ρ : O →+* Module.End R N) (σ : O →+* R) (u : N) : u ∈ eigSp ρ σ ↔ ∀ a, ρ a u = σ a • u := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

def Splits (ρ : O →+* Module.End R N) (τ : ι → O →+* R) : Prop :=
  ∀ m : N, ∃! f : ι → N, (∀ s a, ρ a (f s) = τ s a • f s) ∧ ∑ s, f s = m

def sumMap (ρ : O →+* Module.End R N) (τ : ι → O →+* R) : (∀ s, eigSp ρ (τ s)) →ₗ[R] N :=
  ∑ s, (eigSp ρ (τ s)).subtype ∘ₗ LinearMap.proj s

theorem sumMap_apply (ρ : O →+* Module.End R N) (τ : ι → O →+* R) (g : ∀ s, eigSp ρ (τ s)) :
    sumMap ρ τ g = ∑ s, (g s : N) := by
  simp [sumMap, LinearMap.sum_apply]

theorem sumMap_bij {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) :
    Function.Bijective (sumMap ρ τ) := by
  constructor
  · intro g g' e
    have := (h (sumMap ρ τ g)).unique (y₁ := fun s => (g s : N)) (y₂ := fun s => (g' s : N))
      ⟨fun s a => (mem_eig ρ (τ s) _).1 (g s).2 a, (sumMap_apply ρ τ g).symm⟩
      ⟨fun s a => (mem_eig ρ (τ s) _).1 (g' s).2 a, by rw [e, sumMap_apply]⟩
    exact funext fun s => Subtype.ext (congrFun this s)
  · intro m
    obtain ⟨f, ⟨hf, hs⟩, -⟩ := h m
    exact ⟨fun s => ⟨f s, (mem_eig ρ (τ s) _).2 (hf s)⟩, by rw [sumMap_apply]; exact hs⟩

theorem exists_bases [DecidableEq ι] [IsLocalRing R] [Module.Finite R N] [Module.Projective R N]
    {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) :
    ∃ r : ι → ℕ, Nonempty (∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) := by
  let e := LinearEquiv.ofBijective (sumMap ρ τ) (sumMap_bij h)
  haveI hP : Module.Projective R (∀ s, eigSp ρ (τ s)) := Module.Projective.of_equiv e.symm
  have key : ∀ s, Module.Free R (eigSp ρ (τ s)) ∧ Module.Finite R (eigSp ρ (τ s)) := fun s => by
    haveI : Module.Finite R (∀ s, eigSp ρ (τ s)) := Module.Finite.equiv e.symm
    haveI : Module.Finite R (eigSp ρ (τ s)) :=
      Module.Finite.of_surjective (LinearMap.proj s : (∀ s, eigSp ρ (τ s)) →ₗ[R] eigSp ρ (τ s))
        (fun y => ⟨Pi.single s y, by simp⟩)
    haveI : Module.Projective R (eigSp ρ (τ s)) :=
      Module.Projective.of_split (LinearMap.single R (fun s => eigSp ρ (τ s)) s) (LinearMap.proj s)
        (LinearMap.ext fun y => by simp)
    haveI : Module.FinitePresentation R (eigSp ρ (τ s)) := Module.finitePresentation_of_projective _ _
    exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩
  refine ⟨fun s => Module.finrank R (eigSp ρ (τ s)), ⟨fun s => ?_⟩⟩
  haveI := (key s).1
  haveI := (key s).2
  exact Module.finBasis R _

def totBasis [DecidableEq ι] {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) {r : ι → ℕ}
    (b : ∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) : Module.Basis (Σ s, Fin (r s)) R N :=
  (Pi.basis b).map (LinearEquiv.ofBijective (sumMap ρ τ) (sumMap_bij h))

theorem totBasis_apply [DecidableEq ι] {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) {r : ι → ℕ}
    (b : ∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) (s : ι) (i : Fin (r s)) :
    totBasis h b ⟨s, i⟩ = b s i := by
  simp only [totBasis, Module.Basis.map_apply, LinearEquiv.ofBijective_apply, sumMap_apply, Pi.basis_apply]
  rw [Finset.sum_eq_single s]
  · simp
  · intro s' _ hs
    simp [Pi.single_eq_of_ne hs]
  · simp

variable {T N' : Type} [CommRing T] [AddCommGroup N'] [Module T N']

theorem image_frame [DecidableEq ι] {θ : R →+* T} {ρ : O →+* Module.End R N} {τ : ι → O →+* R}
    {ρ' : O →+* Module.End T N'} (h' : Splits ρ' fun s => θ.comp (τ s)) {r : ι → ℕ}
    (b : ∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) (β : N →ₛₗ[θ] N')
    (B : Module.Basis (Σ s, Fin (r s)) T N') (hB : ∀ s i, B ⟨s, i⟩ = β (b s i))
    (hρ : ∀ a e, ρ' a (β e) = β (ρ a e)) (s : ι) :
    LinearIndependent T (fun i => β (b s i)) ∧
      Submodule.span T (Set.range fun i => β (b s i)) = eigSp ρ' (θ.comp (τ s)) := by
  have hv : ∀ s i, ∀ a, ρ' a (β (b s i)) = (θ.comp (τ s)) a • β (b s i) := fun s i a => by
    rw [hρ, (mem_eig ρ (τ s) _).1 (b s i).2 a, β.map_smulₛₗ]
    rfl
  refine ⟨?_, le_antisymm (Submodule.span_le.2 ?_) fun w hw => ?_⟩
  · have := B.linearIndependent.comp (Sigma.mk s) sigma_mk_injective
    convert this using 1
    exact funext fun i => (hB s i).symm
  · rintro _ ⟨i, rfl⟩
    exact (mem_eig ρ' _ _).2 (hv s i)
  · let f : ι → N' := fun s' => ∑ i, B.repr w ⟨s', i⟩ • β (b s' i)
    have hf : ∀ s' a, ρ' a (f s') = (θ.comp (τ s')) a • f s' := fun s' a => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [f, map_sum, Finset.smul_sum, map_smul, hv s']
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
    have hsum : ∑ s', f s' = w := by
      have := B.sum_repr w
      rw [Fintype.sum_sigma] at this
      simpa only [f, hB] using this
    have hw' := (mem_eig ρ' _ _).1 hw
    have hu := (h' w).unique (y₁ := f) (y₂ := fun s' => if s' = s then w else 0) ⟨hf, hsum⟩
      ⟨fun s' a => by
        by_cases e : s' = s
        · subst e; simpa using hw' a
        · simp [e], by simp⟩
    have : w = f s := by simpa using (congrFun hu s).symm
    rw [this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Linear

end GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk

namespace GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk

open GlobalTheory.CompanionTheory.Ar.LieVB

theorem splits_of {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    {S : Type} [CommRing S] (κ : c.F →+* S) {N : Type} [AddCommGroup N] [Module S N]
    (ρ : 𝓞 E →+* Module.End S N) : Splits ρ (fun s : E →+* ℂ => κ.comp (tauIn c s)) := by
  letI : Algebra c.F S := κ.toAlgebra
  exact fun m => _root_.GlobalTheory.Frames.existsUnique_eigen_sum E H l c S N ρ m

theorem exists_stableEig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (A : Type) [CommRing A] [IsLocalRing A] (x : Sp A ⟶ X) (κ : c.F →+* A) (σ : E →+* ℂ), ∃ (r : ℕ) (e : Fin r → (epsAt x ⟶ t.G)), StableEig t x κ σ e := by
  classical
  intro E _ _ _ H l c X t A _ _ x κ σ
  haveI hsm : Smooth t.G.hom := t.semi.smooth
  obtain ⟨N, _, _, ⟨M⟩⟩ := lieModel_exists X t.G A x
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act X t.G A x N M (𝓞 E) t.act.act t.act.hom t.act.one t.act.mul
    t.act.add
  obtain ⟨hfin, hproj, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange X t.G A x N M
  have hsp := splits_of c κ ρ
  obtain ⟨r, ⟨b⟩⟩ := exists_bases hsp
  refine ⟨r σ, fun i => M.pt (b σ i), ?_⟩
  intro T _ θ x' hx' v hv
  subst hx'
  obtain ⟨N', _, _, ⟨M'⟩⟩ := lieModel_exists X t.G T (spMap θ ≫ x)
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act X t.G T (spMap θ ≫ x) N' M' (𝓞 E) t.act.act t.act.hom
    t.act.one t.act.mul t.act.add
  let q := Fintype.equivFin (Σ s, Fin (r s))
  obtain ⟨β, B, hB, hβ⟩ := basis_tr θ x (spMap θ ≫ x) rfl M M' ((totBasis hsp b).reindex q)
  have hB' : ∀ s i, (B.reindex q.symm) ⟨s, i⟩ = β (b s i) := fun s i => by
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, hB, Module.Basis.reindex_apply, Equiv.symm_apply_apply,
      totBasis_apply]
  have hact : ∀ a e, ρ' a (β e) = β (ρ a e) := fun a e => pt_left_inj M' (by
    rw [hβ, hρ a e, Over.comp_left, ← Category.assoc, ← hβ e, hρ' a (β e), Over.comp_left])
  have hsp' : Splits ρ' (fun s : E →+* ℂ => θ.comp (κ.comp (tauIn c s))) := splits_of c (θ.comp κ) ρ'
  obtain ⟨hli, hspan⟩ := image_frame hsp' b β (B.reindex q.symm) hB' hact σ
  have hvv : v = fun k => M'.pt (β (b σ k)) := funext fun k => Over.OverMorphism.ext (by
    rw [hv k, hβ])
  rw [hvv]
  exact (((_root_.GlobalTheory.CompanionTheory.Ar.Fl.Bridge.comb_eig_frame X T t.G (spMap θ ≫ x) N' M').2 (𝓞 E) t.act ρ' ((θ.comp κ).comp (tauIn c σ)) hρ').2 _ _).2
    ⟨hli, hspan⟩

end GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitOfNonvanishingPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_unit_of_nonvanishing_points : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (U : X.Opens) (a : Γ(X, U)), LocallyOfFiniteType s → (∀ x : Sp ℂ ⟶ X, x ≫ s = 𝟙 _ → centre x ∈ U → valAt' x U a ≠ 0) → IsUnit a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.GagaC.isUnit_of_forall_complexPoint | exact GlobalTheory.CompanionTheory.Ar.Flat.GagaC.isUnit_of_forall_complexPoint | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.GagaC.isUnit_of_forall_complexPoint <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelDescendsBaseChange
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem dualMap_comp_algebraMap (c : R →+* R') :
    (dualMap c).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp c := by
  refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap (c : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap c) =
      c.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [dualMap]

theorem dualMap_comp_epsMul (c : R →+* R') (r : R) :
    (dualMap c).comp (epsMul r) = (epsMul (c r)).comp (dualMap c) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, epsMul]
  · simp [dualMap, epsMul, mul_comm]

def epsBase (c : R →+* R') (x : Sp R ⟶ S) : epsAt (spMap c ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (dualMap c)) (by
    change spMap (dualMap c) ≫ Spec.map _ ≫ x = Spec.map _ ≫ spMap c ≫ x
    simp only [spMap]
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, dualMap_comp_algebraMap])

def ptBase (c : R →+* R') (x : Sp R ⟶ S) : Over.mk (spMap c ≫ x) ⟶ Over.mk x :=
  Over.homMk (spMap c) rfl

theorem isTanAt_base (G : Over S) [GrpObj G] (c : R →+* R') (x : Sp R ⟶ S) (v : epsAt x ⟶ G)
    (hv : IsTanAt G x v) : IsTanAt G (spMap c ≫ x) (epsBase c x ≫ v) := by
  have h1 : (ptBase c x ≫ (1 : Over.mk x ⟶ G)) = 1 := MonObj.comp_one _
  have h2 : spMap c ≫ (1 : Over.mk x ⟶ G).left = (1 : Over.mk (spMap c ≫ x) ⟶ G).left := by
    rw [← h1]; rfl
  unfold IsTanAt at hv ⊢
  rw [← h2, ← hv]
  change Spec.map _ ≫ spMap (dualMap c) ≫ v.left = spMap c ≫ Spec.map _ ≫ v.left
  simp only [spMap]
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, fst_comp_dualMap]

theorem exists_isBaseChange (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R R' : Type)
    [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (E' : Type) [AddCommGroup E'] [Module R' E']
    [Module R E'] [IsScalarTower R R' E'] (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module R E) (M : LieModel G x E) (j : E →ₗ[R] E'),
      IsBaseChange R' j ∧ ∀ e, (M'.pt (j e)).left = spMap (dualMap (algebraMap R R')) ≫ (M.pt e).left := by
  obtain ⟨E, iA, iM, ⟨M⟩⟩ := lieModel_exists S G R x
  have hex : ∀ e, ∃ e', M'.pt e' = epsBase (algebraMap R R') x ≫ M.pt e :=
    fun e => M'.onto _ (isTanAt_base G _ x _ (M.tan e))
  choose f hf using hex
  have hleft : ∀ e, (M'.pt (f e)).left = spMap (dualMap (algebraMap R R')) ≫ (M.pt e).left := fun e => by
    rw [hf e]; rfl
  let j : E →ₗ[R] E' :=
    { toFun := f
      map_add' := fun a b => M'.inj (by
        rw [M'.add, hf, hf, hf, M.add, MonObj.comp_mul])
      map_smul' := fun r a => M'.inj (Over.OverMorphism.ext (by
        rw [RingHom.id_apply, ← algebraMap_smul R' r (f a), M'.smul, hleft, hleft, M.smul]
        simp only [spMap]
        rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← CommRingCat.ofHom_comp, dualMap_comp_epsMul])) }
  refine ⟨E, iA, iM, M, j, _root_.GlobalTheory.CompanionTheory.Ar.lieModel_isBaseChange S G R R' x E E' M M' j fun e => ?_, hleft⟩
  simpa only [Category.comp_id, j, LinearMap.coe_mk, AddHom.coe_mk] using hleft e

end GlobalTheory.CompanionTheory.Ar.LieBaseChange
end
end

