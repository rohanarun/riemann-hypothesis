module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0812
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0883
public import GroundTheory.Brauer.TensorSimple
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0895
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicNormsAndIntegrality
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.IntAwayP

theorem norm_self_padicAlgCl (p : ℕ) [Fact p.Prime] : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  have := PadicAlgCl.norm_extends p (p : ℚ_[p])
  rw [map_natCast] at this
  rw [this, Padic.norm_p]

theorem norm_prime_padicAlgCl_of_ne (ℓ p : ℕ) [hℓ : Fact ℓ.Prime] (hp : p.Prime) (h : ℓ ≠ p) :
    ‖(p : PadicAlgCl ℓ)‖ = 1 := by
  have h1 := PadicAlgCl.norm_extends ℓ (p : ℚ_[ℓ])
  rw [map_natCast] at h1
  rw [h1]
  have h2 : ‖(p : ℤ_[ℓ])‖ = 1 := (PadicInt.norm_natCast_eq_one_iff).2 ((Nat.coprime_primes hℓ.out hp).2 h)
  rw [← h2, PadicInt.norm_def]
  simp

theorem isIntegral_of_pow_mul (K : Type) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]
    (z : K) (N : ℕ) (hN : IsIntegral ℤ ((p : K) ^ N * z))
    (h : ∀ φ : K →+* PadicAlgCl p, ‖φ z‖ ≤ 1) : IsIntegral ℤ z := by
  refine GlobalTheory.isIntegral_of_forall_padicAlgCl_norm_le_one K z fun q _ τ => ?_
  by_cases hq : q = p
  · subst hq; exact h τ
  · have h1 : ‖τ ((p : K) ^ N * z)‖ ≤ 1 :=
      GlobalTheory.norm_le_one_of_isIntegral_int (hN.map τ.toIntAlgHom)
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow,
      norm_prime_padicAlgCl_of_ne q p hp.out hq, one_pow, one_mul] at h1
    exact h1

theorem exists_pow_mul_isIntegral : ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (B : ℝ), ∃ m₀ : ℕ, ∀ (c : K) (D : ℕ), (∃ m : ℕ, IsIntegral ℤ ((p : K) ^ m * D * c)) → (∀ φ : K →+* PadicAlgCl p, ‖φ c‖ ≤ B) → IsIntegral ℤ ((p : K) ^ m₀ * D * c) := by
  intro K _ _ p _ B
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨m₀, hm₀⟩ := pow_unbounded_of_one_lt B hp1
  refine ⟨m₀, fun c D ⟨m, hm⟩ hB => ?_⟩
  apply isIntegral_of_pow_mul K p _ m
  · have e : (p : K) ^ m * ((p : K) ^ m₀ * D * c) = (p : K) ^ m₀ * ((p : K) ^ m * D * c) := by ring
    rw [e]
    have hpi : IsIntegral ℤ ((p : K) ^ m₀) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := (p : ℤ))).pow m₀
    exact hpi.mul hm
  · intro φ
    rw [map_mul, map_mul, map_pow, map_natCast, map_natCast, norm_mul, norm_mul, norm_pow,
      norm_self_padicAlgCl]
    have hD := IsUltrametricDist.norm_natCast_le_one (PadicAlgCl p) D
    have h2 : ‖(D : PadicAlgCl p)‖ * ‖φ c‖ ≤ (p : ℝ) ^ m₀ :=
      (mul_le_of_le_one_left (norm_nonneg _) hD).trans ((hB φ).trans hm₀.le)
    rw [mul_assoc, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
    exact h2

end GlobalTheory.IntAwayP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceOffLevelSetProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


open SplitOffPlaces _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory in
theorem offS_not_type_places : ∀ {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (Pg : Finset (HeightOneSpectrum (𝓞 D.host.E))) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : HeightOneSpectrum (𝓞 D.host.E)), (∀ PP, PP ∈ Pg ↔ ∃ k, Pb.Div k PP) → (∀ PP ∈ Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ S) → OffS D S P → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ∀ PP ∈ Pg, PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
  intro D Pb Pg S P hPg hS hP
  have key : ∀ PP ∈ Pg, PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
    intro PP h
    obtain ⟨x, hx, hxP⟩ := hP _ (hS PP h)
    have hx' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ PP.asIdeal := hx
    refine ⟨fun e => hxP _ rfl (e ▸ hx'), fun hc => ?_⟩
    obtain ⟨c', h1, h2⟩ := hc _ hx'
    refine hxP c' ?_ h1
    rw [h2]
    exact (D.sp.cm.fixed _).2 ⟨(x : D.host.F), rfl⟩
  have hne : ∀ PP ∈ Pg, PP ≠ P := fun PP h => (key PP h).1
  have hne' : ∀ PP ∈ Pg, PP ≠ conjSpec P := by
    intro PP h e
    apply (key PP h).2
    intro c hc
    rw [e] at hc
    exact ⟨cO D.host.E c, hc, rfl⟩
  have hg : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro k hk
    have h1 : Pb.pb k ≠ P.under (𝓞 D.host.K) := fun e => hne P ((hPg P).2 ⟨k, e.symm⟩) rfl
    have h2 : Pb.pb k ≠ (conjSpec P).under (𝓞 D.host.K) := fun e =>
      hne' (conjSpec P) ((hPg _).2 ⟨k, e.symm⟩) rfl
    obtain ⟨x, hx, hx1, hx2⟩ := exists_mem_not_mem h1 h2
    obtain ⟨x', n, hx', hn⟩ := exists_norm D x
    have hnP : (n : 𝓞 D.host.E) ∉ P.asIdeal := by
      intro h
      have e : (n : 𝓞 D.host.E) = algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x * cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x) := by
        rw [← hx', ← map_mul, hn, map_intCast]
      rw [e] at h
      rcases P.isPrime.mem_or_mem h with h | h
      · exact hx1 h
      · exact hx2 h
    have hnb : (n : 𝓞 D.host.K) ∈ (Pb.pb k).asIdeal := hn ▸ Ideal.mul_mem_right _ _ hx
    have hp : Prime (D.host.g k : ℤ) := Nat.prime_iff_prime_int.1 (D.host.g_prime k)
    by_cases hd : (D.host.g k : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := hd
      apply hnP
      push_cast
      exact Ideal.mul_mem_right _ _ hk
    · obtain ⟨a, b, hab⟩ := (hp.irreducible.coprime_iff_not_dvd).2 hd
      apply (Pb.pb k).isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : (1 : 𝓞 D.host.K) = a * ((D.host.g k : ℕ) : 𝓞 D.host.K) + b * n := by
        exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.K) hab.symm
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ (Pb.pb_over k)) (Ideal.mul_mem_left _ _ hnb)
  refine ⟨?_, key⟩
  intro h
  rw [Nat.cast_mul] at h
  rcases P.isPrime.mem_or_mem h with h | h
  · exact hg 0 h
  · exact hg 1 h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveEigenvectorOfSimilitudeUnique
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem exists_smul_eq_of_eigvec_of_charpoly_separable {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g.charpoly.Separable) {μ : ℂ} {x y : Fin n → ℂ} (hx0 : x ≠ 0)
    (hx : g *ᵥ x = μ • x) (hy : g *ᵥ y = μ • y) : ∃ c : ℂ, y = c • x := by
  set f := Matrix.toLin' g
  have hc : f.charpoly = g.charpoly := Matrix.charpoly_toLin' g
  have h1 : Module.finrank ℂ (Module.End.maxGenEigenspace f μ) ≤ 1 := by
    rw [LinearMap.finrank_maxGenEigenspace_eq, hc]
    exact Polynomial.rootMultiplicity_le_one_of_separable hg μ
  have mem : ∀ v : Fin n → ℂ, g *ᵥ v = μ • v → v ∈ Module.End.maxGenEigenspace f μ := fun v hv => by
    rw [Module.End.mem_maxGenEigenspace]
    exact ⟨1, by simp [f, hv]⟩
  have h2 : Module.finrank ℂ (Module.End.maxGenEigenspace f μ) = 1 := le_antisymm h1
    (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x, mem x hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨x, mem x hx⟩ : Module.End.maxGenEigenspace f μ)
    fun h => hx0 (congrArg Subtype.val h)).1 h2 ⟨y, mem y hy⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem form_conjTranspose_mul_mul {n : ℕ} (A g : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    star u ⬝ᵥ (gᴴ * A * g) *ᵥ v = star (g *ᵥ u) ⬝ᵥ A *ᵥ (g *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem eigvec_pos_unique_of_similitude : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian),
    A.det ≠ 0 → sigPosH hA = 1 → ∀ (g : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 < s →
    gᴴ * A * g = (s : ℂ) • A → g.charpoly.Separable → ∀ x y : Fin n → ℂ,
    0 < (star x ⬝ᵥ A *ᵥ x).re → 0 < (star y ⬝ᵥ A *ᵥ y).re →
    (∃ μ : ℂ, g *ᵥ x = μ • x) → (∃ ν : ℂ, g *ᵥ y = ν • y) → ∃ c : ℂ, y = c • x := by
  intro n A hA hdet hsig g s hs hsim hsep x y hxp hyp ⟨μ, hμ⟩ ⟨ν, hν⟩
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxp
  have hy0 : y ≠ 0 := by rintro rfl; simp at hyp
  have Q : ∀ u v : Fin n → ℂ, star (g *ᵥ u) ⬝ᵥ A *ᵥ (g *ᵥ v) = (s : ℂ) * (star u ⬝ᵥ A *ᵥ v) := by
    intro u v
    rw [← form_conjTranspose_mul_mul, hsim]
    have e : ((s : ℂ) • A) *ᵥ v = (s : ℂ) • (A *ᵥ v) := by
      exact Matrix.smul_mulVec (s : ℂ) A v
    rw [e, dotProduct_smul, smul_eq_mul]
  have scal : ∀ (a b : ℂ) (u v : Fin n → ℂ), star (a • u) ⬝ᵥ A *ᵥ (b • v) = star a * b * (star u ⬝ᵥ A *ᵥ v) := by
    intro a b u v
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]; ring
  have hQx : star x ⬝ᵥ A *ᵥ x ≠ 0 := fun h => by rw [h] at hxp; simp at hxp
  have hQy : star y ⬝ᵥ A *ᵥ y ≠ 0 := fun h => by rw [h] at hyp; simp at hyp
  have eμ : star μ * μ = (s : ℂ) := by
    have := Q x x; rw [hμ, scal] at this; exact mul_right_cancel₀ hQx this
  have eν : star ν * ν = (s : ℂ) := by
    have := Q y y; rw [hν, scal] at this; exact mul_right_cancel₀ hQy this
  have exy : (star μ * ν - s) * (star x ⬝ᵥ A *ᵥ y) = 0 := by
    have := Q x y; rw [hμ, hν, scal] at this; rw [sub_mul, this, sub_self]
  by_cases hμν : μ = ν
  · subst hμν
    exact exists_smul_eq_of_eigvec_of_charpoly_separable hsep hx0 hμ hν
  · exfalso
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hμ0 : star μ ≠ 0 := fun h => hs0 (by rw [← eμ, h, zero_mul])
    have hne : star μ * ν - s ≠ 0 := by
      intro h
      apply hμν
      have : star μ * ν = star μ * μ := by rw [eμ]; exact sub_eq_zero.1 h
      exact (mul_left_cancel₀ hμ0 this).symm
    have horth : star x ⬝ᵥ A *ᵥ y = 0 := (mul_eq_zero.1 exy).resolve_left hne
    have := GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one A hA hdet hsig x y hxp horth hy0
    linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSumsVanishOfTrivialFlags
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.CoordArch

variable {p : ℕ} [Fact p.Prime]

open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
private theorem mem_span_infinitePlace_embedding (K : Type) [Field K] [NumberField K]
    [_root_.NumberField.IsTotallyComplex K] (w : InfinitePlace K → ℂ) :
    w ∈ Submodule.span ℝ (Set.range fun (f : K) (u : InfinitePlace K) => u.embedding f) := by
  have hc : ∀ u : InfinitePlace K, u.IsComplex := fun u => IsTotallyComplex.isComplex u
  let P : mixedEmbedding.mixedSpace K →ₗ[ℝ] (InfinitePlace K → ℂ) :=
    { toFun := fun x u => x.2 ⟨u, hc u⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hP : ∀ f : K, P (mixedEmbedding K f) = fun u => u.embedding f := by
    intro f; funext u
    exact mixedEmbedding.mixedEmbedding_apply_isComplex K f ⟨u, hc u⟩
  have hmem : ((0, fun u => w u.1) : mixedEmbedding.mixedSpace K) ∈
      Submodule.span ℝ (Set.range (mixedEmbedding.latticeBasis K)) := by
    rw [(mixedEmbedding.latticeBasis K).span_eq]; trivial
  have hmap := Submodule.mem_map_of_mem (f := P) hmem
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact ⟨_, (by rw [mixedEmbedding.latticeBasis_apply, hP])⟩

open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
private theorem mem_span_range_psi {p : ℕ} [Fact p.Prime] (G : _root_.GlobalTheory.LKTrip.HTGroup p)
    (v : InfinitePlace G.F) (M : Matrix (Fin G.n) (Fin G.n) ℂ) :
    M ∈ Submodule.span ℂ (Set.range (G.psi v)) := by
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hsc : ∀ f : G.F, algebraMap G.F (Matrix (Fin G.n) (Fin G.n) ℂ) f =
      Matrix.scalar (Fin G.n) (v.embedding f) := by
    intro f; ext i j
    simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      RingHom.algebraMap_toAlgebra]
  let ψ : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ :=
    { G.psi v with
      commutes' := fun f => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe]
        rw [G.psi_F, hsc] }
  let φ : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψ (fun z c => Algebra.commutes z _)
  have hφ : ∀ (z : ℂ) (c : G.C), φ (z ⊗ₜ c) = z • G.psi v c := by
    intro z c
    change (Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψ _) (z ⊗ₜ[G.F] c) = _
    erw [Algebra.TensorProduct.lift_tmul]
    rw [Algebra.ofId_apply, Algebra.smul_def]; rfl
  have hn : 0 < G.n := G.n_pos
  have hinj : Function.Injective φ := by
    let χ : G.C ⊗[G.F] ℂ →+* Matrix (Fin G.n) (Fin G.n) ℂ :=
      φ.toRingHom.comp (Algebra.TensorProduct.comm G.F G.C ℂ).toRingEquiv.toRingHom
    have hker : TwoSidedIdeal.ker χ = ⊥ := by
      by_contra h
      obtain ⟨b, hb, hmem⟩ := _root_.GroundTheory.Brauer.exists_one_tmul_mem_of_ne_bot (TwoSidedIdeal.ker χ) h
      rw [TwoSidedIdeal.mem_ker] at hmem
      have h1 : χ (1 ⊗ₜ b) = b • (1 : Matrix (Fin G.n) (Fin G.n) ℂ) := by
        change φ ((Algebra.TensorProduct.comm G.F G.C ℂ) (1 ⊗ₜ b)) = _
        rw [Algebra.TensorProduct.comm_tmul, hφ, map_one]
      rw [hmem] at h1
      have h2 := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
      simp at h2
      exact hb h2.symm
    have hχ : Function.Injective χ := (TwoSidedIdeal.ker_eq_bot χ).1 hker
    intro x y hxy
    apply (Algebra.TensorProduct.comm G.F G.C ℂ).symm.injective
    apply hχ
    simpa [χ] using hxy
  have hrank : Module.finrank ℂ (ℂ ⊗[G.F] G.C) =
      Module.finrank ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) := by
    rw [Module.finrank_baseChange, G.rankC, Module.finrank_matrix,
      Module.finrank_self]
    simp [sq]
  have hsurj : Function.Surjective φ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj
  obtain ⟨t, rfl⟩ := hsurj M
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul z c =>
    change φ (z ⊗ₜ c) ∈ _
    rw [hφ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hx hy


open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
theorem _root_.GlobalTheory.CoordArch.coord_bound : ∀ (p : ℕ) [Fact p.Prime] (G : _root_.GlobalTheory.LKTrip.HTGroup p), ∃ R : ℝ, ∀ (c : G.C) (i : Fin (Module.finrank ℚ G.C)),
    |((Module.finBasis ℚ G.C).repr c i : ℝ)| ≤ R * ∑ w : InfinitePlace G.F, ∑ a : Fin G.n, ∑ b : Fin G.n, ‖G.psi w c a b‖ := by
  intro p _ G
  classical
  let B := Module.finBasis ℚ G.C
  let Φ : G.C → (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) := fun c u => G.psi u c
  let L : (Fin (Module.finrank ℚ G.C) → ℝ) →ₗ[ℝ] (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) :=
    Fintype.linearCombination ℝ (fun i => Φ (B i))
  have hL : ∀ c : G.C, L (fun i => (B.repr c i : ℝ)) = Φ c := by
    intro c
    funext u a b
    have h := congrArg (fun x => G.psi u x a b) (B.sum_repr c)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Matrix.sum_apply, map_rat_smul] at h
    simp only [L, Φ, Fintype.linearCombination_apply, Finset.sum_apply, Matrix.sum_apply]
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Rat.smul_def]
  have hF : ∀ (w : InfinitePlace G.F → ℂ) (c : G.C),
      (fun u => w u • G.psi u c) ∈ Submodule.span ℝ (Set.range Φ) := by
    intro w c
    have hw := mem_span_infinitePlace_embedding G.F w
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, rfl⟩ := hx
      refine Submodule.subset_span ⟨algebraMap G.F G.C f * c, ?_⟩
      funext u
      simp only [Φ, map_mul, G.psi_F]
      rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    | zero =>
      convert Submodule.zero_mem (Submodule.span ℝ (Set.range Φ)) using 1
      funext u
      simp
    | add x y _ _ hx hy =>
      convert Submodule.add_mem _ hx hy using 1
      funext u
      simp [add_smul]
    | smul r x _ hx =>
      convert Submodule.smul_mem _ r hx using 1
      funext u
      simpa only [Pi.smul_apply] using (smul_assoc r (x u) (G.psi u c))
  have hspan : ∀ y : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ,
      y ∈ Submodule.span ℝ (Set.range Φ) := by
    intro y
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ fun u _ => ?_
    suffices h : ∀ M ∈ Submodule.span ℂ (Set.range (G.psi u)), ∀ z : ℂ,
        Pi.single u (z • M) ∈ Submodule.span ℝ (Set.range Φ) by
      simpa using h _ (mem_span_range_psi G u (y u)) 1
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      intro z
      convert hF (Pi.single u z) c using 1
      funext u'
      by_cases h : u' = u
      · subst h; simp
      · simp [h]
    | zero =>
      intro z
      rw [smul_zero, Pi.single_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      intro z
      rw [smul_add, Pi.single_add]
      exact Submodule.add_mem _ (hx z) (hy z)
    | smul z' x _ hx =>
      intro z
      rw [smul_smul]
      exact hx _
  have hrange : LinearMap.range L = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    refine Submodule.span_le.mpr ?_ (hspan y)
    rintro _ ⟨c, rfl⟩
    exact ⟨_, hL c⟩
  have hdim : Module.finrank ℝ (Fin (Module.finrank ℚ G.C) → ℝ) =
      Module.finrank ℝ (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank G.F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces G.F
    have h3 := IsTotallyComplex.nrRealPlaces_eq_zero G.F
    have h4 := Module.finrank_mul_finrank ℚ G.F G.C
    have h5 := G.rankC
    rw [Module.finrank_fin_fun, Module.finrank_pi_fintype]
    simp only [Module.finrank_matrix, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [← h4, h5, ← h1, h2, h3]
    ring
  have hinj : Function.Injective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2
      (LinearMap.range_eq_top.1 hrange)
  let E : (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) ≃ₗ[ℝ]
      (InfinitePlace G.F → Fin G.n → Fin G.n → ℂ) :=
    LinearEquiv.piCongrRight fun _ => (Matrix.ofLinearEquiv ℝ).symm
  obtain ⟨K, -, hK⟩ :=
    (LinearMap.injective_iff_antilipschitz (E.toLinearMap ∘ₗ L)).1 (E.injective.comp hinj)
  refine ⟨K, fun c i => ?_⟩
  have hx := hK.le_mul_dist (fun j => (B.repr c j : ℝ)) 0
  rw [dist_zero_right, map_zero, dist_zero_right] at hx
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hL] at hx
  rw [← Real.norm_eq_abs]
  refine (norm_le_pi_norm (fun j => (B.repr c j : ℝ)) i).trans (hx.trans ?_)
  gcongr
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun u => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun b => ?_
  exact (Finset.single_le_sum (f := fun b => ‖G.psi u c a b‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ b)).trans ((Finset.single_le_sum (f := fun a => ∑ b, ‖G.psi u c a b‖)
    (fun _ _ => by positivity) (Finset.mem_univ a)).trans
    (Finset.single_le_sum (f := fun u => ∑ a, ∑ b, ‖G.psi u c a b‖)
    (fun _ _ => by positivity) (Finset.mem_univ u)))

end GlobalTheory.CoordArch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullUnitEqZero
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem AddCls.pull_unit_eq_zero {S : Scheme.{0}} {A T Z : Over S} [GrpObj A] {c : Pic (A ⊗ T).left}
    (h : AddCls A c) (t : Z ⟶ T) : CechPic.pull (lift (1 : Z ⟶ A) t).left c = 0 := by
  have h1 := h Z 1 1 t
  rw [_root_.mul_one] at h1
  exact left_eq_add.1 h1

theorem addF_separated : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → (∀ (T : Over S) (y y' : (addF A).obj (op T)), (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧ (addF A).map z.op y = (addF A).map z.op y') → y = y') := by
  intro S A _ hA T y y' h
  refine Subtype.ext (sub_eq_zero.1 (_root_.GlobalTheory.PicGlue.eq_zero_of_rigid_of_locally_zero S A T hA (y.1 - y'.1) ?_ fun p ↦ ?_))
  · rw [map_sub, y.2.pull_unit_eq_zero, y'.2.pull_unit_eq_zero, sub_zero]
  · obtain ⟨Z, z, hz, hp, e⟩ := h p
    refine ⟨Z, z, hz, hp, ?_⟩
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val e

end GlobalTheory.PicGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedSpecialFibreGlobalField
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.RedFibreField

noncomputable section



open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite in
open Scheme.IdealSheafData in
theorem _root_.GlobalTheory.RedFibreField.isReduced_nilradical_subscheme (X : Scheme.{0}) : IsReduced X.nilradical.subscheme := by
  have h : X.nilradical = vanishingIdeal (⊥ : X.IdealSheafData).support := by
    rw [Scheme.nilradical, vanishingIdeal_support]
  rw [h]
  exact _root_.GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal _

end

end GlobalTheory.RedFibreField

namespace GlobalTheory.RedFibreField

end GlobalTheory.RedFibreField
end

