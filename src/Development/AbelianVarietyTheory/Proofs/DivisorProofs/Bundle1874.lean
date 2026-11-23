module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinalRowWeightGramAlgebraic
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevelUnip

theorem pow_apply_eq_zero {R : Type} [CommRing R] {n : ℕ} (N : Matrix (Fin n) (Fin n) R)
    (hN : ∀ i j : Fin n, (j : ℕ) ≤ i → N i j = 0) :
    ∀ k : ℕ, ∀ i j : Fin n, (j : ℕ) < i + k → (N ^ k) i j = 0 := by
  intro k
  induction k with
  | zero =>
    intro i j hij
    rw [pow_zero, Matrix.one_apply_ne]
    intro h; subst h; omega
  | succ k ih =>
    intro i j hij
    rw [pow_succ', Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : (l : ℕ) ≤ i
    · rw [hN i l hl, zero_mul]
    · rw [ih l j (by omega), mul_zero]

theorem sub_one_pow_eq_zero' {κ : Type} [CommRing κ] {n : ℕ} (X : Matrix (Fin n) (Fin n) κ)
    (h0 : ∀ i j : Fin n, (j : ℕ) < i → X i j = 0) (h1 : ∀ i, X i i = 1) : (X - 1) ^ n = 0 := by
  have hN : ∀ i j : Fin n, (j : ℕ) ≤ i → (X - 1) i j = 0 := by
    intro i j hij
    rcases Nat.lt_or_eq_of_le hij with h | h
    · have h' : j ≠ i := fun e => by subst e; omega
      rw [Matrix.sub_apply, Matrix.one_apply_ne h'.symm, h0 i j h, sub_zero]
    · have e : j = i := Fin.ext h
      subst e
      rw [Matrix.sub_apply, Matrix.one_apply_eq, h1 j, sub_self]
  ext i j
  rw [pow_apply_eq_zero _ hN n i j (by omega), Matrix.zero_apply]

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem exists_matrix_pow (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)}) {y : GL (Fin n) (Formalism.L2.Herm.intAf F E)} {r : ℕ}
    (h : ∀ P ∈ T, (((Formalism.UG.bc (resS F P) y : GL (Fin n) (kP P)) : Matrix (Fin n) (Fin n) (kP P)) - 1) ^ r = 0)
    {b : 𝓞 E} (hb : b ∈ J) :
    ∃ s : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E), oToS F E b • ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r = M • s := by
  have key : ∀ i j, ∃ c, oToS F E b * ((((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r) i j) = M • c := by
    intro i j
    have h0 : ∀ P ∈ T, resS F P ((((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r) i j) = resS F P 0 := by
      intro P hP
      have e : (resS F P).mapMatrix (((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r) =
          (((Formalism.UG.bc (resS F P) y : GL (Fin n) (kP P)) : Matrix (Fin n) (Fin n) (kP P)) - 1) ^ r := by
        rw [map_pow, map_sub, map_one]; rfl
      have := congrFun (congrFun (e.trans (h P hP)) i) j
      rw [map_zero]
      exact this
    have h1 : (((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r) i j ∈ (∏ P ∈ T, P.asIdeal).map (oToS F E) := by
      have := GlobalTheory.LevelUnique.mem_map_prod (oToS F E) T fun P hP => GlobalTheory.LevelUnique.sub_mem_idS (h0 P hP)
      simpa using this
    have h2 := Ideal.mul_mem_mul h1 (Ideal.mem_map_of_mem (oToS F E) hb)
    rw [← Ideal.map_mul, hJ, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton'] at h2
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, by rw [mul_comm, ← hc, nsmul_eq_mul, mul_comm]⟩
  choose c hc using key
  exact ⟨Matrix.of c, Matrix.ext fun i j => by rw [Matrix.smul_apply, smul_eq_mul, hc i j]; rfl⟩

end Res

theorem keeps_hat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ)
    (s : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) {K : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hK : ∀ i j, (β.1 * s.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1) i j = Algebra.TensorProduct.comm F _ E (K i j)) :
    ∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), K *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) := by
  have hN := fun z hz => (hfr _).2 (GlobalTheory.LevelUnique.conj_mulVec_mem _ β s z ((hfr z).1 hz))
  generalize β.1 * s.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 = N at hN hK
  intro z hz
  have h4 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ (hN _ (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz))
  convert h4 using 1
  ext i
  simp [Matrix.mulVec, dotProduct, hK, map_sum, map_mul]

theorem exists_pow_hat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ)
    (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ} (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)})
    {x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hx : x ∈ St β) {r : ℕ}
    (h : ∀ P ∈ T, (((redFn β P x : GL (Fin n) (kP P)) : Matrix (Fin n) (Fin n) (kP P)) - 1) ^ r = 0) {b : 𝓞 E} (hb : b ∈ J)
    {K : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hK : ∀ i j, x.1 i j = Algebra.TensorProduct.comm F _ E (K i j)) :
    ∃ N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E),
      (∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), N *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) ∧
        ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) • (K - 1) ^ r = M • N := by
  obtain ⟨y, rfl⟩ := hx
  simp only [redFn_frGL] at h
  obtain ⟨s, hs⟩ := exists_matrix_pow T hJ h hb
  have e0 : ((frGL β y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      β.1 * (Formalism.L2.Herm.intAf F E).subtype.mapMatrix (y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) * (β⁻¹).1 := rfl
  have e2 : (((frGL β y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) ^ r =
      β.1 * (Formalism.L2.Herm.intAf F E).subtype.mapMatrix (((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r) * (β⁻¹).1 := by
    have e1 : ((frGL β y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1 =
        β.1 * (Formalism.L2.Herm.intAf F E).subtype.mapMatrix ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) * (β⁻¹).1 := by
      rw [e0, map_sub, map_one, mul_sub, sub_mul, mul_one, Units.mul_inv]
    rw [e1, Units.conj_pow, map_pow]
  have e4 : ((oToS F E b : Formalism.L2.Herm.intAf F E) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) •
      (Formalism.L2.Herm.intAf F E).subtype.mapMatrix (((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r) =
      M • (Formalism.L2.Herm.intAf F E).subtype.mapMatrix s := by
    ext i j
    have := congrArg (fun m : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) => (Formalism.L2.Herm.intAf F E).subtype (m i j)) hs
    simp only [Matrix.smul_apply, map_nsmul, smul_eq_mul, map_mul] at this
    simpa [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul] using this
  have e3 : ((oToS F E b : Formalism.L2.Herm.intAf F E) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) •
      ((((frGL β y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) ^ r) =
      M • (β.1 * (Formalism.L2.Herm.intAf F E).subtype.mapMatrix s * (β⁻¹).1) := by
    rw [e2, ← smul_mul_assoc, ← mul_smul_comm, e4, mul_smul_comm, smul_mul_assoc]
  refine ⟨(β.1 * (Formalism.L2.Herm.intAf F E).subtype.mapMatrix s * (β⁻¹).1).map (Algebra.TensorProduct.comm F _ E).symm,
    keeps_hat hfr s (fun i j => by rw [Matrix.map_apply, AlgEquiv.apply_symm_apply]; rfl), Matrix.ext fun i j => ?_⟩
  apply (Algebra.TensorProduct.comm F _ E).injective
  have hm : ((frGL β y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      (Algebra.TensorProduct.comm F _ E).toRingHom.mapMatrix K := Matrix.ext fun i j => hK i j
  have hpow : ((((frGL β y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) ^ r) i j =
      Algebra.TensorProduct.comm F _ E (((K - 1) ^ r) i j) := by
    rw [hm, ← map_one (Algebra.TensorProduct.comm F _ E).toRingHom.mapMatrix, ← map_sub, ← map_pow]
    rfl
  rw [Matrix.smul_apply, Matrix.smul_apply, map_nsmul, Matrix.map_apply, AlgEquiv.apply_symm_apply, smul_eq_mul, map_mul,
    ← hpow]
  exact congrFun (congrFun e3 i) j

variable {D : D7}

theorem sub_one_mulVec_mem {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) {k : GA D V} (hk : Lev.finE V k ∈ St β) :
    ∀ z ∈ latGHat V 1, ((finHom V k : Matrix (Fin V.rank) (Fin V.rank) _) - 1) *ᵥ z ∈ latGHat V 1 := by
  have hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨y, hy⟩ := hk
  have hN : ∀ z ∈ latHat V, (finHom V k : Matrix (Fin V.rank) (Fin V.rank) _) *ᵥ z ∈ latHat V := by
    rw [hl]
    exact keeps_hat hfr (y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))
      (fun i j => by
        have := congrArg (fun x : GL (Fin V.rank) (Lev.EAf D) => (x : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j) hy
        exact this)
  intro z hz
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact sub_mem (GlobalTheory.LevelUnique.mulVec_mem_latGHat _ hN z hz) hz

theorem exists_pow_cong {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (T : Finset (Pl D.host.E)) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 D.host.E)}) {k : GA D V} (hk : Lev.finE V k ∈ St β) {r : ℕ}
    (h : ∀ P ∈ T, (((redFn β P (Lev.finE V k) : GL (Fin V.rank) (kP P)) : Matrix (Fin V.rank) (Fin V.rank) (kP P)) - 1) ^ r = 0)
    {b : 𝓞 D.host.E} (hb : b ∈ J) :
    ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) •
        ((((finHom V k : Matrix (Fin V.rank) (Fin V.rank) _) - 1) ^ r) *ᵥ z -
          (0 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ z) = M • w := by
  have hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨N, hN, e⟩ := exists_pow_hat hfr T hJ hk h hb (K := (finHom V k : Matrix (Fin V.rank) (Fin V.rank) _))
    (fun _ _ => rfl)
  rw [← hl] at hN
  intro z hz
  refine ⟨_, GlobalTheory.LevelUnique.mulVec_mem_latGHat _ hN z hz, ?_⟩
  rw [Matrix.zero_mulVec, sub_zero, ← Matrix.smul_mulVec, e, Matrix.smul_mulVec]

theorem step {R : Type} [CommRing R] {n : ℕ} (K P : Matrix (Fin n) (Fin n) R) (y₀ y₁ v w₁ w₂ : Fin n → R) (M : ℕ)
    (e₁ : y₁ - K *ᵥ y₀ = M • w₁) (e₂ : y₀ - P *ᵥ v = M • w₂) :
    (y₁ - y₀) - ((K - 1) * P) *ᵥ v = M • (w₁ + (K - 1) *ᵥ w₂) := by
  have e₂' := eq_sub_of_add_eq' (sub_eq_iff_eq_add.mp e₂).symm
  have e₁' := sub_eq_iff_eq_add.mp e₁
  rw [← Matrix.mulVec_mulVec, e₂', e₁', Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul, smul_add]
  abel

theorem approx_pow {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    {K : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)}
    (hK : ∀ z ∈ latGHat V 1, (K - 1) *ᵥ z ∈ latGHat V 1) {f : La →ₗ[𝓞 D.host.E] La}
    (hf : ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (f a)) - K *ᵥ finVec V (ι a) = M • w) :
    ∀ n : ℕ, ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (((f - 1) ^ n) a)) - ((K - 1) ^ n) *ᵥ finVec V (ι a) = M • w := by
  have hm : ∀ a, finVec V (ι a) ∈ latGHat V 1 := fun a =>
    (GlobalTheory.Member.LatMove.mem_lat_iff V 1 _).1 (hι.2 ▸ LinearMap.mem_range_self ι a)
  have hJ : ∀ (g : La →ₗ[𝓞 D.host.E] La) a, a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La) →
      g a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La) := by
    intro g a ha
    have : g a ∈ (J • (⊤ : Submodule (𝓞 D.host.E) La)).map g := Submodule.mem_map_of_mem ha
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  intro n
  induction n with
  | zero =>
    intro a _
    exact ⟨0, zero_mem _, by rw [pow_zero, pow_zero, Matrix.one_mulVec, Module.End.one_apply, sub_self, smul_zero]⟩
  | succ n ih =>
    intro a ha
    obtain ⟨w₂, hw₂, e₂⟩ := ih a ha
    obtain ⟨w₁, hw₁, e₁⟩ := hf _ (hJ ((f - 1) ^ n) a ha)
    refine ⟨w₁ + (K - 1) *ᵥ w₂, add_mem hw₁ (hK _ hw₂), ?_⟩
    have ex : ((f - 1) ^ (n + 1)) a = f (((f - 1) ^ n) a) - ((f - 1) ^ n) a := by
      rw [pow_succ', Module.End.mul_apply]; rfl
    have hsub : ∀ u v : Fin V.rank → D.host.E, finVec V (u - v) = finVec V u - finVec V v := fun u v => by
      funext i; simp [finVec, TensorProduct.tmul_sub]
    rw [ex, pow_succ', map_sub ι, hsub]
    exact step _ _ _ _ _ _ _ _ e₁ e₂

end GlobalTheory.LevelUnip

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFrameChangeTriangular
section
noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem exists_ringEquiv {A : Type} [CommRing A] {Z : Scheme.{0}} (κ : Sp A ⟶ Z) [IsOpenImmersion κ] :
    ∃ θ : A ≃+* Γ(Z, κ.opensRange), spMap θ.toRingHom ≫ κ = (isAffineOpen_opensRange κ).fromSpec := by
  let e := IsOpenImmersion.isoOfRangeEq (isAffineOpen_opensRange κ).fromSpec κ
    (isAffineOpen_opensRange κ).range_fromSpec
  let e' : CommRingCat.of A ≅ Γ(Z, κ.opensRange) := (Scheme.Spec.preimageIso (X := .op _) (Y := .op _) e).unop
  refine ⟨e'.commRingCatIsoToRingEquiv, ?_⟩
  have : spMap e'.commRingCatIsoToRingEquiv.toRingHom = e.hom := Scheme.Spec.map_preimage e.hom
  rw [this]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

structure Atlas (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) where
  B : Type
  fin : Finite B
  k : B → ECh Y p
  aff : ∀ b, IsAffineOpen (k b).V
  cov : ∀ x : Y.X, ∃ b, x ∈ (k b).V
  N : ℕ
  A : ∀ b, Matrix (Fin (N + 1)) (Fin (k b).M.n) Γ(Y.X, (k b).V)
  C : ∀ b, Matrix (Fin (k b).M.n) (Fin (N + 1)) Γ(Y.X, (k b).V)
  CA : ∀ b, C b * A b = 1
  tw : ∀ (S : Type) [CommRing S] (x : Sp S ⟶ Y.X) (b b' : B) (h : ⊤ ≤ x ⁻¹ᵁ (k b).V) (h' : ⊤ ≤ x ⁻¹ᵁ (k b').V)
    (hM : ⊤ ≤ x ⁻¹ᵁ ((k b').M.U ⊓ (k b).M.U)), ∃ a : Sˣ, (A b).map (ev x _ h) =
      (a : S) • ((A b').map (ev x _ h') * (chg (k b').M.toMChart (k b).M.toMChart).map (ev x _ hM))

variable {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)} (A : Atlas Y p)

namespace Atlas

abbrev V (b : A.B) : Y.X.affineOpens := ⟨(A.k b).V, A.aff b⟩

def alpha (b : A.B) : c.F →+* Γ(Y.X, (A.V b).1) := str (tau (A.aff b))

def cv (b : A.B) : Let Dw.mult → Fin (A.N + 1) → Γ(Y.X, (A.V b).1) :=
  fun z r => (A.A b * (A.k b).u z.1) r z.2

def Dv (b : A.B) : Let Dw.mult → Fin (A.N + 1) → Γ(Y.X, (A.V b).1) :=
  fun z r => ((A.k b).w z.1 * A.C b) z.2 r

end Atlas

variable {A}

structure Cells (A : Atlas Y p) {Z : Scheme.{0}} (π : Z ⟶ Y.X)
    (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1))
    (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) : Prop where
  proper : IsProper π
  normal : Geo.Tor.IsNormalScheme Z
  plk : HasPlk (RingHom.id c.F) A.V A.alpha A.cv π g κ
  cover : ∀ z : Z, ∃ b w, z ∈ Set.range (κ b w)
  ext : ∀ (W : Scheme.{0}) (a a' : W ⟶ Z), a ≫ π = a' ≫ π → (∀ en, a ≫ g en = a' ≫ g en) → a = a'

def cellMat (U : Y.X.affineOpens) (σ : E →+* ℂ) : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) (CR Dw.mult U) :=
  Matrix.of (cell MvPolynomial.X σ)

theorem det_cellMat (U : Y.X.affineOpens) (σ : E →+* ℂ) : (cellMat (Dw := Dw) U σ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [cellMat, cell]
  · intro i j hij
    have h1 : ¬ j < i := not_lt.2 (le_of_lt hij)
    have h2 : i ≠ j := ne_of_lt hij
    simp [cellMat, cell, h1, h2]


variable (A) in
abbrev cC (b : A.B) : Γ(Y.X, (A.k b).V) →+* CR Dw.mult (A.V b) := MvPolynomial.C


variable (A) in
def uC (b : A.B) (w : Pm Dw.mult) (σ : E →+* ℂ) :
    Matrix (Fin (A.k b).M.n) (Fin (Dw.mult σ)) (CR Dw.mult (A.V b)) :=
  (((A.k b).u σ).map (cC A b)).submatrix id (w σ) * cellMat (A.V b) σ


variable (A) in
def wC (b : A.B) (w : Pm Dw.mult) (σ : E →+* ℂ) :
    Matrix (Fin (Dw.mult σ)) (Fin (A.k b).M.n) (CR Dw.mult (A.V b)) :=
  (cellMat (A.V b) σ)⁻¹ * (((A.k b).w σ).map (cC A b)).submatrix (w σ) id

theorem wC_mul_uC (b : A.B) (w : Pm Dw.mult) (σ : E →+* ℂ) : wC A b w σ * uC A b w σ = 1 := by
  have h1 : (((A.k b).w σ).map (cC A b)).submatrix (w σ) id * (((A.k b).u σ).map (cC A b)).submatrix id (w σ) = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, ← Matrix.map_mul, (A.k b).wu,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.submatrix_one_equiv]
  have h2 : IsUnit (cellMat (Dw := Dw) (A.V b) σ).det := by rw [det_cellMat]; exact isUnit_one
  calc wC A b w σ * uC A b w σ
      = (cellMat (A.V b) σ)⁻¹ * ((((A.k b).w σ).map (cC A b)).submatrix (w σ) id *
          (((A.k b).u σ).map (cC A b)).submatrix id (w σ)) * cellMat (A.V b) σ := by
        simp only [wC, uC, Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, Matrix.nonsing_inv_mul _ h2]

variable {Z : Scheme.{0}} {π : Z ⟶ Y.X} {g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)}
  {κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)} [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ)


variable (κ) in
def cellθ (k : A.B × Pm Dw.mult) : CR Dw.mult (A.V k.1) ≃+* Γ(Z, (κ k.1 k.2).opensRange) :=
  (exists_ringEquiv (κ k.1 k.2)).choose

theorem spMap_cellθ (k : A.B × Pm Dw.mult) :
    spMap (cellθ κ k).toRingHom ≫ κ k.1 k.2 = (isAffineOpen_opensRange (κ k.1 k.2)).fromSpec :=
  (exists_ringEquiv (κ k.1 k.2)).choose_spec

include hZ in
theorem cell_le (k : A.B × Pm Dw.mult) : (κ k.1 k.2).opensRange ≤ π ⁻¹ᵁ (A.k k.1).M.U := by
  rintro _ ⟨y, rfl⟩
  have e : κ k.1 k.2 ≫ π = cbase Dw.mult (A.V k.1) := hZ.plk.base _ _
  have h : (κ k.1 k.2 ≫ π) y ∈ ((A.V k.1).1 : Set Y.X) := by
    rw [e, cbase, Scheme.Hom.comp_apply]
    exact (A.V k.1).2.range_fromSpec.le ⟨_, rfl⟩
  exact (A.k k.1).le (by rw [Scheme.Hom.comp_apply] at h; exact h)

def FlagCellFrameChangeTriangular : Prop :=
  ∀ (k k' : A.B × Pm Dw.mult) (σ : E →+* ℂ), ∃ B : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ))
      Γ(Z, (κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange), B.BlockTriangular id ∧
    (chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map
        (π.appLE ((A.k k.1).M.U ⊓ (A.k k'.1).M.U) ((κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange)
          (inf_le_inf (cell_le hZ k) (cell_le hZ k'))).hom *
      ((uC A k'.1 k'.2 σ).map (cellθ κ k')).map (resG Z inf_le_right) =
      ((uC A k.1 k.2 σ).map (cellθ κ k)).map (resG Z inf_le_left) * B

def cellFrames (ht : FlagCellFrameChangeTriangular hZ) : Frames Y π where
  J := A.B × Pm Dw.mult
  U k := (κ k.1 k.2).opensRange
  cover := eq_top_iff.2 fun z _ => by
    obtain ⟨b, w, h⟩ := hZ.cover z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(b, w), h⟩
  M k := (A.k k.1).M
  le := cell_le hZ
  u k σ := (uC A k.1 k.2 σ).map (cellθ κ k)
  split k σ := ⟨(wC A k.1 k.2 σ).map (cellθ κ k), by
    rw [← Matrix.map_mul, wC_mul_uC, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  tri := ht

end GlobalTheory.FlagMod.FieldFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatThetaQuotientAtPrincipalLevelProof
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseCmp

open GlobalTheory.PlaceModel


open Classical in
theorem resC_eq_of_kerDat {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}
    {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle} {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ} {B : Base (Vc D i) (Wc D i)} (hB : B.Good)
    (hK : KerDat R i ξ χ ξR B.de.Q ω φ) (hc : ChrEq B.de.chi ξ) {PP : Pl D.host.E} (hPP : PP ∈ B.de.Q) :
    ξR PP = B.de.resC PP := by
  refine MonoidHom.ext fun u => Units.ext ?_
  obtain ⟨x, hx⟩ := exists_isLocUnit (hB.de.split.isIdemAt hPP) u
  obtain ⟨k1, k2⟩ := hx.res
  have e1 := eq_res_of_chrEq hc (hB.de.split.isIdemAt hPP) (hK.tame PP) (hK.res PP hPP) x hx.off k1 u k2
  have e2 := hx.eq (hB.de.res PP hPP)
  rw [← e1, e2]
  rfl


open Classical in
theorem omegaFlat_eq_locFn_empty {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}
    {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle} {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ} {B : Base (Vc D i) (Wc D i)} (hB : B.Good)
    (hK : KerDat R i ξ χ ξR B.de.Q ω φ) (hc : ChrEq B.de.chi ξ) (y : Reds D (Wc D i).rank (Vc D i).rank) :
    omegaFlat B.de.Q (Wc D i).rank ξR y = (GlobalTheory.FlatVecSum.princ B).locFn ∅ (fun _ _ => 1) y := by
  rw [GlobalTheory.FlatVecSum.omegaFlat_eq_prod, Base.locFn]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  exact Finset.prod_congr rfl fun PP hP => by rw [resC_eq_of_kerDat hB hK hc hP]; rfl


open Classical in
theorem flatTwoStep_holds : FlatTwoStep := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR ω φ B hB h hK hc
  obtain ⟨hvac, e, he, -⟩ := hK.vec
  have hψ := hvac.1
  have sV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βV i))
  have sW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βW i))
  have fV := Formalism.IndefR.Fin.PDA.selfDual_isFullLattice (Vc D i) (R.ΛV i) sV
  have fW := Formalism.IndefR.Fin.PDA.selfDual_isFullLattice (Wc D i) (R.ΛW i) sW
  have hdisj : Disjoint R.Pg B.de.Q := h.Pg ▸ hB.places.disj
  obtain ⟨eg, eQ, hg, hq, h1, h2, h3⟩ := GlobalTheory.FlatVecExist.idemSum_split he hdisj
  have hinfg := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg)
  obtain ⟨fg, hfg⟩ := GlobalTheory.PlaceVec.exists_isThetaAt hψ sV sW (a := cA D eg)
    (by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self hg]) hinfg
    (GlobalTheory.PlaceModelSum.placeModelExistsSum D R.ψ hψ _ _ _ _ sV sW _ eg hg _ hvac.2.theta hvac.2.lat).2
    (GlobalTheory.PlaceVec.isSBHalf_of_red fV fW hinfg (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
      (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _) R.Pg
      (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h)
  have hoQ := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hq
  have fix : ∀ u, (∀ a b, cA D eg * u a b = 0 ∧ eg * u a b = 0) →
      heisO R.ψ (Vc D i) (Wc D i) u (R.vacP i) = R.vacP i → heisO R.ψ (Vc D i) (Wc D i) u fg = fg :=
    fun u hu h0 => GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ (cA D eg) _ 1 _ _ fg hfg u
      (fun a b => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hu a b) h0
  have hPM := GlobalTheory.FlatVecExist.exists_model_of_fix hψ sV sW hoQ hq.2
    (fun u hu => fix u (fun a b => (GlobalTheory.FlatVecExist.off_of_half h1 (by rw [mul_comm, h3])
        ((isHalf_iff _ _).2 hu.2) a b).symm)
      (hoQ.heisO_eq (by rw [mul_comm, hq.2]) hvac.2.lat u hu))
    (fun u hu => fix u (fun a b => (GlobalTheory.FlatVecExist.off_of_half h2
        (by rw [← RingHom.map_mul, h1, map_zero]) ((isHalf_iff _ _).2 hu.2) a b).symm)
      (hoQ.conj.heisO_eq (by rw [GlobalTheory.DualPairCheck.cA_cA, hq.2]) hvac.2.lat u hu))
  have hinfQ := GlobalTheory.PlaceDatum.infPart_idemSum hq
  obtain ⟨K, hK', hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO fV fW (R.βV i) (R.βW i)
  obtain ⟨f, hf⟩ := GlobalTheory.PlaceDatum.exists_isThetaAt hψ sV sW (GlobalTheory.PlaceDatum.idemSum_mul_self hq) hinfQ hPM
    (GlobalTheory.PlaceDatum.isSBHalf_of_red eQ _ (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)) (GlobalTheory.PlaceDatum.frMapO_add _ _)
      (GlobalTheory.PlaceDatum.exists_den_frMapO sV.1.fg sW.1.fg _ _)
      ⟨K, hK', fun x hx => hC x (GlobalTheory.PlaceDatum.infPart_of_half hinfQ hx)⟩ B.de.Q
      (fun y => GlobalTheory.ConjTwist.omegaFlat B.de.Q (Wc D i).rank ξR y) fun y y' h => GlobalTheory.FlatVecExist.omegaFlat_congr _ _ _ h)
  have hfeq : f = (GlobalTheory.FlatVecSum.princ B).vecBase := by
    have k1 := hfg
    have k2 := hf
    simp only [omegaFlat_eq_locFn_empty hB hK hc] at k2
    rw [← idem_eq hg] at k1
    rw [← idem_eq hq] at k2
    rw [← h.ψ, ← h.ΛS, ← h.ΛT, ← h.βS, ← h.βT] at k1 k2
    rw [← h.vac, ← h.Pg] at k1
    unfold Base.vecBase Base.vecAt
    rw [Finset.union_empty]
    refine GlobalTheory.FlatVecSum.eq_vec_of_two_steps (G := GlobalTheory.FlatVecSum.princG B.G) hB.frame hB.places (fun y y' hy => ?_)
      (fg := fg) ?_ k2
    · unfold Base.locFn
      rw [Finset.prod_congr rfl fun PP hPP => by rw [hy PP hPP]]
    · simp only [GlobalTheory.FlatVecSum.omegaG_princ]
      exact k1
  refine ⟨eg, eQ, fg, hg, hq, hfg, ?_⟩
  rw [← hfeq]
  exact hf

end GlobalTheory.BaseCmp
end
end

