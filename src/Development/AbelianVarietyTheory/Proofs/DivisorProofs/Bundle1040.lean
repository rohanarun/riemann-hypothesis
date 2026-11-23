module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardQuotientBound
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

theorem isIntB_lattice_principal_eventually : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ I : Set (v.adicCompletion ℚ ⊗[ℚ] L), 0 ∈ I →
      (∀ x ∈ I, ∀ y ∈ I, x + y ∈ I) → (∀ ρ, IsIntB v ℓ ρ → ∀ x ∈ I, ρ * x ∈ I) →
      (∃ D : ℤ, D ≠ 0 ∧ (∀ x, IsIntB v ℓ x → (D : v.adicCompletion ℚ ⊗[ℚ] L) * x ∈ I) ∧
        ∀ x ∈ I, IsIntB v ℓ ((D : v.adicCompletion ℚ ⊗[ℚ] L) * x)) →
      ∃ m : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, ∀ x, x ∈ I ↔ ∃ ρ, IsIntB v ℓ ρ ∧ x = ↑m * ρ := by
  intro L _ _ κ ℓ
  obtain ⟨S₁, hS₁⟩ := isIntB_mul_star_eventually L
    (RingHom.toOpposite (RingHom.id L) fun x y => mul_comm x y) κ ℓ
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.T.adicIntegralTensorBasis_iff_exists_integral_multiple L κ ℓ
  refine ⟨S₁ ∪ S₂, fun v hv I h0 hadd hmul ⟨D, hD0, hDI, hIO⟩ => ?_⟩
  have hv₁ : v ∉ S₁ := fun h => hv (Finset.mem_union_left _ h)
  have hv₂ : v ∉ S₂ := fun h => hv (Finset.mem_union_right _ h)
  have hOmul := (hS₁ v hv₁).1
  have hloc := hS₂ v hv₂
  have hOadd : ∀ y z, IsIntB v ℓ y → IsIntB v ℓ z → IsIntB v ℓ (y + z) := fun y z hy hz i => by
    rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hy i) (hz i)
  have hone : (1 : ℤ) ∉ v.asIdeal := fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hloc1 : ∀ c : ℤ, ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * (c : L)) := fun c =>
    ⟨1, hone, by rw [Int.cast_one, one_mul, ← eq_intCast (algebraMap ℤ L)]; exact isIntegral_algebraMap⟩
  have hcast : ∀ c : ℤ, ((c : v.adicCompletion ℚ ⊗[ℚ] L)) = (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (c : L) :=
    fun c => by rw [← Algebra.TensorProduct.includeRight_apply, map_intCast]
  have hO : ∀ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) →
      IsIntB v ℓ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c) := fun c hc => (hloc c).2 hc
  have htm : ∀ a b : L, ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] a) * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] b) =
      (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (a * b) := fun a b => by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hDL : (D : L) ≠ 0 := Int.cast_ne_zero.2 hD0
  let K : Set L := {a | (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (a / D) ∈ I}
  have hK0 : (0 : L) ∈ K := by
    show _ ∈ I; rw [zero_div, TensorProduct.tmul_zero]; exact h0
  have hKadd : ∀ a ∈ K, ∀ b ∈ K, a + b ∈ K := fun a ha b hb => by
    show _ ∈ I; rw [add_div, TensorProduct.tmul_add]; exact hadd _ ha _ hb
  have hKmul : ∀ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) → ∀ a ∈ K, c * a ∈ K :=
    fun c hc a ha => by
      show _ ∈ I; rw [mul_div_assoc, ← htm]; exact hmul _ (hO c hc) _ ha
  have hKloc : ∀ a ∈ K, ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * a) := fun a ha => by
    apply (hloc a).1
    have := hIO _ ha
    rwa [hcast, htm, mul_div_cancel₀ _ hDL] at this
  obtain ⟨g, hgK, hg⟩ := GlobalTheory.T.exists_generator_localized_integers_ideal_in_field L v K hK0 hKadd hKmul hKloc
  have hDK : (D : L) * D ∈ K := by
    show _ ∈ I
    have h1 := hDI _ (hO _ (hloc1 1))
    rwa [Int.cast_one, ← Algebra.TensorProduct.one_def, mul_one, hcast,
      ← mul_div_cancel_right₀ (D : L) hDL] at h1
  obtain ⟨c₀, hc₀, hc₀g⟩ := hg _ hDK
  have hg0 : g ≠ 0 := by
    rintro rfl; rw [mul_zero] at hc₀g; exact hDL (mul_self_eq_zero.1 hc₀g)
  have e1 : g / D * (D / g) = 1 := by field_simp
  have e1' : D / g * (g / D) = 1 := by field_simp
  let m : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ :=
    { val := (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (g / D), inv := (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (D / g),
      val_inv := by rw [htm, e1]; rfl
      inv_val := by rw [htm, e1']; rfl }
  refine ⟨m, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨y, ρ₁, hρ₁, rfl⟩ := GlobalTheory.T.adicTensor_exists_rational_add_integral_mul L κ ℓ v x D hD0
    have hy : (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] y ∈ I := by
      have h2 : (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] ((-1 : ℤ) : L) * ((D : v.adicCompletion ℚ ⊗[ℚ] L) * ρ₁) ∈ I :=
        hmul _ (hO _ (hloc1 _)) _ (hDI _ hρ₁)
      have := hadd _ hx _ h2
      convert this using 1
      rw [← hcast]; push_cast; ring
    have hyK : (D : L) * y ∈ K := by
      show _ ∈ I; rwa [mul_div_cancel_left₀ _ hDL]
    obtain ⟨c, hc, hcg⟩ := hg _ hyK
    have e2 : g / D * c = y := by
      rw [div_mul_eq_mul_div, mul_comm g c, ← hcg, mul_div_cancel_left₀ _ hDL]
    have e3 : g / D * c₀ = D := by
      rw [div_mul_eq_mul_div, mul_comm g c₀, ← hc₀g, mul_div_cancel_left₀ _ hDL]
    refine ⟨(1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c + (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c₀ * ρ₁,
      hOadd _ _ (hO c hc) (hOmul _ _ (hO c₀ hc₀) hρ₁), ?_⟩
    show _ = (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (g / D) * _
    rw [mul_add, htm, ← mul_assoc, htm, e2, e3, hcast]
  · rintro ⟨ρ, hρ, rfl⟩
    rw [mul_comm]
    exact hmul ρ hρ _ hgK

end GlobalTheory.AdicSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestDegreeComponentInvariant
section
open scoped TensorProduct Kronecker

noncomputable section

open Formalism.BasicNotions.TH MvPolynomial

namespace GlobalTheory.KFixIrr.LowStable

theorem deg_X_pderiv {σ : Type} (a b : σ) (P : MvPolynomial σ ℂ) :
    (X a * pderiv b P).totalDegree ≤ P.totalDegree := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [P.as_sum, map_sum, Finset.mul_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [pderiv_monomial]
  by_cases h : s b = 0
  · simp [h]
  · refine le_trans ?_ (le_totalDegree hs)
    rw [X, monomial_mul]
    refine (totalDegree_monomial_le _ _).trans (le_of_eq ?_)
    have h1 : s = Finsupp.single b 1 + (s - Finsupp.single b 1) := by
      rw [add_tsub_cancel_of_le]
      exact Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h)
    conv_rhs => rw [h1]
    rw [Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_add_index' (by simp) (by simp)]
    simp [Function.id_def]

theorem deg_pderiv_X {σ : Type} (a b : σ) (P : MvPolynomial σ ℂ) :
    (pderiv b (X a * P)).totalDegree ≤ P.totalDegree := by
  classical
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  refine (totalDegree_add _ _).trans (max_le (deg_X_pderiv _ _ _) ?_)
  rw [pderiv_X, Pi.single_apply]
  split_ifs <;> simp

def nonRaising (σ : Type) : Submodule ℂ (Module.End ℂ (MvPolynomial σ ℂ)) where
  carrier := {L | ∀ P, (L P).totalDegree ≤ P.totalDegree}
  add_mem' {L L'} h h' P := (totalDegree_add _ _).trans (max_le (h P) (h' P))
  zero_mem' P := by simp
  smul_mem' c L h P := (totalDegree_smul_le _ _).trans (h P)

theorem mem_nonRaising {σ : Type} {L : Module.End ℂ (MvPolynomial σ ℂ)} :
    L ∈ nonRaising σ ↔ ∀ P, (L P).totalDegree ≤ P.totalDegree := Iff.rfl

theorem rl_pos {P Q R S : ℕ} (l l' : Ln P Q R S) (hl : linePos l = true) (hl' : linePos l' = true) :
    raiB l * lowB l' ∈ nonRaising (Ln P Q R S) := by
  refine mem_nonRaising.2 fun g => ?_
  rw [Module.End.mul_apply, raiB, lowB, if_pos hl, if_pos hl', LinearMap.mulLeft_apply, Derivation.coeFn_coe]
  exact deg_X_pderiv _ _ _

theorem rl_neg {P Q R S : ℕ} (l l' : Ln P Q R S) (hl : linePos l = false) (hl' : linePos l' = false) :
    raiB l * lowB l' ∈ nonRaising (Ln P Q R S) := by
  refine mem_nonRaising.2 fun g => ?_
  rw [Module.End.mul_apply, raiB, lowB, if_neg (by simp [hl]), if_neg (by simp [hl']), LinearMap.mulLeft_apply,
    LinearMap.neg_apply, Derivation.coeFn_coe, totalDegree_neg]
  exact deg_pderiv_X _ _ _

theorem omE_mem {P Q R S : ℕ} (l l' : Ln P Q R S) (h : linePos l = linePos l') :
    omE l l' ∈ nonRaising (Ln P Q R S) := by
  rw [omE]
  refine Submodule.add_mem _ ?_ ?_
  · cases hl : linePos l
    · exact rl_neg l l' hl (h ▸ hl)
    · exact rl_pos l l' hl (h ▸ hl)
  · split_ifs
    · exact Submodule.smul_mem _ _ (mem_nonRaising.2 fun g => le_rfl)
    · exact Submodule.zero_mem _

theorem linePos_same {P Q R S : ℕ} (a : Ix P Q) (c d : Ix R S) (h : sameBlock c d) :
    linePos ((a, c) : Ln P Q R S) = linePos (a, d) := by
  rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;> simp_all [sameBlock, linePos]

theorem fockAct2_mem {P Q R S : ℕ} (Z : Mat R S) (hZ : IsKC Z) :
    fockAct2 P Q R S Z ∈ nonRaising (Ln P Q R S) := by
  classical
  rw [show fockAct2 P Q R S Z = omAct P Q R S ((1 : Mat P Q) ⊗ₖ Z) from rfl, omAct_apply]
  refine Submodule.sum_mem _ fun l _ => Submodule.sum_mem _ fun l' _ => ?_
  rcases l with ⟨a, c⟩
  rcases l' with ⟨a', d⟩
  rw [Matrix.kroneckerMap_apply]
  by_cases ha : a = a'
  · subst ha
    by_cases hcd : sameBlock c d
    · exact Submodule.smul_mem _ _ (omE_mem _ _ (linePos_same a c d hcd))
    · rw [hZ c d hcd, mul_zero, zero_smul]; exact Submodule.zero_mem _
  · rw [Matrix.one_apply_ne ha, zero_mul, zero_smul]; exact Submodule.zero_mem _

theorem fockAct2_lowOne : ∀ (P Q R S : ℕ) (x : ℚ) (d : ℕ) (Z : Formalism.BasicNotions.TH.Mat R S), Formalism.BasicNotions.TH.IsKC Z →
    ∀ f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x d, Formalism.BasicNotions.TH.fockAct2 P Q R S Z f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x d := by
  intro P Q R S x d Z hZ f hf
  rw [mem_lowOne] at hf ⊢
  refine ⟨?_, (mem_nonRaising.1 (fockAct2_mem Z hZ) f).trans hf.2⟩
  rw [mem_chiOne] at hf ⊢
  intro X hX
  have h := LinearMap.congr_fun ((GlobalTheory.FockPair.pair_lie_commute P Q R S).2.2 X Z) f
  simp only [Module.End.mul_apply] at h
  rw [h, hf.1 X hX, map_smul]

end GlobalTheory.KFixIrr.LowStable

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCentralizerRegularTwistedCentraliser
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.CarryCent

theorem commute_of_commute_sep {K : Type} [Field K] {n : ℕ} (N A B : Matrix (Fin n) (Fin n) K)
    (hN : N.charpoly.Separable) (hA : Commute A N) (hB : Commute B N) : Commute A B := by
  obtain ⟨q, rfl⟩ := GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute n N A hN hA
  obtain ⟨q', rfl⟩ := GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute n N B hN hB
  change _ * _ = _ * _
  rw [← map_mul, ← map_mul, mul_comm]

theorem map_coord_commute {K R : Type} [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) K) (X : Matrix (Fin n) (Fin n) R)
    (hX : Commute X (N.map (algebraMap K R))) (f : R →ₗ[K] K) : Commute (X.map f) N := by
  have k1 : (X * N.map (algebraMap K R)).map f = X.map f * N := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have k2 : (N.map (algebraMap K R) * X).map f = N * X.map f := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have h := congrArg (fun Y => Y.map f) hX.eq
  simp only [k1, k2] at h
  exact h

theorem commute_of_commute_map {K R : Type} [Field K] [CommRing R] [Algebra K R] [Module.Finite K R] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) K) (hN : N.charpoly.Separable) (X Y : Matrix (Fin n) (Fin n) R)
    (hX : Commute X (N.map (algebraMap K R))) (hY : Commute Y (N.map (algebraMap K R))) : Commute X Y := by
  let b := Module.Free.chooseBasis K R
  have dec : ∀ Z : Matrix (Fin n) (Fin n) R, Z = ∑ k, b k • (Z.map (b.coord k)).map (algebraMap K R) := by
    intro Z
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, Module.Basis.coord_apply, smul_eq_mul]
    conv_lhs => rw [← b.sum_repr (Z i j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, mul_comm]
  rw [dec X, dec Y]
  refine Commute.sum_left _ _ _ fun k _ => Commute.sum_right _ _ _ fun l _ => ?_
  refine ((Commute.map ?_ (algebraMap K R).mapMatrix).smul_left _).smul_right _
  exact commute_of_commute_sep N _ _ hN (map_coord_commute N X hX _) (map_coord_commute N Y hY _)

variable {p : ℕ} [Fact p.Prime]

theorem commute_of_commute_reg (G : HTGroup p) (r : ℕ) (hr : 0 < r) (γ : Gp G) (hγ : regular₂ G γ) (a b : Gr G r)
    (ha : Commute a (inclG G r γ)) (hb : Commute b (inclG G r γ)) : Commute a b := by
  refine Prod.ext ?_ (funext fun w => ?_)
  · change a.1 * b.1 = b.1 * a.1
    apply Units.ext
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [Matrix.mul_apply, mul_comm]
  · change a.2 w * b.2 w = b.2 w * a.2 w
    letI : Algebra (G.Fw w) (KQ p (G.Fw w) r) := Algebra.TensorProduct.leftAlgebra
    haveI : FiniteDimensional ℚ_[p] (Qr p r) :=
      ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr
    haveI : Module.Finite (G.Fw w) (KQ p (G.Fw w) r) :=
      inferInstanceAs (Module.Finite (G.Fw w) ((G.Fw w) ⊗[ℚ_[p]] Qr p r))
    have hw : ∀ x : Gr G r, Commute x (inclG G r γ) →
        Commute (x.2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r))
          (((γ.2 w : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)).map
            (algebraMap (G.Fw w) (KQ p (G.Fw w) r))) := by
      intro x hx
      have := congrArg (fun y : Gr G r => ((y.2 w : GL (Fin G.n) (KQ p (G.Fw w) r)) :
        Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r))) hx.eq
      exact this
    exact Units.ext (commute_of_commute_map _ (hγ w) _ _ (hw a ha) (hw b hb)).eq

end GlobalTheory.CarryCent

namespace GlobalTheory.CarryCent

variable {p : ℕ} [Fact p.Prime]

theorem map_centralizer_carry : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ) (γ : Gp G) (δ z : Gr G r),
    0 < r → regular₂ G γ → IsNrm G r γ δ z →
    (Subgroup.centralizer {γ}).map (carry G r z) = GlobalTheory.BCT.twCent (sigG G r) δ := by
  intro p _ G r γ δ z hr hγ hN
  set δ' := z * δ * (sigG G r z)⁻¹ with hδ'
  have hN' : nrmG (sigG G r) r δ' = inclG G r γ := by
    have h := (GlobalTheory.T.twistedNormConj_normalize_and_degree_one p G).1 r γ δ z hr hN
    simpa [IsNrm] using h
  obtain ⟨hit, hfix, hinj, hrange⟩ := GlobalTheory.T.hermitianTripleFrobeniusTwist_order_fixed_points p G r hr
  have hδc : Commute δ' (inclG G r γ) := by
    have h2 := (GlobalTheory.T.twistedNormProductIterate_twistedConj (sigG G r) r δ' 1).2
    rw [hN', hfix, hit] at h2
    exact h2
  have memT : ∀ h, h ∈ GlobalTheory.BCT.twCent (sigG G r) δ' ↔ ∃ g ∈ Subgroup.centralizer {γ}, inclG G r g = h := by
    intro h
    constructor
    · intro hh
      change h * δ' = δ' * sigG G r h at hh
      have hc : Commute h (inclG G r γ) := by
        have h1 := (GlobalTheory.T.twistedNormProductIterate_twistedConj (sigG G r) r δ' h).1
        have e : h⁻¹ * δ' * sigG G r h = δ' := by rw [mul_assoc, ← hh, inv_mul_cancel_left]
        rw [e, hN', hit] at h1
        change h * inclG G r γ = inclG G r γ * h
        calc h * inclG G r γ = h * (h⁻¹ * inclG G r γ * h) := by rw [← h1]
          _ = inclG G r γ * h := by group
      have hcd : Commute h δ' := commute_of_commute_reg G r hr γ hγ h δ' hc hδc
      have hs : sigG G r h = h := mul_left_cancel (hh.symm.trans hcd.eq)
      obtain ⟨g, rfl⟩ := hrange h hs
      refine ⟨g, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hinj
      rw [map_mul, map_mul]
      exact hc.eq
    · rintro ⟨g, hg, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hg
      have hc : Commute (inclG G r g) (inclG G r γ) := by
        change inclG G r g * inclG G r γ = inclG G r γ * inclG G r g
        rw [← map_mul, ← map_mul, hg]
      have hcd := commute_of_commute_reg G r hr γ hγ _ δ' hc hδc
      change inclG G r g * δ' = δ' * sigG G r (inclG G r g)
      rw [hfix]
      exact hcd.eq
  have conjT : ∀ x, x ∈ GlobalTheory.BCT.twCent (sigG G r) δ ↔ z * x * z⁻¹ ∈ GlobalTheory.BCT.twCent (sigG G r) δ' := by
    intro x
    change x * δ = δ * sigG G r x ↔ z * x * z⁻¹ * δ' = δ' * sigG G r (z * x * z⁻¹)
    rw [hδ', map_mul, map_mul, map_inv]
    have e1 : z * x * z⁻¹ * (z * δ * (sigG G r z)⁻¹) = z * (x * δ) * (sigG G r z)⁻¹ := by group
    have e2 : z * δ * (sigG G r z)⁻¹ * (sigG G r z * sigG G r x * (sigG G r z)⁻¹) =
        z * (δ * sigG G r x) * (sigG G r z)⁻¹ := by group
    rw [e1, e2, mul_left_inj, mul_right_inj]
  ext x
  rw [conjT, memT, Subgroup.mem_map]
  refine exists_congr fun g => and_congr_right fun _ => ?_
  change z⁻¹ * inclG G r g * z⁻¹⁻¹ = x ↔ inclG G r g = z * x * z⁻¹
  constructor
  · rintro rfl; group
  · intro e; rw [e]; group

end GlobalTheory.CarryCent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkingRootsDilationCoprimeLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.DilateLevel

open GlobalTheory.Dict.MarkMove

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

theorem level_smul_levQ (q : LevQ Dw l) : l.M • q = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul (level_mem l).1 trivial

theorem cSep_smul_levQ (q : LevQ Dw l) : cSep l • q = q := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  have e : cSep l • y - y = (cSep l - 1) • y := by rw [sub_smul, one_smul]
  rw [e]
  exact Submodule.smul_mem_smul (cSep_spec l).2 trivial

theorem sub_sepRep (q : LevQ Dw l) (x : Dw.La) (hx : x ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La))
    (hq : Submodule.Quotient.mk x = q) : ∃ z : Dw.La, x - cSep l • levRep q = l.M • z := by
  have h1 : x - levRep q ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) :=
    (Submodule.Quotient.eq _).1 (hq.trans (Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)).symm)
  obtain ⟨b1, hb1⟩ := modN_smul l ((mul_comm _ _).trans l.prod) (cSep_spec l).1 h1
  obtain ⟨b2, hb2⟩ := modN_smul l l.prod (cSep_spec l).2 hx
  refine ⟨b1 - b2, ?_⟩
  rw [smul_sub, ← hb1, ← hb2, smul_sub, sub_smul, one_smul]
  abel

end GlobalTheory.DilateLevel

namespace GlobalTheory.DilateLevel

open GlobalTheory.Dict.MarkMove

theorem dilate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (r n : ℕ) (L : Lt E r) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)) (m : ℤ), IsCoprime m (l.M : ℤ) → (IsMark l L mk → IsMark l L (m • mk)) ∧ ∀ (N : ℕ) (Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E), ((∀ a, mk a ∈ L) → IsRoots l L mk N Y → IsRoots l L (m • mk) N (fun q => Y (m • q))) ∧ ∀ (g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (w : E) (Λ : Lt E n) (v : TF n g) (c : (Fin n → LevQ Dw l) → ℂ), gphi X bas w Λ L v (fun q => c (m • q)) (fun q => Y (m • q)) = gphi X bas w Λ L v c Y := by
  intro E _ _ _ H Dw l r n L mk m hm
  refine hm.elim fun α hβ => hβ.elim fun β hab => ?_
  have hM0 : (l.M : E) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
  have hsm : ∀ a, (m • mk) a = m • mk a := fun a => LinearMap.smul_apply _ _ _
  have hbez : ∀ x : Fin r → E, x = α • (m • x) + β • (l.M • x) := fun x => by
    rw [smul_smul, ← natCast_zsmul, smul_smul, ← add_smul, hab, one_smul]
  refine ⟨fun h => ?_, fun N Y => ⟨fun hmem h => ?_, fun g X bas w Λ v c => ?_⟩⟩
  · refine ⟨fun a => by rw [hsm]; exact zsmul_mem (h.mem a) m, fun a ha hu => ?_, fun v hv => ?_⟩
    · refine hu.elim fun u hu' => h.inj a ha ⟨α • u + β • mk a, add_mem (zsmul_mem hu'.1 α) (zsmul_mem (h.mem a) β), ?_⟩
      have e : m • mk a = l.M • u := (hsm a).symm.trans hu'.2
      refine (hbez (mk a)).trans ?_
      rw [e, smul_add, smul_comm α, smul_comm β]
    · have hvL : v ∈ L := Submodule.smul_le_right hv
      refine (h.surj (α • v) (zsmul_mem hv α)).elim fun a1 h1 => h1.elim fun ha1 h2 => h2.elim fun u1 h3 => ?_
      refine ⟨a1, ha1, m • u1 + β • v, add_mem (zsmul_mem h3.1 m) (zsmul_mem hvL β), ?_⟩
      have e : α • v = mk a1 + l.M • u1 := h3.2
      refine (hbez v).trans ?_
      rw [smul_comm α m, e, hsm, smul_add, smul_add, smul_comm m, smul_comm β]
      abel
  · intro q b
    have h0 := h (m • q) b
    refine ⟨?_, h0.2⟩
    refine h0.1.elim fun a0 k => k.elim fun ha0 k2 => ?_
    have hq0 : Submodule.Quotient.mk a0 = m • q b := k2.1
    have hY0 := k2.2
    set a' : Dw.La := cSep l • levRep (q b) with ha'
    have ha'm : a' ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := Submodule.smul_mem_smul (cSep_spec l).1 trivial
    have hcls : (Submodule.Quotient.mk a' : LevQ Dw l) = q b := by
      have hr : (Submodule.Quotient.mk (levRep (q b)) : LevQ Dw l) = q b :=
        Classical.choose_spec (Submodule.Quotient.mk_surjective _ (q b))
      rw [ha', Submodule.Quotient.mk_smul, hr, cSep_smul_levQ]
    refine ⟨a', ha'm, hcls, ?_⟩
    have hm' : (Submodule.Quotient.mk (m • a') : LevQ Dw l) = m • q b := by
      rw [Submodule.Quotient.mk_smul, hcls]
    refine (sub_sepRep (m • q b) a0 ha0 hq0).elim fun z1 hz1 => ?_
    refine (sub_sepRep (m • q b) (m • a') (zsmul_mem ha'm m) hm').elim fun z2 hz2 => ?_
    have hd : a0 - m • a' = l.M • (z1 - z2) := by
      rw [smul_sub, ← hz1, ← hz2]; abel
    have key : ((l.M : E)⁻¹) • (mk a0 - (m • mk) a') = mk (z1 - z2) := by
      rw [hsm, ← map_zsmul mk, ← map_sub, hd, map_nsmul, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM0]
    have := add_mem hY0 (hmem (z1 - z2))
    rw [← key] at this
    convert this using 1
    rw [smul_sub]
    abel
  · have hk : ∀ q : Fin n → LevQ Dw l, ((l.M : ℤ)) • q = 0 := fun q => funext fun b => by
      rw [Pi.smul_apply, natCast_zsmul, level_smul_levQ]; rfl
    have hinv : ∀ q : Fin n → LevQ Dw l, α • m • q = q := fun q => by
      rw [smul_smul, show α * m = 1 - β * l.M by linear_combination hab, sub_smul, one_smul, mul_smul, hk,
        smul_zero, sub_zero]
    let e : (Fin n → LevQ Dw l) ≃ (Fin n → LevQ Dw l) :=
      { toFun := fun q => m • q
        invFun := fun q => α • q
        left_inv := fun q => hinv q
        right_inv := fun q => by
          change m • α • q = q
          rw [smul_comm]; exact hinv q }
    exact finsum_comp_equiv e (f := fun q => c q • heisG X bas (Y q) (projA X bas w (tens Λ L) v))

end GlobalTheory.DilateLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyPeriodLatticePropertiesHold
section
noncomputable section

namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker

theorem periodLattices : PeriodLattices := by
  intro D X s cc δ B χ cD _hX hok _h1 _h2 hcc hδ _hχ _hdg _hY a b S ha hb hconj hU
  exact ⟨KS.Lat.delta_ne hcc hδ, nonempty_tau s, hconj, hU, aa_fg s cc,
    fun N N' hN hN' => ⟨e_fixed_ambOf s B χ cD N N' hok hcc hδ (s.admissible_of_selfDual_lattices hok ha hb hN hN'),
      laFacts_ambOf s B χ cD N N' hok hcc hδ (s.admissible_of_selfDual_lattices hok ha hb hN hN')⟩⟩

end GlobalTheory.ColNorms
end
end

