module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FderivEqOfJetOf
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorusA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CorrOfJetsOfAnalyticFrameProducts
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal.JetCorr

theorem jet_point_eq {K : Type} [Field K] {J : Type} {m : ℕ} (p : PrimeSpectrum (Jet K J m)) :
    p = IsLocalRing.closedPoint (Jet K J m) := by
  apply PrimeSpectrum.ext
  refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun a ha => ?_
  have hn : IsNilpotent a := by
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hn := jet_nilpotent_of_orig K J m (sub_const_mem_orig (R := K) q)
    have h0 : MvPolynomial.constantCoeff q = 0 := by
      by_contra hne
      refine (IsLocalRing.mem_maximalIdeal _).mp ha ?_
      have e : algebraMap K (Jet K J m) (MvPolynomial.constantCoeff q) =
          Ideal.Quotient.mk (orig K J ^ (m + 1)) (MvPolynomial.C (MvPolynomial.constantCoeff q)) := by
        rw [← MvPolynomial.algebraMap_eq]; rfl
      have hsplit : Ideal.Quotient.mk (orig K J ^ (m + 1)) q =
          algebraMap K (Jet K J m) (MvPolynomial.constantCoeff q) +
            Ideal.Quotient.mk (orig K J ^ (m + 1)) (q - MvPolynomial.C (MvPolynomial.constantCoeff q)) := by
        rw [map_sub, e, add_sub_cancel]
      rw [hsplit]
      exact IsNilpotent.isUnit_add_left_of_commute hn
        ((isUnit_iff_ne_zero.mpr hne).map (algebraMap K (Jet K J m))) (Commute.all _ _)
    rwa [h0, map_zero, sub_zero] at hn
  obtain ⟨n, hn⟩ := hn
  exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)

section JetOf

variable {N : ℕ} (m : ℕ)

theorem jetOf_one' : jetOf m (fun _ : Fin N → ℂ => (1 : ℂ)) = 1 := by
  rw [jetOf_const, map_one]

theorem jetOf_pow' {F : (Fin N → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0) (k : ℕ) :
    jetOf m (fun v => F v ^ k) = jetOf m F ^ k := by
  induction k with
  | zero => simpa using jetOf_one' m
  | succ k ih =>
    rw [pow_succ, ← ih, ← jetOf_mul m (hF.fun_pow k).contDiffAt hF.contDiffAt]
    congr 1

theorem jetOf_mul_inv {F : (Fin N → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0) (h0 : F 0 ≠ 0) :
    jetOf m F * jetOf m (fun v => (F v)⁻¹) = 1 := by
  rw [← jetOf_mul m hF.contDiffAt (hF.fun_inv h0).contDiffAt, ← jetOf_one' m]
  refine jetOf_congr m ((hF.continuousAt.eventually_ne h0).mono fun v hv => ?_)
  exact mul_inv_cancel₀ hv

theorem jetOf_zpow {F : (Fin N → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0) (h0 : F 0 ≠ 0)
    (u : (Jet ℂ (Fin 1 × Fin N) m)ˣ) (hu : u.val = jetOf m F) (a : ℤ) :
    jetOf m (fun v => F v ^ a) = (u ^ a).val := by
  obtain ⟨k, rfl | rfl⟩ := a.eq_nat_or_neg
  · simp only [zpow_natCast, Units.val_pow_eq_pow_val, hu]
    exact jetOf_pow' m hF k
  · simp only [zpow_neg, zpow_natCast]
    symm
    apply Units.inv_eq_of_mul_eq_one_right
    rw [Units.val_pow_eq_pow_val, hu, ← jetOf_pow' m hF k]
    exact jetOf_mul_inv m (hF.fun_pow k) (pow_ne_zero _ h0)

theorem jetOf_prod {K : Type} (s : Finset K) {F : K → (Fin N → ℂ) → ℂ} (hF : ∀ k, AnalyticAt ℂ (F k) 0) :
    jetOf m (fun v => ∏ k ∈ s, F k v) = ∏ k ∈ s, jetOf m (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jetOf_one' m
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← ih, ← jetOf_mul m (hF a).contDiffAt
      (Finset.analyticAt_fun_prod s fun k _ => hF k).contDiffAt]
    congr 1
    funext v
    simp [Finset.prod_insert ha]

end JetOf

theorem jetN_prod_zpow {n g : ℕ} (m : ℕ) {K : Type} [Fintype K] (f : K → (Fin g → ℂ) → ℂ)
    (hf : ∀ k, AnalyticAt ℂ (f k) 0) (h0 : ∀ k, f k 0 ≠ 0)
    (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ε : K → ℤ) :
    ∃ u : K → (Jet ℂ (Fin n × Fin g) m)ˣ, (∀ k, (u k).val = jetN m fun w => f k (Λ k w)) ∧
      jetN m (fun w => ∏ k, f k (Λ k w) ^ ε k) = (∏ k, u k ^ ε k).val := by
  have hc : colsOf n g 0 = 0 := rfl
  have hA : ∀ k, AnalyticAt ℂ (fun v => f k (Λ k (colsOf n g v))) 0 := fun k => by
    have h1 : AnalyticAt ℂ (colsOf n g) 0 :=
      AnalyticAt.pi fun i => AnalyticAt.pi fun j =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n * g) => ℂ) (finProdFinEquiv (i, j))).analyticAt 0
    have h2 : AnalyticAt ℂ (fun v => Λ k (colsOf n g v)) 0 :=
      ((LinearMap.toContinuousLinearMap (Λ k)).analyticAt _).comp h1
    exact (hf k).comp_of_eq h2 (by rw [hc, map_zero])
  have hz : ∀ k, f k (Λ k (colsOf n g 0)) ≠ 0 := fun k => by rw [hc, map_zero]; exact h0 k
  let u0 : K → (Jet ℂ (Fin 1 × Fin (n * g)) m)ˣ := fun k =>
    Units.mkOfMulEqOne _ _ (jetOf_mul_inv m (hA k) (hz k))
  refine ⟨fun k => Units.map (renN n g m).toMonoidHom (u0 k), fun k => rfl, ?_⟩
  unfold jetN
  rw [jetOf_prod m Finset.univ (F := fun k v => f k (Λ k (colsOf n g v)) ^ ε k)
    fun k => (hA k).fun_zpow (hz k), map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [jetOf_zpow m (hA k) (hz k) (u0 k) rfl, ← map_zpow]
  rfl

open scoped Classical in
theorem prod_zpow_fiber {M T K : Type*} [CommGroup M] [Fintype K] (s : Finset T) (φ : K → T) (hs : ∀ k, φ k ∈ s)
    (ε : K → ℤ) (w : T → M) :
    ∏ k, w (φ k) ^ ε k = ∏ ψ ∈ s, w ψ ^ (∑ k, if φ k = ψ then ε k else 0) := by
  have h : ∀ ψ, w ψ ^ (∑ k, if φ k = ψ then ε k else 0) = ∏ k, if φ k = ψ then w ψ ^ ε k else 1 := fun ψ => by
    have hz : ∀ t : Finset K, ∀ a : K → ℤ, w ψ ^ (∑ k ∈ t, a k) = ∏ k ∈ t, w ψ ^ a k := fun t a => by
      induction t using Finset.induction_on with
      | empty => simp
      | insert b t hb ih => rw [Finset.sum_insert hb, Finset.prod_insert hb, zpow_add, ih]
    rw [hz]
    refine Finset.prod_congr rfl fun k _ => ?_
    split_ifs <;> simp
  simp only [h]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_ite_eq, if_pos (hs k)]


open scoped Classical in
theorem prod_zpow_eq {M T K K' : Type*} [CommGroup M] [Fintype K] [Fintype K'] (φ : K → T) (ε : K → ℤ)
    (φ' : K' → T) (ε' : K' → ℤ) (u : K → M) (u' : K' → M)
    (h₁ : ∀ k l, φ k = φ l → u k = u l) (h₂ : ∀ k l, φ' k = φ' l → u' k = u' l)
    (h₃ : ∀ k l, φ k = φ' l → u k = u' l)
    (hs : ∀ ψ, (∑ k, if φ k = ψ then ε k else 0) = ∑ k', if φ' k' = ψ then ε' k' else 0) :
    ∏ k, u k ^ ε k = ∏ k, u' k ^ ε' k := by
  let w : T → M := fun ψ => if h : ∃ k, φ k = ψ then u h.choose else if h' : ∃ k, φ' k = ψ then u' h'.choose else 1
  have hw : ∀ k, u k = w (φ k) := fun k => by
    have h : ∃ l, φ l = φ k := ⟨k, rfl⟩
    simp only [w, dif_pos h]
    exact h₁ _ _ h.choose_spec.symm
  have hw' : ∀ k, u' k = w (φ' k) := fun k => by
    by_cases h : ∃ l, φ l = φ' k
    · simp only [w, dif_pos h]
      exact (h₃ _ _ h.choose_spec).symm
    · have h' : ∃ l, φ' l = φ' k := ⟨k, rfl⟩
      simp only [w, dif_neg h, dif_pos h']
      exact h₂ _ _ h'.choose_spec.symm
  simp only [hw, hw']
  rw [prod_zpow_fiber (Finset.univ.image φ ∪ Finset.univ.image φ') φ (fun k => by simp) ε w,
    prod_zpow_fiber (Finset.univ.image φ ∪ Finset.univ.image φ') φ' (fun k => by simp) ε' w]
  simp only [hs]

section Frame

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)


set_option backward.isDefEq.respectTransparency false in
theorem origin_mem {n m : ℕ} {ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left}
    {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (h : Φ.JetMap m ψ Λ) {U : A.left.Opens}
    (p : Sp (Jet ℂ (Fin n × Fin g) m)) (hp : ψ p ∈ U) : ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ U := by
  obtain ⟨hol, rfl⟩ := h
  rw [Scheme.Hom.comp_apply, jet_point_eq (K := ℂ) (J := Fin 1 × Fin (n * g)) (m := m)
      (spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) p),
    jetPt_closedPoint] at hp
  have hc : colsOf n g 0 = 0 := rfl
  rw [hc, map_zero] at hp
  exact top_le_of_mem hp

theorem fr_analyticAt (j : L.L.ι) (h : ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U j) : AnalyticAt ℂ (Φ.fr j) 0 :=
  GlobalTheory.SCV.analyticAt_of_differentiableOn (Φ.fr_hol j) ((Φ.hol (L.L.U j) 0).1.mem_nhds h)

end Frame


set_option backward.isDefEq.respectTransparency false in
theorem corr_of_jetRd : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), Φ.Imm → ∀ (n m : ℕ) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (φ' : K' → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε' : K' → ℤ) (τ' : LB.Gen (LB.LinComb L.L φ' ε')) (Λ' : K' → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.JetRd m φ ε τ Λ → Φ.JetRd m φ' ε' τ' Λ' → LB.SameSum φ ε φ' ε' → LB.Gen.Corr L.L φ ε φ' ε' τ τ' := by
  intro S A _ _ L x0 g Φ hI n m K K' _ _ φ ε τ Λ φ' ε' τ' Λ' h h' hs j j' c c' cc
  by_cases hW : ∃ p, p ∈ LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j'
  · obtain ⟨p, hp⟩ := hW
    have hT : ⊤ ≤ LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j' := fun q _ => by
      have e1 := jet_point_eq (K := ℂ) (J := Fin n × Fin g) (m := m) p
      have e2 := jet_point_eq (K := ℂ) (J := Fin n × Fin g) (m := m) q
      rw [e2, ← e1]
      exact hp
    have o : ∀ k, ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U (j k) := fun k =>
      origin_mem Φ (h.1 k) p (LB.wchart_le L.L φ j k hp.1)
    have o' : ∀ k, ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U (j' k) := fun k =>
      origin_mem Φ (h'.1 k) p (LB.wchart_le L.L φ' j' k hp.2)
    obtain ⟨u, hu, hP⟩ := jetN_prod_zpow m (fun k => Φ.fr (j k)) (fun k => fr_analyticAt Φ _ (o k))
      (fun k => Φ.fr_ne _ _ (o k)) Λ ε
    obtain ⟨u', hu', hP'⟩ := jetN_prod_zpow m (fun k => Φ.fr (j' k)) (fun k => fr_analyticAt Φ _ (o' k))
      (fun k => Φ.fr_ne _ _ (o' k)) Λ' ε'
    have hE : ∏ k, u k ^ ε k = ∏ k, u' k ^ ε' k := by
      refine prod_zpow_eq φ ε φ' ε' u u' (fun k l e => Units.ext ?_) (fun k l e => Units.ext ?_)
        (fun k l e => Units.ext ?_) hs
      · rw [hu, hu, c k l e]
        exact GlobalTheory.AnVal.JetUniq.jet_uniq S A L x0 g Φ hI n m (φ l) _ _ (e ▸ h.1 k) (h.1 l) _
      · rw [hu', hu', c' k l e]
        exact GlobalTheory.AnVal.JetUniq.jet_uniq S A L x0 g Φ hI n m (φ' l) _ _ (e ▸ h'.1 k) (h'.1 l) _
      · rw [hu, hu', cc k l e]
        exact GlobalTheory.AnVal.JetUniq.jet_uniq S A L x0 g Φ hI n m (φ' l) _ _ (e ▸ h.1 k) (h'.1 l) _
    have r := h.2 j (hT.trans inf_le_left)
    have r' := h'.2 j' (hT.trans inf_le_right)
    rw [hP, hE, ← hP', ← r'] at r
    apply Units.ext
    have r2 := congrArg ((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map
      (homOfLE (le_top : LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j' ≤ ⊤)).op).hom r
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp] at r2
    exact r2
  · have hB : LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j' = ⊥ := by
      rw [eq_bot_iff]
      exact fun p hp => (hW ⟨p, hp⟩).elim
    have : Subsingleton Γ(Sp (Jet ℂ (Fin n × Fin g) m), LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j') := by
      rw [hB]; infer_instance
    exact Units.ext (Subsingleton.elim _ _)

end GlobalTheory.AnVal.JetCorr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiablePolyDeriv
section
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.ThFr

section Deriv

variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] {F : W → ℂ}

theorem differentiable_polyDeriv (hF : ContDiff ℂ (⊤ : ℕ∞) F) (P : MvPolynomial σ ℂ) (u : σ → W) :
    Differentiable ℂ fun y => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u F y := by
  simp only [polyDeriv_eq_of_subset P u F _ subset_rfl, pdTerm_eq_itD]
  exact Differentiable.fun_sum fun m _ => (itD_differentiable hF _).const_mul _

theorem polyDeriv_mul_X (hF : ContDiff ℂ (⊤ : ℕ∞) F) (P : MvPolynomial σ ℂ) (u : σ → W) (l : σ)
    (x : W) : _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (P * X l) u F x = fderiv ℂ (fun y => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u F y) x (u l) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    have h (m : σ →₀ ℕ) : (monomial m c : MvPolynomial σ ℂ) = c • monomial m 1 := by
      simp [smul_monomial]
    rw [X, monomial_mul, mul_one, h, h]
    simp only [polyDeriv_smul, polyDeriv_monomial_one, pdTerm_eq_itD]
    rw [fderiv_const_mul (itD_differentiable hF _ x), ContinuousLinearMap.smul_apply, smul_eq_mul,
      ← itD_cons hF, ← List.map_cons]
    refine congrArg _ (congrFun (ct_itD_perm hF (List.Perm.map u ?_)) x)
    rw [← Multiset.coe_eq_coe, ← Multiset.cons_coe, Multiset.coe_toList, Multiset.coe_toList,
      map_add, Finsupp.toMultiset_single, one_nsmul, add_comm, Multiset.singleton_add]
  | add P Q hP hQ =>
    simp only [add_mul, polyDeriv_add, hP, hQ]
    rw [fderiv_fun_add (differentiable_polyDeriv hF P u x) (differentiable_polyDeriv hF Q u x),
      ContinuousLinearMap.add_apply]

theorem polyDeriv_algHom (hF : ContDiff ℂ (⊤ : ℕ∞) F) (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ)
    (s : σ → ℂ) (j : σ → σ) (hΦ : ∀ l, Φ (X l) = X l + C (s l) * X (j l)) (u : σ → W)
    (P : MvPolynomial σ ℂ) (x : W) :
    _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (Φ P) u F x = _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (fun l => u l + s l • u (j l)) F x := by
  induction P using MvPolynomial.induction_on generalizing x with
  | C a =>
    have h : (C a : MvPolynomial σ ℂ) = a • monomial 0 1 := by simp [smul_eq_C_mul]
    rw [algHom_C, algebraMap_eq, h]
    simp [polyDeriv_smul, polyDeriv_monomial_one, pdTerm_eq_itD, -smul_monomial, -monomial_zero']
  | add P Q hP hQ => simp only [map_add (f := _), polyDeriv_add, hP, hQ]
  | mul_X P l hP =>
    rw [map_mul, hΦ, mul_add, mul_left_comm, C_mul', polyDeriv_add, polyDeriv_smul,
      polyDeriv_mul_X hF, polyDeriv_mul_X hF, polyDeriv_mul_X hF, funext hP]
    simp

end Deriv

section Triangular

variable {J V : Type*} [Fintype J] [DecidableEq J] [AddCommGroup V] [Module ℂ V]

theorem eigen_of_triangular (f : (J → V) → ℂ) (lt : J → J → Prop) (rk : J → ℕ)
    (hrk : ∀ i j, lt i j → rk i < rk j) (d : J → ℕ)
    (hadd : ∀ i j, lt i j → ∀ (s : ℂ) u, f (Function.update u j (u j + s • u i)) = f u)
    (hsc : ∀ j (s : ℂ) u, f (Function.update u j (s • u j)) = s ^ d j * f u)
    (N : J → J → ℂ) (hN : ∀ i j, i ≠ j → ¬ lt i j → N i j = 0) (u : J → V) :
    f (fun j => ∑ i, N i j • u i) = (∏ j, N j j ^ d j) * f u := by
  have hne : ∀ i j, lt i j → i ≠ j := fun i j h e => (hrk i j h).ne (congrArg rk e)
  have one (y : J → V) (j : J) (T : Finset J) (hT : j ∉ T) :
      f (Function.update y j (N j j • y j + ∑ i ∈ T, N i j • y i)) = N j j ^ d j * f y := by
    induction T using Finset.induction_on with
    | empty => simpa using hsc j _ y
    | insert i T hi ih =>
      have hij : i ≠ j := fun e => hT (e ▸ Finset.mem_insert_self _ _)
      rw [Finset.sum_insert hi, ← ih fun h => hT (Finset.mem_insert_of_mem h)]
      by_cases h : lt i j
      · rw [← hadd i j h (N i j) (Function.update y j (N j j • y j + ∑ i ∈ T, N i j • y i)),
          Function.update_idem,
          Function.update_self, Function.update_of_ne hij]
        congr 2
        abel
      · rw [hN i j hij h, zero_smul, zero_add]
  have key (S : Finset J) : f (fun j => if j ∈ S then ∑ i, N i j • u i else u j) =
      (∏ j ∈ S, N j j ^ d j) * f u := by
    induction S using Finset.induction_on_min_value rk with
    | empty => simp
    | insert a S ha hmin ih =>
      rw [Finset.prod_insert ha, mul_assoc, ← ih, ← one _ a (Finset.univ.erase a) (by simp)]
      congr 1
      funext j
      by_cases hj : j = a
      · subst hj
        rw [Function.update_self, if_pos (Finset.mem_insert_self _ _), if_neg ha,
          ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        by_cases h : lt i j
        · rw [if_neg fun hS => (hmin i hS).not_gt (hrk i j h)]
        · rw [hN i j (Finset.ne_of_mem_erase hi) h, zero_smul, zero_smul]
      · simp [Function.update_of_ne hj, hj]
  simpa using key Finset.univ

end Triangular


open Harm in
theorem polyDeriv_triangular {T κ W : Type*} [Fintype T] [Fintype κ] {p q : ℕ}
    [NormedAddCommGroup W] [NormedSpace ℂ W] {F : W → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F)
    {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ} {P : Poly ℂ T p q κ} (hP : P ∈ rowHighest ℂ c c')
    (N : T × (Fin p ⊕ Fin q) → T × (Fin p ⊕ Fin q) → ℂ)
    (hN : ∀ i j, i ≠ j → ¬ (i.1 = j.1 ∧ RowLT i.2 j.2) → N i j = 0) (u : Var T p q κ → W) (x : W) :
    _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (fun l => ∑ i, N i (l.1, l.2.1) • u (i.1, i.2, l.2.2)) F x =
      (∏ j, N j j ^ Sum.elim (partOf (c j.1)) (partOf (c' j.1)) j.2) * _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u F x := by
  classical
  obtain ⟨-, hdeg, hinv⟩ := mem_rowHighest_iff_rowAdd.1 hP
  have h := eigen_of_triangular
    (fun w : T × (Fin p ⊕ Fin q) → κ → W => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (fun l => w (l.1, l.2.1) l.2.2) F x)
    (fun i j => i.1 = j.1 ∧ RowLT i.2 j.2) (fun i => Sum.elim Fin.val Fin.val i.2) ?_
    (fun j => Sum.elim (partOf (c j.1)) (partOf (c' j.1)) j.2) ?_ ?_ N hN
    fun i k => u (i.1, i.2, k)
  · simpa only [Finset.sum_apply, Pi.smul_apply] using h
  · rintro ⟨t, a | a⟩ ⟨t', b | b⟩ ⟨-, h⟩ <;> first | exact h | exact h.elim
  · rintro ⟨t, r⟩ ⟨t', r'⟩ ⟨rfl, h⟩ s w
    conv_rhs => rw [← rowAdd_eq_self_of_forall_int (hinv t r r' h) s]
    rw [polyDeriv_algHom hF _ (fun l => if l.1 = t ∧ l.2.1 = r' then s else 0)
      (fun l => (t, r, l.2.2)) (fun ⟨t', r'', k⟩ => by rw [rowAdd_X]; split_ifs <;> simp)]
    congr 1
    funext ⟨t', r'', k⟩
    by_cases e : t' = t ∧ r'' = r'
    · obtain ⟨rfl, rfl⟩ := e
      simp
    · rw [Function.update_of_ne (by simpa using e), if_neg e]
      simp
  · rintro ⟨t, r⟩ s w
    rw [← polyDeriv_smul_letter P (fun l => if l.1 = t ∧ l.2.1 = r then s else 1) _ fun m hm => ?_]
    · congr 1
      funext ⟨t', r'', k⟩
      by_cases e : t' = t ∧ r'' = r
      · obtain ⟨rfl, rfl⟩ := e
        simp
      · rw [Function.update_of_ne (by simpa using e), if_neg e]
        simp
    · rw [← hdeg t r (mem_support_iff.1 hm), Finsupp.weight_apply, Finsupp.sum,
        ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [rowInd_apply]
      split_ifs with h <;> simp [h]

end GlobalTheory.ThFr
end

