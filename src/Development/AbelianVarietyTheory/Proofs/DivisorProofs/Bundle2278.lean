module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0193
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpacePullbackEigenDeterminantDivisorEqGraded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEvenCubicalValuesNotMemMaximalIdealPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.QuadTend

theorem dickson_fin {J : Type*} (n : ℕ) (f : J → Fin n → ℕ) :
    ∃ F : Finset J, ∀ i, ∃ j ∈ F, f j ≤ f i := by
  classical
  set s : Set (Fin n → ℕ) := Set.range f
  have hpwo : s.IsPWO := Set.isPWO_of_wellQuasiOrderedLE s
  set m : Set (Fin n → ℕ) := {x | Minimal (· ∈ s) x}
  have hm : m.Finite := (setOf_minimal_antichain (· ∈ s)).finite_of_partiallyWellOrderedOn
    (hpwo.mono (fun x hx => hx.prop))
  have hpre : ∀ x ∈ m, ∃ j, f j = x := fun x hx => hx.prop
  rcases isEmpty_or_nonempty J with hJ | hJ
  · exact ⟨∅, fun i => isEmptyElim i⟩
  choose! g hg using hpre
  refine ⟨hm.toFinset.image g, fun i => ?_⟩
  obtain ⟨x, hxi, hx⟩ := hpwo.exists_le_minimal (Set.mem_range_self i)
  exact ⟨g x, Finset.mem_image_of_mem g (hm.mem_toFinset.mpr hx), by rw [hg x hx]; exact hxi⟩

section Cl

variable {G X : Type*} [CommGroup G] [AddCommGroup X] (κ : X → G)

def defect (a b : X) : G := κ (a + b) / (κ a * κ b)

variable {κ}

theorem kappa_zero (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) :
    κ 0 = 1 := by
  have h := hc 0 0 0
  simp only [add_zero] at h
  have h2 : κ 0 * (κ 0 * κ 0 * κ 0) = 1 * (κ 0 * κ 0 * κ 0) := by
    rw [_root_.one_mul]; simpa only [_root_.mul_assoc] using h
  exact mul_right_cancel h2

theorem defect_add_left (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b))
    (a a' b : X) : defect κ (a + a') b = defect κ a b * defect κ a' b := by
  unfold defect
  rw [div_mul_div_comm, div_eq_div_iff_mul_eq_mul]
  have h := hc a a' b
  calc κ (a + a' + b) * (κ a * κ b * (κ a' * κ b)) = (κ (a + a' + b) * κ a * κ a' * κ b) * κ b := by
        simp only [mul_comm, _root_.mul_assoc, _root_.mul_left_comm]
    _ = (κ (a + a') * κ (a + b) * κ (a' + b)) * κ b := by rw [h]
    _ = κ (a + b) * κ (a' + b) * (κ (a + a') * κ b) := by simp only [mul_comm, _root_.mul_assoc, _root_.mul_left_comm]

theorem defect_comm (a b : X) : defect κ a b = defect κ b a := by
  unfold defect; rw [add_comm, _root_.mul_comm]

theorem defect_zero_left (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b))
    (b : X) : defect κ 0 b = 1 := by
  have h := defect_add_left hc 0 0 b
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem defect_neg_left (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b))
    (a b : X) : defect κ (-a) b = (defect κ a b)⁻¹ := by
  have h := defect_add_left hc a (-a) b
  rw [add_neg_cancel, defect_zero_left hc] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem kappa_add (a b : X) : κ (a + b) = κ a * κ b * defect κ a b := by
  unfold defect; rw [mul_div_cancel]

theorem mem_closure_of_gen (hn : ∀ a, κ (-a) = κ a)
    (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b))
    {J : Type*} (e : J → X) (he : AddSubgroup.closure (Set.range e) = ⊤) (a : X) :
    κ a ∈ Subgroup.closure (Set.range (Sum.elim (fun i => κ (e i)) (fun p : J × J => κ (e p.1 + e p.2)))) := by
  set H := Subgroup.closure (Set.range (Sum.elim (fun i => κ (e i)) (fun p : J × J => κ (e p.1 + e p.2))))
  have hk : ∀ i, κ (e i) ∈ H := fun i => Subgroup.subset_closure ⟨Sum.inl i, rfl⟩
  have hg : ∀ i j, defect κ (e i) (e j) ∈ H := fun i j =>
    H.div_mem (Subgroup.subset_closure ⟨Sum.inr (i, j), rfl⟩) (H.mul_mem (hk i) (hk j))
  have mem : ∀ x : X, x ∈ AddSubgroup.closure (Set.range e) := fun x => he ▸ AddSubgroup.mem_top x
  have step1 : ∀ i b, defect κ (e i) b ∈ H := by
    intro i b
    induction mem b using AddSubgroup.closure_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hg i j
    | zero => rw [defect_comm, defect_zero_left hc]; exact H.one_mem
    | add x y _ _ hx hy =>
      rw [defect_comm, defect_add_left hc, defect_comm x, defect_comm y]; exact H.mul_mem hx hy
    | neg x _ hx => rw [defect_comm, defect_neg_left hc, defect_comm]; exact H.inv_mem hx
  have step2 : ∀ a b, defect κ a b ∈ H := by
    intro a b
    induction mem a using AddSubgroup.closure_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact step1 j b
    | zero => rw [defect_zero_left hc]; exact H.one_mem
    | add x y _ _ hx hy => rw [defect_add_left hc]; exact H.mul_mem hx hy
    | neg x _ hx => rw [defect_neg_left hc]; exact H.inv_mem hx
  induction mem a using AddSubgroup.closure_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hk j
  | zero => rw [kappa_zero hc]; exact H.one_mem
  | add x y _ _ hx hy => rw [kappa_add (κ := κ)]; exact H.mul_mem (H.mul_mem hx hy) (step2 x y)
  | neg x _ hx => rw [hn]; exact hx

end Cl

theorem finite_not_mem_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (κ : X → (FractionRing R)ˣ), (∀ a, κ (-a) = κ a) → (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) → (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R _ s) → ∀ n : ℕ, {a | ¬ ∃ s ∈ maximalIdeal R ^ n, (κ a : FractionRing R) = algebraMap R _ s}.Finite := by
  intro R _ _ _ _ _ X _ _ κ hneg hcube hm n
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top (R := ℤ) (M := X))
  have hcl : AddSubgroup.closure (Set.range (fun x : S => (x : X))) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, Subtype.range_coe_subtype, Finset.setOf_mem, hS]; rfl
  have hΓ := mem_closure_of_gen hneg hcube (fun x : S => (x : X)) hcl
  set gg := Sum.elim (fun i : S => κ (i : X)) (fun p : S × S => κ ((p.1 : X) + p.2))
  set Γ := Subgroup.closure (Set.range gg)
  obtain ⟨s, v, hv1, hv2⟩ := _root_.GlobalTheory.HtVal.exists_vals R (S ⊕ (S × S)) gg
  set K := FractionRing R
  let w : Kˣ → Fin s → ℤ := fun x i => Multiplicative.toAdd (v i x)
  have wmul : ∀ x y i, w (x * y) i = w x i + w y i := fun x y i => by simp [w]
  have winv : ∀ x i, w x⁻¹ i = - w x i := fun x i => by simp [w]
  have wone : ∀ i, w 1 i = 0 := fun i => by simp [w]
  have hk0 := kappa_zero hcube
  have wκ : ∀ a i, 0 ≤ w (κ a) i := by
    intro a i
    by_cases ha : a = 0
    · rw [ha, hk0, wone]
    · obtain ⟨t, -, ht⟩ := hm a ha
      exact hv1 i (κ a) t ht

  have unitOf : ∀ x ∈ Γ, (∀ i, w x i = 0) → ∃ r : R, IsUnit r ∧ (x : K) = algebraMap R K r := by
    intro x hx h0
    obtain ⟨r, hr⟩ := hv2 x hx (fun i => (h0 i).ge)
    obtain ⟨r', hr'⟩ := hv2 x⁻¹ (Γ.inv_mem hx) (fun i => show 0 ≤ w x⁻¹ i by rw [winv, h0 i, neg_zero])
    have hrr : r * r' = 1 := IsFractionRing.injective R K (by
      rw [map_mul, ← hr, ← hr', map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
    exact ⟨r, ⟨Units.mkOfMulEqOne r r' hrr, rfl⟩, hr⟩
  let q : X → ℤ := fun a => ∑ i, w (κ a) i
  have hqneg : ∀ a, q (-a) = q a := fun a => by simp only [q, hneg]
  have hqcube : ∀ a a' b, q (a + a' + b) + q a + q a' + q b = q (a + a') + q (a + b) + q (a' + b) := by
    intro a a' b
    have h := congrArg (fun x => ∑ i, w x i) (hcube a a' b)
    simp only [wmul, Finset.sum_add_distrib] at h
    simpa only [q] using h
  have hqpos : ∀ a, a ≠ 0 → 1 ≤ q a := by
    intro a ha
    obtain ⟨t, htm, ht⟩ := hm a ha
    by_contra hlt
    have hsum0 : q a = 0 := le_antisymm (by omega) (Finset.sum_nonneg fun i _ => wκ a i)
    have hall : ∀ i, w (κ a) i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => wκ a i)).mp hsum0 i (Finset.mem_univ i)
    obtain ⟨r, hru, hr⟩ := unitOf (κ a) (hΓ a) hall
    have : t = r := IsFractionRing.injective R K (ht.symm.trans hr)
    exact (IsLocalRing.mem_maximalIdeal t).mp htm (this ▸ hru)

  let P := {x : Kˣ // x ∈ Γ ∧ (∀ i, 0 ≤ w x i) ∧ 0 < ∑ i, w x i}
  obtain ⟨F, hF⟩ := dickson_fin s (fun x : P => fun i => (w x.1 i).toNat)
  set C : ℤ := 1 + ∑ j ∈ F, ∑ i, w j.1 i
  have hC : ∀ j ∈ F, ∑ i, w j.1 i + 1 ≤ C := by
    intro j hj
    have := Finset.single_le_sum (f := fun j : P => ∑ i, w j.1 i)
      (fun j _ => Finset.sum_nonneg fun i _ => j.2.2.1 i) hj
    omega
  have hC1 : 1 ≤ C := by
    have := Finset.sum_nonneg (s := F) (f := fun j : P => ∑ i, w j.1 i) (fun j _ => Finset.sum_nonneg fun i _ => j.2.2.1 i)
    simp only [C]; omega
  have hPm : ∀ j : P, ∃ t ∈ maximalIdeal R, (j.1 : K) = algebraMap R K t := by
    intro j
    obtain ⟨t, ht⟩ := hv2 j.1 j.2.1 j.2.2.1
    refine ⟨t, ?_, ht⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨u, rfl⟩ := hu
    have hinv : ((j.1⁻¹ : Kˣ) : K) = algebraMap R K (u⁻¹ : Rˣ) := by
      rw [Units.val_inv_eq_inv_val, ht]; symm; apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, Units.inv_mul, map_one]
    have hle : ∀ i, w j.1 i ≤ 0 := fun i => by
      have := hv1 i j.1⁻¹ _ hinv
      have h2 := winv j.1 i
      simp only [w] at h2 ⊢; omega
    have := j.2.2.2
    have := Finset.sum_nonpos (s := Finset.univ) (fun i _ => hle i)
    omega
  have key : ∀ k : ℕ, ∀ x ∈ Γ, (∀ i, 0 ≤ w x i) → C * k ≤ ∑ i, w x i →
      ∃ t ∈ maximalIdeal R ^ k, (x : K) = algebraMap R K t := by
    intro k
    induction k with
    | zero =>
      intro x hx h0 _
      obtain ⟨t, ht⟩ := hv2 x hx h0
      exact ⟨t, by simp, ht⟩
    | succ k ih =>
      intro x hx h0 hsum
      have hpos : 0 < ∑ i, w x i := by push_cast at hsum; nlinarith
      obtain ⟨j, hjF, hjle⟩ := hF ⟨x, hx, h0, hpos⟩
      have hle : ∀ i, w j.1 i ≤ w x i := by
        intro i
        have h1 := hjle i
        have h2 := j.2.2.1 i
        have h3 := h0 i
        simp only at h1
        omega
      have hjC := hC j hjF
      obtain ⟨t', ht'm, ht'⟩ := ih (x * j.1⁻¹) (Γ.mul_mem hx (Γ.inv_mem j.2.1))
        (fun i => by rw [wmul, winv]; linarith [hle i])
        (by
          simp only [wmul, winv, Finset.sum_add_distrib, Finset.sum_neg_distrib]
          push_cast at hsum ⊢
          nlinarith)
      obtain ⟨t, htm, ht⟩ := hPm j
      refine ⟨t' * t, ?_, ?_⟩
      · rw [pow_succ]; exact Ideal.mul_mem_mul ht'm htm
      · rw [map_mul, ← ht', ← ht, ← Units.val_mul, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
  apply (_root_.GlobalTheory.posquad_finite X q hqneg hqcube hqpos (C * n)).subset
  intro a ha
  by_contra hlt
  exact ha (key n (κ a) (hΓ a) (wκ a) (le_of_lt (not_le.mp hlt)))

end GlobalTheory.QuadTend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsPosCombinationDefiniteSum
section
open GlobalTheory.PolFan GlobalTheory.LocM

noncomputable section

namespace GlobalTheory.Poinc.MinSysLat

theorem finite_of_pos_lat {Y : Type} [AddCommGroup Y] {n : ℕ} (eb : Y ≃ₗ[ℤ] (Fin n → ℤ))
    (G : LinearMap.BilinForm ℤ Y) (hs : ∀ a b, G a b = G b a)
    (hn : ∀ x, 0 ≤ G x x) (hp : ∀ x, x ≠ 0 → 0 < G x x) (B : ℤ) : {x | G x x ≤ B}.Finite := by
  set G' : LinearMap.BilinForm ℤ (Fin n → ℤ) :=
    LinearMap.compl₁₂ G eb.symm.toLinearMap eb.symm.toLinearMap with hG'
  have happ : ∀ a b, G' a b = G (eb.symm a) (eb.symm b) := fun a b => rfl
  have h := GlobalTheory.Poinc.MinSys.finite_of_pos G' (fun a b => by rw [happ, happ, hs])
    (fun x => by rw [happ]; exact hn _)
    (fun x hx => by rw [happ]; exact hp _ (by simpa using hx)) B
  refine (h.preimage eb.injective.injOn).subset fun x hx => ?_
  simp only [Set.mem_preimage, Set.mem_setOf_eq, happ, LinearEquiv.symm_apply_apply]
  exact hx

theorem finite_minimiser_systems_lat : ∀ (Y : Type) [AddCommGroup Y] (n N : ℕ) [NeZero N] (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ Y), (∀ j x y, γ j x y = γ j y x) → (∀ j y, 0 ≤ γ j y y) → (∀ x, x ≠ 0 → 0 < ∑ j, γ j x x) → ∃ S : Finset ((Fin n → ZMod N) → Y), ∀ (b : LinearMap.BilinForm ℤ Y) (k : ℕ) (cf : Fin m → ℕ), 0 < k → (∀ j, 0 < cf j) → k • b = ∑ j, cf j • γ j → ∀ μ : (Fin n → ZMod N) → Y, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → μ ∈ S := by
  intro Y _ n N _ eb m γ hsym hnn hdef
  classical
  set G : LinearMap.BilinForm ℤ Y := ∑ j, γ j with hG
  have hGapp : ∀ a b, G a b = ∑ j, γ j a b := fun a b => by simp [hG, LinearMap.sum_apply]
  have hGsym : ∀ a b, G a b = G b a := fun a b => by simp only [hGapp, hsym _ a b]
  have hGnn : ∀ y, 0 ≤ G y y := fun y => by rw [hGapp]; exact Finset.sum_nonneg fun j _ => hnn j y
  have hGpos : ∀ x, x ≠ 0 → 0 < G x x := fun x hx => by rw [hGapp]; exact hdef x hx
  let T : (Fin n → ZMod N) → Type := fun c =>
    {α : Y // ∀ i, ((eb α i : ℤ) : ZMod N) = c i}
  have hD : ∀ c, ∃ F : Finset (T c), ∀ α : T c, ∃ β ∈ F,
      (fun j => (γ j β.1 β.1).toNat) ≤ (fun j => (γ j α.1 α.1).toNat) :=
    fun c => GlobalTheory.dickson_finite_below_every m (fun (α : T c) j => (γ j α.1 α.1).toNat)
  choose F hF using hD
  let Bd : (Fin n → ZMod N) → ℤ := fun c => ∑ β ∈ F c, G β.1 β.1
  have hfin : {μ : (Fin n → ZMod N) → Y | ∀ c, μ c ∈ {α | G α α ≤ Bd c}}.Finite :=
    Set.Finite.pi' fun c => finite_of_pos_lat eb G hGsym hGnn hGpos (Bd c)
  refine ⟨hfin.toFinset, fun b k cf hk hcf hkb μ hμ hmin => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  intro c
  obtain ⟨β, hβF, hβ⟩ := hF c ⟨μ c, hμ c⟩
  have hle : ∀ j, γ j β.1 β.1 ≤ γ j (μ c) (μ c) := fun j => by
    have h1 : (γ j β.1 β.1).toNat ≤ (γ j (μ c) (μ c)).toNat := hβ j
    have := hnn j β.1
    have := hnn j (μ c)
    omega
  have hkq : ∀ α, (k : ℤ) * b α α = ∑ j, (cf j : ℤ) * γ j α α := fun α => by
    have := congrArg (fun f : LinearMap.BilinForm ℤ Y => f α α) hkb
    simpa [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul] using this
  have h2 : ∑ j, (cf j : ℤ) * γ j (μ c) (μ c) ≤ ∑ j, (cf j : ℤ) * γ j β.1 β.1 := by
    rw [← hkq, ← hkq]
    exact mul_le_mul_of_nonneg_left (hmin c β.1 β.2) (by positivity)
  have h3 : ∀ j, γ j (μ c) (μ c) - γ j β.1 β.1 ≤
      (cf j : ℤ) * γ j (μ c) (μ c) - (cf j : ℤ) * γ j β.1 β.1 := fun j => by
    have h4 := hle j
    have h5 : (1 : ℤ) ≤ cf j := by exact_mod_cast hcf j
    nlinarith
  have h6 : ∑ j, γ j (μ c) (μ c) ≤ ∑ j, γ j β.1 β.1 := by
    have h7 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h3 j
    simp only [Finset.sum_sub_distrib] at h7
    linarith
  have h8 : G β.1 β.1 ≤ Bd c :=
    Finset.single_le_sum (f := fun β : T c => G β.1 β.1)
      (fun β _ => hGnn β.1) hβF
  rw [hGapp] at h8 ⊢
  linarith

end GlobalTheory.Poinc.MinSysLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusKernelQuotientLePowCotangent
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.FrobKerDim

theorem finrank_quot_frobKerIdeal_le : ∀ (q : ℕ) (K H : Type) [Field K] [CommRing H] [Bialgebra K H]
    [Module.Finite K H], 0 < q →
    Module.finrank K (H ⧸ frobKerIdeal q K H) ≤ q ^ Module.finrank K (Cot K H) := by
  intro q K H _ _ _ _ hq
  classical
  set J := frobKerIdeal q K H with hJ
  set ε := Bialgebra.counitAlgHom K H with hε
  set mk := Ideal.Quotient.mkₐ K J with hmk
  have hJI : ∀ a ∈ J, ε a = 0 := fun a ha => frobKerIdeal_le_augIdeal hq.ne' K H ha
  set εQ : (H ⧸ J) →ₐ[K] K := Ideal.Quotient.liftₐ J ε hJI with hεQ
  have hεQmk : ∀ a, εQ (mk a) = ε a := fun a => rfl
  have hmks : Function.Surjective mk := Ideal.Quotient.mkₐ_surjective K J
  haveI hfinQ : Module.Finite K (H ⧸ J) := Module.Finite.of_surjective mk.toLinearMap hmks
  haveI : IsNoetherianRing (H ⧸ J) := isNoetherian_of_tower K inferInstance

  have hkerQ : ∀ z ∈ RingHom.ker εQ, ∃ a ∈ RingHom.ker ε, mk a = z := by
    intro z hz
    obtain ⟨a, rfl⟩ := hmks z
    refine ⟨a, ?_, rfl⟩
    rw [RingHom.mem_ker] at hz ⊢
    rw [← hεQmk]; exact hz
  have hpowQ : ∀ z ∈ RingHom.ker εQ, z ^ q = 0 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hkerQ z hz
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal ha)
  have hnil : IsNilpotent (RingHom.ker εQ) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro f hf
    exact ⟨q, hpowQ f hf⟩

  haveI : Module.Finite K (AugCot ε) := Module.Finite.of_surjective _ (AugCot.d_surjective ε)
  set d := Module.finrank K (AugCot ε) with hd
  let b := Module.finBasis K (AugCot ε)
  choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)
  have hsum : ∀ l : Fin d → K, AugCot.d ε (∑ i, l i • (x i : H)) = ∑ i, l i • b i := by
    intro l
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, hx]
  have hmem : ∀ l : Fin d → K, (∑ i, l i • (x i : H)) ∈ RingHom.ker ε := by
    intro l
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (x i).2
  have hspanH : ∀ a ∈ RingHom.ker ε, ∃ l : Fin d → K, a - ∑ i, l i • (x i : H) ∈ RingHom.ker ε ^ 2 := by
    intro a ha
    refine ⟨b.repr (AugCot.d ε a), ?_⟩
    have h1 : AugCot.d ε (a - ∑ i, b.repr (AugCot.d ε a) i • (x i : H)) = 0 := by
      rw [map_sub, hsum, b.sum_repr, sub_self]
    rwa [AugCot.d_of_mem _ (sub_mem ha (hmem _)), Ideal.toCotangent_eq_zero] at h1
  let y : Fin d → H ⧸ J := fun i => mk (x i)
  have hy : ∀ i, y i ∈ RingHom.ker εQ := fun i => by
    rw [RingHom.mem_ker, hεQmk]; exact (x i).2
  have hmapI : Ideal.map mk (RingHom.ker ε) ≤ RingHom.ker εQ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact ha
  have hspan : ∀ z ∈ RingHom.ker εQ, ∃ l : Fin d → K, z - ∑ i, l i • y i ∈ RingHom.ker εQ ^ 2 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hkerQ z hz
    obtain ⟨l, hl⟩ := hspanH a ha
    refine ⟨l, ?_⟩
    have h1 : mk (a - ∑ i, l i • (x i : H)) ∈ Ideal.map mk (RingHom.ker ε ^ 2) :=
      Ideal.mem_map_of_mem _ hl
    rw [Ideal.map_pow] at h1
    have h2 := Ideal.pow_right_mono hmapI 2 h1
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [y, map_sub, map_sum, map_smul] using h2
  have hsurj := GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent εQ hnil y hy hspan
  have hyq : ∀ i, y i ^ q = 0 := fun i => hpowQ _ (hy i)

  let mon : (Fin d → Fin q) → H ⧸ J := fun e => ∏ i, y i ^ (e i : ℕ)
  have htop : Submodule.span K (Set.range mon) = ⊤ := by
    have hall : ∀ P : MvPolynomial (Fin d) K, MvPolynomial.aeval y P ∈ Submodule.span K (Set.range mon) := by
      intro P
      induction P using MvPolynomial.induction_on' with
      | monomial u a =>
        rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
          ← Algebra.smul_def]
        refine Submodule.smul_mem _ _ ?_
        by_cases h : ∀ i, u i < q
        · exact Submodule.subset_span ⟨fun i => ⟨u i, h i⟩, rfl⟩
        · push_neg at h
          obtain ⟨i, hi⟩ := h
          have h0 : y i ^ u i = 0 := pow_eq_zero_of_le hi (hyq i)
          rw [Finset.prod_eq_zero (i := i) (Finset.mem_univ i) h0]
          exact Submodule.zero_mem _
      | add P Q hP hQ => rw [map_add (f := _)]; exact Submodule.add_mem _ hP hQ
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨P, rfl⟩ := hsurj z
    exact hall P
  have h1 := finrank_range_le_card (R := K) (b := mon)
  rw [Set.finrank, htop, finrank_top] at h1
  simpa [Fintype.card_fun, Fintype.card_fin] using h1

end GlobalTheory.FrobKerDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.FlagFamily

open _root_.CategoryTheory.Limits

theorem isProjOver_pullback_over {k : Type} [CommRing k] {B X Y : Scheme.{0}} {q : B ⟶ Sp k} (hq : IsProjOver q)
    {f : X ⟶ B} {g : Y ⟶ B} (hf : IsProjOver (f ≫ q)) (hg : IsProjOver (g ≫ q)) :
    IsProjOver (pullback.fst f g ≫ f ≫ q) := by
  have : IsProper q := projProper k B q hq
  have h := ProjSpace.isProjOver_comp_of_isClosedImmersion (pullback.mapDesc f g q)
    (ProjSpace.isProjOver_pullback hf hg)
  rwa [pullback.lift_fst_assoc, Category.comp_id] at h

end GlobalTheory.FlagFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpacePullbackEigenDeterminantDivisorEqGradedStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

open GlobalTheory.EigDivPic GlobalTheory.ShFam

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagSpacePullback_eigenDeterminantDivisor_eq_gradedLines : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)) (a : (E →+* ℂ) → ℤ) (D : CartierDiv (X₀ TF.Y Z)), (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ s₀ TF.Y Z = spMap φ₀ → (∀ (x : X₀ TF.Y Z) (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι)) (fK : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)), (X₀ TF.Y Z).fromSpecStalk x ≫ s₀ TF.Y Z = spMap φ → (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) (algebraMap _ (X₀ TF.Y Z).functionField) fK → D.IsEqn x (∏ τ, (fK.isUnit_det_co f₀ τ).unit ^ (-a τ))) → CechPic.pull (π₀ TF.X Z) (cls (toLB D) (isLB_toLB D)) = cls (LL₀ TF.X Z fun ix => ix.elim 0 fun x => a x.1) (LB.isLB_pull (TF.X.F.isLB_LL _) _) := by
  intro E _ _ _ H Dw l Xo c TF Z _ φ₀ f₀ a D h₀ hD
  have hL := pull_isLB (isLB_toLB D) (π₀ TF.X Z)
  have hM : (LL₀ TF.X Z fun ix => ix.elim 0 fun x => a x.1).IsLB := LB.isLB_pull (TF.X.F.isLB_LL _) _
  rw [← cls_pull (isLB_toLB D) _ hL, cls_eq_iff]
  refine exists_gen_of_rel (LB.isLB_div hM hL) (fun p => IsQuot TF Z f₀ a (p.1 PUnit.unit) (p.2 PUnit.unit).1.2)
    (fun p y hy => exists_isQuot TF Z f₀ a D h₀ hD _ _ _ (p.2 PUnit.unit).2.2 _ (fun _ h => mem_pull.1 (inf_le_left (a := (LL₀ TF.X Z fun ix => ix.elim 0 fun x => a x.1).U p.1)
        (b := ((toLB D).pull (π₀ TF.X Z)).U p.2) h))
      (fun _ h => mem_pull.1 (inf_le_right (a := (LL₀ TF.X Z fun ix => ix.elim 0 fun x => a x.1).U p.1)
        (b := ((toLB D).pull (π₀ TF.X Z)).U p.2) h)) y hy) fun p q y u u' hp hq h h' => ?_
  have h1 : inc₀ TF.X Z y ∈ TF.X.F.U (p.1 PUnit.unit) ⊓ TF.X.F.U (q.1 PUnit.unit) := ⟨mem_pull.1 hp.1, mem_pull.1 hq.1⟩
  have h2 : π₀ TF.X Z y ∈ (toLB D).U (p.2 PUnit.unit) ⊓ (toLB D).U (q.2 PUnit.unit) := ⟨mem_pull.1 hp.2, mem_pull.1 hq.2⟩
  rw [gm_div' _ _ (𝟙 _) y p q hp hq, gm_pull_g _ _ (𝟙 _) y _ _ hp.1 hq.1, gm_pull_g _ _ (𝟙 _) y _ _ hp.2 hq.2,
    Category.id_comp, Category.id_comp]
  refine (IsQuot.compare TF Z f₀ a h h' (top_le_stalk_preimage y _ h1) _ (gm_val_ev _ y _ h1 _ _)
    (Units.map ((X₀ TF.Y Z).presheaf.germ _ _ h2).hom.toMonoidHom ((toLB D).g _ _)) (Units.ext ?_)).trans ?_
  · rw [Units.val_div_eq_div_val, ← fnOf_toLB_g _ _ (gen_mem h2)]
    exact algebraMap_germ h2 _
  · congr 3
    exact Units.ext (gm_val_stalk _ y _ h2 _).symm

end

