module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PointsFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsSpanEntMonApproxOfMemWtPart
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop
open UpperTheory.V.U3 hiding emb_apply

private theorem one_mem_entMon {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) :
    (1 : R) ∈ entMon r 0 :=
  ⟨[], rfl, rfl⟩

private theorem mul_mem_entMon {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) {i j : ℤ} {a b : R}
    (ha : a ∈ entMon r i) (hb : b ∈ entMon r j) : a * b ∈ entMon r (i + j) := by
  obtain ⟨L, rfl, rfl⟩ := ha
  obtain ⟨M, rfl, rfl⟩ := hb
  exact ⟨L ++ M, by simp, by simp⟩

private theorem mat_mem_entMon {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (g : G) (a b : Fin 3) :
    (r g).mat a b ∈ entMon r (wt1 a - wt1 b) :=
  ⟨[(g, a, b)], by simp [wt], by simp⟩

private theorem theta_left {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (c : G)
    (h1 : (r c).right = -1) (h2 : (r c).mat = 1) (g : G) :
    (theta (r g).left : Matrix (Fin 3) (Fin 3) R) = (r (c * g)).mat := by
  have h : (r c).left = 1 := Units.ext h2
  rw [map_mul, GG.mat, SemidirectProduct.mul_left, h, h1, one_mul, sgnAct_neg_one]

private theorem emb_mem {O G R : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R]
    (r : G →* GG (m := 3) (R := R)) (c : G)
    (h1 : (r c).right = -1) (h2 : (r c).mat = 1) (g : G) (a b : Fin 3 ⊕ Fin 3) :
    emb (r g) a b ∈ Submodule.span O (entMon r (wt6 a - wt6 b)) := by
  rw [_root_.UpperTheory.V.U3.Mop.emb_apply, theta_left r c h1 h2]
  split_ifs <;> rcases a with a | a <;> rcases b with b | b <;>
    first
    | exact Submodule.zero_mem _
    | exact Submodule.subset_span (mat_mem_entMon r _ a b)

theorem UpperTheory.exists_span_entMon_approx_of_mem_wtPart :
    ∀ {O G R σ : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R] [Finite σ]
      (η : G →* ℤˣ) (Ψ : G →* Oˣ) (r : G →* GG (m := 3) (R := R)) (c : G),
          (r c).right = -1 → (r c).mat = 1 → ∀ (w : σ → ℤ) (Φ : MvPowerSeries σ O →ₐ[O] R) (m : Ideal R), (∀ s, Φ (MvPowerSeries.X s) ∈ m) →
          (∀ s, ∃ g a b, w s = wt6 a - wt6 b ∧ Φ (MvPowerSeries.X s) =
            emb (r g) a b - algebraMap O R (emb (r0 η Ψ g) a b)) →
          ∀ j, ∀ F ∈ wtPart O w j, ∀ n : ℕ, ∃ y ∈ Submodule.span O (entMon r j), Φ F - y ∈ m ^ n := by
  intro O G R σ _ _ _ _ _ η Ψ r c h1 h2 w Φ m hm hX j F hF n
  refine approx w Φ m (fun j => Submodule.span O (entMon r j))
    (Submodule.subset_span (one_mem_entMon r)) ?_ hm ?_ j F hF n
  · intro i j a ha b hb
    have h := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact mul_mem_entMon r hx hy
  · intro s
    obtain ⟨g, a, b, hw, he⟩ := hX s
    rw [hw, he]
    refine Submodule.sub_mem _ (emb_mem r c h1 h2 g a b) ?_
    by_cases h : wt6 a = wt6 b
    · rw [h, sub_self, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (one_mem_entMon r))
    · rw [unitaryEmbedding_residualRep_eq_zero_of_weight_ne η Ψ g a b h, map_zero]
      exact Submodule.zero_mem _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsSurjectionUnivNormCondKerSpanNEq
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop
open UpperTheory.V.U3 hiding emb_apply

private theorem mat_symm {R : Type} [CommRing R] (x : GG (m := 3) (R := R))
    (h2 : x * x = 1) (hx : x.right = -1) :
    x.mat = Jmat (R := R) 3 * x.matᵀ * Jmat (R := R) 3 := by
  have h : x.left * theta x.left = 1 := by
    have := congrArg SemidirectProduct.left h2
    rwa [SemidirectProduct.mul_left, hx, sgnAct_neg_one] at this
  have h' : x.left = (theta x.left)⁻¹ := eq_inv_of_mul_eq_one_left h
  have := theta_inv_val x.left
  rw [← h'] at this
  exact this

private theorem norm_iff {G R : Type} [Group G] [CommRing R] (c g₁ : G)
    (r : G →* GG (m := 3) (R := R)) (hc : c * c = 1)
    (hr : (r c).right = -1) : Normalised c g₁ r ↔ ∀ i, nEq c g₁ r i = 0 := by
  have hs := mat_symm (r c) (by rw [← map_mul, hc, map_one]) hr
  have hsym : ∀ i j, (r c).mat i j = (r c).mat j.rev i.rev := by
    intro i j
    conv_lhs => rw [hs]
    fin_cases j <;> simp [Matrix.mul_apply, Jmat, Fin.sum_univ_three]
  constructor
  · rintro ⟨h1, h2, h3⟩ i
    fin_cases i <;> simp [nEq, h1, h2, h3]
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    have h6 := h 6
    have h7 := h 7
    simp [nEq, sub_eq_zero] at h0 h1 h2 h3 h4 h5 h6 h7
    have e12 : (r c).mat 1 2 = (r c).mat 0 1 := hsym 1 2
    have e21 : (r c).mat 2 1 = (r c).mat 1 0 := hsym 2 1
    have e22 : (r c).mat 2 2 = (r c).mat 0 0 := hsym 2 2
    refine ⟨?_, h6, h7⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0, h1, h2, h3, h4, h5, e12, e21, e22]

private theorem nEq_map {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} (c g₁ : Γ) {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R']
    [Algebra O R'] [IsCO O R'] (r : GLift O η Ψ R) (f : R →ₐ[O] R') (i : Fin 8) :
    nEq c g₁ (r.map f).hom i = f (nEq c g₁ r.hom i) := by
  have hm : ∀ g, ((r.map f).hom g).mat = (r.hom g).mat.map f := fun g => GG.map_mat (f : R →+* R') (r.hom g)
  fin_cases i <;> simp [nEq, zmat, hm, map_sub, map_one]

private theorem ext_lemma {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (a b : GLift O η Ψ R) (h : ∀ x, (a.hom x).mat = (b.hom x).mat) : a = b := by
  apply GLift.ext
  apply MonoidHom.ext
  intro x
  apply SemidirectProduct.ext
  · exact Units.ext (h x)
  · rw [a.hasMult x, b.hasMult x]

private theorem gLift_map_hom_mat_eq_map {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R']
    [Algebra O R'] [IsCO O R'] (r : GLift O η Ψ R) (f : R →ₐ[O] R') (x : Γ) :
    ((r.map f).hom x).mat = (r.hom x).mat.map f :=
  GG.map_mat (f : R →+* R') (r.hom x)

private theorem comp_lemma_3 {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R R' R'' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R']
    [Algebra O R'] [IsCO O R'] [CommRing R''] [Algebra O R''] [IsCO O R''] (r : GLift O η Ψ R)
    (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') : r.map (g.comp f) = (r.map f).map g := by
  apply ext_lemma
  intro x
  rw [gLift_map_hom_mat_eq_map, gLift_map_hom_mat_eq_map, gLift_map_hom_mat_eq_map]
  ext i j
  simp

private theorem gLift_map_id {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (r : GLift O η Ψ R) : r.map (AlgHom.id O R) = r := by
  apply ext_lemma
  intro x
  rw [gLift_map_hom_mat_eq_map]
  ext i j
  simp

theorem UpperTheory.exists_surjection_univ_normCond_ker_span_nEq :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {P : GCond O η Ψ} (c g₁ : Γ)
          (B : Univ P) (S : Univ (NormCond c g₁ P)), c * c = 1 → η c = -1 →
          ∃ p : B.R →ₐ[O] S.R, Function.Surjective p ∧ B.r.map p = S.r ∧ RingHom.ker p = Ideal.span (Set.range (nEq c g₁ B.r.hom)) := by
  intro O _ _ Γ _ _ η Ψ P c g₁ B S hc hη
  have hr : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r : GLift O η Ψ R),
      (r.hom c).right = -1 := fun R _ _ _ r => by rw [r.hasMult c, hη]
  have hNS : NormCond c g₁ P S.R S.r := by
    have h := (S.rep S.R).1 (AlgHom.id O S.R)
    rwa [gLift_map_id] at h
  obtain ⟨p, hp, -⟩ := (B.rep S.R).2 S.r hNS.2
  have hI : Ideal.span (Set.range (nEq c g₁ B.r.hom)) ≤ RingHom.ker p := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    show p (nEq c g₁ B.r.hom i) = 0
    rw [← nEq_map, hp]
    exact (norm_iff c g₁ S.r.hom hc (hr _ S.r)).1 hNS.1 i
  set I := Ideal.span (Set.range (nEq c g₁ B.r.hom)) with hIdef
  haveI : Nontrivial (B.R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (RingHom.ker_ne_top _) hI)
  haveI : IsCO O (B.R ⧸ I) := co_quot O B.R (B.R ⧸ I) (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ_surjective O I)
  have hNq : NormCond c g₁ P (B.R ⧸ I) (B.r.map (Ideal.Quotient.mkₐ O I)) := by
    refine ⟨(norm_iff c g₁ _ hc (hr _ _)).2 (fun i => ?_), (B.rep _).1 _⟩
    rw [nEq_map]
    show Ideal.Quotient.mk I _ = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
  obtain ⟨s, hs, -⟩ := (S.rep (B.R ⧸ I)).2 _ hNq
  have hsp : s.comp p = Ideal.Quotient.mkₐ O I := by
    obtain ⟨u, -, hu⟩ := (B.rep (B.R ⧸ I)).2 _ hNq.2
    have e1 := hu (s.comp p) (by
      show GLift.map (s.comp p) B.r = _
      rw [comp_lemma_3, hp, hs])
    have e2 := hu (Ideal.Quotient.mkₐ O I) rfl
    rw [e1, e2]
  have hker : RingHom.ker p = I := by
    refine le_antisymm (fun x hx => ?_) hI
    have h0 : Ideal.Quotient.mkₐ O I x = 0 := by
      rw [← hsp, AlgHom.comp_apply, RingHom.mem_ker.1 hx, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.1 h0
  have hI' : ∀ a ∈ I, p a = 0 := fun a ha => RingHom.mem_ker.1 (hI ha)
  let p' := Ideal.Quotient.liftₐ I p hI'
  have hp'q : ∀ z, p' (Ideal.Quotient.mkₐ O I z) = p z := fun z => by
    show Ideal.Quotient.lift I (p : B.R →+* S.R) hI' (Ideal.Quotient.mk I z) = p z
    exact Ideal.Quotient.lift_mk I _ _
  have hpq : p'.comp (Ideal.Quotient.mkₐ O I) = p := AlgHom.ext hp'q
  have hid : p'.comp s = AlgHom.id O S.R := by
    obtain ⟨u, -, hu⟩ := (S.rep S.R).2 S.r hNS
    have e1 := hu (p'.comp s) (by
      show GLift.map (p'.comp s) S.r = S.r
      rw [comp_lemma_3, hs, ← comp_lemma_3, hpq, hp])
    have e2 := hu (AlgHom.id O S.R) (gLift_map_id _)
    rw [e1, e2]
  refine ⟨p, fun y => ?_, hp, hker⟩
  obtain ⟨z, hz⟩ := Ideal.Quotient.mkₐ_surjective O I (s y)
  refine ⟨z, ?_⟩
  rw [← hp'q, hz]
  exact congrArg (fun f => f y) hid
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsTorusTwistEqLocalPointOfWeightedPres
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop
open UpperTheory.V.U3 hiding emb_apply

open Polynomial in
private theorem pts_int {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have halg : IsIntegral ℚ_[l] x := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) x).isIntegral
  have hmon : (minpoly ℚ_[l] x).Monic := minpoly.monic halg
  have hn : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [hn, spectralValue_le_one_iff hmon]
  constructor
  · intro hx n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hx, Polynomial.coeff_map]
    exact PadicInt.norm_le_one ((minpoly ℤ_[l] x).coeff n)
  · intro h
    have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hmon
    refine ⟨q, hqm, ?_⟩
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l), ← Polynomial.eval₂_map, hq,
      ← Polynomial.aeval_def]
    exact minpoly.aeval ℚ_[l] x

private theorem pts_unit {B K : Type} [CommRing B] [Field K] [Algebra B K] (hi : Function.Injective (algebraMap B K))
    (b : B) (h0 : algebraMap B K b ≠ 0) (h : IsIntegral B (algebraMap B K b)⁻¹) : IsUnit b := by
  classical
  obtain ⟨p, hpm, hp⟩ := h
  set y := (algebraMap B K b)⁻¹ with hy
  have hy0 : y ≠ 0 := inv_ne_zero h0
  letI : Invertible y := invertibleOfNonzero hy0
  have hrev := Polynomial.eval₂_reverse_mul_pow (algebraMap B K) y p
  rw [hp, invOf_eq_inv, hy, inv_inv] at hrev
  have hq : Polynomial.eval₂ (algebraMap B K) (algebraMap B K b) p.reverse = 0 :=
    (mul_eq_zero.mp hrev).resolve_right (pow_ne_zero _ (inv_ne_zero h0))
  rw [Polynomial.eval₂_at_apply] at hq
  have hq' : Polynomial.eval b p.reverse = 0 := hi (by rw [hq, map_zero])
  obtain ⟨r, hr⟩ := Polynomial.X_dvd_sub_C (p := p.reverse)
  have he := congrArg (Polynomial.eval b) hr
  rw [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.coeff_zero_reverse, hpm.leadingCoeff, hq',
    Polynomial.eval_mul, Polynomial.eval_X] at he
  have h1 : b * -Polynomial.eval b r = 1 := by
    rw [mul_neg, ← he]
    ring
  exact ⟨⟨b, _, h1, (mul_comm _ _).trans h1⟩, rfl⟩

private theorem automorphic_points_exist {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O ℤ R) (h : W.HasOrigin)
    (s : W.σ) : W.z s ∈ maximalIdeal R := mem_max_of_zero (W.origin h) (origin_presentation_var_eq_zero W h s)

private theorem pts_sur {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] [Field K] [Algebra O K]
    (f : R →ₐ[O] K) (x : R) (h0 : f x ≠ 0) (h3 : IsIntegral O (f x)⁻¹) : IsUnit x := by
  classical
  have hu : IsUnit (⟨f x, AlgHom.mem_range_self f x⟩ : f.range) :=
    pts_unit (B := f.range) (K := K) (fun a b hab => Subtype.ext hab) _ h0 h3.tower_top
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨r, hr⟩ := (AlgHom.mem_range f).1 v.2
  have hfr : f x * f r = 1 := by
    rw [hr]
    exact congrArg Subtype.val hv
  by_contra hxu
  have hm : x * r ∈ maximalIdeal R := Ideal.mul_mem_right r _ hxu
  have hunit := (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (x * r) hm).map f
  rw [map_sub, map_one, map_mul, hfr, sub_self] at hunit
  exact not_isUnit_zero hunit

private theorem pts_loc {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R] [IsLocalRing R]
    (f : R →ₐ[c.O] PadicAlgCl l) : IsLocPt f := by
  intro x hx
  by_contra hge
  push_neg at hge
  have h0 : f x ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hge
    linarith
  have hint : IsIntegral ℤ_[l] (f x)⁻¹ :=
    (pts_int _).mpr (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hge)
  exact hx (pts_sur f x h0 hint.tower_top)

private theorem fg_lemma {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {K : Type} [Field K]
    [Algebra O K] (P : Submodule O A) (I : Ideal A) (ξ : A →ₐ[O] K) (hξ : ∀ a ∈ I, ξ a = 0)
    (h : (Submodule.map (Ideal.Quotient.mkₐ O I).toLinearMap P).FG) :
    (Submodule.map ξ.toLinearMap P).FG := by
  have he : ξ.toLinearMap = (Ideal.Quotient.liftₐ I ξ hξ).toLinearMap ∘ₗ
      (Ideal.Quotient.mkₐ O I).toLinearMap := by
    ext a
    rfl
  rw [he, Submodule.map_comp]
  exact h.map _

set_option maxHeartbeats 1000000 in
theorem UpperTheory.exists_torus_twist_eq_localPoint_of_weightedPres :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {R S : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] [CommRing S] [Algebra c.O S] [IsCO c.O S]
          (W : WPres c.O ℤ R) (h : W.HasOrigin) (qh : R →ₐ[c.O] S), Function.Surjective qh → ∀ {κ : Type} (g : κ → W.A) (w : κ → ℤ), (∀ i, g i ∈ W.gr (w i)) →
          RingHom.ker qh = Ideal.span (Set.range fun i => (g i : R)) → M2 W.gr (Ideal.span (Set.range g)) →
          ∀ ξ : W.A →ₐ[c.O] PadicAlgCl l, OnS (Ideal.span (Set.range g)) ξ →
            ∃ (t : (PadicAlgCl l)ˣ) (f : S →ₐ[c.O] PadicAlgCl l), IsLocPt f ∧ act W.gr (tz t) ξ = f.comp (qh.comp W.A.val) := by
  intro l _ c R S _ _ _ _ _ _ W h qh hqh κ g w hg hk hM ξ hOn
  have hfg : (Submodule.map ξ.toLinearMap (W.gr 0)).FG := fg_lemma (W.gr 0) _ ξ hOn hM
  haveI : IsLocalRing c.O := IsDiscreteValuationRing.toIsLocalRing
  haveI : Module.Finite ℤ_[l] c.O := c.fin
  obtain ⟨hcomp, -, -, hinj, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI := hcomp
  haveI : Algebra.IsAlgebraic c.O (PadicAlgCl l) := Algebra.IsAlgebraic.mk fun x =>
    ((IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] (PadicAlgCl l)).mpr
      (Algebra.IsAlgebraic.isAlgebraic x)).extendScalars hinj
  obtain ⟨t, Ξ, hΞ, -⟩ := points_finite c.O ℤ R W (automorphic_points_exist W h) (PadicAlgCl l) ξ hfg
  have hker : ∀ a ∈ RingHom.ker qh, Ξ a = 0 := by
    intro a ha
    rw [hk] at ha
    have hle : Ideal.span (Set.range fun i => (g i : R)) ≤ RingHom.ker Ξ := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      have h1 := congrArg (fun φ : W.A →ₐ[c.O] PadicAlgCl l => φ (g i)) hΞ
      simp only [AlgHom.comp_apply, Subalgebra.coe_val] at h1
      rw [h1, act_of_mem W.gr t ξ (hg i), hOn (g i) (Ideal.subset_span ⟨i, rfl⟩), mul_zero]
    exact RingHom.mem_ker.mp (hle ha)
  let f : S →ₐ[c.O] PadicAlgCl l := (Ideal.Quotient.liftₐ (RingHom.ker qh) Ξ hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective hqh).symm.toAlgHom
  have hf : ∀ r, f (qh r) = Ξ r := by
    intro r
    have hmk : (Ideal.quotientKerAlgEquivOfSurjective hqh).symm (qh r) =
        Ideal.Quotient.mk (RingHom.ker qh) r := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    show Ideal.Quotient.liftₐ (RingHom.ker qh) Ξ hker
      ((Ideal.quotientKerAlgEquivOfSurjective hqh).symm (qh r)) = Ξ r
    rw [hmk]
    rfl
  refine ⟨(zpowersHom (PadicAlgCl l)ˣ).symm t, f, pts_loc f, ?_⟩
  rw [show tz ((zpowersHom (PadicAlgCl l)ˣ).symm t) = t from Equiv.apply_symm_apply _ _, ← hΞ]
  refine AlgHom.ext fun a => ?_
  simp only [AlgHom.comp_apply, hf]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.GLiftToLiftInHAndSurjective
section
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg

private theorem hh_emb {O R : Type} [CommRing O] [CommRing R] [Algebra O R]
    (h : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) R)
    (h1 : hᵀ * (form6 O).JR R * h = (form6 O).JR R)
    (h2 : ∀ a b, (form6 O).blk a ≠ (form6 O).blk b → h a b = 0) :
    ∃ x : GG (m := 3) (R := R), x.right = 1 ∧ emb x = h := by
  have hB : h.toBlocks₁₂ = 0 := by
    ext i j
    exact h2 (Sum.inl i) (Sum.inr j) (by simp [form6])
  have hC : h.toBlocks₂₁ = 0 := by
    ext i j
    exact h2 (Sum.inr i) (Sum.inl j) (by simp [form6])
  rw [blockPairingForm_JR, ← fromBlocks_toBlocks h, hB, hC, fromBlocks_transpose, fromBlocks_multiply,
    fromBlocks_multiply] at h1
  simp only [transpose_zero, zero_mul, mul_zero, add_zero, zero_add, Matrix.fromBlocks_inj] at h1
  obtain ⟨-, hk, -, -⟩ := h1
  have hJJ : Jmat R 3 * Jmat R 3 = 1 := Jmat_mul_Jmat 3
  have hr : h.toBlocks₁₁ᵀ * (Jmat R 3 * h.toBlocks₂₂ * Jmat R 3) = 1 := by
    calc h.toBlocks₁₁ᵀ * (Jmat R 3 * h.toBlocks₂₂ * Jmat R 3)
        = (h.toBlocks₁₁ᵀ * Jmat R 3 * h.toBlocks₂₂) * Jmat R 3 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hk, hJJ]
  have hl : (Jmat R 3 * h.toBlocks₂₂ * Jmat R 3)ᵀ * h.toBlocks₁₁ = 1 := by
    have ht := congrArg transpose hr
    rwa [transpose_mul, transpose_transpose, transpose_one] at ht
  have hr' : h.toBlocks₁₁ * (Jmat R 3 * h.toBlocks₂₂ * Jmat R 3)ᵀ = 1 := mul_eq_one_comm.mp hl
  let u : GL (Fin 3) R := ⟨h.toBlocks₁₁, (Jmat R 3 * h.toBlocks₂₂ * Jmat R 3)ᵀ, hr', hl⟩
  refine ⟨⟨u, 1⟩, rfl, ?_⟩
  rw [emb_apply, ite_eq_left rfl]
  conv_rhs => rw [← fromBlocks_toBlocks h, hB, hC]
  refine Matrix.fromBlocks_inj.mpr ⟨rfl, rfl, rfl, ?_⟩
  rw [theta_val]
  have hu : ((u⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      (Jmat R 3 * h.toBlocks₂₂ * Jmat R 3)ᵀ := rfl
  rw [hu, transpose_transpose]
  calc Jmat R 3 * (Jmat R 3 * h.toBlocks₂₂ * Jmat R 3) * Jmat R 3
      = (Jmat R 3 * Jmat R 3) * h.toBlocks₂₂ * (Jmat R 3 * Jmat R 3) := by
        simp only [Matrix.mul_assoc]
    _ = h.toBlocks₂₂ := by rw [hJJ, Matrix.one_mul, Matrix.mul_one]

theorem UpperTheory.gLift_toLift_inH_and_surjective :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} (hη : IsLocallyConstant η)
          {R : Type} [CommRing R] [Algebra O R] [IsCO O R],
          (∀ r : GLift O η Ψ R, (form6 O).InH (emb.comp (r0 η Ψ)) R (r.toLift hη)) ∧
          ∀ r' : Lift O (emb.comp (rbar O η Ψ)) R, (form6 O).InH (emb.comp (r0 η Ψ)) R r' → ∃ r : GLift O η Ψ R, r.toLift hη = r' := by
  intro O _ _ Γ _ _ η Ψ hη R _ _ _
  have hra : (res O R : R →+* ResidueField O).comp (algebraMap O R) = residue O := by
    ext a
    simp [IsLocalRing.ResidueField.algebraMap_eq]
  refine ⟨fun r s => ?_, fun r' hr => ?_⟩
  · have hrt : ∀ g, (r.hom g).right = η g := r.hasMult
    show (form6 O).HH (emb (r.hom s) * (emb (r0 η Ψ s⁻¹)).map (algebraMap O R))
    rw [← emb_map', ← map_mul emb]
    set x := r.hom s * GG.map (algebraMap O R) (r0 η Ψ s⁻¹) with hxdef
    have hx : x.right = 1 := by
      rw [hxdef, SemidirectProduct.mul_right, GG.map_right, unitaryThreeReflection_right, hrt, ← map_mul, mul_inv_cancel,
        map_one]
    refine ⟨emb_form O x, fun a b hab => ?_, ?_⟩
    · by_contra hne
      have hb := emb_blk x a b hne
      rw [ite_eq_left hx] at hb
      exact hab hb
    · rw [show (emb x).map ⇑(res O R) = emb (GG.map (res O R : R →+* ResidueField O) x) from
        (emb_map' _ x).symm]
      rw [hxdef, map_mul, r.red, GG.map_map, hra, baseLift_map_residue, ← map_mul, mul_inv_cancel, map_one, map_one]
  · have hr2 : ∀ s, (form6 O).HH (r'.hom s * (emb (r0 η Ψ s⁻¹)).map (algebraMap O R)) := fun s => hr s
    choose x hx1 hx2 using fun s => hh_emb (O := O) _ (hr2 s).1 (hr2 s).2.1
    have hF : ∀ s, emb (x s * GG.map (algebraMap O R) (r0 η Ψ s)) = r'.hom s := by
      intro s
      rw [map_mul emb, hx2 s, ← emb_map', Matrix.mul_assoc, ← map_mul emb, ← map_mul, ← map_mul,
        inv_mul_cancel, map_one, map_one, map_one, Matrix.mul_one]
    have hR : ∀ s, (x s * GG.map (algebraMap O R) (r0 η Ψ s)).right = η s := by
      intro s
      rw [SemidirectProduct.mul_right, hx1, GG.map_right, unitaryThreeReflection_right, one_mul]
    let hom : Γ →* GG (m := 3) (R := R) :=
      { toFun := fun s => x s * GG.map (algebraMap O R) (r0 η Ψ s)
        map_one' := by
          refine eq_of_emb ?_ ?_
          · rw [hR, map_one, SemidirectProduct.one_right]
          · rw [hF, map_one, map_one]
        map_mul' := fun s t => by
          refine eq_of_emb ?_ ?_
          · rw [hR, SemidirectProduct.mul_right, hR, hR, map_mul]
          · rw [hF, map_mul emb, hF, hF, map_mul] }
    refine ⟨⟨hom, fun a b => ?_, fun g => ?_⟩, ?_⟩
    · have he : (fun g => (hom g).mat a b) =
          fun g => r'.hom g (Sum.inl a) (Sum.inl b) + r'.hom g (Sum.inl a) (Sum.inr b) := by
        funext g
        rw [mat_eq_emb']
        show emb (x g * _) _ _ + emb (x g * _) _ _ = _
        rw [hF]
      rw [he]
      intro N
      have h1 := r'.cont (Sum.inl a) (Sum.inl b) N
      have h2 := r'.cont (Sum.inl a) (Sum.inr b) N
      convert h1.add h2 using 1
      funext g
      exact map_add (Ideal.Quotient.mk (maximalIdeal R ^ N)) _ _
    · refine eq_of_emb ?_ ?_
      · rw [GG.map_right, ← baseLift_map_residue, GG.map_right, unitaryThreeReflection_right]
        exact hR g
      · rw [emb_map']
        ext a b
        rw [Matrix.map_apply]
        show (res O R) (emb (x g * _) a b) = _
        rw [hF]
        exact r'.red g a b
    · exact Lift.ext (MonoidHom.ext fun g => hF g)
end

