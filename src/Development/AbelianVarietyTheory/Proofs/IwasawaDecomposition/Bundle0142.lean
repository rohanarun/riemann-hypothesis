module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RightTranslationActionApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0136

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining
section
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.TopStep

section Coord

variable {K L : Type} [Field K] [Field L] (σ : K →+* L)

theorem exists_coords : ∃ (ι : Type) (e : ι → L) (c : ι → L →+ K), (∀ i k a, c i (σ k * a) = k * c i a) ∧
    ∀ a, ∃ T : Finset ι, ∀ T' : Finset ι, T ⊆ T' → ∑ i ∈ T', e i * σ (c i a) = a := by
  letI : Algebra K L := σ.toAlgebra
  let b := Module.Basis.ofVectorSpace K L
  refine ⟨_, b, fun i => (b.coord i).toAddMonoidHom, fun i k a => ?_, fun a => ⟨(b.repr a).support, fun T' hT => ?_⟩⟩
  · exact (b.coord i).map_smul k a
  · conv_rhs => rw [← b.linearCombination_repr a, Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset _ hT _ (by simp)]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

variable {I : Type}

def coefMap (c : L →+ K) (p : MvPolynomial I L) : MvPolynomial I K :=
  ∑ m ∈ p.support, MvPolynomial.monomial m (c (p.coeff m))

theorem coeff_coefMap (c : L →+ K) (p : MvPolynomial I L) (m : I →₀ ℕ) : (coefMap c p).coeff m = c (p.coeff m) := by
  classical
  simp only [coefMap, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, map_zero]

theorem coefMap_add (c : L →+ K) (p q : MvPolynomial I L) : coefMap c (p + q) = coefMap c p + coefMap c q := by
  ext m
  simp only [coeff_coefMap, MvPolynomial.coeff_add, map_add (f := _)]

theorem coefMap_zero (c : L →+ K) : coefMap c (0 : MvPolynomial I L) = 0 := by
  ext m
  simp only [coeff_coefMap, MvPolynomial.coeff_zero, map_zero]
  change c 0 = 0
  exact map_zero c

theorem coefMap_sum {J : Type*} (c : L →+ K) (s : Finset J) (p : J → MvPolynomial I L) :
    coefMap c (∑ j ∈ s, p j) = ∑ j ∈ s, coefMap c (p j) := by
  ext m
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coeff_coefMap, MvPolynomial.coeff_sum, map_sum]

variable {σ}

theorem coefMap_smul_map {c : L →+ K} (hc : ∀ k a, c (σ k * a) = k * c a) (a : L) (p : MvPolynomial I K) :
    coefMap c (a • MvPolynomial.map σ p) = c a • p := by
  ext m
  rw [coeff_coefMap, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, smul_eq_mul,
    mul_comm, hc, mul_comm]

theorem coefMap_smul {c : L →+ K} (hc : ∀ k a, c (σ k * a) = k * c a) (k : K) (p : MvPolynomial I L) :
    coefMap c (σ k • p) = k • coefMap c p := by
  ext m
  rw [coeff_coefMap, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, coeff_coefMap, smul_eq_mul, smul_eq_mul, hc]

theorem exists_sum_coefMap {ι : Type} {e : ι → L} {c : ι → L →+ K}
    (h : ∀ a, ∃ T : Finset ι, ∀ T' : Finset ι, T ⊆ T' → ∑ i ∈ T', e i * σ (c i a) = a) (p : MvPolynomial I L) :
    ∃ T : Finset ι, ∀ T' : Finset ι, T ⊆ T' → ∑ i ∈ T', e i • MvPolynomial.map σ (coefMap (c i) p) = p := by
  classical
  choose T hT using h
  refine ⟨p.support.biUnion fun m => T (p.coeff m), fun T' hT' => ?_⟩
  ext m
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, coeff_coefMap, smul_eq_mul]
  by_cases hm : m ∈ p.support
  · exact hT _ _ ((Finset.subset_biUnion_of_mem (fun m => T (p.coeff m)) hm).trans hT')
  · simp [MvPolynomial.notMem_support_iff.1 hm]

variable (σ)

theorem linearIndependent_map_pi {D J : Type*} {f : J → D → MvPolynomial I K} (hf : LinearIndependent K f) :
    LinearIndependent L fun j d => MvPolynomial.map σ (f j d) := by
  obtain ⟨ι, e, c, hc, h⟩ := exists_coords σ
  rw [linearIndependent_iff'] at hf ⊢
  intro s g hg j hj
  have h0 : ∀ i, c i (g j) = 0 := fun i => by
    refine hf s (fun j => c i (g j)) (funext fun d => ?_) j hj
    have h1 := congrArg (coefMap (c i)) (congrFun hg d)
    rw [Finset.sum_apply, coefMap_sum, Pi.zero_apply, coefMap_zero] at h1
    rw [Finset.sum_apply, Pi.zero_apply, ← h1]
    exact Finset.sum_congr rfl fun k _ => (coefMap_smul_map (hc i) _ _).symm
  obtain ⟨T, hT⟩ := h (g j)
  rw [← hT T le_rfl]
  simp [h0]

theorem VV_induction {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {P : Pol L ι n → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hs : ∀ (a : L) (v : VV K lam), P (a • MvPolynomial.map σ v.1))
    (x : Pol L ι n) (hx : x ∈ VV L lam) : P x := by
  have e : x = ∑ i, (bVV L lam).repr ⟨x, hx⟩ i • bVVfun L lam i := by
    conv_lhs => rw [show x = ((⟨x, hx⟩ : VV L lam) : Pol L ι n) from rfl, ← (bVV L lam).sum_repr ⟨x, hx⟩]
    simp only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe]
  rw [e]
  refine Finset.sum_induction _ P hadd h0 fun i _ => ?_
  obtain ⟨F, hF, hF'⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc σ lam i
  rw [hF']
  exact hs _ ⟨F, hF⟩

variable {σ}

theorem coefMap_mem_VV {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {c : L →+ K}
    (hc : ∀ k a, c (σ k * a) = k * c a) (x : Pol L ι n) (hx : x ∈ VV L lam) : coefMap c x ∈ VV K lam := by
  refine VV_induction σ lam (P := fun x => coefMap c x ∈ VV K lam) ?_ (fun x y hx hy => ?_) (fun a v => ?_) x hx
  · rw [coefMap_zero]; exact zero_mem _
  · rw [coefMap_add]; exact add_mem hx hy
  · rw [coefMap_smul_map hc]; exact Submodule.smul_mem _ _ v.2

end Coord

section CForms

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (σ : X.K →+* ℂ) (lam : X.Tau → DomWeight n)

theorem coefMap_rhoC {c : ℂ →+ X.K} (hc : ∀ k a, c (σ k * a) = k * c a) (γ : UF X.E n) (x : Pol ℂ X.Tau n)
    (hx : x ∈ VV ℂ lam) :
    coefMap c (rhoC σ lam γ x) = (rhoV X.emb lam (ufGL X.E n γ) ⟨coefMap c x, coefMap_mem_VV lam hc x hx⟩).1 := by
  have h : ∃ y : VV X.K lam, y.1 = coefMap c x ∧ coefMap c (rhoC σ lam γ x) = (rhoV X.emb lam (ufGL X.E n γ) y).1 := by
    refine VV_induction σ lam (P := fun x => ∃ y : VV X.K lam, y.1 = coefMap c x ∧
      coefMap c (rhoC σ lam γ x) = (rhoV X.emb lam (ufGL X.E n γ) y).1) ⟨0, (coefMap_zero c).symm, ?_⟩ ?_ ?_ x hx
    · rw [map_zero, coefMap_zero, map_zero]
      rfl
    · rintro x y ⟨u, hu, hu'⟩ ⟨v, hv, hv'⟩
      refine ⟨u + v, by rw [coefMap_add, ← hu, ← hv]; rfl, ?_⟩
      rw [map_add (f := _), coefMap_add, hu', hv', map_add (f := _)]
      rfl
    · intro a v
      refine ⟨c a • v, (coefMap_smul_map hc a v.1).symm, ?_⟩
      rw [map_smul, rhoC_map, coefMap_smul_map hc, map_smul]
      rfl
  obtain ⟨y, hy, h⟩ := h
  rw [h]
  exact congrArg (fun z => (rhoV X.emb lam (ufGL X.E n γ) z).1) (Subtype.ext hy)

variable (L : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → Submodule (𝓞 X.E) (Sp X.E n)) (Λ : LevFam X.E X.K n SG)

def coordForm {c : ℂ →+ X.K} (hc : ∀ k a, c (σ k * a) = k * c a) (F : cForms ST σ lam Λ) :
    (formGSD (squarePk X lam L) Λ).EqFun :=
  ⟨fun d => ⟨coefMap c (F.1 d), coefMap_mem_VV lam hc _ (F.2 d).1⟩, fun g d => Subtype.ext <| by
    refine (congrArg (coefMap c) ((F.2 d).2 g)).trans ?_
    rw [coefMap_smul hc, coefMap_rhoC σ lam hc _ _ (F.2 d).1]
    rfl⟩

theorem toCForm_linearIndependent {J : Type*} {φ : J → (formGSD (squarePk X lam L) Λ).EqFun} (h : LinearIndependent X.K φ) :
    LinearIndependent ℂ fun j => toCForm σ lam L Λ (φ j) := by
  refine LinearIndependent.of_comp (cForms ST σ lam Λ).subtype ?_
  let i : (formGSD (squarePk X lam L) Λ).EqFun →ₗ[X.K] (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → Pol X.K X.Tau n) :=
    { toFun := fun φ d => (φ.1 d).1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hi : Function.Injective i := fun _ _ e => Subtype.ext (funext fun d => Subtype.ext (congrFun e d))
  exact linearIndependent_map_pi σ (h.map' i (LinearMap.ker_eq_bot.2 hi))

theorem exists_finite_determining (hX : X.Ok) : ∃ s : Set (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)), s.Finite ∧
    ∀ F : cForms ST σ lam Λ, (∀ d ∈ s, F.1 d = 0) → F = 0 := by
  obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
  refine ⟨s, hs, fun F hF => Subtype.ext (funext fun d => ?_)⟩
  obtain ⟨d0, hd0, g, rfl⟩ := hrep d
  have h := ((mem_cForms σ lam Λ F.1).1 F.2 d0).2 g 1
  rw [hF d0 hd0, map_zero, smul_zero] at h
  exact h

theorem toCForm_span (hX : X.Ok) : Submodule.span ℂ (Set.range (toCForm σ lam L Λ)) = ⊤ := by
  classical
  obtain ⟨ι, e, c, hc, h⟩ := exists_coords σ
  obtain ⟨s, hs, hdet⟩ := exists_finite_determining (ST := ST) σ lam Λ hX
  refine eq_top_iff.2 fun F _ => ?_
  choose T hT using fun d => exists_sum_coefMap h (F.1 d)
  have e1 : F = ∑ i ∈ hs.toFinset.biUnion T, e i • toCForm σ lam L Λ (coordForm σ lam L Λ (hc i) F) := by
    refine sub_eq_zero.1 (hdet _ fun d hd => ?_)
    rw [Submodule.coe_sub, Pi.sub_apply, Submodule.coe_sum, Finset.sum_apply, sub_eq_zero]
    exact (hT d _ (Finset.subset_biUnion_of_mem T (hs.mem_toFinset.2 hd))).symm
  rw [e1]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem toCForm_span_of_span (hX : X.Ok) {J : Type*} {φ : J → (formGSD (squarePk X lam L) Λ).EqFun}
    (h : Submodule.span X.K (Set.range φ) = ⊤) : Submodule.span ℂ (Set.range fun j => toCForm σ lam L Λ (φ j)) = ⊤ := by
  refine eq_top_iff.2 ((toCForm_span σ lam L Λ hX).ge.trans (Submodule.span_le.2 ?_))
  rintro _ ⟨ψ, rfl⟩
  have hψ : ψ ∈ Submodule.span X.K (Set.range φ) := h ▸ trivial
  induction hψ using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact Submodule.subset_span ⟨j, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

end CForms

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (σ : X.K →+* ℂ)

theorem toMtilde_linearIndependent {J : Type*} {φ : J → MtildeV W Ch sel mu P} (h : LinearIndependent X.K φ) :
    LinearIndependent ℂ fun j => toMtP W Ch sel mu P σ (φ j) := toCForm_linearIndependent σ W.sgTrue _ _ h

theorem toMtilde_span (hX : X.Ok) : Submodule.span ℂ (Set.range (toMtP W Ch sel mu P σ)) = ⊤ := toCForm_span σ W.sgTrue _ _ hX

end Rows

end GlobalTheory.Mem.Col2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProjMapProportionalSections
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ProjSpace GlobalTheory.Cartier

namespace GlobalTheory.ProjBlowup

variable {X W : Scheme.{0}} {L : LB X} {m : ℕ}

theorem exists_unit_appLE_sec (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (k l : L.ι) {T : W.Opens}
    (hk : T ≤ g ⁻¹ᵁ L.U k) (hl : T ≤ g ⁻¹ᵁ L.U l) : ∃ u : Γ(W, T)ˣ, ∀ j,
      (g.appLE (L.U k) T hk).hom ((σ j).f k) = u * (g.appLE (L.U l) T hl).hom ((σ j).f l) := by
  have hT : T ≤ g ⁻¹ᵁ (L.U k ⊓ L.U l) := le_inf hk hl
  refine ⟨Units.map (g.appLE (L.U k ⊓ L.U l) T hT).hom.toMonoidHom (L.g k l), fun j => ?_⟩
  have := congrArg (g.appLE (L.U k ⊓ L.U l) T hT).hom
    (sec_compat (σ j) k l (inf_le_left : L.U k ⊓ L.U l ≤ _) inf_le_right)
  rw [map_mul, appLE_resG, appLE_resG, appLE_resG] at this
  exact this

theorem exists_quot_of_span_eq {B : Type} [CommRing B] {ι : Type} [Fintype ι] {f : B} (hf : f ∈ nonZeroDivisors B)
    {s : ι → B} (h : Ideal.span {f} = Ideal.span (Set.range s)) :
    ∃ a c : ι → B, (∀ j, s j = a j * f) ∧ ∑ j, c j * a j = 1 := by
  have h1 : ∀ j, ∃ a, a * f = s j := fun j =>
    Ideal.mem_span_singleton'.1 (h ▸ Ideal.subset_span ⟨j, rfl⟩)
  choose a ha using h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 (h ▸ Ideal.mem_span_singleton_self f)
  refine ⟨a, c, fun j => (ha j).symm, (mul_cancel_right_mem_nonZeroDivisors hf).1 ?_⟩
  rw [one_mul, Finset.sum_mul]
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hc
  rw [mul_assoc, ha]

theorem exists_mem_basicOpen_of_sum {A : W.Opens} {a c : Fin (m + 1) → Γ(W, A)} (h : ∑ j, c j * a j = 1)
    {y : W} (hy : y ∈ A) : ∃ j, y ∈ W.basicOpen (a j) := by
  by_contra hne
  have h1 : (W.presheaf.germ A y hy).hom (∑ j, c j * a j) ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk y) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ fun hu => hne ⟨j, (W.mem_basicOpen _ y hy).2 hu⟩
  rw [h, map_one] at h1
  exact h1 isUnit_one

theorem exists_proportional (R : Type) [CommRing R] (X W : Scheme.{0}) (I : W.IdealSheafData) (L : LB X) (m : ℕ)
    (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (q : W ⟶ Sp R) (hσ : GeneratesAlong I σ g) (hI : FinalTheorems.EffCartier I) :
    ∃ ψ : W ⟶ PSpace R m, ψ ≫ PSpace.str R m = q ∧ Proportional σ g ψ := by
  obtain ⟨D, rfl⟩ := EffCartierData.exists_idealSheaf_eq hI
  have loc : ∀ y : W, ∃ (A : W.Opens) (k : L.ι) (hk : A ≤ g ⁻¹ᵁ L.U k) (i : D.ι) (hi : A ≤ D.U i)
      (a c : Fin (m + 1) → Γ(W, A)), y ∈ A ∧
      (∀ j, (g.appLE (L.U k) A hk).hom ((σ j).f k) = a j * resG W hi (D.f i)) ∧ ∑ j, c j * a j = 1 := by
    intro y
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hσ.1.ge (Set.mem_univ y))
    obtain ⟨i, hi⟩ := D.exists_mem y
    obtain ⟨A, hy, hA⟩ := EffCartierData.exists_affine_le (V := g ⁻¹ᵁ L.U k ⊓ D.U i) (x := y) ⟨hk, hi⟩
    obtain ⟨a, c, h⟩ := exists_quot_of_span_eq (D.regular i _ (hA.trans inf_le_right))
      ((D.ideal_idealSheaf A i (hA.trans inf_le_right)).symm.trans (hσ.2 k A (hA.trans inf_le_left)))
    exact ⟨A.1, k, _, i, _, a, c, hy, h⟩
  choose A k hk i hi a c hy ha hc using loc
  have ha' : ∀ y {T : W.Opens} (hT : T ≤ A y) j, (g.appLE (L.U (k y)) T (hT.trans (hk y))).hom ((σ j).f (k y)) =
      resG W hT (a y j) * resG W (hT.trans (hi y)) (D.f (i y)) := fun y T hT j => by
    have := congrArg (resG W hT) (ha y j)
    rwa [map_mul, resG_appLE, resG_resG] at this
  have tr : ∀ y z, ∃ u : Γ(W, A y ⊓ A z)ˣ, ∀ j,
      resG W (inf_le_left : A y ⊓ A z ≤ A y) (a y j) =
        (u : Γ(W, A y ⊓ A z)) * resG W (inf_le_right : A y ⊓ A z ≤ A z) (a z j) := fun y z => by
    obtain ⟨u, hu⟩ := exists_unit_appLE_sec σ g (k y) (k z) (T := A y ⊓ A z)
      (inf_le_left.trans (hk y)) (inf_le_right.trans (hk z))
    have hy' : A y ⊓ A z ≤ D.U (i y) := inf_le_left.trans (hi y)
    have hz' : A y ⊓ A z ≤ D.U (i z) := inf_le_right.trans (hi z)
    refine ⟨u * Units.map (resG W (le_inf hz' hy')).toMonoidHom (D.trans (i z) (i y)), fun j => ?_⟩
    refine ((D.regular (i y)).resG hy').mul_right_cancel ?_
    have e := hu j
    rw [ha' y inf_le_left, ha' z inf_le_right, D.trans_spec_on (i z) (i y) hz' hy'] at e
    rw [e]
    change _ = (u : Γ(W, A y ⊓ A z)) * resG W (le_inf hz' hy') (D.trans (i z) (i y)) * _ * _
    ring
  choose u hu using tr
  let B : LB W := { ι := W, U := A, g := u }
  let t : Fin (m + 1) → B.Sec := fun j => { f := fun y => a y j, compat := fun y z => hu y z j }
  have ht : ⨆ j, Out.nonzeroLocus (t j) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨j, hj⟩ := exists_mem_basicOpen_of_sum (hc y) (hy y)
    exact Opens.mem_iSup.2 ⟨j, (mem_nonzeroLocus_iff (t j) y (hy y)).2 hj⟩
  refine ⟨toProj q t ht, toProj_str q t ht, fun V l hl p hp j => ext_germ fun y hyV => ?_⟩
  have hm : y ∈ V ⊓ A y := ⟨hyV, hy y⟩
  have key : resG W (inf_le_left : V ⊓ A y ≤ V) ((g.appLE (L.U l) V hl).hom ((σ j).f l)) =
      resG W inf_le_left (pullRatio (toProj q t ht) V p hp j * (g.appLE (L.U l) V hl).hom ((σ p).f l)) := by
    obtain ⟨v, hv⟩ := exists_unit_appLE_sec σ g l (k y) (T := V ⊓ A y)
      (inf_le_left.trans hl) (inf_le_right.trans (hk y))
    have e : resG W inf_le_right (a y j) = _ * resG W inf_le_right (a y p) :=
      sec_eq_pullRatio_toProj_mul q t ht p j y (W := V ⊓ A y) (inf_le_left.trans hp) inf_le_right
    rw [map_mul, resG_appLE, resG_appLE, resG_pullRatio, hv, hv, ha' y inf_le_right, ha' y inf_le_right, e]
    ring
  have := congrArg (W.presheaf.germ _ y hm).hom key
  rwa [germ_resG, germ_resG] at this

end GlobalTheory.ProjBlowup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionsGenerateIdealProjective
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjBlowup

variable {R : Type} [CommRing R] {N : ℕ} {X : Scheme.{0}}

theorem exists_formOn_eq (a : Fin (N + 1)) (s : Γ(PSpace R N, chart R N a)) :
    ∃ (d : ℕ) (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous d),
      formOn (chart R N a) a le_rfl d F hF = s := by
  obtain ⟨p, rfl⟩ := (chartAlgEquiv R N a).surjective s
  obtain ⟨x, rfl⟩ := (polyEquivAway R N a).symm.surjective p
  obtain ⟨n, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem R N a) x
  refine ⟨n, f, by simpa using hf, ?_⟩
  rw [← chartAlgEquiv_dehom, ← awayToPoly_mk R N a n f hf]
  rfl

def pullForm (φ : X ⟶ PSpace R N) (W : X.Opens) (i : Fin (N + 1)) (hi : W ≤ φ ⁻¹ᵁ chart R N i)
    (d : ℕ) (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous d) : Γ(X, W) :=
  (φ.appLE (chart R N i) W hi).hom (formOn (chart R N i) i le_rfl d F hF)

section

variable {φ : X ⟶ PSpace R N} {W V : X.Opens} {i j : Fin (N + 1)} {hi : W ≤ φ ⁻¹ᵁ chart R N i}
  {d : ℕ} {F : MvPolynomial (Fin (N + 1)) R}

theorem resG_pullForm (h : V ≤ W) (hF : F.IsHomogeneous d) :
    resG X h (pullForm φ W i hi d F hF) = pullForm φ V i (h.trans hi) d F hF :=
  resG_appLE φ hi h _

theorem pullForm_zero : pullForm φ W i hi d 0 (isHomogeneous_zero _ R d) = 0 := by
  rw [pullForm, formOn_zero, map_zero]

theorem pullForm_eq_pow_mul (hj : W ≤ φ ⁻¹ᵁ chart R N j) (hF : F.IsHomogeneous d) :
    pullForm φ W i hi d F hF = pullRatio φ W i hi j ^ d * pullForm φ W j hj d F hF := by
  have hW : W ≤ φ ⁻¹ᵁ (chart R N i ⊓ chart R N j) := le_inf hi hj
  have := congrArg (φ.appLE _ W hW).hom
    (formOn_eq_ratioOn_pow_mul (U := chart R N i ⊓ chart R N j) (hi := inf_le_left) inf_le_right hF)
  rw [map_mul, map_pow, appLE_ratioOn, ← resG_formOn (hi := le_rfl) inf_le_left,
    ← resG_formOn (hi := le_rfl) inf_le_right, appLE_resG, appLE_resG] at this
  exact this

theorem pullForm_X_pow_mul (n : ℕ) (hF : F.IsHomogeneous d) {e : ℕ}
    (hG : (MvPolynomial.X j ^ n * F).IsHomogeneous e) :
    pullForm φ W i hi e _ hG = pullRatio φ W i hi j ^ n * pullForm φ W i hi d F hF := by
  rw [pullForm, pullForm, pullRatio, formOn_eq_aeval, formOn_eq_aeval, map_mul, map_pow, aeval_X, map_mul,
    map_pow]

end

def pullO (φ : X ⟶ PSpace R N) (e : ℕ) : LB X where
  ι := Fin (N + 1)
  U i := φ ⁻¹ᵁ chart R N i
  g i j := (Units.mkOfMulEqOne (pullRatio φ _ i inf_le_left j) (pullRatio φ _ j inf_le_right i)
    (pullRatio_mul_pullRatio.trans pullRatio_self)) ^ e

def pullFormSec (φ : X ⟶ PSpace R N) {e : ℕ} (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous e) :
    (pullO φ e).Sec where
  f i := pullForm φ _ i le_rfl e F hF
  compat i j := by
    refine (resG_pullForm inf_le_left hF).trans ((pullForm_eq_pow_mul (j := j) inf_le_right hF).trans ?_)
    exact congrArg₂ (· * ·) (Units.val_pow_eq_pow_val (Units.mkOfMulEqOne _ _ _) e).symm
      (resG_pullForm inf_le_right hF).symm

abbrev affChart (φ : X ⟶ PSpace R N) [IsClosedImmersion φ] (i : Fin (N + 1)) : X.affineOpens :=
  ⟨φ ⁻¹ᵁ chart R N i, (isAffineOpen_chart R N i).preimage φ⟩

theorem exists_pow_mul_pullForm_mem (φ : X ⟶ PSpace R N) [IsClosedImmersion φ] (J : X.IdealSheafData)
    {a : Fin (N + 1)} {d : ℕ} {F : MvPolynomial (Fin (N + 1)) R} (hF : F.IsHomogeneous d)
    (h : pullForm φ _ a le_rfl d F hF ∈ J.ideal (affChart φ a)) (b : Fin (N + 1)) :
    ∃ n, pullRatio φ _ b le_rfl a ^ n * pullForm φ _ b le_rfl d F hF ∈ J.ideal (affChart φ b) := by
  let r : Γ(X, (affChart φ b).1) := pullRatio φ _ b le_rfl a
  have ha : X.basicOpen r ≤ φ ⁻¹ᵁ chart R N a := basicOpen_pullRatio.le.trans inf_le_right
  have h1 : resG X ha (pullForm φ _ a le_rfl d F hF) ∈ J.ideal (X.affineBasicOpen r) :=
    J.ideal_le_comap_ideal (U := X.affineBasicOpen r) (V := affChart φ a) ha h
  have h2 : resG X (X.basicOpen_le r) (pullForm φ _ b le_rfl d F hF) ∈ J.ideal (X.affineBasicOpen r) := by
    rw [resG_pullForm] at h1 ⊢
    rw [pullForm_eq_pow_mul (j := a) ha]
    exact Ideal.mul_mem_left _ _ h1
  rw [← J.map_ideal_basicOpen] at h2
  have inst := (affChart φ b).2.isLocalization_basicOpen r
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (.powers r)
    Γ(X, X.basicOpen r) _ _).1 h2
  exact ⟨n, hn⟩

theorem exists_form_of_mem (φ : X ⟶ PSpace R N) [IsClosedImmersion φ] (J : X.IdealSheafData)
    (a : Fin (N + 1)) (g : Γ(X, (affChart φ a).1)) (hg : g ∈ J.ideal (affChart φ a)) :
    ∃ e₀, ∀ e, e₀ ≤ e → ∃ (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous e),
      pullForm φ _ a le_rfl e F hF = g ∧ ∀ b, pullForm φ _ b le_rfl e F hF ∈ J.ideal (affChart φ b) := by
  obtain ⟨s, rfl⟩ := φ.app_surjective _ (isAffineOpen_chart R N a) g
  obtain ⟨d, F, hF, rfl⟩ := exists_formOn_eq a s
  have e₁ : pullForm φ _ a le_rfl d F hF = (φ.app (chart R N a)).hom (formOn (chart R N a) a le_rfl d F hF) := by
    rw [pullForm, Scheme.Hom.app_eq_appLE]
  choose n hn using exists_pow_mul_pullForm_mem φ J hF (e₁ ▸ hg)
  refine ⟨Finset.univ.sup n + d, fun e he => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (le_of_add_le_right he)
  refine ⟨MvPolynomial.X a ^ k * F, (isHomogeneous_X_pow a k).mul hF, ?_, fun b => ?_⟩
  · rw [pullForm_X_pow_mul k hF, pullRatio_self, one_pow, one_mul]
    exact e₁
  · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le'
      ((Finset.le_sup (f := n) (Finset.mem_univ b)).trans (Nat.le_of_add_le_add_right he))
    rw [pullForm_X_pow_mul _ hF, pow_add, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hn b)

theorem exists_generates (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (hs : IsProjOver s) (J : X.IdealSheafData) :
    ∃ (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec), Generates J σ := by
  classical
  obtain ⟨N, φ, _, -⟩ := hs
  have fg : ∀ a, (J.ideal (affChart φ a)).FG := fun a => by
    have : IsNoetherianRing Γ(PSpace R N, chart R N a) :=
      isNoetherianRing_of_ringEquiv _ (chartAlgEquiv R N a).toRingEquiv
    have : IsNoetherianRing Γ(X, (affChart φ a).1) :=
      isNoetherianRing_of_surjective _ _ _ (φ.app_surjective _ (isAffineOpen_chart R N a))
    exact IsNoetherian.noetherian _
  choose S hS using fg
  choose e₀ he₀ using fun p : Σ a, S a =>
    exists_form_of_mem φ J p.1 p.2.1 (hS p.1 ▸ Ideal.subset_span p.2.2)
  choose F hF hFa hFb using fun p => he₀ p (Finset.univ.sup e₀) (Finset.le_sup (Finset.mem_univ p))
  let q := (Fintype.equivFinOfCardEq (Fintype.card_option (α := Σ a, S a))).symm
  let τ : Option (Σ a, S a) → (pullO φ (Finset.univ.sup e₀)).Sec := fun o =>
    o.elim (pullFormSec φ 0 (isHomogeneous_zero _ R _)) fun p => pullFormSec φ (F p) (hF p)
  refine ⟨_, _, fun j => τ (q j), (isCoordFamily_pullRatio φ).cover, fun k V h => ?_⟩
  have key : J.ideal (affChart φ k) = Ideal.span (Set.range fun j => (τ (q j)).f k) := by
    refine le_antisymm ?_ (Ideal.span_le.2 ?_)
    · rw [← hS k]
      refine Ideal.span_mono fun g hg => ⟨q.symm (some ⟨k, g, hg⟩), ?_⟩
      simp only [q.apply_symm_apply]
      exact hFa ⟨k, g, hg⟩
    · rintro _ ⟨j, rfl⟩
      dsimp only
      cases q j with
      | none =>
        exact (congrArg (· ∈ J.ideal (affChart φ k)) (pullForm_zero (φ := φ) (hi := le_rfl))).mpr (zero_mem _)
      | some p => exact hFb p k
  rw [← J.map_ideal (V := affChart φ k) h, key]
  erw [Ideal.map_span, ← Set.range_comp]
  rfl

end GlobalTheory.ProjBlowup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeNormalFormViaMatrixStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeNormalForm_via_matrix : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ h : AutY X R j, GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P h → ∃ (e : Fin (cOf R j) → ℤ) (z : Fin (R.N j) → X.E), (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (fun l : Fin (R.N j + cOf R j) => if hl : l.1 < R.N j then z ⟨l.1, hl⟩ else 0) ∈ lamYat (Pr := Pr) (R := R) j P ∧ (lamYat (Pr := Pr) (R := R) j P).map (h.toLinearMap.restrictScalars (𝓞 X.E)) = (lamYat (Pr := Pr) (R := R) j P).map ((Matrix.toLin' (nfMat (R.N j) (cOf R j) (qOf P : X.E) e z)).restrictScalars (𝓞 X.E)) := by
  first | exact @GlobalTheory.Mem.Col2.IdxEx.nf_matrix | exact GlobalTheory.Mem.Col2.IdxEx.nf_matrix | (intros; apply GlobalTheory.Mem.Col2.IdxEx.nf_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterStepZeroTypePrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacter_stepZero_typePrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), cst.sharp = true → (∀ a : X.E, IntAt P.1 a → cst.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a)) → ChrG Ch sel mu cst 0 P 1 (colLev Ch 0 ⟨P.1, hP⟩) := by
  first | exact @GlobalTheory.Proof.levelCharacter_stepZero_typePrime.chrG_zero | exact GlobalTheory.Proof.levelCharacter_stepZero_typePrime.chrG_zero | (intros; apply GlobalTheory.Proof.levelCharacter_stepZero_typePrime.chrG_zero <;> assumption)
end

