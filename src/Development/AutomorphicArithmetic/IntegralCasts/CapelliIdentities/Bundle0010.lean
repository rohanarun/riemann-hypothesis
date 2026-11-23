module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ContDiffHerm
section
namespace UpperTheory.Reformulated.B.Qj20

@[reducible] noncomputable def Mat (k r : ℕ) : Type :=
  Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

noncomputable def Hpk (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  fun i j =>
    if (i : ℕ) < r ∧ (i : ℕ) + (j : ℕ) = 2 * r + k then 1
    else if (j : ℕ) < r ∧ (i : ℕ) + (j : ℕ) = 2 * r + k then 1
    else if r ≤ (i : ℕ) ∧ (i : ℕ) ≤ r + k ∧ i = j then
      if (i : ℕ) = r + k then -1 else 1
    else 0

noncomputable def inLie (k r : ℕ) (X : Mat k r) : Prop :=
  X.conjTranspose * Hpk k r + Hpk k r * X = 0

theorem aux4 (n : ℕ) : IsTopologicalRing (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstance

noncomputable def RdV.{u_1} {n : ℕ} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (g : Matrix (Fin n) (Fin n) ℂ) : E :=
  letI : NormedSpace ℝ E := NormedSpace.complexToReal
  deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0

noncomputable def herm.{u_1} {ι : Type u_1} [Fintype ι] (H : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ :=
  star w ⬝ᵥ H.mulVec v

noncomputable def bvec {m : ℕ} (i : Fin m) : Fin m → ℂ :=
  Pi.single i 1

theorem aux8 (k r : ℕ) (a : Fin r) : (a : ℕ) < 2 * r + k + 1 := by
  have := a.isLt
  omega

noncomputable def eI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) :=
  ⟨a.val, aux8 k r a⟩

noncomputable def Top.{u_1} {n : ℕ} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → Matrix (Fin n) (Fin n) ℂ → E)
    (u : ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (g : Matrix (Fin n) (Fin n) ℂ) : E :=
  (if a = b then u • f g else 0) + Eop a b f g

noncomputable def qminorOp.{u_1} {n : ℕ} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {t : ℕ} (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → Matrix (Fin n) (Fin n) ℂ → E)
    (a b : Fin t → Fin n) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  ∑ σ : Equiv.Perm (Fin t),
    ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun k : Fin t => Top Eop (u - (k : ℂ)) (a (σ k)) (b k)).foldr
        (fun T h => T h) f

theorem aux12 : (1 + 1).AtLeastTwo :=
  ⟨by decide⟩

noncomputable def hpart1 {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Z - H⁻¹ * Z.conjTranspose * H)

noncomputable def hpart2 {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 / (2 * Complex.I) : ℂ) • (Z + H⁻¹ * Z.conjTranspose * H)

noncomputable def EabH.{u_1} {n : ℕ} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (g : Matrix (Fin n) (Fin n) ℂ) : E :=
  RdV (hpart1 H (Matrix.single a b 1)) f g +
    Complex.I • RdV (hpart2 H (Matrix.single a b 1)) f g

noncomputable def xR (k r m : ℕ) (h : m ≤ r) (l : Fin m) : Fin (2 * r + k + 1) :=
  eI k r (Fin.castLE h l)

noncomputable def AAop.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (k r m : ℕ) (hm : m ≤ r) (u : ℂ) (f : Mat k r → E) (g : Mat k r) : E :=
  ∑ c : Fin m → Fin (2 * r + k + 1),
    if StrictMono c then
      (Matrix.of fun a l : Fin m =>
        herm (Hpk k r) (g.mulVec (bvec (c l))) (bvec (eI k r (Fin.castLE hm a)))).det •
      qminorOp (EabH (Hpk k r)) (xR k r m hm) c u f g
    else 0

section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem Hpk_herm (k r : ℕ) : (Hpk k r).conjTranspose = Hpk k r := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | simp

private theorem Hpk_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.mul_apply]
  obtain ⟨s, hs⟩ : ∃ s : Fin (2 * r + k + 1),
      (s : ℕ) = if r ≤ (i : ℕ) ∧ (i : ℕ) ≤ r + k then (i : ℕ) else 2 * r + k - i :=
    ⟨⟨if r ≤ (i : ℕ) ∧ (i : ℕ) ≤ r + k then (i : ℕ) else 2 * r + k - i,
      by split_ifs <;> omega⟩, rfl⟩
  rw [Finset.sum_eq_single s]
  · simp only [Hpk, Matrix.one_apply, Fin.ext_iff]
    split_ifs at hs <;> split_ifs <;> first | omega | simp
  · intro b _ hb
    have hb' : (b : ℕ) ≠ s := fun h => hb (Fin.ext h)
    have h0 : Hpk k r i b = 0 := by
      simp only [Hpk, Fin.ext_iff]
      split_ifs at hs <;> split_ifs <;> first | omega | rfl
    rw [h0, zero_mul]
  · simp

private theorem Hpk_inv (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r :=
  Matrix.inv_eq_right_inv (Hpk_sq k r)

private theorem inLie_hpart1 (k r : ℕ) (Z : Mat k r) : inLie k r (hpart1 (Hpk k r) Z) := by
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  simp only [inLie, hpart1, Hpk_inv, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Hpk_herm, h2,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Hpk_sq,
    Matrix.mul_one]
  rw [← Matrix.mul_assoc (Hpk k r) (Hpk k r), Hpk_sq, Matrix.one_mul, ← smul_add]
  simp

private theorem inLie_hpart2 (k r : ℕ) (Z : Mat k r) : inLie k r (hpart2 (Hpk k r) Z) := by
  have h2 : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp
  simp only [inLie, hpart2, Hpk_inv, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Hpk_herm, h2,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Hpk_sq,
    Matrix.mul_one]
  rw [← Matrix.mul_assoc (Hpk k r) (Hpk k r), Hpk_sq, Matrix.one_mul, neg_smul,
    add_comm (Hpk k r * Z), neg_add_cancel]

private theorem contDiff_entry {n : ℕ} (i j : Fin n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : Matrix (Fin n) (Fin n) ℂ => g i j) :=
  contDiff_apply_apply ℝ i j

private theorem contDiff_cst {n : ℕ} (c : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : Matrix (Fin n) (Fin n) ℂ => c) :=
  contDiff_const

private theorem contDiff_herm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g : Matrix (Fin n) (Fin n) ℂ => herm H (g.mulVec v) w) := by
  simp only [herm, dotProduct, Matrix.mulVec]
  refine ContDiff.sum fun a _ => contDiff_const.mul ?_
  refine ContDiff.sum fun b _ => contDiff_const.mul ?_
  exact ContDiff.sum fun c _ => (contDiff_entry b c).mul contDiff_const

private theorem contDiff_det {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ → Fin m → Fin m → ℂ)
    (hA : ∀ a l, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => A g a l)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (Matrix.of (A g)).det) := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun l _ => hA _ _)

private theorem closed_sum {X E ι : Type*} [AddCommMonoid E] (P : (X → E) → Prop)
    (hadd : ∀ f₁ f₂, P f₁ → P f₂ → P fun x => f₁ x + f₂ x) (h0 : P fun _ => 0)
    (s : Finset ι) (F : ι → X → E) (hF : ∀ i, P (F i)) : P fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact hadd _ _ (hF a) ih

private theorem closed_foldr {Y : Type*} (P : Y → Prop) (f : Y) (hf : P f) (L : List (Y → Y))
    (hL : ∀ T ∈ L, ∀ y, P y → P (T y)) : P (L.foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact hf
  | cons T L ih =>
    exact hL T (List.mem_cons_self ..) _ (ih fun S hS => hL S (List.mem_cons_of_mem _ hS))

theorem aa_closed.{u_1} {k r : ℕ} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : (Mat k r → E) → Prop)
    (hR : ∀ (X : Mat k r) (f : Mat k r → E), inLie k r X → P f → P (RdV X f))
    (hadd : ∀ f₁ f₂ : Mat k r → E, P f₁ → P f₂ → P fun x => f₁ x + f₂ x)
    (hmul : ∀ φ : Mat k r → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      ∀ f : Mat k r → E, P f → P fun x => φ x • f x)
    (h0 : P fun _ => 0) (m : ℕ) (hm : m ≤ r) (u : ℂ) (f : Mat k r → E) (hf : P f) :
    P (AAop k r m hm u f) := by
  have hc : ∀ (c : ℂ) (f : Mat k r → E), P f → P fun x => c • f x :=
    fun c f hf => hmul (fun _ => c) (contDiff_cst c) f hf
  have hE : ∀ a b (f : Mat k r → E), P f → P (EabH (Hpk k r) a b f) := fun a b f hf =>
    hadd _ _ (hR _ f (inLie_hpart1 k r _) hf) (hc _ _ (hR _ f (inLie_hpart2 k r _) hf))
  have hT : ∀ (v : ℂ) a b (f : Mat k r → E), P f → P (Top (EabH (Hpk k r)) v a b f) := by
    intro v a b f hf
    refine hadd (fun g => if a = b then v • f g else 0) _ ?_ (hE a b f hf)
    by_cases hab : a = b
    · simp only [if_pos hab]; exact hc v f hf
    · simp only [if_neg hab]; exact h0
  have hQ : ∀ (a b : Fin m → Fin (2 * r + k + 1)),
      P (qminorOp (EabH (Hpk k r)) a b u f) := by
    intro a b
    unfold qminorOp
    rw [Finset.sum_fn]
    refine closed_sum P hadd h0 _ _ fun σ => ?_
    refine hc _ _ (closed_foldr P f hf _ fun T hTm => ?_)
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hTm
    exact hT _ _ _
  unfold AAop
  refine closed_sum P hadd h0 _ _ fun c => ?_
  by_cases hcm : StrictMono c
  · simp only [if_pos hcm]
    exact hmul _ (contDiff_det _ fun a l => contDiff_herm _ _ _) _ (hQ _ c)
  · simp only [if_neg hcm]
    exact h0

end

end UpperTheory.Reformulated.B.Qj20
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CosetOfCover
section
namespace UpperTheory.Reformulated.B.Qn18

@[reducible] noncomputable def Mat : Type → ℕ → Type :=
  fun C N ↦ Matrix (Fin N) (Fin N) C

@[reducible] noncomputable def MP : (C : Type) → [Field C] → ℕ → Type :=
  fun C [Field C] N ↦ MvPolynomial (Fin N × Fin N) C

noncomputable def ev : {C : Type} → [inst : Field C] → {N : ℕ} → Mat C N → MP C N → C :=
  fun {C} [Field C] {N} x f ↦ MvPolynomial.eval (fun p ↦ x p.1 p.2) f

noncomputable def dAt :
    {C : Type} → [inst : Field C] → {N : ℕ} → MP C N → Mat C N → Mat C N → C :=
  fun {C} [Field C] {N} f x Y ↦
    ∑ p : Fin N × Fin N, ev x (MvPolynomial.pderiv p f) * Y p.1 p.2

noncomputable def Chain : Prop :=
  ∀ (C : Type) [inst : Field C] (N M : ℕ) (φ : Mat C N →ₗ[C] Mat C M) (f : MP C M),
    ∃ (f' : MP C N),
      (∀ (x : Mat C N), ev x f' = ev (φ x) f) ∧
      ∀ (x Y : Mat C N), dAt f' x Y = dAt f (φ x) (φ Y)

noncomputable def OpenCoset : Prop :=
  ∀ (Γ C : Type) [inst : Group Γ] [inst_1 : TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [inst_4 : Field C] (n : ℕ) (r : Γ →* GL (Fin n) C)
    (f : MP C n) (O : Set Γ), IsOpen O → O.Nonempty →
    (∀ g ∈ O, ev ↑(r g) f = 0) →
    ∃ (U : Subgroup Γ),
      U.Normal ∧ U.FiniteIndex ∧ ∃ (g : Γ), ∀ u ∈ U, ev ↑(r (g * u)) f = 0

open scoped Pointwise in
private theorem coset_of_cover {G : Type} [Group G] [TopologicalSpace G]
    [TopologicalSpace.NoetherianSpace G] (hc : ∀ h : G, Continuous fun x : G => h * x)
    (Z : Set G) (hZ : IsClosed Z) (s : Finset G) (hs : ∀ x : G, ∃ a ∈ s, a * x ∈ Z) :
    ∃ U : Subgroup G, U.Normal ∧ U.FiniteIndex ∧ ∃ g : G, ∀ u ∈ U, g * u ∈ Z := by
  classical
  haveI : ContinuousConstSMul G G := ⟨hc⟩
  set X : Set G := irreducibleComponent (1 : G) with hX
  have hXc : X ∈ irreducibleComponents G := irreducibleComponent_mem_irreducibleComponents _
  have horb : MulAction.orbit G X ⊆ irreducibleComponents G := by
    rintro _ ⟨h, rfl⟩
    refine ⟨?_, ?_⟩
    · exact hXc.1.image _ (hc h).continuousOn
    · intro Y hY hle
      have h1 : IsIrreducible (h⁻¹ • Y) := IsIrreducible.image hY _ (hc h⁻¹).continuousOn
      have h2 : X ⊆ h⁻¹ • Y := by
        have : h • X ⊆ Y := hle
        exact Set.smul_set_subset_iff_subset_inv_smul_set.mp this
      have h3 : h⁻¹ • Y ⊆ X := hXc.2 h1 h2
      have h4 : Y ⊆ h • X := by
        have := Set.smul_set_subset_iff_subset_inv_smul_set.mp h3
        simpa using this
      exact h4
  have hfin : (MulAction.orbit G X).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset horb
  haveI : (MulAction.stabilizer G X).FiniteIndex := by
    refine ⟨?_⟩
    rw [MulAction.index_stabilizer]
    exact ((Set.ncard_pos hfin).mpr ⟨X, MulAction.mem_orbit_self X⟩).ne'
  obtain ⟨W, hW, hXW⟩ := isIrreducible_iff_sUnion_isClosed.mp hXc.1
    (s.image fun a => (fun x : G => a * x) ⁻¹' Z)
    (by
      intro z hz
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz
      exact hZ.preimage (hc a))
    (by
      intro x _
      obtain ⟨a, ha, hx⟩ := hs x
      exact ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ ha), hx⟩)
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hW
  refine ⟨(MulAction.stabilizer G X).normalCore, inferInstance, inferInstance, a, ?_⟩
  intro u hu
  have hu' : u • X = X := Subgroup.normalCore_le _ hu
  have : u ∈ X := by
    rw [← hu']
    exact ⟨1, mem_irreducibleComponent, by simp⟩
  exact hXW this

private theorem finite_cover {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (O : Set G) (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ s : Finset G, ∀ x : G, ∃ a ∈ s, a * x ∈ O := by
  obtain ⟨o, ho⟩ := hne
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun a : G => (fun x : G => a * x) ⁻¹' O)
    (fun a => hO.preimage (continuous_const_mul a))
    (fun x _ => Set.mem_iUnion.mpr ⟨o * x⁻¹, by simpa using ho⟩)
  refine ⟨s, fun x => ?_⟩
  simpa using hs (Set.mem_univ x)

theorem main :
    Chain → OpenCoset := by
  intro hch Γ C _ _ _ _ _ n r f O hO hne hf
  obtain ⟨s, hs⟩ := finite_cover O hO hne
  let p : Γ → PrimeSpectrum (MvPolynomial (Fin n × Fin n) C) := fun g =>
    ⟨RingHom.ker (MvPolynomial.eval fun q : Fin n × Fin n =>
      (↑(r g) : Matrix (Fin n) (Fin n) C) q.1 q.2), RingHom.ker_isPrime _⟩
  have hp : ∀ (g : Γ) (S : Set (MvPolynomial (Fin n × Fin n) C)),
      p g ∈ PrimeSpectrum.zeroLocus S ↔
        ∀ k ∈ S, ev ↑(r g) k = 0 := by
    intro g S
    rw [PrimeSpectrum.mem_zeroLocus]
    exact Iff.rfl
  letI : TopologicalSpace Γ := TopologicalSpace.induced p inferInstance
  have hcl (k : MP C n) : IsClosed {g | ev ↑(r g) k = 0} := by
    refine (isClosed_induced_iff (f := p)).mpr ⟨_, PrimeSpectrum.isClosed_zeroLocus {k}, ?_⟩
    ext g
    simp [hp]
  haveI : TopologicalSpace.NoetherianSpace Γ :=
    (show Topology.IsInducing p from ⟨rfl⟩).noetherianSpace
  have hc (h : Γ) : Continuous fun x => h * x := by
    refine continuous_iff_isClosed.mpr ?_
    intro T hT
    obtain ⟨T', hT', rfl⟩ := (isClosed_induced_iff (f := p)).mp hT
    obtain ⟨S, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus _).mp hT'
    choose F hF using fun k => hch C n n
      (LinearMap.mulLeft C (↑(r h) : Matrix (Fin n) (Fin n) C)) k
    have : (fun x => h * x) ⁻¹' (p ⁻¹' PrimeSpectrum.zeroLocus S) =
        ⋂ k ∈ S, {g | ev ↑(r g) (F k) = 0} := by
      ext g
      simp only [Set.mem_preimage, hp, Set.mem_iInter, Set.mem_setOf_eq, (hF _).1,
        LinearMap.mulLeft_apply, map_mul, Units.val_mul]
    rw [this]
    exact isClosed_biInter fun k _ => hcl (F k)
  exact coset_of_cover hc _ (hcl f) s fun x => by
    obtain ⟨a, ha, hx⟩ := hs x
    exact ⟨a, ha, hf _ hx⟩

end UpperTheory.Reformulated.B.Qn18
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CurveDVRPrecompleteFinite
section
theorem UpperTheory.Reformulated.B.PrecompleteOfFiniteOverAdicComplete.curveDVR_prec_finite :
    ∀ {O M : Type} [inst : CommRing O] [IsNoetherianRing O]
    (I : Ideal O) [IsAdicComplete I O] [inst_3 : AddCommGroup M] [inst_4 : _root_.Module O M] [Module.Finite O M],
    IsPrecomplete I M := by
  intro O M _ _ I _ _ _ _
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
  | tmul r m =>
    obtain ⟨a, rfl⟩ := AdicCompletion.of_surjective I O r
    refine ⟨a • m, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    exact (algebraMap_smul (AdicCompletion I O) a (AdicCompletion.of I M m)).symm
  | add x z hx hz =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CuspidalIrreducibleSubrep
section
noncomputable def UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev :
    {I : Type} →
      [Fintype I] →
        {W : I → Type} →
          [inst : (i : I) → AddCommGroup (W i)] →
            [inst_1 : (i : I) → _root_.Module ℂ (W i)] →
              ((i : I) → Module.Dual ℂ (W i)) → (PiTensorProduct ℂ fun (i : I) ↦ W i) →ₗ[ℂ] ℂ :=
    fun {I : Type} [Fintype I] {W : I → Type} [(i : I) → AddCommGroup (W i)] [(i : I) → _root_.Module ℂ (W i)]
        (f : (i : I) → Module.Dual ℂ (W i)) ↦
      (PiTensorProduct.lift : ((∀ i, W i) →ₘₗ[ℂ] ℂ) → (PiTensorProduct ℂ fun (i : I) ↦ W i) →ₗ[ℂ] ℂ)
        ((MultilinearMap.mkPiAlgebra ℂ I ℂ).compLinearMap f)

theorem UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev_tprod :
    ∀ {I : Type} [inst : Fintype I] [dI : DecidableEq I] {W : I → Type} [inst_1 : (i : I) → AddCommGroup (W i)]
      [inst_2 : (i : I) → _root_.Module ℂ (W i)] (f : (i : I) → Module.Dual ℂ (W i)) (m : (i : I) → W i),
      (UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev f : (PiTensorProduct ℂ fun (i : I) ↦ W i) → ℂ)
          ((PiTensorProduct.tprod ℂ : ((i : I) → W i) → PiTensorProduct ℂ fun (i : I) ↦ W i) m) =
        ∏ i : I, (f i : W i → ℂ) (m i) := by
  intro I _ _ W _ _ f m
  simp [UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CutSub
section
noncomputable def UpperTheory.Reformulated.B.FirstCoordinatesSubmodule.cutSub :
    (K : Type) → [inst : Field K] → [NumberField K] → (r : ℕ) → ℕ → Submodule (NumberField.RingOfIntegers K) (Fin r → K) :=
  fun K _ _ r n =>
    { carrier := {v : Fin r → K | ∀ i : Fin r, n ≤ (i : ℕ) → v i = 0}
      add_mem' := by
        intro v w hv hw i hi
        rw [Pi.add_apply, hv i hi, hw i hi, add_zero]
      zero_mem' := fun _ _ => rfl
      smul_mem' := by
        intro c v hv i hi
        rw [Pi.smul_apply, hv i hi, smul_zero] }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclicSubtraction
section
noncomputable def UpperTheory.Reformulated.B.CyclicSubtraction.cycSub.{u_1, u_2} :
    {G : Type u_1} → {M : Type u_2} → [inst : Group G] → [inst_1 : AddCommGroup M] → Representation ℤ G M → G → M →+ M :=
    fun {G : Type u_1} {M : Type u_2} [Group G] [AddCommGroup M] (ρ : Representation ℤ G M) (σ : G) ↦
      ((ρ : G → M →ₗ[ℤ] M) σ - LinearMap.id).toAddMonoidHom

theorem UpperTheory.Reformulated.B.CyclicSubtraction.apply_eq_of_cycSub_eq_zero.{u_1, u_2} :
    ∀ {G : Type u_1} {M : Type u_2} [inst : Group G] [inst_1 : AddCommGroup M] (ρ : Representation ℤ G M) {σ : G},
      (∀ (g : G), g ∈ Subgroup.zpowers σ) →
        ∀ {x : M}, (UpperTheory.Reformulated.B.CyclicSubtraction.cycSub ρ σ : M → M) x = (0 : M) → ∀ (g : G), ((ρ : G → M →ₗ[ℤ] M) g : M → M) x = x := by
  intro G M _ _ ρ σ hσ x hx g
  have h0 : ρ σ x - x = 0 := hx
  have h1 : ρ σ x = x := sub_eq_zero.mp h0
  let H : Subgroup G :=
    { carrier := {g | ρ g x = x}
      one_mem' := by
        show ρ 1 x = x
        rw [map_one]
        rfl
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a x = x := ha
        have hb' : ρ b x = x := hb
        show ρ (a * b) x = x
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ a x = x := ha
        show ρ a⁻¹ x = x
        calc ρ a⁻¹ x = ρ a⁻¹ (ρ a x) := by rw [ha']
          _ = ρ (a⁻¹ * a) x := by rw [map_mul, Module.End.mul_apply]
          _ = x := by
            rw [inv_mul_cancel, map_one]
            rfl }
  have hle : Subgroup.zpowers σ ≤ H := (Subgroup.zpowers_le).mpr h1
  exact hle (hσ g)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EpEqOneIff
section
theorem UpperTheory.Reformulated.B.Qj15.ep_eq_one_iff :
    ∀ (t : ℝ),
    Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑t : ℂ)) = (1 : ℂ) ↔ ∃ (n : ℤ), t = (↑n : ℝ) := by
  intro t
  rw [Complex.exp_eq_one_iff]
  refine exists_congr fun n => ?_
  rw [mul_comm ((n : ℤ) : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero]
  exact_mod_cast Iff.rfl
end

