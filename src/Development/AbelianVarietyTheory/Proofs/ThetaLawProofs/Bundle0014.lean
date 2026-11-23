module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDiffSumSmulOfIsLieComb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory

namespace DiffLin

open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR jetAug dualLift dualLift_zR fstD_comp_dualLift ker_jetAug_pow)

variable {R : Type} [CommRing R] {n : ℕ}

theorem fst_dualLift (t : Fin n → R) (y : Chart.JetR R (Fin n) 1) :
    (dualLift t y).fst = jetAug R (Fin n) 1 y :=
  AlgHom.congr_fun (fstD_comp_dualLift t) y

theorem snd_dualLift_sum {k : ℕ} (c : Fin k → R) (t : Fin k → Fin n → R) (y : Chart.JetR R (Fin n) 1) :
    (dualLift (∑ i, c i • t i) y).snd = ∑ i, c i * (dualLift (t i) y).snd := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : ∀ s : Fin n → R,
        (dualLift s (Ideal.Quotient.mk _ (MvPolynomial.C a))).snd = 0 := fun s => by
      have := (dualLift s).commutes a
      exact (congrArg TrivSqZeroExt.snd this).trans rfl
    simp only [h, mul_zero, Finset.sum_const_zero]
  | add p q hp hq =>
    simp only [map_add (f := _), TrivSqZeroExt.snd_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    have h : ∀ s : Fin n → R,
        (dualLift s (Ideal.Quotient.mk _ (p * MvPolynomial.X j))).snd =
          jetAug R (Fin n) 1 (Ideal.Quotient.mk _ p) * s j := fun s => by
      rw [map_mul, map_mul, dualLift_zR, DualNumber.snd_mul, fst_dualLift]
      simp
    simp only [h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem spMap_dualLift_surjective (t : Fin n → R) :
    Function.Surjective (spMap (dualLift t : Chart.JetR R (Fin n) 1 →+* DualNumber R)) := by
  intro p
  have hs : Function.Surjective (jetAug R (Fin n) 1 : Chart.JetR R (Fin n) 1 →+* R) := fun a =>
    ⟨algebraMap R _ a, (jetAug R (Fin n) 1).commutes a⟩
  have hp : (p : PrimeSpectrum (Chart.JetR R (Fin n) 1)) ∈
      Set.range (PrimeSpectrum.comap (jetAug R (Fin n) 1 : Chart.JetR R (Fin n) 1 →+* R)) := by
    rw [range_comap_of_surjective _ _ hs]
    intro a ha
    apply (PrimeSpectrum.isPrime p).mem_of_pow_mem (1 + 1)
    have : a ^ (1 + 1) ∈ (RingHom.ker (jetAug R (Fin n) 1)) ^ (1 + 1) := Ideal.pow_mem_pow ha _
    rw [ker_jetAug_pow, Ideal.mem_bot] at this
    rw [this]
    exact Ideal.zero_mem _
  obtain ⟨q, rfl⟩ := hp
  refine ⟨PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom q, ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun y => ?_)
  change (dualLift t y).fst ∈ q.asIdeal ↔ jetAug R (Fin n) 1 y ∈ q.asIdeal
  rw [fst_dualLift]

theorem top_le_preimage_of_dualLift {X : Scheme.{0}} (x : Sp (Chart.JetR R (Fin n) 1) ⟶ X) (U : X.Opens)
    (t : Fin n → R)
    (h : ⊤ ≤ (spMap (dualLift t : Chart.JetR R (Fin n) 1 →+* DualNumber R) ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := spMap_dualLift_surjective t p
  exact h (Set.mem_univ q)

open GlobalTheory.TangentOrigin in
theorem evalPt_of_eq {X : Scheme.{0}} (x : Sp (Chart.JetR R (Fin n) 1) ⟶ X) (U : X.Opens)
    (hx : ⊤ ≤ x ⁻¹ᵁ U) (t : Fin n → R) (v : Sp (DualNumber R) ⟶ X)
    (e : v = spMap (dualLift t : Chart.JetR R (Fin n) 1 →+* DualNumber R) ≫ x) (f : Γ(X, U)) :
    ∃ h : ⊤ ≤ v ⁻¹ᵁ U, evalPt v U h f = dualLift t (evalPt x U hx f) := by
  subst e
  exact ⟨fun p _ => hx (Set.mem_univ _), evalPt_spMap_comp _ x U hx _ f⟩

end DiffLin


open GlobalTheory.TangentOrigin DiffLin in
theorem isDiff_sum_smul_of_isLieComb :
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g n : ℕ) (u : HolUnif A L g)
    (v : Fin n → (epsR ℂ ⟶ A)) (W : Fin n → Fin g → ℂ) (c : Fin n → ℂ) (w : epsR ℂ ⟶ A),
    (∀ i, IsTangent (v i)) → (∀ i, u.IsDiff (W i) (v i)) → IsLieComb c v w → u.IsDiff (∑ i, c i • W i) w := by
  intro A _ hA L g n u v W c w hv hd hc U h f
  have : Smooth A.hom := hA.smooth
  obtain ⟨m, x, hx⟩ := Chart.univChartLoc A
  have htan : ∀ i, Chart.IsTan (v i) := fun i => (Chart.isTan_iff _).mpr (hv i)
  obtain ⟨hw, e⟩ := Chart.prodPts_tan hx c v htan
  have ew : w.left = spMap (Chart.dualLift (∑ i, c i • Chart.tcoord hx (v i) (htan i)) :
      Chart.JetR ℂ (Fin m) 1 →+* DualNumber ℂ) ≫ (x 1).left := by
    rw [← e, (Chart.isLieComb_iff c v w).1 hc]
    exact congrArg CommaMorphism.left (Chart.tcoord_spec hx _ hw)
  have ev : ∀ i, (v i).left = spMap (Chart.dualLift (Chart.tcoord hx (v i) (htan i)) :
      Chart.JetR ℂ (Fin m) 1 →+* DualNumber ℂ) ≫ (x 1).left := fun i =>
    congrArg CommaMorphism.left (Chart.tcoord_spec hx _ (htan i))
  have hU : ⊤ ≤ (x 1).left ⁻¹ᵁ U := top_le_preimage_of_dualLift _ U _ (ew ▸ h)
  obtain ⟨h', e'⟩ := evalPt_of_eq (x 1).left U hU _ w.left ew f
  change (evalPt (R := DualNumber ℂ) w.left U h' f).snd = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e', snd_dualLift_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨hi, ei⟩ := evalPt_of_eq (x 1).left U hU _ (v i).left (ev i) f
  rw [← ei, map_smul, smul_eq_mul]
  exact congrArg (c i * ·) (hd i U hi f)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_id isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)

namespace GlobalTheory.LieComb

open GlobalTheory.SqZero

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {v : Fin n → (epsR R ⟶ G)}

theorem isLieComb_iff_tanExp (c : Fin n → R) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = tanExp v c := isLieComb_iff_lieExp c w

theorem isTangent_tanExp (hv : ∀ i, IsTangent (v i)) (c : Fin n → R) : IsTangent (tanExp v c) :=
  (isTan_iff _).1 (isTanOver_tanExp hv c)

def combHom (hv : ∀ i, IsTangent (v i)) :
    (Fin n → R) →+ Additive (sp (R₀ := R) (DualNumber R) ⟶ G) :=
  AddMonoidHom.mk' (fun c => Additive.ofMul (tanExp v c)) (fun c c' => by
    rw [← ofMul_mul]
    refine congrArg Additive.ofMul ?_
    rw [← lieExp_add hv _ _ _ _ (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)
      (fun _ => by rw [← TrivSqZeroExt.inr_add]; exact TrivSqZeroExt.inr_mul_inr _ _ _)]
    exact lieExp_congr _ (fun i => TrivSqZeroExt.inr_add _ _ _) _ _)

theorem tanExp_tanExp (hv : ∀ i, IsTangent (v i)) {m : ℕ} (M : Fin m → Fin n → R)
    (c : Fin m → R) : tanExp (fun i => tanExp v (M i)) c = tanExp v (∑ i, c i • M i) := by
  change _ = (combHom hv (∑ i, c i • M i)).toMul
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, toMul_sum, tanExp, lieExp]
  refine Finset.prod_congr rfl fun i _ => ?_
  refine (comp_lieExp v _ _ _).trans ?_
  exact lieExp_congr _ (fun j => by
    simp [epsTo, dualTo_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inl_mul_inr,
      mul_comm, smul_smul]) _ _

theorem tanExp_single (hv : ∀ i, IsTangent (v i)) (i : Fin n) :
    tanExp v (Pi.single i (1 : R)) = v i := by
  rw [tanExp, lieExp, Finset.prod_eq_single i]
  · have : ∀ h, epsTo R (inr ((Pi.single i (1 : R) : Fin n → R) i) : DualNumber R) h =
        AlgHom.id R _ := fun h => DualNumber.algHom_ext (by
      rw [epsTo_eps, Pi.single_eq_same]; rfl)
    rw [this, spMap_id]
    exact Category.id_comp _
  · intro j _ hj
    exact epsTo_zero_comp ((isTan_iff _).2 (hv j)) _ (by simp [Pi.single_eq_of_ne hj]) _
  · simp

theorem isLieBasis_iff_isUnit_det (hv : IsLieBasis v) (M : Matrix (Fin n) (Fin n) R) :
    IsLieBasis (fun i => tanExp v (M i)) ↔ IsUnit M.det := by
  have key : ∀ c : Fin n → R,
      tanExp (fun i => tanExp v (M i)) c = tanExp v (Matrix.vecMul c M) := fun c => by
    rw [Matrix.vecMul_eq_sum]
    exact tanExp_tanExp hv.1 (fun i => M i) c
  have hinj : Function.Injective (fun c : Fin n → R => tanExp v c) := by
    intro a b hab
    obtain ⟨c, hc, hu⟩ := hv.2 (tanExp v b) (isTangent_tanExp hv.1 b)
    have ha : IsLieComb a v (tanExp v b) :=
      (isLieComb_iff_tanExp _ _).2 hab.symm
    have hb : IsLieComb b v (tanExp v b) :=
      (isLieComb_iff_tanExp _ _).2 rfl
    exact (hu a ha).trans (hu b hb).symm
  rw [← Matrix.isUnit_iff_isUnit_det]
  constructor
  · intro h
    refine Matrix.vecMul_surjective_iff_isUnit.1 fun d => ?_
    obtain ⟨c, hc, -⟩ := h.2 _ (isTangent_tanExp hv.1 d)
    rw [isLieComb_iff_tanExp, key] at hc
    exact ⟨c, (hinj hc).symm⟩
  · intro h
    refine ⟨fun i => isTangent_tanExp hv.1 _, fun w hw => ?_⟩
    obtain ⟨d, hd, -⟩ := hv.2 w hw
    obtain ⟨c, hc⟩ := Matrix.vecMul_surjective_iff_isUnit.2 h d
    have hc' : Matrix.vecMul c M = d := hc
    rw [isLieComb_iff_tanExp] at hd
    refine ⟨c, ?_, fun c' h' => ?_⟩
    · change IsLieComb _ _ _
      rw [isLieComb_iff_tanExp, key, hc', hd]
    · change IsLieComb _ _ _ at h'
      rw [isLieComb_iff_tanExp, key, hd, ← hc'] at h'
      exact Matrix.vecMul_injective_of_isUnit h (hinj h').symm

theorem lieComb_algebra (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (n : ℕ) (v : Fin n → (epsR R ⟶ G)) (hv : ∀ i, IsTangent (v i)) :
    (∀ c, ∃! w, IsLieComb c v w) ∧ (∀ c w, IsLieComb c v w → IsTangent w) ∧
    (∀ (m : ℕ) (M : Fin m → Fin n → R) (v' : Fin m → (epsR R ⟶ G)) (c : Fin m → R) (w),
      (∀ i, IsLieComb (M i) v (v' i)) → IsLieComb c v' w → IsLieComb (∑ i, c i • M i) v w) ∧
    (∀ i, IsLieComb (Pi.single i 1) v (v i)) ∧
    ∀ (M : Matrix (Fin n) (Fin n) R) (v' : Fin n → (epsR R ⟶ G)), IsLieBasis v →
      (∀ i, IsLieComb (M i) v (v' i)) → (IsLieBasis v' ↔ IsUnit M.det) := by
  refine ⟨fun c => ⟨tanExp v c, (isLieComb_iff_tanExp _ _).2 rfl,
    fun w hw => (isLieComb_iff_tanExp _ _).1 hw⟩, fun c w hw => ?_, fun m M v' c w hM hw => ?_,
    fun i => (isLieComb_iff_tanExp _ _).2 (tanExp_single hv i).symm, fun M v' hb hM => ?_⟩
  · rw [(isLieComb_iff_tanExp _ _).1 hw]
    exact isTangent_tanExp hv c
  · obtain rfl : v' = fun i => tanExp v (M i) :=
      funext fun i => (isLieComb_iff_tanExp _ _).1 (hM i)
    rw [isLieComb_iff_tanExp] at hw ⊢
    rw [hw, tanExp_tanExp hv]
  · obtain rfl : v' = fun i => tanExp v (M i) :=
      funext fun i => (isLieComb_iff_tanExp _ _).1 (hM i)
    exact isLieBasis_iff_isUnit_det hb M

end GlobalTheory.LieComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsThetaFnAndNeZeroOfIsFn
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace SectionFn

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem differentiable_of_isFn (hL : L.IsLB) {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ) :
    Differentiable ℂ θ := by
  intro z
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left hL
  have hn := (u.hol (L.U i) (s.f i)).1.mem_nhds hi
  have d : DifferentiableOn ℂ (fun w => valAt' (u.ex w).left (L.U i) (s.f i) * (u.fr i w)⁻¹)
      {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ L.U i} :=
    (u.hol (L.U i) (s.f i)).2.mul ((u.fr_hol i).inv fun w hw => u.fr_ne i w hw)
  refine (d.differentiableAt hn).congr_of_eventuallyEq (Filter.mem_of_superset hn fun w hw => ?_)
  have := u.fr_ne i w hw
  change θ w = valAt' (u.ex w).left (L.U i) (s.f i) * (u.fr i w)⁻¹
  rw [h i w hw]
  field_simp

theorem isThetaFn_of_isFn (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ)
    {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ) : u.IsThetaFn Hm χ 1 θ := by
  refine ⟨differentiable_of_isFn u hL h, fun l z => ?_⟩
  have hper : u.ex (z + l) = u.ex z := by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left hL
  have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have h1 := h i z hi
  have h2 := h i (z + l) hi'
  rw [hper, h1, hAH.2.2.2 l i z hi] at h2
  refine mul_right_cancel₀ (u.fr_ne i _ hi') ?_
  rw [← h2, pow_one]
  unfold hermForm
  ring

theorem ne_zero_of_isFn [LocallyOfFiniteType A.hom] {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ)
    {p : A.left} (hp : p ∈ Out.nonzeroLocus s) : θ ≠ 0 := by
  rintro rfl
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  have hle : A.left.basicOpen (s.f i) ≤ ⊥ := by
    refine ComplexPoints.opens_le_of_complexPoints A.hom _ _ fun y hy hyb => ?_
    obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk y hy)
    have hzy : (u.ex z).left = y := by rw [hz]; rfl
    subst hzy
    have hne := (top_le_preimage_basicOpen_iff _ _ _).1 hyb
    have hU := top_le_preimage_of_valAt'_ne_zero _ hne
    exact absurd (by simpa using h i z hU) hne
  exact hle hi

end SectionFn

theorem isThetaFn_and_ne_zero_of_isFn :
    ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
    (θ : (Fin x.P.g → ℂ) → ℂ), u.IsAH Hm χ → u.IsFn x.th θ → u.IsThetaFn Hm χ 1 θ ∧ θ ≠ 0 := by
  intro x u Hm χ θ hAH h
  refine ⟨SectionFn.isThetaFn_of_isFn u x.P.isLB hAH h, ?_⟩
  obtain ⟨p, -, hp⟩ := x.th_ne (default : PrimeSpectrum ℂ)
  have := x.P.smoothDim
  have : Smooth x.P.A.hom := SmoothOfRelativeDimension.smooth x.P.g _
  exact SectionFn.ne_zero_of_isFn u h hp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NonzeroLocusConstMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PowChange

open GlobalTheory.PowLie

variable {R : Type} [CommRing R]

theorem sc_zero_comp {G : Over (Sp R)} [GrpObj G] {v : epsR R ⟶ G} (hv : IsTangent v) :
    sc 0 ≫ v = 1 := by
  have h : sc (0 : R) = toUnit _ ≫ zeroPt R := by
    refine Over.OverMorphism.ext ?_
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  rw [h, Category.assoc, (isTangent_iff v).1 hv, Hom.one_def]

theorem exists_block_basis {G' G : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    {j g n : ℕ} (p : Out.IsPowGrp G' G j) (hg : j * g = n) {v v' : Fin g → (epsR R ⟶ G)}
    (hv : IsLieBasis v) (hv' : IsLieBasis v') (M : Matrix (Fin g) (Fin g) R)
    (hM : ∀ i, IsLieComb (M i) v (v' i)) (u : Fin n → (epsR R ⟶ G'))
    (hu : ∀ (i i' : Fin j) (k : Fin g),
      u ((finProdFinEquiv (i, k)).cast hg) ≫ p.pr i' = if i = i' then v k else 1) :
    ∃ (w : Fin n → (epsR R ⟶ G')) (M' : Matrix (Fin n) (Fin n) R), IsLieBasis w ∧
      (∀ (i i' : Fin j) (k : Fin g),
        w ((finProdFinEquiv (i, k)).cast hg) ≫ p.pr i' = if i = i' then v' k else 1) ∧
      (∀ i, IsLieComb (M' i) u (w i)) ∧ M'.det = M.det ^ j := by
  subst hg
  obtain ⟨w, hw, hw'⟩ := isLieBasis_pow R G' G j g p v' hv'
  let e : Fin g × Fin j ≃ Fin (j * g) := (Equiv.prodComm _ _).trans finProdFinEquiv
  refine ⟨w, Matrix.reindex e e (Matrix.blockDiagonal fun _ => M), hw, hw', fun m => ?_, ?_⟩
  · obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective m
    rw [isLieComb_iff_prod]
    refine p.lim.hom_ext fun ⟨i'⟩ => ?_
    have := p.hom i'
    change _ ≫ p.pr i' = _ ≫ p.pr i'
    refine Eq.trans ?_ (map_prod (IsMonHom.monoidHom (p.pr i') (epsR R)) _ _).symm
    have hu' : ∀ (i : Fin j) (k : Fin g), u (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1 :=
      fun i k => hu i i' k
    rw [hw', ← finProdFinEquiv.prod_comp, Fintype.prod_prod_type, Finset.prod_eq_single i']
    · have h₁ : ∀ k', (IsMonHom.monoidHom (p.pr i') (epsR R))
          (sc (Matrix.reindex e e (Matrix.blockDiagonal fun _ => M) (finProdFinEquiv (i, k))
            (finProdFinEquiv (i', k'))) ≫ u (finProdFinEquiv (i', k'))) =
          sc (if i = i' then M k k' else 0) ≫ v k' := fun k' => by
        change (sc _ ≫ u _) ≫ p.pr i' = _
        rw [Category.assoc, hu', if_pos rfl]
        congr 2
        simp [e, Matrix.blockDiagonal_apply]
      rw [Finset.prod_congr rfl fun k' _ => h₁ k']
      split_ifs with h
      · exact (isLieComb_iff_prod _ _ _).1 (hM k)
      · exact (Finset.prod_eq_one fun k' _ => sc_zero_comp (hv.1 k')).symm
    · intro i'' _ hi
      refine Finset.prod_eq_one fun k' _ => ?_
      change (sc _ ≫ u _) ≫ p.pr i' = _
      rw [Category.assoc, hu', if_neg hi, comp_one]
    · simp
  · rw [Matrix.det_reindex_self, Matrix.det_blockDiagonal]
    simp

theorem appLE_constFn {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R) (f : Y ⟶ X) (hf : f ≫ q = q')
    (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V h).hom (constFn q U a) = constFn q' V a := by
  subst hf
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE f q ⊤ U V (fun _ _ => trivial) h)

theorem res_constFn {X : Scheme.{0}} (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn q U a) = constFn q V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map q (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem constFn_pow {X : Scheme.{0}} (q : X ⟶ Sp R) (U : X.Opens) (a : R) (n : ℕ) :
    constFn q U (a ^ n) = constFn q U a ^ n := by
  simp only [constFn, map_pow]

def constMul {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} (a : R) (s : L.Sec) : L.Sec where
  f i := constFn q _ a * s.f i
  compat i j := by
    rw [map_mul, map_mul, res_constFn, res_constFn, s.compat, mul_left_comm]

theorem nonzeroLocus_constMul {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} {a : R} (ha : IsUnit a) (s : L.Sec) :
    Out.nonzeroLocus (constMul q a s) = Out.nonzeroLocus s := by
  refine iSup_congr fun i => ?_
  have h : IsUnit (constFn q (L.U i) a) := (ha.map _).map _
  change X.basicOpen (constFn q _ a * s.f i) = _
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ h]
  exact inf_eq_right.2 (X.basicOpen_le _)

theorem isKeyPow_change : ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K) (M : Matrix (Fin P.g) (Fin P.g) K) (j : ℕ) (y : KeyIn K), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → GlobalTheory.KeyPow.IsKeyPow y ⟨P, hg, rig, hr, th, hth, v, hv⟩ j → ∃ (t : y.P.L.Sec) (ht : _) (w : _) (hw : _) (M' : Matrix (Fin y.P.g) (Fin y.P.g) K), GlobalTheory.KeyPow.IsKeyPow ⟨y.P, y.g_pos, y.rig, y.rig_gen, t, ht, w, hw⟩ ⟨P, hg, rig, hr, th', hth', v', hv'⟩ j ∧ (∀ i, t.f i = constFn y.P.A.hom _ (a ^ j) * y.th.f i) ∧ (∀ i, IsLieComb (M' i) y.v (w i)) ∧ M'.det = M.det ^ j := by
  intro K _ P hg rig hr th hth v hv th' hth' v' hv' a M j y ha hM ⟨p, hj, h₁, h₂, h₃⟩
  have h0 : a ≠ 0 := by
    rintro rfl
    obtain ⟨x, -, hx⟩ := hth' (default : PrimeSpectrum K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    rw [ha i, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  haveI := y.P.isAb.comm
  haveI := P.isAb.comm
  obtain ⟨w, M', hw, hw', hM', hdet⟩ := exists_block_basis p.toIsPowGrp hj hv hv' M hM y.v h₃
  refine ⟨constMul y.P.A.hom (a ^ j) y.th, fun s => ?_, w, hw, M', ⟨p, hj, h₁, fun jj b h => ?_, hw'⟩,
    fun _ => rfl, hM', hdet⟩
  · rw [nonzeroLocus_constMul _ (pow_ne_zero j h0).isUnit]
    exact y.th_ne s
  · have h₄ := h₂ jj b h
    have h₅ : ∀ i, ((p.pr i).left.appLE _ _ (h i)).hom (th'.f (jj i)) =
        constFn y.P.A.hom _ a * ((p.pr i).left.appLE _ _ (h i)).hom (th.f (jj i)) := fun i => by
      rw [ha, map_mul, appLE_constFn _ _ _ (Over.w (p.pr i))]
    refine (Finset.prod_congr rfl fun i _ => h₅ i).trans ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (congrArg (_ * ·) h₄).trans ?_
    have h₆ : resG _ (inf_le_right : (Out.boxLB P.L p.pr).U jj ⊓ y.P.L.U b ≤ _)
        ((constMul y.P.A.hom (a ^ j) y.th).f b) =
        constFn y.P.A.hom _ a ^ j * resG _ inf_le_right (y.th.f b) := by
      rw [← constFn_pow, ← res_constFn y.P.A.hom (inf_le_right : (Out.boxLB P.L p.pr).U jj ⊓ y.P.L.U b ≤ _)]
      exact map_mul _ _ _
    exact (mul_left_comm _ _ _).trans (congrArg (_ * ·) h₆.symm)

end GlobalTheory.PowChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaLawMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyPow


open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi in
theorem thetaLaw_mul : ∀ (g : ℕ) (sp sq : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (n n' m m' k k' : Fin g → ℤ), sp ∈ Matrix.symplecticGroup (Fin g) ℤ → sq ∈ Matrix.symplecticGroup (Fin g) ℤ → GlobalTheory.KeyPow.ThetaLaw g sq n n' m m' → GlobalTheory.KeyPow.ThetaLaw g sp m m' k k' → GlobalTheory.KeyPow.ThetaLaw g (sp * sq) n n' k k' := by
  intro g x y n n' m m' k k' hx hy Hy Hx
  obtain ⟨c₁, hc₁, h₁⟩ := Hy
  obtain ⟨c₂, hc₂, h₂⟩ := Hx
  refine ⟨c₂ * c₁, by rw [mul_pow, hc₁, hc₂, _root_.one_mul], fun τ hτ z => ?_⟩
  have hjy := jAut_isUnit hy hτ
  have hτ₂ := spAct_mem hy hτ
  have hjx := jAut_isUnit hx hτ₂
  rw [spAct_mul x y τ hjy, zAct_mul x y τ hjy z, h₂ _ hτ₂, h₁ τ hτ z, det_jAut_mul x y τ hjy,
    expArg_mul x y τ hjy hjx (sp_A hy hτ.1 hjy) z, eC_add]
  ring

end GlobalTheory.KeyPow
end

