module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueRealLinearOfEventuallyAddModDiscrete
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieBasisOfHolUnif
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTan JetR
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.UnifLieBasis

open TangentOrigin
open ReciprocityTheory.ChartRestriction.G.Chart (JetR jetAug qD rD scaleD IsTan isTan_iff prodPts isLieComb_iff)

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem spMap_jetAug_surjective :
    Function.Surjective (spMap (jetAug ℂ (Fin 2) 1).toRingHom) := by
  intro q
  have : q ∈ Set.range (PrimeSpectrum.comap (jetAug ℂ (Fin 2) 1).toRingHom) := by
    rw [range_comap_of_surjective _ _ (fun a => ⟨algebraMap ℂ _ a, (jetAug ℂ (Fin 2) 1).commutes a⟩)]
    intro b hb
    refine q.2.mem_of_pow_mem (1 + 1) ?_
    have h := Ideal.pow_mem_pow (I := RingHom.ker (jetAug ℂ (Fin 2) 1)) hb (1 + 1)
    rw [Chart.ker_jetAug_pow, Ideal.mem_bot] at h
    rw [h]
    exact zero_mem _
  exact this


omit u in
theorem snd_evalPt_mul {v v' : epsR ℂ ⟶ A} (hv : _root_.ReciprocityTheory.ChartRestriction.G.Chart.IsTan (R := ℂ) (G := A) v) (hv' : _root_.ReciprocityTheory.ChartRestriction.G.Chart.IsTan (R := ℂ) (G := A) v')
    (U : A.left.Opens) (h0 : ⊤ ≤ (1 : Chart.sp (R₀ := ℂ) ℂ ⟶ A).left ⁻¹ᵁ U)
    (h : ⊤ ≤ v.left ⁻¹ᵁ U) (h' : ⊤ ≤ v'.left ⁻¹ᵁ U) (h'' : ⊤ ≤ (v * v').left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    (evalPt (R := DualNumber ℂ) (v * v').left U h'' f).snd =
      (evalPt (R := DualNumber ℂ) v.left U h f).snd + (evalPt (R := DualNumber ℂ) v'.left U h' f).snd := by
  let P : Chart.sp (R₀ := ℂ) (_root_.ReciprocityTheory.ChartRestriction.G.Chart.JetR ℂ (Fin 2) 1) ⟶ A := (Chart.spMap (qD 0) ≫ v) * (Chart.spMap (qD 1) ≫ v')
  have hP : Chart.spMap (jetAug ℂ (Fin 2) 1) ≫ P = 1 := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, Chart.spMap_comp, Chart.spMap_comp,
      Chart.jetAug_comp_qD, Chart.jetAug_comp_qD, hv, hv', _root_.mul_one]
  have hPU : ⊤ ≤ P.left ⁻¹ᵁ U := fun p _ => by
    obtain ⟨q, rfl⟩ := spMap_jetAug_surjective p
    rw [← hP] at h0
    exact h0 (Set.mem_univ q)
  have hval : ∀ l : ℂ × ℂ →ₗ[ℂ] ℂ, Chart.spMap (rD l) ≫ P =
      (Chart.spMap (scaleD (l ((1 : ℂ), (0 : ℂ)))) ≫ v) * (Chart.spMap (scaleD (l ((0 : ℂ), (1 : ℂ)))) ≫ v') := by
    intro l
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, Chart.spMap_comp, Chart.spMap_comp,
      Chart.restrictDiag_comp_incl_fst, Chart.restrictDiag_comp_incl_snd]
  have key : ∀ (l : ℂ × ℂ →ₗ[ℂ] ℂ) (w : epsR ℂ ⟶ A) (hw : ⊤ ≤ w.left ⁻¹ᵁ U), Chart.spMap (rD l) ≫ P = w →
      evalPt (R := DualNumber ℂ) w.left U hw f = rD l (evalPt (R := _root_.ReciprocityTheory.ChartRestriction.G.Chart.JetR ℂ (Fin 2) 1) P.left U hPU f) := by
    rintro l w hw rfl
    exact evalPt_spMap_comp (rD l : _root_.ReciprocityTheory.ChartRestriction.G.Chart.JetR ℂ (Fin 2) 1 →+* DualNumber ℂ) P.left U hPU hw f
  rw [key (LinearMap.fst ℂ ℂ ℂ) v h, key (LinearMap.snd ℂ ℂ ℂ) v' h',
    key (LinearMap.fst ℂ ℂ ℂ + LinearMap.snd ℂ ℂ ℂ) (v * v') h'', Chart.snd_rD_add]
  · rw [hval]
    simp only [LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply, add_zero, zero_add]
    rw [Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Category.id_comp]
  · rw [hval]
    simp only [LinearMap.fst_apply, LinearMap.snd_apply]
    rw [Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Chart.spMap_scaleD_zero hv, _root_.one_mul]
  · rw [hval]
    simp only [LinearMap.fst_apply, LinearMap.snd_apply]
    rw [Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Chart.spMap_scaleD_zero hv', _root_.mul_one]

theorem isDiff_add {w w' : Fin g → ℂ} {v v' : epsR ℂ ⟶ A} (hv : _root_.ReciprocityTheory.ChartRestriction.G.Chart.IsTan (R := ℂ) (G := A) v)
    (hv' : _root_.ReciprocityTheory.ChartRestriction.G.Chart.IsTan (R := ℂ) (G := A) v') (hd : u.IsDiff w v) (hd' : u.IsDiff w' v') : u.IsDiff (w + w') (v * v') := by
  intro U h'' f
  have ht := Chart.isTan_mul hv hv'
  have h0 := (tangent_mem_iff (u := u) ((isTan_iff _).1 ht) U).1 h''
  have h := (tangent_mem_iff (u := u) ((isTan_iff _).1 hv) U).2 h0
  have h' := (tangent_mem_iff (u := u) ((isTan_iff _).1 hv') U).2 h0
  have h1 : ⊤ ≤ (1 : Chart.sp (R₀ := ℂ) ℂ ⟶ A).left ⁻¹ᵁ U := by
    rw [← hv]
    exact fun p _ => h (Set.mem_univ _)
  rw [map_add (f := _), ← hd U h f, ← hd' U h' f]
  exact snd_evalPt_mul hv hv' U h1 h h' h'' f

theorem isDiff_smul {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} (hv : _root_.ReciprocityTheory.ChartRestriction.G.Chart.IsTan (R := ℂ) (G := A) v) (hd : u.IsDiff w v) (c : ℂ) :
    u.IsDiff (c • w) (Chart.spMap (scaleD c) ≫ v) := by
  intro U h' f
  have h0 := (tangent_mem_iff (u := u) ((isTan_iff _).1 (Chart.isTan_scale c hv)) U).1 h'
  have h := (tangent_mem_iff (u := u) ((isTan_iff _).1 hv) U).2 h0
  rw [map_smul, ← hd U h f]
  refine (congrArg TrivSqZeroExt.snd
    (evalPt_spMap_comp (scaleD c : DualNumber ℂ →+* DualNumber ℂ) v.left U h h' f)).trans ?_
  exact TrivSqZeroExt.snd_map _ _

theorem isDiff_zero : u.IsDiff 0 (1 : epsR ℂ ⟶ A) := by
  intro U h f
  have ht : _root_.ReciprocityTheory.ChartRestriction.G.Chart.IsTan (R := ℂ) (G := A) (1 : epsR ℂ ⟶ A) := Chart.isTan_one
  have h1 : ⊤ ≤ (1 : Chart.sp (R₀ := ℂ) ℂ ⟶ A).left ⁻¹ᵁ U := by
    rw [← ht]
    exact fun p _ => h (Set.mem_univ _)
  have key : ∀ (w : epsR ℂ ⟶ A) (hw : ⊤ ≤ w.left ⁻¹ᵁ U), w = 1 →
      (evalPt (R := DualNumber ℂ) w.left U hw f).snd = (evalPt (R := DualNumber ℂ) (1 : epsR ℂ ⟶ A).left U h f).snd := by
    rintro w hw rfl
    rfl
  have h2 : ⊤ ≤ (1 * 1 : epsR ℂ ⟶ A).left ⁻¹ᵁ U := by rwa [_root_.mul_one]
  have := snd_evalPt_mul ht ht U h1 h h h2 f
  rw [key _ h2 (_root_.mul_one _)] at this
  rw [map_zero]
  exact left_eq_add.1 this

theorem isDiff_list_prod : ∀ {k : ℕ} (w : Fin k → Fin g → ℂ) (v : Fin k → (epsR ℂ ⟶ A)),
    (∀ i, _root_.ReciprocityTheory.ChartRestriction.G.Chart.IsTan (R := ℂ) (G := A) (v i)) → (∀ i, u.IsDiff (w i) (v i)) →
    _root_.ReciprocityTheory.ChartRestriction.G.Chart.IsTan (R := ℂ) (G := A) (List.ofFn v).prod ∧ u.IsDiff (∑ i, w i) (List.ofFn v).prod := by
  intro k
  induction k with
  | zero =>
    intro w v _ _
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨Chart.isTan_one, isDiff_zero u⟩
  | succ k ih =>
    intro w v hv hd
    obtain ⟨h1, h2⟩ := ih (fun i => w i.succ) (fun i => v i.succ)
      (fun i => hv i.succ) (fun i => hd i.succ)
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact ⟨Chart.isTan_mul (hv 0) h1, isDiff_add u (hv 0) h1 (hd 0) h2⟩

theorem isTangent_comp (f : A ⟶ A) [IsMonHom f] {v : epsR ℂ ⟶ A} (hv : IsTangent v) : IsTangent (v ≫ f) := by
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]

theorem isDiff_comp (f : A ⟶ A) [IsMonHom f] (F : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A}
    (hv : IsTangent v) (hd : u.IsDiff w v) : u.IsDiff (F w) (v ≫ f) := by
  intro U h s
  have h1 := hd (f.left ⁻¹ᵁ U) h ((f.left.app U).hom s)
  have e : ((v ≫ f).left.appLE U ⊤ h).hom s =
      (v.left.appLE (f.left ⁻¹ᵁ U) ⊤ h).hom ((f.left.app U).hom s) := by
    have := Scheme.Hom.comp_appLE v.left f.left U ⊤ h
    exact congrArg (fun φ => φ.hom s) this
  have hdiff := differentiableAt_val u ((tangent_mem_iff (u := u) (isTangent_comp f hv) U).1 h) s
  have hfun : (fun z => valAt' (u.ex z).left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s)) =
      (fun z => valAt' (u.ex z).left U s) ∘ F := by
    funext z
    rw [valAt'_comp, Function.comp_apply, hF]
    rfl
  have hch := (HasFDerivAt.comp (0 : Fin g → ℂ) (f := F)
    (by rw [map_zero]; exact hdiff.hasFDerivAt) F.hasFDerivAt).fderiv
  rw [hfun, hch] at h1
  rw [e]
  exact h1

end GlobalTheory.UnifLieBasis


open GlobalTheory.UnifLieBasis in
open ReciprocityTheory.ChartRestriction.G.Chart (IsTan isTan_iff prodPts isLieComb_iff isTan_scale) in
theorem GlobalTheory.exists_lieBasis_of_holUnif : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), Smooth A.hom → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → ∃ v : Fin g → (epsR ℂ ⟶ A), IsLieBasis v ∧ ∀ (f : A ⟶ A) (c : Fin g → ℂ), IsMonHom f → (∀ z, u.ex (fun k => c k * z k) = u.ex z ≫ f) → ∀ i, (v i ≫ f).left = spMap (epsScale (c i)) ≫ (v i).left := by
  intro A _ L g u _ h1 h2
  choose v hv using fun i : Fin g => (h2 (Pi.single i 1)).exists
  have ht : ∀ i, _root_.ReciprocityTheory.ChartRestriction.G.Chart.IsTan (R := ℂ) (G := A) (v i) := fun i => (isTan_iff _).2 (hv i).1
  have hp : ∀ c : Fin g → ℂ, IsTangent (prodPts (R := ℂ) (G := A) c v) ∧ u.IsDiff c (prodPts (R := ℂ) (G := A) c v) := by
    intro c
    obtain ⟨a, b⟩ := isDiff_list_prod u (fun i => c i • (Pi.single i 1 : Fin g → ℂ)) _
      (fun i => isTan_scale (c i) (ht i)) (fun i => isDiff_smul u (ht i) (hv i).2 (c i))
    rw [← pi_eq_sum_univ' c] at b
    exact ⟨(isTan_iff _).1 a, b⟩
  refine ⟨v, ⟨fun i => (hv i).1, fun w hw => ?_⟩, fun f c hf hF i => ?_⟩
  · obtain ⟨c, hc, hcu⟩ := h1 w hw
    refine ⟨c, (isLieComb_iff c v w).2 ((h2 c).unique ⟨hw, hc⟩ (hp c)), fun c' hc' => hcu c' ?_⟩
    rw [(isLieComb_iff c' v w).1 hc']
    exact (hp c').2
  · let F : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := ContinuousLinearMap.pi fun k => c k • ContinuousLinearMap.proj k
    have hd := isDiff_comp u f F hF (hv i).1 (hv i).2
    have e : F (Pi.single i 1) = c i • (Pi.single i 1 : Fin g → ℂ) := by
      funext k
      by_cases hk : k = i <;> simp [F, hk]
    rw [e] at hd
    exact congrArg CommaMorphism.left ((h2 _).unique ⟨isTangent_comp f (hv i).1, hd⟩
      ⟨(isTan_iff _).1 (isTan_scale (c i) (ht i)), isDiff_smul u (ht i) (hv i).2 (c i)⟩)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology

namespace GlobalTheory.LocLift

noncomputable section

section Hol

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {X Y : Scheme.{0}}

theorem isHolTo_comp_hom {B : Set V} {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (φ : X ⟶ Y) :
    IsHolTo B (fun b => y b ≫ φ) := by
  intro U f
  have := h (φ ⁻¹ᵁ U) ((φ.app U).hom f)
  simpa only [valAt'_comp, ← top_le_preimage_comp] using this

theorem isHolTo_comp {B : Set V} {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) {C : Set W} (hC : IsOpen C) {β : W → V}
    (hβ : DifferentiableOn ℂ β C) (hm : Set.MapsTo β C B) : IsHolTo C (fun w => y (β w)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  refine ⟨?_, h2.comp (hβ.mono fun w hw => hw.1) fun w hw => ⟨hm hw.1, hw.2⟩⟩
  have := hβ.continuousOn.isOpen_inter_preimage hC h1
  convert this using 1
  ext w
  exact ⟨fun hw => ⟨hw.1, hm hw.1, hw.2⟩, fun hw => ⟨hw.1, hw.2.2⟩⟩

theorem isHolTo_congr {B : Set V} {y y' : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (e : ∀ b ∈ B, y' b = y b) :
    IsHolTo B y' := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have : {b ∈ B | ⊤ ≤ y' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext b
    exact and_congr_right fun hb => by rw [e b hb]
  rw [this]
  exact ⟨h1, h2.congr fun b hb => by rw [e b hb.1]⟩

theorem isHolTo_mono {B C : Set V} {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (hC : IsOpen C) (hCB : C ⊆ B) :
    IsHolTo C y :=
  isHolTo_comp (β := id) h hC differentiableOn_id hCB

end Hol

section Grp

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Q : Type} [Group Q]

theorem hom_zero {A : Type} [AddGroup A] {e : A → Q} (h : ∀ z w, e (z + w) = e z * e w) : e 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem hom_sub_eq_one {A : Type} [AddGroup A] {e : A → Q} (h : ∀ z w, e (z + w) = e z * e w) {z w : A} :
    e (z - w) = 1 ↔ e z = e w := by
  have := h (z - w) w
  rw [sub_add_cancel] at this
  rw [this, mul_eq_right]

theorem hom_nsmul {A : Type} [AddGroup A] {e : A → Q} (h : ∀ z w, e (z + w) = e z * e w) (z : A) (n : ℕ) :
    e (n • z) = e z ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, hom_zero h]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

def homKer {A : Type} [AddGroup A] {e : A → Q} (h : ∀ z w, e (z + w) = e z * e w) : AddSubgroup A :=
  (AddMonoidHom.mk' (G := Additive Q) (fun z => Additive.ofMul (e z)) fun z w => congrArg _ (h z w)).ker

theorem mem_homKer {A : Type} [AddGroup A] {e : A → Q} (h : ∀ z w, e (z + w) = e z * e w) {z : A} :
    z ∈ homKer h ↔ e z = 1 := Iff.rfl

theorem isDiscrete_of_norm {K : AddSubgroup W} {r : ℝ} (hr : 0 < r) (h : ∀ z ∈ K, ‖z‖ < r → z = 0) :
    IsDiscrete (K : Set W) := by
  have : DiscreteTopology K := DiscreteTopology.of_forall_le_norm (E := K) hr fun x hx =>
    not_lt.1 fun h' => hx (Subtype.ext (h x x.2 h'))
  exact DiscreteTopology.isDiscrete

theorem linear_lift_unique {e : W → Q} (h : ∀ z w, e (z + w) = e z * e w) {r : ℝ} (hr : 0 < r)
    (hk : ∀ z, ‖z‖ < r → e z = 1 → z = 0) {L L' : V →ₗ[ℂ] W} (hL : ∀ z, e (L z) = e (L' z)) : L = L' := by
  have := realLinear_eq_of_sub_mem_discrete (Γ := homKer h) (isDiscrete_of_norm hr fun z hz hn => hk z hn hz)
    (L := L.restrictScalars ℝ) (L' := L'.restrictScalars ℝ) fun x => (hom_sub_eq_one h).2 (hL x)
  ext z
  exact DFunLike.congr_fun this z

theorem fderiv_lift {x : V → Q} {e : W → Q} (hx : ∀ z w, x (z + w) = x z * x w) (h : ∀ z w, e (z + w) = e z * e w)
    (hs : Function.Surjective e) {r : ℝ} (hr : 0 < r) (hk : ∀ z, ‖z‖ < r → e z = 1 → z = 0) {ζ : V → W}
    (hd : DifferentiableAt ℂ ζ 0) (hζ : ∀ᶠ z in 𝓝 0, e (ζ z) = x z) (z : V) : e (fderiv ℂ ζ 0 z) = x z := by
  letI : CommGroup Q := { (inferInstance : Group Q) with
    mul_comm := fun a b => by
      obtain ⟨a, rfl⟩ := hs a
      obtain ⟨b, rfl⟩ := hs b
      rw [← h, ← h, add_comm] }
  exact apply_fderiv_eq_of_germ (𝕜 := ℂ) (A := Additive Q)
    (ex := AddMonoidHom.mk' (fun z => Additive.ofMul (x z)) fun z w => congrArg _ (hx z w))
    (ex' := AddMonoidHom.mk' (fun z => Additive.ofMul (e z)) fun z w => congrArg _ (h z w))
    (isDiscrete_of_norm hr fun z hz hn => hk z hn hz) hd hζ z

theorem exists_linearEquiv_lift [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {x : V → Q} {e : W → Q}
    (hx : ∀ z w, x (z + w) = x z * x w) (h : ∀ z w, e (z + w) = e z * e w) (hsx : Function.Surjective x)
    (hs : Function.Surjective e) (hkx : IsDiscrete {z | x z = 1})
    {r : ℝ} (hr : 0 < r) (hk : ∀ z, ‖z‖ < r → e z = 1 → z = 0) {ζ : V → W}
    (hd : DifferentiableAt ℂ ζ 0) (hζ : ∀ᶠ z in 𝓝 0, e (ζ z) = x z) : ∃ L : V ≃L[ℂ] W, ∀ z, e (L z) = x z := by
  letI : CommGroup Q := { (inferInstance : Group Q) with
    mul_comm := fun a b => by
      obtain ⟨a, rfl⟩ := hs a
      obtain ⟨b, rfl⟩ := hs b
      rw [← h, ← h, add_comm] }
  obtain ⟨L, hL, -⟩ := existsUnique_linearEquiv_of_uniformisations (𝕜 := ℂ) (A := Additive Q)
    (ex := AddMonoidHom.mk' (fun z => Additive.ofMul (x z)) fun z w => congrArg _ (hx z w))
    (ex' := AddMonoidHom.mk' (fun z => Additive.ofMul (e z)) fun z w => congrArg _ (h z w))
    hkx (isDiscrete_of_norm hr fun z hz hn => hk z hn hz) (fun q _ => hsx q) hd hζ
  exact ⟨L, hL.1⟩

theorem eq_zero_of_small {T : Type} [TopologicalSpace T] {B : Set T} (hB : IsPreconnected B) {d : T → W}
    (hd : ContinuousOn d B) {r : ℝ} (hr : 0 < r) (h : ∀ b ∈ B, ‖d b‖ < r → d b = 0) {b₀ : T} (hb₀ : b₀ ∈ B)
    (h0 : d b₀ = 0) : ∀ b ∈ B, d b = 0 := by
  intro b hb
  refine h b hb (not_le.1 fun hle => ?_)
  obtain ⟨c, hc, hc'⟩ := hB.intermediate_value hb₀ hb hd.norm
    (show r / 2 ∈ Set.Icc ‖d b₀‖ ‖d b‖ from ⟨by rw [h0, norm_zero]; positivity, by linarith⟩)
  have hc'' : ‖d c‖ = r / 2 := hc'
  have := h c hc (by linarith)
  rw [this, norm_zero] at hc''
  linarith

end Grp

section Exp

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}

def IsExp (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) : Prop :=
  (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)

def HasLifts (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X))
    (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) : Prop :=
  ∀ (n : ℕ) (W : Set (Fin n → ℂ)) (β : (Fin n → ℂ) → (Fin m → ℂ)) (x : ∀ w, Over.mk (y (β w)) ⟶ G)
    (w₀ : Fin n → ℂ) (z₀ : Fin g → ℂ), IsOpen W → w₀ ∈ W → DifferentiableOn ℂ β W → Set.MapsTo β W B →
    IsHolTo W (fun w => (x w).left) → e (β w₀) z₀ = x w₀ →
    ∃ ζ : (Fin n → ℂ) → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w

omit [GrpObj G] in
theorem HasLifts.lift {B : Set (Fin m → ℂ)} {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)}
    {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} (h : HasLifts B y e) {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] {W : Set V} {β : V → (Fin m → ℂ)} (x : ∀ w, Over.mk (y (β w)) ⟶ G)
    {w₀ : V} {z₀ : Fin g → ℂ} (hW : IsOpen W) (hw₀ : w₀ ∈ W) (hβ : DifferentiableOn ℂ β W)
    (hm : Set.MapsTo β W B) (hx : IsHolTo W (fun w => (x w).left)) (h0 : e (β w₀) z₀ = x w₀) :
    ∃ ζ : V → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w := by
  let φ : V ≃L[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨u₀, rfl⟩ := φ.symm.surjective w₀
  have hW' : IsOpen (φ.symm ⁻¹' W) := hW.preimage φ.symm.continuous
  obtain ⟨ζ, h1, h2, h3⟩ := h _ (φ.symm ⁻¹' W) (fun u => β (φ.symm u)) (fun u => x (φ.symm u)) u₀ z₀ hW' hw₀
    (hβ.comp φ.symm.differentiableOn fun _ hu => hu) (fun _ hu => hm hu)
    (isHolTo_comp hx hW' φ.symm.differentiableOn fun _ hu => hu) h0
  refine ⟨fun w => ζ (φ w), by simpa using h1, ?_, ?_⟩
  · exact AnalyticAt.comp_of_eq h2 (φ.toContinuousLinearMap.analyticAt (φ.symm u₀)) (by simp)
  · have ht : map φ.symm (𝓝 u₀) = 𝓝 (φ.symm u₀) := φ.symm.toHomeomorph.map_nhds_eq u₀
    rw [← ht, eventually_map]
    simpa only [φ.apply_symm_apply] using h3

theorem isDerivAt0_comp {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (h : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) (w : Fin g → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 (fun z => e (h z)) w v ↔ IsDerivAt0 e (h w) v := by
  have key : ∀ (U : X.Opens) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (h z)) U f) 0 w =
      fderiv ℂ (fun z => valAt' (e z) U f) 0 (h w) := fun U f => by
    have := h.comp_right_fderiv (f := fun z => valAt' (e z) U f) (x := 0)
    rw [map_zero] at this
    exact DFunLike.congr_fun this w
  simp only [IsDerivAt0, key, map_zero]

theorem IsExp.comp {y : Sp ℂ ⟶ X} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : IsExp y e)
    (h : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) : IsExp y (fun z => e (h z)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := he
  refine ⟨fun z w => by simp only [map_add (f := _), h1], h2.comp h.surjective,
    isHolTo_comp h3 isOpen_univ h.differentiableOn (Set.mapsTo_univ _ _), fun w => ?_, fun v hv => ?_⟩
  · simpa only [isDerivAt0_comp (e := fun z => (e z).left)] using h4 (h w)
  · simp only [isDerivAt0_comp (e := fun z => (e z).left)]
    obtain ⟨w, hw, hu⟩ := h5 v (by simpa only [map_zero] using hv)
    exact ⟨h.symm w, by simpa using hw, fun w' hw' => by rw [← hu _ hw', h.symm_apply_apply]⟩

theorem one_left (y : Sp ℂ ⟶ X) : (1 : Over.mk y ⟶ G).left = y ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl

theorem eq_one_of_mem_range [IsSeparated G.hom] {y : Sp ℂ ⟶ X} (x : Over.mk y ⟶ G)
    (hx : x.left (default : PrimeSpectrum ℂ) ∈ Set.range η[G].left) : x = 1 := by
  have hw : η[G].left ≫ G.hom = 𝟙 _ := Over.w η[G]
  haveI : IsClosedImmersion (η[G].left ≫ G.hom) := hw ▸ inferInstance
  haveI : IsClosedImmersion η[G].left := IsClosedImmersion.of_comp _ G.hom
  haveI : IsReduced (Over.mk y).left := inferInstanceAs (IsReduced (Sp ℂ))
  haveI : Surjective (pullback.fst x.left η[G].left) := ⟨fun p => by
    have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    subst this
    change _ ∈ Set.range _
    rw [Scheme.Pullback.range_fst]
    exact hx⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.fst x.left η[G].left)
  have e : x.left = (inv (pullback.fst x.left η[G].left) ≫ pullback.snd _ _) ≫ η[G].left := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  have e' : inv (pullback.fst x.left η[G].left) ≫ pullback.snd _ _ = y := by
    have := Over.w x
    rw [e, Category.assoc, hw] at this
    exact (Category.comp_id _).symm.trans this
  rw [e'] at e
  exact Over.OverMorphism.ext (e.trans (one_left y).symm)

theorem isOpen_ne_one [IsSeparated G.hom] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V}
    {y : V → (Sp ℂ ⟶ X)} {x : ∀ b, Over.mk (y b) ⟶ G} (hx : IsHolTo B (fun b => (x b).left)) :
    IsOpen {b ∈ B | x b ≠ 1} := by
  have hw : η[G].left ≫ G.hom = 𝟙 _ := Over.w η[G]
  haveI : IsClosedImmersion (η[G].left ≫ G.hom) := hw ▸ inferInstance
  haveI : IsClosedImmersion η[G].left := IsClosedImmersion.of_comp _ G.hom
  let U : G.left.Opens := ⟨(Set.range η[G].left)ᶜ, η[G].left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  convert (hx U 0).1 using 3 with b
  refine and_congr_right fun _ => ?_
  rw [top_le_preimage_iff_mem]
  refine not_congr ⟨fun h => ?_, eq_one_of_mem_range _⟩
  beta_reduce
  rw [h, one_left]
  exact ⟨y b (default : PrimeSpectrum ℂ), rfl⟩

end Exp

end

end GlobalTheory.LocLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSumSmulSeparatingInertia
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
theorem _root_.GlobalTheory.exists_sum_smul_separating_inertia :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (B : Type) [CommRing B] [MulSemiringAction Γ B]
      (q : Ideal B), q.IsPrime → ∃ (n : ℕ) (c d : Fin n → B) (s : B), s ∉ q ∧ ∀ g : Γ,
        (g ∈ q.inertia Γ → (∑ j, d j * g • c j) - s ∈ q) ∧
        (g ∉ q.inertia Γ → (∑ j, d j * g • c j) ∈ q) := by
  intro Γ _ _ B _ _ q hq
  classical
  haveI := Fintype.ofFinite Γ
  have hmem : ∀ g : Γ, g ∈ q.inertia Γ ↔ ∀ x, g • x - x ∈ q := fun g => Iff.rfl
  have factor : ∀ h : Γ, ∃ x y : B, x + y ∉ q ∧ (h ∉ q.inertia Γ → h • x + y ∈ q) := by
    intro h
    by_cases hh : h ∈ q.inertia Γ
    · exact ⟨1, 0, by simpa using hq.one_notMem, fun h' => (h' hh).elim⟩
    · obtain ⟨x, hx⟩ : ∃ x, h • x - x ∉ q := by simpa [hmem] using hh
      refine ⟨x, -(h • x), fun hm => hx ?_, fun _ => by simp⟩
      rw [← neg_sub]
      exact q.neg_mem (by rwa [sub_eq_add_neg])
  choose x y hxy hzero using factor
  let e := (Fintype.equivFin (Finset Γ)).symm
  have key : ∀ g : Γ, ∑ j, (∏ h ∈ Finset.univ \ e j, y h) * g • ∏ h ∈ e j, x h =
      ∏ h, (g • x h + y h) := by
    intro g
    rw [Finset.prod_add, Finset.powerset_univ,
      Equiv.sum_comp e (fun t => (∏ h ∈ Finset.univ \ t, y h) * g • ∏ h ∈ t, x h)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.smul_prod', mul_comm]
  refine ⟨Fintype.card (Finset Γ), fun j => ∏ h ∈ e j, x h, fun j => ∏ h ∈ Finset.univ \ e j, y h,
    ∏ h, (x h + y h), ?_, fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · intro hs
    obtain ⟨h, -, hh⟩ := Ideal.IsPrime.prod_mem_iff.mp hs
    exact hxy h hh
  · rw [key, ← Ideal.Quotient.eq, map_prod, map_prod]
    refine Finset.prod_congr rfl fun h _ => ?_
    rw [Ideal.Quotient.eq]
    simpa using (hmem g).mp hg (x h)
  · rw [key]
    exact Ideal.IsPrime.prod_mem_iff.mpr ⟨g, Finset.mem_univ g, hzero g hg⟩

end GlobalTheory
end

