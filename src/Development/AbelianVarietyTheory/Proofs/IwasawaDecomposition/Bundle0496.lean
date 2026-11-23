module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FiniteOfLocallyFinite
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0489

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameActionUpperTriangularBlockExists
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.BlockTransporter

theorem exists_unitary_mul_upper {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) :
    ∃ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ t : Matrix (Fin n) (Fin n) ℂ, t.BlockTriangular id ∧ y = u * t := by
  first
  | exact @_root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular
  | exact _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular
  | (apply _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular ..)

theorem exists_unitary_block {r p : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (hB : B.det ≠ 0)
    (h0 : ∀ a c : Fin r, (c : ℕ) < p → ¬ (a : ℕ) < p → B a c = 0) :
    ∃ u t : Matrix (Fin r) (Fin r) ℂ, u ∈ Matrix.unitaryGroup (Fin r) ℂ ∧
      (∀ a c : Fin r, (c : ℕ) < p → ¬ (a : ℕ) < p → u a c = 0) ∧
      t.det ≠ 0 ∧ (∀ a c : Fin r, c < a → t a c = 0) ∧ B = u * t := by
  obtain ⟨u, hu, t, ht, e⟩ := exists_unitary_mul_upper B
  have hud : u.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 hu)
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  have htd : t.det ≠ 0 := by
    intro h; rw [e, det_mul, h, mul_zero] at hB; exact hB rfl
  letI := invertibleOfIsUnitDet t htd.isUnit
  have hti : (t⁻¹).BlockTriangular id := blockTriangular_inv_of_blockTriangular ht
  have hu' : u = B * t⁻¹ := by rw [e, Matrix.mul_nonsing_inv_cancel_right _ _ htd.isUnit]
  refine ⟨u, t, hu, fun a c hc ha => ?_, htd, fun a c h => ht h, e⟩
  rw [hu', Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k ≤ c
  · rw [h0 a k (lt_of_le_of_lt (Fin.le_def.1 hk) hc) ha, zero_mul]
  · rw [hti (not_le.1 hk), mul_zero]

end GlobalTheory.BlockTransporter

namespace GlobalTheory.BlockTransporter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def unitBlock (X : Data E r) : Set (Frame X.Ψ r) :=
  {u | ∀ τ, mat u τ ∈ Matrix.unitaryGroup (Fin r) ℂ ∧
    ∀ a c : Fin r, (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0}

theorem isCompact_unitBlock (X : Data E r) : IsCompact (unitBlock X) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have : unitBlock X = ⋂ τ, ({u : Frame X.Ψ r | star (mat u τ) * mat u τ = 1} ∩
        ⋂ a : Fin r, ⋂ c : Fin r, {u | (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0}) := by
      ext u
      simp only [unitBlock, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
      simp only [Matrix.mem_unitaryGroup_iff']
    rw [this]
    refine isClosed_iInter fun τ => IsClosed.inter ?_ (isClosed_iInter fun a => isClosed_iInter fun c => ?_)
    · have hc : Continuous fun u : Frame X.Ψ r => mat u τ := continuous_apply τ
      exact isClosed_eq (hc.star.matrix_mul hc) continuous_const
    · by_cases h : (c : ℕ) < X.p0 ∧ ¬ (a : ℕ) < X.p0
      · have : {u : Frame X.Ψ r | (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0} = {u | u τ a c = 0} := by
          ext u; simp only [Set.mem_setOf_eq]; exact ⟨fun hu => hu h.1 h.2, fun hu _ _ => hu⟩
        rw [this]
        exact isClosed_eq ((continuous_apply c).comp ((continuous_apply a).comp (continuous_apply τ)))
          continuous_const
      · have : {u : Frame X.Ψ r | (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0} = Set.univ := by
          ext u; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; intro h1 h2; exact absurd ⟨h1, h2⟩ h
        rw [this]; exact isClosed_univ
  · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun u hu => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun τ => ?_
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun a => ?_
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun c => ?_
    exact entry_norm_bound_of_unitary (hu τ).1 a c

theorem continuous_rmul (X : Data E r) : Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => rmul p.1 p.2 := by
  refine continuous_pi fun τ => ?_
  have h1 : Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => mat p.1 τ := (continuous_apply τ).comp continuous_fst
  have h2 : Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => mat p.2 τ := (continuous_apply τ).comp continuous_snd
  exact h1.matrix_mul h2

end GlobalTheory.BlockTransporter

namespace GlobalTheory.BlockTransporter

theorem finite_blockTransporter : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (K : Set (ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)), IsCompact K → K ⊆ X.dom →
    {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ x ∈ K, ∃ y ∈ K, ∃ b : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r,
      (∀ τ, (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0) ∧
      (∀ τ (a c : Fin r), (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → b τ a c = 0) ∧
      ReciprocityTheory.ChartRestriction.G.FD.lact γ x = ReciprocityTheory.ChartRestriction.G.FD.rmul y b}.Finite := by
  intro E _ _ _ r X K hK hKd
  set K' := (fun p : Frame X.Ψ r × Frame X.Ψ r => rmul p.1 p.2) '' (K ×ˢ unitBlock X) with hK'
  have hK'c : IsCompact K' := (hK.prod (isCompact_unitBlock X)).image (continuous_rmul X)
  have hK'd : K' ⊆ X.dom := by
    rintro _ ⟨⟨y, u⟩, ⟨hy, hu⟩, rfl⟩
    refine GlobalTheory.PointOfFrames.rmul_mem_dom X (hKd hy) u (fun τ h => ?_) (fun τ => (hu τ).2)
    have := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 (hu τ).1)
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  have hfin := GlobalTheory.PropDiscCompare.compact_of_local X (GlobalTheory.propDisc_of_flagDomainData E r X) (K ∪ K')
    (hK.union hK'c) (Set.union_subset hKd hK'd)
  refine hfin.subset ?_
  rintro γ ⟨hγ, x, hx, y, hy, b, hb, h0, e⟩
  have key : ∀ τ : X.Ψ, ∃ u t : Matrix (Fin r) (Fin r) ℂ, u ∈ Matrix.unitaryGroup (Fin r) ℂ ∧
      (∀ a c : Fin r, (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u a c = 0) ∧
      t.det ≠ 0 ∧ (∀ a c : Fin r, c < a → t a c = 0) ∧ mat b τ = u * t :=
    fun τ => exists_unitary_block (mat b τ) (hb τ) (h0 τ)
  choose u t hu hu0 htd ht hbut using key
  refine ⟨hγ, x, Or.inl hx, rmul y (fun τ => u τ), Or.inr ⟨(y, fun τ => u τ), ⟨hy, fun τ => ⟨hu τ, hu0 τ⟩⟩, rfl⟩,
    fun τ => t τ, fun τ => ⟨htd τ, ht τ⟩, ?_⟩
  rw [e]
  funext τ
  show mat y τ * mat b τ = (mat y τ * u τ) * t τ
  rw [Matrix.mul_assoc, ← hbut τ]

end GlobalTheory.BlockTransporter
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.FactorDepth

namespace GlobalTheory.LatDRFree

attribute [local instance] Over.cartesianMonoidalCategory

theorem intO_isLocalRing (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] : IsLocalRing ↥(intO C) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  have hu : ∀ b : ↥(intO C), ‖(b : C)‖ = 1 → IsUnit b := fun b hb => by
    have h0 : (b : C) ≠ 0 := fun h => by simp [h] at hb
    have hi : (b : C)⁻¹ ∈ intO C := by
      show ‖(b : C)⁻¹‖ ≤ 1
      rw [norm_inv, hb, inv_one]
    exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ h0))
  have ha : ‖(a : C)‖ ≤ 1 := a.2
  rcases ha.eq_or_lt with h | h
  · exact Or.inl (hu a h)
  · refine Or.inr (hu _ ?_)
    have : ‖(1 : C) + (-(a : C))‖ = max ‖(1 : C)‖ ‖-(a : C)‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg, norm_one]; exact h.ne')
    rw [norm_neg, norm_one, max_eq_left h.le, ← sub_eq_add_neg] at this
    exact this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

open MonObj in
theorem comb_map {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) :
    IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_alg])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_epsMul]
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

theorem latDR_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (xO : Sp ↥(intO C) ⟶ X), (∀ xO' : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ xO' = spMap (intO C).subtype ≫ xO → xO' = xO) → ∃ (g : ℕ) (v : Fin g → (Sp (DualNumber C) ⟶ t.G.left)), (∀ i, IsTanAtG t (spMap (intO C).subtype ≫ xO) (v i)) ∧ (∀ w, IsTanAtG t (spMap (intO C).subtype ≫ xO) w → ∃! cf : Fin g → C, IsCombAtG t (spMap (intO C).subtype ≫ xO) v cf w) ∧ ∀ (cf : Fin g → C) w, IsCombAtG t (spMap (intO C).subtype ≫ xO) v cf w → (w ∈ latDR t (spMap (intO C).subtype ≫ xO) ↔ ∀ i, ‖cf i‖ ≤ 1) := by
  intro E _ _ _ H X t C _ _ xO huniq
  have := intO_isLocalRing C
  obtain ⟨n, D, hD, hDb⟩ := GlobalTheory.LieLocBasis.exists_lie_basis_stable E H X t (↥(intO C)) xO
  have h1 : spMap (RingHom.id ↥(intO C)) = 𝟙 _ := Spec.map_id _
  have h2 : dualMap (RingHom.id ↥(intO C)) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [dualMap]
  have h3 : spMap (dualMap (RingHom.id ↥(intO C))) = 𝟙 _ := by rw [h2]; exact Spec.map_id _
  have hD0 : ∀ w, IsTanAtG t xO w → ∃! a : Fin n → ↥(intO C), IsCombAtG t xO D a w := by
    have h := hDb _ (RingHom.id ↥(intO C))
    simp only [h1, h3, Category.id_comp] at h
    exact h
  have hDk := fun j => isTanAtG_map t (intO C).subtype (hD j)
  refine ⟨n, fun e => spMap (dualMap (intO C).subtype) ≫ D e, hDk, hDb C _, fun cf w hw => ⟨?_, fun hc => ?_⟩⟩
  · rintro ⟨xO', hx, vO, hv, rfl⟩
    obtain rfl := huniq xO' hx
    obtain ⟨a, ha, -⟩ := hD0 vO hv
    have e := (hDb C _ _ (isTanAtG_map t (intO C).subtype hv)).unique hw (comb_map t (intO C).subtype ha)
    intro i
    rw [e]
    exact (a i).2
  · let a : Fin n → ↥(intO C) := fun i => ⟨cf i, hc i⟩
    have ha : IsCombAtG t xO D a (combT xO (fun j => ovT (hD j)) a).left :=
      (isCombAtG_iff t xO (fun j => ovT (hD j)) a _).2 rfl
    refine ⟨xO, rfl, _, isTanAtG_of _ (combT_tan _ (fun j => ovT (hD j)) (fun j => smT_zero_ovT _) a), ?_⟩
    have hb := comb_map t (intO C).subtype ha
    exact ((isCombAtG_iff t _ (fun j => ovT (hDk j)) _ _).1 hb).symm.trans
      ((isCombAtG_iff t _ (fun j => ovT (hDk j)) _ _).1 hw)

end GlobalTheory.LatDRFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocM.FrameBC

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X}

theorem tv_sum' {κ : Type} (s : Finset κ) (f : κ → TanM x t.G) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  simp only [tv, toMul_sum]
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

def Full {κ : Type} [Fintype κ] (v : κ → TanM x t.G) : Prop :=
  ∀ n : TanM x t.G, ∃! a : κ → S, n = ∑ k, a k • v k

theorem full_equiv {κ κ' : Type} [Fintype κ] [Fintype κ'] (e : κ' ≃ κ) {v : κ → TanM x t.G} (hv : Full v) :
    Full (fun i => v (e i)) := fun n => by
  obtain ⟨a, ha, hu⟩ := hv n
  refine ⟨fun i => a (e i), ha.trans (e.sum_comp (fun k => a k • v k)).symm, fun b hb => ?_⟩
  have := hu (fun k => b (e.symm k)) (hb.trans (by
    rw [← e.sum_comp]; simp only [Equiv.symm_apply_apply]))
  funext i; rw [← this]; simp

theorem full_iff {m : ℕ} {G' : Over (Sp S)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ t.G.left}
    (h : IsGrpPullback G' t.G x Φ) {u : Fin m → (epsR S ⟶ G')} {v : Fin m → TanM x t.G}
    (e : ∀ i, pushHom h (epsR S) (u i) = tv (v i)) : IsLieBasis u ↔ Full v := by
  have key : ∀ a p n, pushHom h (epsR S) p = tv n → (IsLieComb a u p ↔ n = ∑ k, a k • v k) := fun a p n hp => by
    rw [isLieComb_iff h, hp]
    simp only [e]
    exact ⟨fun q => tanM_ext (q.trans (by rw [tv_sum']; rfl)), fun q => (congrArg tv q).trans (by rw [tv_sum']; rfl)⟩
  refine ⟨fun hu n => ?_, fun hv => ⟨fun i => (isTangent_iff h _).2 (by rw [e]; exact tv_mem _), fun p hp => ?_⟩⟩
  · obtain ⟨p, hp⟩ := push_surj h (tv n)
    simpa only [key _ p n hp] using hu.2 p ((isTangent_iff h p).2 (by rw [hp]; exact tv_mem n))
  · simpa only [key _ p (mkT _ ((isTangent_iff h p).1 hp)) rfl] using hv (mkT _ ((isTangent_iff h p).1 hp))

def resM (ψ : S →+* T) (n : TanM x t.G) : TanM (spMap ψ ≫ x) t.G := tanOf (isTan_map ψ rfl (isTan_tv n))

theorem full_bc {m : ℕ} (ψ : S →+* T) {v : Fin m → TanM x t.G} (hv : Full v) : Full fun i => resM ψ (v i) := by
  have h₀ := isGrpPullback_pullback t.G x
  have h := isGrpPullback_pullback t.G (spMap ψ ≫ x)
  choose u hu using fun i => push_surj h₀ (tv (v i))
  choose u' hu' using fun i => push_surj h (tv (resM ψ (v i)))
  have := t.semi.smooth
  have : Smooth ((Over.pullback x).obj t.G).hom := show Smooth (pullback.snd _ _) from inferInstance
  refine (full_iff h hu').1 (Chart.frameLieBCR _ ((full_iff h₀ hu).2 hv) ψ (Chart.isGrpPullback_factor x (spMap ψ) h)
    (fun a b v hv => push_inj h (by
      have := smT_add _ _ ((isTangent_iff h v).1 ((Chart.isTan_iff _).1 hv)) a b
      rw [← push_scK h, ← push_scK h, ← push_scK h, ← map_mul] at this
      exact this)) (fun i => (isTangent_iff h _).2 (by rw [hu']; exact tv_mem _)) fun i => ?_)
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc]
    exact (congrArg (fun q => q.left) (hu' i)).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (hu i)).symm)
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (u' i), Category.assoc]
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (Over.w (u i)).symm)
    exact (spMap_comp_spMap _ _).trans ((congrArg spMap (PullbackSections.dualMap_comp_alg _).symm).trans (spMap_comp_spMap _ _).symm)

variable {l : Level H} (c : Coeff l) [Algebra c.F S]

theorem eig_iff (τ : E →+* ℂ) (n : TanM x t.G) :
    (∀ a : 𝓞 E, (tv n).left ≫ (t.act.act a).left = spMap (epsMul (algebraMap c.F S (embK c τ a))) ≫ (tv n).left) ↔
      IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) n :=
  forall_congr' fun _ => ⟨fun h => tan_ext h, fun h => congrArg (fun V => (tv V).left) h⟩

theorem eig_comb' (τ : E →+* ℂ) {m : ℕ} (v : Fin m → TanM x t.G)
    (hv : ∀ i, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (v i)) (a : Fin m → S) :
    IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (∑ i, a i • v i) := by
  intro b
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hv i b, smul_comm]

theorem full_of_eig {d : (E →+* ℂ) → ℕ} (v : ∀ τ, Fin (d τ) → TanM x t.G)
    (hv : ∀ τ i, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (v τ i))
    (hb : ∀ τ n, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) n → ∃! a : Fin (d τ) → S, n = ∑ i, a i • v τ i) :
    Full (fun k : (Σ τ : E →+* ℂ, Fin (d τ)) => v k.1 k.2) := by
  classical
  intro m
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := x) (S := S) t.act
  have hsum : ∑ τ, proj ρ (embK c) α τ m = m := by
    have := congrArg (fun e : Module.End S (TanM x t.G) => e m) (sum_proj ρ (embK c) α hinj)
    simpa [LinearMap.sum_apply] using this
  have hE : ∀ τ, IsEigV ρ (embK c τ) (proj ρ (embK c) α τ m) := fun τ =>
    eig_of_alpha ρ (embK c) α hN τ (proj_eig_alpha ρ (embK c) α hinj f hf hfs τ m)
  choose a ha hu using fun τ => hb τ (proj ρ (embK c) α τ m) (hE τ)
  refine ⟨fun k => a k.1 k.2, ?_, fun b hb => ?_⟩
  · show m = ∑ k : (Σ τ : E →+* ℂ, Fin (d τ)), a k.1 k.2 • v k.1 k.2
    rw [Fintype.sum_sigma]
    conv_lhs => rw [← hsum]
    exact Finset.sum_congr rfl fun τ _ => ha τ
  · have hb' : m = ∑ k : (Σ τ : E →+* ℂ, Fin (d τ)), b k • v k.1 k.2 := hb
    rw [Fintype.sum_sigma] at hb'
    funext k
    obtain ⟨τ, i⟩ := k
    have hn := proj_sum_eig ρ (embK c) α hinj (fun τ => ∑ i, b ⟨τ, i⟩ • v τ i)
      (fun τ => eig_comb' c τ _ (fun i => hv τ i) _) τ
    rw [← hb'] at hn
    have := hu τ (fun i => b ⟨τ, i⟩) hn
    exact congrFun this i

theorem eig_of_full {d : (E →+* ℂ) → ℕ} (v : ∀ τ, Fin (d τ) → TanM x t.G)
    (hE : ∀ τ i, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (v τ i))
    (hfull : Full (fun k : (Σ τ : E →+* ℂ, Fin (d τ)) => v k.1 k.2)) (τ : E →+* ℂ) (w : TanM x t.G)
    (hm : IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) w) : ∃! a : Fin (d τ) → S, w = ∑ i, a i • v τ i := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, -, -⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := x) (S := S) t.act
  have hproj : proj ρ (embK c) α τ w = w := by
    have := proj_sum_eig ρ (embK c) α hinj (fun σ' => if σ' = τ then w else 0)
      (fun σ' => by
        split_ifs with h
        · subst h; exact hm
        · exact fun a => by simp) τ
    simpa [Finset.sum_ite_eq'] using this
  obtain ⟨A, hA, hAu⟩ := hfull w
  have hcomp : proj ρ (embK c) α τ w = ∑ i, A ⟨τ, i⟩ • v τ i := by
    have h1 := proj_sum_eig ρ (embK c) α hinj (fun σ' => ∑ i, A ⟨σ', i⟩ • v σ' i)
      (fun σ' => eig_comb' c σ' _ (fun i => hE σ' i) _) τ
    rw [← Fintype.sum_sigma (fun k : (Σ σ : E →+* ℂ, Fin (d σ)) => A k • v k.1 k.2), ← hA] at h1
    exact h1
  refine ⟨fun i => A ⟨τ, i⟩, hproj.symm.trans hcomp, fun b hb => ?_⟩
  have hb : w = ∑ i, b i • v τ i := hb
  let B : (Σ σ : E →+* ℂ, Fin (d σ)) → S := fun k => if h : k.1 = τ then b (h ▸ k.2) else 0
  have hB : w = ∑ k, B k • v k.1 k.2 := by
    rw [Fintype.sum_sigma, hb, Finset.sum_eq_single τ]
    · exact Finset.sum_congr rfl fun i _ => by simp [B]
    · intro σ _ hσ
      exact Finset.sum_eq_zero fun i _ => by simp [B, hσ]
    · intro h; exact absurd (Finset.mem_univ τ) h
  have := hAu B hB
  funext i
  have := congrFun this ⟨τ, i⟩
  simpa [B] using this

end GlobalTheory.LocM.FrameBC


open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
  ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.LocM.FrameBC in
theorem GlobalTheory.LocM.isFrame_bc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (f : c.F →+* R) (φ : R →+* S) (x : Sp R ⟶ X) (u : Vecs Dw t R), GlobalTheory.LocM.IsFrame t f x u → GlobalTheory.LocM.IsFrame t (φ.comp f) (spMap φ ≫ x) (u.bc φ) := by
  intro E _ _ _ H Dw l c X t R S _ _ f φ x u hu
  letI : Algebra c.F R := f.toAlgebra
  letI : Algebra c.F S := (φ.comp f).toAlgebra
  let v : ∀ τ, Fin (Dw.mult τ) → TanM x t.G := fun τ i => tanOf (hu.1 τ i).1
  have he : ∀ τ i (a : 𝓞 E), u.bc φ τ i ≫ (t.act.act a).left =
      spMap (epsMul ((φ.comp f) (embK c τ a))) ≫ u.bc φ τ i := fun τ i a => by
    show (spMap (dualMap φ) ≫ u τ i) ≫ _ = _ ≫ spMap (dualMap φ) ≫ u τ i
    rw [Category.assoc, (hu.1 τ i).2 a, ← Category.assoc, Formalism.L2.Pj.FrCov.eps_dual, Category.assoc, RingHom.comp_apply]
  have h1 := full_of_eig c v (fun τ i => (eig_iff c τ (v τ i)).1 (hu.1 τ i).2) fun τ n hn => by
    exact (existsUnique_congr fun a => LieMet.isComb_iff (v τ) a n).1 (hu.2 τ _ (isTan_tv n) ((eig_iff c τ n).2 hn))
  have h2 : Full fun k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => resM φ (v k.1 k.2) := by
    have h := full_equiv (eB Dw).symm (full_bc φ (full_equiv (eB Dw) h1))
    exact (funext fun k => congrArg (fun j : IxB Dw => resM φ (v j.1 j.2)) ((eB Dw).apply_symm_apply k)) ▸ h
  refine ⟨fun τ i => ⟨isTan_map φ rfl (hu.1 τ i).1, he τ i⟩, fun τ w hw hwe => ?_⟩
  have h3 := eig_of_full c (fun τ i => resM φ (v τ i)) (fun τ i => (eig_iff c τ _).1 (he τ i)) h2 τ (tanOf hw)
    ((eig_iff c τ _).1 hwe)
  exact (existsUnique_congr fun a => LieMet.isComb_iff (fun i => resM φ (v τ i)) a (tanOf hw)).2 h3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT

namespace GlobalTheory.KeyFourth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def Tied {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (s : LB.Sec (PPx x)) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left))
    (Φ : FibKey Xo S x) : Prop :=
  SecTie Φ.m Φ.th s ∧ ∃ hg : Φ.T.g = g, ∀ i : Fin Φ.T.g,
    (Φ.v i).left ≫ Φ.m.φ = u (e (i.cast hg)).1 (e (i.cast hg)).2

def kch {S : Type} [CommRing S] (t : Ix Dw → Sˣ) : Sˣ := ∏ i, t i ^ keyEx Dw i

theorem kch_mul {S : Type} [CommRing S] (t t' : Ix Dw → Sˣ) : kch (t * t') = kch t * kch t' := by
  simp only [kch, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem kch_inv {S : Type} [CommRing S] (t : Ix Dw → Sˣ) : kch t⁻¹ = (kch t)⁻¹ := by
  simp only [kch, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]

theorem kch_eq {S : Type} [CommRing S] (t : Ix Dw → Sˣ) :
    kch t = (∏ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t (some x)) * (t none ^ 2)⁻¹ := by
  rw [kch, Fintype.prod_option, mul_comm]
  simp only [keyEx, zpow_one, zpow_neg]
  rfl

def RootVal {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (y : FrPt Xo c (CAt σ)) (v : ℂ) : Prop :=
  ∃ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (U.un k x) y ∧
    v = Formalism.L2.PjFree.toC ((kch t : (CAt σ)ˣ) : CAt σ)

end GlobalTheory.KeyFourth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorBlockDecomposition
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

theorem lminor_block : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ H : Matrix (Fin r) (Fin r) ℂ, IsUnit (reindex e e H).toBlocks₂₂.det → (∀ (i : Fin (r + 1)) (k : Fin (q + 1)), (i : ℕ) = k → lminor H i = lminor (reindex e e H).toBlocks₂₂ k) ∧ ∀ (i : Fin (r + 1)) (k : Fin (p + 1)), (i : ℕ) = q + k → lminor H i = (reindex e e H).toBlocks₂₂.det * lminor (schur (reindex e e H)) k := by
  intro r p q e he H hH
  constructor
  · rintro ⟨i, hi⟩ ⟨k, hk⟩ h
    obtain rfl : i = k := h
    unfold lminor
    congr 1
    ext a b
    simp only [submatrix_apply, toBlocks₂₂, reindex_apply, of_apply]
    congr 1 <;> exact Fin.ext (by rw [he.2]; rfl)
  · rintro ⟨i, hi⟩ ⟨k, hk⟩ h
    obtain rfl : i = q + k := h
    obtain ⟨f0, hf0⟩ := exists_isBlockOrderedSumEquiv k q
    let f : Fin (q + k) ≃ Fin k ⊕ Fin q := (finCongr (add_comm q k)).trans f0
    have hf : IsBlockSL2Embedding f := ⟨fun a => hf0.1 a, fun a => hf0.2 a⟩
    let c : Fin k → Fin p := Fin.castLE (Nat.le_of_lt_succ hk)
    let G : Matrix (Fin k ⊕ Fin q) (Fin k ⊕ Fin q) ℂ := (reindex e e H).submatrix (Sum.map c id) (Sum.map c id)
    have key : ∀ a, Fin.castLE (Nat.le_of_lt_succ hi) (f.symm a) = e.symm (Sum.map c id a) := by
      rintro (a | a) <;> apply Fin.ext
      · simp only [Fin.val_castLE, Sum.map_inl, hf.1, he.1, c]
      · simp only [Fin.val_castLE, Sum.map_inr, hf.2, he.2, id]
    have h1 : lminor H ⟨q + k, hi⟩ = G.det := by
      unfold lminor
      rw [← det_submatrix_equiv_self f.symm]
      congr 1
      ext a b
      simp only [G, submatrix_apply, reindex_apply, ← key]
    have h2 : G.toBlocks₂₂ = (reindex e e H).toBlocks₂₂ := rfl
    rw [h1, det_eq_mul_schur (h2 ▸ hH), h2]
    rfl

end GlobalTheory.FlagFibre
end

