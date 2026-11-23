module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0021
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1417
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnModelDescends
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstCohomologyVanishesOfIsRelAcyclic
section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.ExactCoboundaryTriple

theorem exists_triple {κ : Type} [LinearOrder κ] {t : Finset κ} (ht : t.card = 3) :
    ∃ i j k, i < j ∧ j < k ∧ t = {i, j, k} := by
  refine ⟨t.orderEmbOfFin ht 0, t.orderEmbOfFin ht 1, t.orderEmbOfFin ht 2,
    (t.orderEmbOfFin ht).strictMono (by decide), (t.orderEmbOfFin ht).strictMono (by decide), ?_⟩
  ext x
  constructor
  · intro hx
    have : x ∈ Set.range (t.orderEmbOfFin ht) := by rw [Finset.range_orderEmbOfFin]; exact hx
    obtain ⟨m, rfl⟩ := this
    fin_cases m <;> simp
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> exact Finset.orderEmbOfFin_mem _ _ _

theorem totalD_triple {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (A : Cube.{0} κ R)
    (x : ∀ s, A.obj s) {i j k : κ} (hij : i < j) (hjk : j < k) :
    Cube.totalD A x {i, j, k} =
      Cube.res A (by intro; simp; tauto) (x {j, k}) - Cube.res A (by intro; simp; tauto) (x {i, k}) +
        Cube.res A (by intro; simp; tauto) (x {i, j}) := by
  have hik := hij.trans hjk
  have e1 : ({i, j, k} : Finset κ).erase i = {j, k} := by
    ext m; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl)
      · exact ⟨hij.ne', by tauto⟩
      · exact ⟨hik.ne', by tauto⟩
  have e2 : ({i, j, k} : Finset κ).erase j = {i, k} := by
    ext m; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl)
      · exact ⟨hij.ne, by tauto⟩
      · exact ⟨hjk.ne', by tauto⟩
  have e3 : ({i, j, k} : Finset κ).erase k = {i, j} := by
    ext m; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl)
      · exact ⟨hik.ne, by tauto⟩
      · exact ⟨hjk.ne, by tauto⟩
  have s1 : cubeSign ({i, j, k} : Finset κ) i = 1 :=
    cubeSign_eq_one_of_forall_le (by simp [hij.le, hik.le])
  have s2 : cubeSign ({i, j, k} : Finset κ) j = -1 := by
    have h := cubeSign_erase_of_lt (t := {i, j, k}) (by simp) hij
    rw [e1, cubeSign_eq_one_of_forall_le (by simp [hjk.le])] at h
    omega
  have s3 : cubeSign ({i, j, k} : Finset κ) k = 1 := by
    have h := cubeSign_erase_of_lt (t := {i, j, k}) (by simp) hik
    have h' := cubeSign_erase_of_lt (t := {j, k}) (by simp) hjk
    rw [e1] at h
    rw [cubeSign_eq_one_of_forall_le (by
      intro m hm
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hm
      exact (hm.2.resolve_left hm.1).ge)] at h'
    omega
  rw [Cube.totalD_apply, Finset.sum_insert (by simp [hij.ne, hik.ne]), Finset.sum_pair hjk.ne,
    Cube.res_congr A x e1 _ (by intro; simp; tauto), Cube.res_congr A x e2 _ (by intro; simp; tauto),
    Cube.res_congr A x e3 _ (by intro; simp; tauto), s1, s2, s3]
  simp only [one_smul, neg_smul, sub_eq_add_neg, add_assoc]

variable {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X)

theorem coboundary_of_exact {κ : Type} [LinearOrder κ] (W : κ → X.Opens)
    (hW : (cechLB f M W).ExactAt (0 + 1)) (Φ : ∀ k l, SecOnR f M (W k ⊓ W l))
    (hΦ : ∀ k l m (O : X.Opens) (h₁ : O ≤ W k ⊓ W l) (h₂ : O ≤ W l ⊓ W m) (h₃ : O ≤ W k ⊓ W m),
      SecOnR.restrict f M h₁ (Φ k l) + SecOnR.restrict f M h₂ (Φ l m) = SecOnR.restrict f M h₃ (Φ k m)) :
    ∃ y : ∀ k, SecOnR f M (W k), ∀ k l (O : X.Opens) (h : O ≤ W k ⊓ W l),
      SecOnR.restrict f M h (Φ k l) =
        SecOnR.restrict f M (h.trans inf_le_right) (y l) - SecOnR.restrict f M (h.trans inf_le_left) (y k) := by
  classical
  have hle : ∀ {s : Finset κ} {i : κ}, i ∈ s → ⨅ j ∈ s, W j ≤ W i := fun {s i} hi => biInf_le W hi
  let x : ∀ s : Finset κ, SecOnR f M (⨅ j ∈ s, W j) := fun s =>
    if h : s.Nonempty then
      SecOnR.restrict f M (le_inf (hle (s.min'_mem h)) (hle (s.max'_mem h))) (Φ (s.min' h) (s.max' h))
    else 0
  have hcongr : ∀ {k l k' l' : κ} (_ : k = k') (_ : l = l') {O : X.Opens} (h : O ≤ W k ⊓ W l)
      (h' : O ≤ W k' ⊓ W l'), SecOnR.restrict f M h (Φ k l) = SecOnR.restrict f M h' (Φ k' l') := by
    rintro k l _ _ rfl rfl O h h'
    rfl
  have hx : ∀ {k l : κ} (_ : k < l), x {k, l} =
      SecOnR.restrict f M (le_inf (hle (by simp)) (hle (by simp))) (Φ k l) := by
    intro k l hkl
    have hn : ({k, l} : Finset κ).Nonempty := by simp
    simp only [x, dif_pos hn]
    exact hcongr (by simp [hkl.le]) (by simp [hkl.le]) _ _
  have hE := (cechComplex_exactAt_succ_iff (secCube f M W) 0).1 hW
  have hd : Cube.d (secCube f M W) (0 + 2) (fun s => x s.1) = 0 := by
    funext t
    rw [Cube.d_apply_eq_totalD (secCube f M W) _ x (fun _ => rfl)]
    obtain ⟨t, ht⟩ := t
    obtain ⟨i, j, k, hij, hjk, rfl⟩ := exists_triple ht
    refine (totalD_triple (secCube f M W) x hij hjk).trans ?_
    rw [hx hij, hx hjk, hx (hij.trans hjk)]
    simp only [res_secCube]
    erw [SecOnR.restrict_restrict, SecOnR.restrict_restrict, SecOnR.restrict_restrict]
    rw [← hΦ i j k _ (le_inf (hle (by simp)) (hle (by simp))) (le_inf (hle (by simp)) (hle (by simp)))]
    change (_ : SecOnR f M _) = 0
    abel
  obtain ⟨z, hz⟩ := (hE _).1 hd
  have hs : ∀ k, W k ≤ ⨅ j ∈ ({k} : Finset κ), W j := fun k => by simp
  let y : ∀ k, SecOnR f M (W k) := fun k => SecOnR.restrict f M (hs k) (z ⟨{k}, Finset.card_singleton k⟩)
  have hlt : ∀ k l, k < l → ∀ (O : X.Opens) (h : O ≤ W k ⊓ W l),
      SecOnR.restrict f M h (Φ k l) =
        SecOnR.restrict f M (h.trans inf_le_right) (y l) - SecOnR.restrict f M (h.trans inf_le_left) (y k) := by
    intro k l hkl O h
    have hO : O ≤ ⨅ j ∈ ({k, l} : Finset κ), W j := by
      simp only [Finset.mem_insert, Finset.mem_singleton, le_iInf_iff]
      rintro j (rfl | rfl)
      · exact h.trans inf_le_left
      · exact h.trans inf_le_right
    have e := (congrFun hz ⟨{k, l}, Finset.card_pair hkl.ne⟩).symm.trans
      (Cube.d_one_apply_pair (secCube f M W) z hkl)
    have e' := congrArg (SecOnR.restrict f M hO) ((hx hkl).symm.trans e)
    simp only [res_secCube] at e'
    erw [map_sub, SecOnR.restrict_restrict, SecOnR.restrict_restrict, SecOnR.restrict_restrict] at e'
    exact e'.trans (congrArg₂ (· - ·) (SecOnR.restrict_restrict f (hs l) _ _).symm
      (SecOnR.restrict_restrict f (hs k) _ _).symm)
  have h0 : ∀ k (O : X.Opens) (h : O ≤ W k ⊓ W k), SecOnR.restrict f M h (Φ k k) = 0 := fun k O h =>
    add_eq_left.1 (hΦ k k k O h h h)
  refine ⟨y, fun k l O h => ?_⟩
  rcases lt_trichotomy k l with hkl | rfl | hkl
  · exact hlt k l hkl O h
  · rw [h0, sub_self]
  · have h' : O ≤ W l ⊓ W k := le_inf (h.trans inf_le_right) (h.trans inf_le_left)
    have e := hΦ k l k O h h' (le_inf (h.trans inf_le_left) (h.trans inf_le_left))
    rw [h0, hlt l k hkl O h'] at e
    rw [eq_neg_of_add_eq_zero_left e, neg_sub]

theorem coboundary_of_refine {I κ : Type} (V : I → X.Opens) (W : κ → X.Opens) (hW : ⨆ k, W k = ⊤) (r : κ → I)
    (hr : ∀ k, W k ≤ V (r k)) (Φ : ∀ a b, SecOnR f M (V a ⊓ V b))
    (hΦ : ∀ a b d (O : X.Opens) (h₁ : O ≤ V a ⊓ V b) (h₂ : O ≤ V b ⊓ V d) (h₃ : O ≤ V a ⊓ V d),
      SecOnR.restrict f M h₁ (Φ a b) + SecOnR.restrict f M h₂ (Φ b d) = SecOnR.restrict f M h₃ (Φ a d))
    (y : ∀ k, SecOnR f M (W k))
    (hy : ∀ k l (O : X.Opens) (h : O ≤ W k ⊓ W l),
      SecOnR.restrict f M (h.trans (inf_le_inf (hr k) (hr l))) (Φ (r k) (r l)) =
        SecOnR.restrict f M (h.trans inf_le_right) (y l) - SecOnR.restrict f M (h.trans inf_le_left) (y k)) :
    ∃ Ψ : ∀ a, SecOnR f M (V a), ∀ a b, Φ a b =
      SecOnR.restrict f M inf_le_left (Ψ a) - SecOnR.restrict f M inf_le_right (Ψ b) := by
  have hcov : ∀ U : X.Opens, U ≤ ⨆ k, U ⊓ W k := fun U => by
    rw [← inf_iSup_eq, hW, inf_top_eq]
  have hg : ∀ a, ∃ t : SecOnR f M (V a), ∀ k, SecOnR.restrict f M (inf_le_left : V a ⊓ W k ≤ V a) t =
      SecOnR.restrict f M (inf_le_inf_left _ (hr k)) (Φ a (r k)) -
        SecOnR.restrict f M inf_le_right (y k) := by
    intro a
    refine (SecOnR.existsUnique_glue f (fun k => V a ⊓ W k) (fun _ => inf_le_left) (hcov _) _ ?_).exists
    intro k l
    simp only [map_sub, SecOnR.restrict_restrict]
    have h : V a ⊓ W k ⊓ (V a ⊓ W l) ≤ W k ⊓ W l := inf_le_inf inf_le_right inf_le_right
    rw [← hΦ a (r k) (r l) _ (inf_le_left.trans (inf_le_inf_left _ (hr k)))
      (h.trans (inf_le_inf (hr k) (hr l))), hy k l _ h]
    abel
  choose Ψ hΨ using hg
  refine ⟨Ψ, fun a b => SecOnR.ext_of_cover f (fun k => V a ⊓ V b ⊓ W k) (fun _ => inf_le_left) (hcov _)
    fun k => ?_⟩
  have ea := congrArg (SecOnR.restrict f M (inf_le_inf_right _ inf_le_left :
    V a ⊓ V b ⊓ W k ≤ V a ⊓ W k)) (hΨ a k)
  have eb := congrArg (SecOnR.restrict f M (inf_le_inf_right _ inf_le_right :
    V a ⊓ V b ⊓ W k ≤ V b ⊓ W k)) (hΨ b k)
  simp only [map_sub, SecOnR.restrict_restrict] at ea eb ⊢
  rw [ea, eb, ← hΦ a b (r k) _ inf_le_left (inf_le_inf inf_le_right (hr k))]
  abel

theorem exists_affine_refinement [CompactSpace X] {I : Type} (V : I → X.Opens) (hV : ⨆ a, V a = ⊤) :
    ∃ (n : ℕ) (W : Fin n → X.Opens) (r : Fin n → I), (∀ k, IsAffineOpen (W k)) ∧ ⨆ k, W k = ⊤ ∧
      ∀ k, W k ≤ V (r k) := by
  classical
  have h : ∀ x : X, ∃ (a : I) (U : X.Opens), IsAffineOpen U ∧ x ∈ U ∧ U ≤ V a := by
    intro x
    have hx : x ∈ ⨆ a, V a := by rw [hV]; trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨U, hU, hxU, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens ha
    exact ⟨a, U, hU, hxU, hle⟩
  choose c U hU hxU hle using h
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set X)) (fun x => (U x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  refine ⟨T.card, fun k => U (T.equivFin.symm k), fun k => c (T.equivFin.symm k), fun _ => hU _, ?_,
    fun _ => hle _⟩
  refine top_unique fun x _ => ?_
  obtain ⟨p, hp, hx⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ x))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨T.equivFin ⟨p, hp⟩, ?_⟩
  simpa using hx

theorem firstCohomologyVanishes_of_isRelAcyclic (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R))
    (M : LB X) (hM : M.IsLB) (hX : CompactSpace X) (h : GlobalTheory.CxForm.IsRelAcyclic f f M) : FirstCohomologyVanishes M := by
  intro I V c hV hc φ hφ
  obtain ⟨n, W, r, hW, hWc, hr⟩ := exists_affine_refinement V hc
  let Φ : ∀ a b, SecOnR f M (V a ⊓ V b) := fun a b =>
    (SecOn.chart hM (c a) (inf_le_left.trans (hV a))).symm (φ a b)
  have hch : ∀ a b (O : X.Opens) (h₁ : O ≤ V a ⊓ V b),
      SecOn.chart hM (c a) (h₁.trans (inf_le_left.trans (hV a))) (SecOnR.restrict f M h₁ (Φ a b)) =
        rs X h₁ (φ a b) := fun a b O h₁ =>
    (SecOn.chart_restrict hM (c a) (inf_le_left.trans (hV a)) h₁ (Φ a b)).trans
      (congrArg _ (LinearEquiv.apply_symm_apply _ _))
  have hΦ : ∀ a b d (O : X.Opens) (h₁ : O ≤ V a ⊓ V b) (h₂ : O ≤ V b ⊓ V d) (h₃ : O ≤ V a ⊓ V d),
      SecOnR.restrict f M h₁ (Φ a b) + SecOnR.restrict f M h₂ (Φ b d) = SecOnR.restrict f M h₃ (Φ a d) := by
    intro a b d O h₁ h₂ h₃
    have ha : O ≤ M.U (c a) := h₁.trans (inf_le_left.trans (hV a))
    have hb : O ≤ M.U (c b) := h₂.trans (inf_le_left.trans (hV b))
    apply (SecOn.chart hM (c a) ha).injective
    have e := congrArg (rs X (le_inf h₁ (h₂.trans inf_le_right) : O ≤ V a ⊓ V b ⊓ V d)) (hφ a b d)
    simp only [map_add (f := _), map_mul, rs_rs] at e
    refine ((SecOn.chart hM (c a) ha).map_add _ _).trans ?_
    refine Eq.trans ?_ (e.trans (hch a d O h₃).symm)
    exact congrArg₂ (· + ·) (hch a b O h₁) ((SecOn.chart_change hM (c a) (c b) ha hb _).trans
      (congrArg (rs X (le_inf ha hb) (M.g (c a) (c b)).val * ·) (hch b d O h₂)))
  obtain ⟨y, hy⟩ := coboundary_of_exact f M W (h ⊤ (isAffineOpen_top _) (Fin n) W hW (by rw [hWc]; rfl) 0)
    (fun k l => SecOnR.restrict f M (inf_le_inf (hr k) (hr l)) (Φ (r k) (r l)))
    (fun k l m O h₁ h₂ h₃ => by
      simp only [SecOnR.restrict_restrict]
      exact hΦ _ _ _ _ _ _ _)
  obtain ⟨Ψ, hΨ⟩ := coboundary_of_refine f M V W hWc r hr Φ hΦ y (fun k l O hO => by
    simpa only [SecOnR.restrict_restrict] using hy k l O hO)
  refine ⟨fun a => SecOn.chart hM (c a) (hV a) (Ψ a), fun a b => ?_⟩
  have ha : V a ⊓ V b ≤ M.U (c a) := inf_le_left.trans (hV a)
  have hb : V a ⊓ V b ≤ M.U (c b) := inf_le_right.trans (hV b)
  have e := congrArg (SecOn.chart hM (c a) ha) (hΨ a b)
  refine ((LinearEquiv.apply_symm_apply _ _).symm.trans e).trans ?_
  refine ((SecOn.chart hM (c a) ha).map_sub _ _).trans ?_
  exact congrArg₂ (· - ·) (SecOn.chart_restrict hM (c a) (hV a) inf_le_left (Ψ a))
    ((SecOn.chart_change hM (c a) (c b) ha hb _).trans
      (congrArg (rs X (le_inf ha hb) (M.g (c a) (c b)).val * ·)
        (SecOn.chart_restrict hM (c b) (hV b) inf_le_right (Ψ b))))

end GlobalTheory.ExactCoboundaryTriple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisRepresentationTateModuleBaseChangeEqOneIff
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TateBaseChange

open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma baseChangePtEquiv_galPts (K L Ω : Type) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] (σ : Ω ≃ₐ[L] Ω)
    (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ptOver L Ω ⟶ (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K L))).obj A) :
    _root_.GlobalTheory.Published.AbVarRed.baseChangePtEquiv A (_root_.GlobalTheory.Published.AbVarRed.galPts _ σ x) =
      _root_.GlobalTheory.Published.AbVarRed.galPts A (σ.restrictScalars K) (_root_.GlobalTheory.Published.AbVarRed.baseChangePtEquiv A x) := by
  apply Over.OverMorphism.ext
  show (_root_.GlobalTheory.Published.AbVarRed.galPts _ σ x).left ≫ _ = (_root_.GlobalTheory.Published.AbVarRed.galPts A (σ.restrictScalars K) _).left
  rw [_root_.GlobalTheory.Published.AbVarRed.galPts_left, _root_.GlobalTheory.Published.AbVarRed.galPts_left, Category.assoc]
  rfl


open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.TateBaseChange.galTate_baseChange_eq_one_iff : ∀ (K L Ω : Type) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] [IsCommMonObj A] [IsCommMonObj ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K L))).obj A)] (l : ℕ) [Fact l.Prime] (σ : Ω ≃ₐ[L] Ω), _root_.GlobalTheory.Published.AbVarRed.galTate ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K L))).obj A) l σ = 1 ↔ _root_.GlobalTheory.Published.AbVarRed.galTate A l (σ.restrictScalars K) = 1 := by
  intro K L Ω _ _ _ _ _ _ _ A _ _ _ l _ σ
  set e := _root_.GlobalTheory.Published.AbVarRed.baseChangePtEquiv (K := K) (L := L) (Ω := Ω) A
  have he := baseChangePtEquiv_galPts K L Ω A σ
  constructor
  · intro h
    refine LinearMap.ext fun s => _root_.GlobalTheory.HTLat.Tate.ext fun n => ?_
    rw [_root_.GlobalTheory.Published.AbVarRed.lev_galTate, Module.End.one_apply]
    have ht := congrArg (fun ρ : Module.End ℤ_[l] _ =>
      (ρ (_root_.GlobalTheory.HTLat.Tate.map l e.symm.toMonoidHom s)).lev n) h
    simp only [_root_.GlobalTheory.Published.AbVarRed.lev_galTate, Module.End.one_apply,
      _root_.GlobalTheory.HTLat.Tate.lev_map] at ht
    have := congrArg e ht
    rw [he] at this
    simpa [e] using this
  · intro h
    refine LinearMap.ext fun t => _root_.GlobalTheory.HTLat.Tate.ext fun n => ?_
    rw [_root_.GlobalTheory.Published.AbVarRed.lev_galTate, Module.End.one_apply]
    have hs := congrArg (fun ρ : Module.End ℤ_[l] _ =>
      (ρ (_root_.GlobalTheory.HTLat.Tate.map l e.toMonoidHom t)).lev n) h
    simp only [_root_.GlobalTheory.Published.AbVarRed.lev_galTate, Module.End.one_apply,
      _root_.GlobalTheory.HTLat.Tate.lev_map] at hs
    apply e.injective
    rw [he]
    exact hs

end GlobalTheory.TateBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeUnitStalkDataGerm
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem fromSpecStalk_preimage_top {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
  intro z _
  have hz : X.fromSpecStalk x z ⤳ x := by
    have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact hz.mem_open U.2 hx

theorem fromSpecStalk_appLE_top {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    (X.fromSpecStalk x).appLE U ⊤ (fromSpecStalk_preimage_top x U hx) =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp]
  have e : ((homOfLE le_top).op ≫ (homOfLE (fromSpecStalk_preimage_top x U hx)).op :
      Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id, Category.comp_id]

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {g g' : X ⟶ Y} (hg : g = g') (V : Y.Opens) (W : X.Opens)
    (h : W ≤ g ⁻¹ᵁ V) (h' : W ≤ g' ⁻¹ᵁ V) : g.appLE V W h = g'.appLE V W h' := by
  subst hg; rfl

theorem germ_comp_of_spec {X Y : Scheme.{0}} {x : X} {y : Y} (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x)
    (f : X ⟶ Y) (hφ : Spec.map φ ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ f)
    (V : Y.Opens) (hy : y ∈ V) (U : X.Opens) (hx : x ∈ U) (h : U ≤ f ⁻¹ᵁ V) :
    Y.presheaf.germ V y hy ≫ φ = f.appLE V U h ≫ X.presheaf.germ U x hx := by
  have h1 : ⊤ ≤ (Spec.map φ ≫ Y.fromSpecStalk y) ⁻¹ᵁ V := by
    intro z _
    exact fromSpecStalk_preimage_top y V hy (Set.mem_univ _)
  have h2 : ⊤ ≤ (X.fromSpecStalk x ≫ f) ⁻¹ᵁ V := hφ ▸ h1
  have key := appLE_eq_of_eq hφ V ⊤ h1 h2
  have eL : (Spec.map φ ≫ Y.fromSpecStalk y).appLE V ⊤ h1 =
      (Y.fromSpecStalk y).appLE V ⊤ (fromSpecStalk_preimage_top y V hy) ≫
        (Spec.map φ).appLE ⊤ ⊤ (by simp) := by
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have eR : (X.fromSpecStalk x ≫ f).appLE V ⊤ h2 =
      f.appLE V U h ≫ (X.fromSpecStalk x).appLE U ⊤ (fromSpecStalk_preimage_top x U hx) := by
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have eT : (Spec.map φ).appLE ⊤ ⊤ (by simp) = (Spec.map φ).appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.preimage_top, Category.comp_id]
    first | rfl | simp
  rw [eL, eR, eT, fromSpecStalk_appLE_top y V hy, fromSpecStalk_appLE_top x U hx, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, ← Category.assoc, ← Category.assoc] at key
  exact (cancel_mono _).1 key

theorem germ_apply_of_spec {X Y : Scheme.{0}} {x : X} {y : Y} (φ : Y.presheaf.stalk y →+* X.presheaf.stalk x)
    (f : X ⟶ Y) (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ f)
    (V : Y.Opens) (hy : y ∈ V) (U : X.Opens) (hx : x ∈ U) (h : U ≤ f ⁻¹ᵁ V) (a : Γ(Y, V)) :
    φ (Y.presheaf.germ V y hy a) = X.presheaf.germ U x hx (f.appLE V U h a) := by
  have e := congrArg (fun g => g.hom a) (germ_comp_of_spec (CommRingCat.ofHom φ) f hφ V hy U hx h)
  exact e

theorem stalkData_germ : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → (∀ (V : S.Opens) (hs : s ∈ V) (U : G.left.Opens) (hU : unitSec G s ∈ U) (h : U ≤ G.hom ⁻¹ᵁ V) (a : Γ(S, V)), π (S.presheaf.germ V s hs a) = G.left.presheaf.germ U _ hU (G.hom.appLE V U h a)) ∧ (∀ (U : G.left.Opens) (hU : unitSec G s ∈ U) (V : S.Opens) (hs : s ∈ V) (h : V ≤ unitSec G ⁻¹ᵁ U) (f : Γ(G.left, U)), ε (G.left.presheaf.germ U _ hU f) = S.presheaf.germ V s hs ((unitSec G).appLE U V h f)) ∧ (∀ (U : G.left.Opens) (hU : unitSec G s ∈ U) (U' : G.left.Opens) (hU' : unitSec G s ∈ U') (h : U' ≤ sqr G ⁻¹ᵁ U) (f : Γ(G.left, U)), m (G.left.presheaf.germ U _ hU f) = G.left.presheaf.germ U' _ hU' ((sqr G).appLE U U' h f)) := by
  intro S G _ s π ε m hD
  exact ⟨fun V hs U hU h a => germ_apply_of_spec π G.hom hD.str V hs U hU h a,
    fun U hU V hs h f => germ_apply_of_spec ε (unitSec G) hD.unit U hU V hs h f,
    fun U hU U' hU' h f => germ_apply_of_spec m (sqr G) hD.sq U hU U' hU' h f⟩

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensDiagEqZero
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.WeilDiagIso

theorem hTens_diag_eq_zero {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {n m : ℕ}
    (c : A →ₐ[R] A) (JA : Matrix (Fin (n + n)) (Fin (n + n)) A) (JB : Matrix (Fin m) (Fin m) A)
    (x y : Matrix (Fin (n + n)) (Fin m) A)
    (hx : ∀ i j, x (Fin.natAdd n i) j = x (Fin.castAdd n i) j)
    (hy : ∀ i j, y (Fin.natAdd n i) j = y (Fin.castAdd n i) j)
    (h1 : ∀ i k, JA (Fin.castAdd n i) (Fin.natAdd n k) = 0)
    (h2 : ∀ i k, JA (Fin.natAdd n i) (Fin.castAdd n k) = 0)
    (h3 : ∀ i k, JA (Fin.natAdd n i) (Fin.natAdd n k) = - JA (Fin.castAdd n i) (Fin.castAdd n k)) :
    hTens c JA JB x y = 0 := by
  unfold hTens
  simp only [Fin.sum_univ_add, hx, hy, h1, h2, h3, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib, add_neg_cancel]

theorem symp_diag_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
    (u u' : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)),
    symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)
      (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u)
      (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u') = 0 := by
  intro F E _ _ _ _ _ σ nS nT JT JB ξ u u'
  unfold symp
  rw [hTens_diag_eq_zero]
  · simp
  · intro i j
    simp [Matrix.mul_apply, diagCols, -Fin.natAdd_eq_addNat]
  · intro i j
    simp [Matrix.mul_apply, diagCols, -Fin.natAdd_eq_addNat]
  · intro i k
    simp [incM, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, -Fin.natAdd_eq_addNat]
  · intro i k
    simp [incM, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, -Fin.natAdd_eq_addNat]
  · intro i k
    simp [incM, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, -Fin.natAdd_eq_addNat]

end GlobalTheory.WeilDiagIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelDegreeZeroResiduesRangeEqTop
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSShort

theorem totRes_incl_zero {K : Type} [Field K] [NumberField K] {X : Data K} {s : Fin X.D → Fin X.N → K} {hs : X.IsGood s} {δ : ℕ}
    (Co : Coord X.toGeo hs δ) (x : X.V 0) : totRes Co (incl X 0 x) = Co.ev 0 (hs.res 0 x.1) := by
  have h : incl X 0 x 0 = x.1 := Pi.single_eq_same (M := fun j => X.toGeo.Sec j) 0 x.1
  simp only [totRes, LinearMap.comp_apply, LinearMap.proj_apply, h, LinearEquiv.coe_coe]

theorem map_totRes_range_incl_zero : Quoted → ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (δ : ℕ) (Co : Coord X.toGeo hs δ), IsNef K X.L₂ → IsBig K X.L₂ → (LinearMap.range (incl X 0)).map (totRes Co) = ⊤ := by
  intro Q K _ _ X s hs δ Co hnef hbig
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨f, hf⟩ := GlobalTheory.HSResOnto.res_onto Q K X.toGeo hnef hbig s hs ((Co.ev 0).symm v)
  have hf' : hs.res 0 (X.toGeo.mulE 0 f) = (Co.ev 0).symm v := hf
  have hm : X.toGeo.mulE 0 f ∈ X.V 0 := X.global_le 0 (Nat.zero_le _) (X.toGeo.mulE_mem_global 0 f)
  refine Submodule.mem_map.2 ⟨incl X 0 ⟨_, hm⟩, LinearMap.mem_range_self _ _, ?_⟩
  rw [totRes_incl_zero, hf', LinearEquiv.apply_symm_apply]

end GlobalTheory.HSShort
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayPolynomialSubringLiftInjectiveStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localizationAway_polynomial_subring_lift_injective : ∀ (k : Type) [Field k] (P : Polynomial k), P ≠ 0 → ∀ (R : Subring k) (P₁ : Polynomial R) (h : IsUnit (((algebraMap (Polynomial k) (Localization.Away P)).comp (Polynomial.mapRingHom R.subtype)) P₁)), P₁.map R.subtype = P → Function.Injective (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ h) := by
  first | exact @GlobalTheory.descentLocInj | exact GlobalTheory.descentLocInj | (intros; apply GlobalTheory.descentLocInj <;> assumption)
end

