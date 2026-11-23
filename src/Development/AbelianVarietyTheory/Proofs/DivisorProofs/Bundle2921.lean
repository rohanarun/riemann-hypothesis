module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmOfKsCoc
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0183
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2876
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2857
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFieldBaseChange
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.FieldCompat

open GlobalTheory.CechKS GlobalTheory.LogKSBal

theorem isTr_comp {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) {G : Over (Sp R)} [GrpObj G]
    {A : Over (Sp K)} [GrpObj A] (m : A.left ⟶ G.left) (hm : IsGrpPullback A G (spMap x₀) m)
    (w : TanM (𝟙 (Sp R)) G) (v : epsR K ⟶ A)
    (hv : v.left ≫ m = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) ≫ (tv w).left) {B : Type} [CommRing B] (φ : K →+* B)
    (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) (y : Sp (DualNumber B) ⟶ A.left) (hy : IsTransl φ x v y) :
    IsTr G (φ.comp x₀) (x ≫ m) w (y ≫ m) := by
  obtain ⟨x₁, v₁, a, b, rfl⟩ := hy
  have dc : (dualMap φ).comp (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) = dualMap (φ.comp x₀) :=
    RingHom.ext fun c ↦ by ext <;> simp [dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  obtain ⟨p, q, h₁, h₂, h₃⟩ := exists_mul_of_isGrpPullback hm _ x₁ v₁
    (spMap (algebraMap B (DualNumber B)) ≫ (x ≫ m) ≫ G.hom) (by
      change _ = spMap ((algebraMap B (DualNumber B)).comp φ) ≫ spMap x₀
      rw [Category.assoc, hm.1.w, ← Category.assoc x, hx, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp'])
  refine ⟨p, q, ?_, ?_, h₃⟩
  · rw [h₁, a]; exact Category.assoc _ _ _
  · rw [h₂, b, ← dc, ← GlobalTheory.LogKSLoc.spMap_comp' (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) (dualMap φ)]
    refine (Category.assoc _ _ _).trans ?_
    rw [hv]
    exact (Category.assoc (spMap (dualMap φ)) (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀)) _).symm

theorem invField_baseChange : ∀ {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (m : A.left ⟶ G.left), IsGrpPullback A G (spMap x₀) m → ∀ (w : TanM (𝟙 (Sp R)) G) (e : Fld G.left), IsInv G w e → ∀ (v : epsR K ⟶ A), IsTangent v → v.left ≫ m = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) ≫ (tv w).left → ∀ (dd : ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), GlobalTheory.KS.IsInvDer v dd → ∀ (O : G.left.Opens) (f : Γ(G.left, O)), dd (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e O f) (m ⁻¹ᵁ O) := by
  intro R _ K _ x₀ G _ _ A _ _ m hm w e he v hvt hv dd hdd O f
  refine ext_valR _ _ fun B _ y hy => ?_
  have hb : y ≫ A.hom = spMap (Spec.preimage (y ≫ A.hom)).hom := (Spec.map_preimage _).symm
  generalize (Spec.preimage (y ≫ A.hom)).hom = β at hb
  obtain ⟨y', hy'⟩ := exists_isTransl β y hb v
  have hO : ⊤ ≤ y' ⁻¹ᵁ (m ⁻¹ᵁ O) := le_preimage_of_red (hy'.red hvt) hy
  rw [← snd_valR_transl hvt hdd hy' hy, CoeffWt.valR_app _ _ _ hO, valR_pbT y m le_rfl hy]
  refine he.2 B (β.comp x₀) (y ≫ m) (y' ≫ m) O f ?_ hy (isTr_comp x₀ m hm w v hv β y hb y' hy')
  rw [Category.assoc, hm.1.w, ← Category.assoc, hb, GlobalTheory.LogKSLoc.spMap_comp']

end GlobalTheory.Heat.FieldCompat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldsCechH1Relation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CoverRefinementPullback

theorem resG_resG' {X : Scheme.{0}} {O₀ O₁ O₂ : X.Opens} (h : O₁ ≤ O₀) (h' : O₂ ≤ O₁) (s : Γ(X, O₀)) :
    resG X h' (resG X h s) = resG X (h'.trans h) s := by
  simp only [resG]; rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem pbT_id' {X : Scheme.{0}} {O₀ : X.Opens} (s : Γ(X, O₀)) {O : X.Opens} (h : O ≤ O₀) :
    pbT (𝟙 X) s O = resG X h s := by
  unfold pbT; rw [dite_eq_left (show O ≤ (𝟙 X) ⁻¹ᵁ O₀ from h)]; simp [Scheme.Hom.appLE, resG, Category.id_comp]; rfl

theorem dlg_res' {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) (i j : L.ι) {T : B.left.Opens} (hT : T ≤ L.U i ⊓ L.U j) :
    rsT (dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) T =
      δ T (res hT (L.g i j)).val * (res hT (L.g i j))⁻¹.val := by
  unfold dlg
  rw [GlobalTheory.KS.rsT_of_le hT, map_mul, pbT_id' _ le_rfl, pbT_id' _ le_rfl, ← hδ.2.2 _ _ hT le_top, resG_resG', resG_resG']
  rfl

theorem dlg_tri {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left) (hL : L.IsLB)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) (i j k : L.ι) {T : B.left.Opens} (h₁ : T ≤ L.U i ⊓ L.U j)
    (h₂ : T ≤ L.U j ⊓ L.U k) (h₃ : T ≤ L.U i ⊓ L.U k) :
    rsT (dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) T + rsT (dlg B (𝟙 _) L δ j k (L.U j ⊓ L.U k)) T =
      rsT (dlg B (𝟙 _) L δ i k (L.U i ⊓ L.U k)) T := by
  rw [dlg_res' B L δ hδ i j h₁, dlg_res' B L δ hδ j k h₂, dlg_res' B L δ hδ i k h₃,
    ← FinAffineCharts.cocycle_on hL i j k h₁ h₂ h₃]
  set u := res h₁ (L.g i j)
  set w := res h₂ (L.g j k)
  rw [mul_inv, Units.val_mul, hδ.2.1 _ le_top, Units.val_mul]
  have hu : (u : Γ(B.left, _)) * (u⁻¹ : Γ(B.left, _)ˣ).val = 1 := Units.mul_inv u
  have hw : (w : Γ(B.left, _)) * (w⁻¹ : Γ(B.left, _)ˣ).val = 1 := Units.mul_inv w
  linear_combination (-(δ _ w.val * (w⁻¹).val)) * hu + (-(δ _ u.val * (u⁻¹).val)) * hw

theorem dlg_refine {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) {κ : Type} (W : κ → B.left.Opens) (c : κ → L.ι) (h : ∀ a, W a ≤ L.U (c a))
    (a b : κ) {T : B.left.Opens} (hT : T ≤ W a ⊓ W b) :
    rsT (dlg B (𝟙 _) (FinAffineCharts.refineLB L W c h) δ a b (W a ⊓ W b)) T =
      rsT (dlg B (𝟙 _) L δ (c a) (c b) (L.U (c a) ⊓ L.U (c b))) T := by
  refine (dlg_res' B (FinAffineCharts.refineLB L W c h) δ hδ a b hT).trans ?_
  rw [dlg_res' B L δ hδ (c a) (c b) (hT.trans (inf_le_inf (h a) (h b)))]
  have e : res hT ((FinAffineCharts.refineLB L W c h).g a b) =
      res (hT.trans (inf_le_inf (h a) (h b))) (L.g (c a) (c b)) := FinAffineCharts.res_res _ _ _
  exact congrArg (fun u : Γ(B.left, T)ˣ => δ T u.val * (u⁻¹).val) e

theorem rsT_cmul {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) {O₀ : Y.Opens} (r : R) (s : Γ(Y, O₀))
    (O : Y.Opens) : rsT (constFn q O₀ r * s) O = constFn q O r * rsT s O := by
  by_cases h : O ≤ O₀
  · rw [GlobalTheory.KS.rsT_mul, GlobalTheory.KS.rsT_constFn q h]
  · unfold rsT; simp [h]

theorem sum_reindex {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) (O : Y.Opens) {d g : ℕ}
    (cc : Fin d → R) (e : Fin d → Fin g) (X : Fin g → Γ(Y, O)) :
    ∑ a, constFn q O (∑ b, if e b = a then cc b else 0) * X a = ∑ b, constFn q O (cc b) * X (e b) := by
  have h0 : ∀ a, constFn q O (∑ b, if e b = a then cc b else 0) = ∑ b, if e b = a then constFn q O (cc b) else 0 := by
    intro a; simp only [constFn, map_sum]; refine Finset.sum_congr rfl fun b _ => ?_; split_ifs <;> simp
  simp only [h0, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (g : ℕ) (w : Fin g → TanM (𝟙 (Sp R)) Dd.toPre.P.A) (dd' : Fin g → Fld Dd.toPre.P.A.left), (∀ a, IsInv Dd.toPre.P.A (w a) (dd' a)) → (∀ u : TanM (𝟙 (Sp R)) Dd.toPre.P.A, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → ∀ z : C1 V, IsCoc V z → ∃ (c : Fin g → R) (y : ∀ i, Γ(Dd.toPre.P.A.left, V i)), ∀ i i', z i i' = ∑ a, constFn Dd.toPre.P.A.hom _ (c a) * rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) (j i) (j i') (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i'))) (V i ⊓ V i') + (rsT (y i') (V i ⊓ V i') - rsT (y i) (V i ⊓ V i')) := by
  intro R _ _ _ _ _ _ Dd g w dd' hinv hspan J V j hV hVj z hz
  have hab : IsAbelianScheme Dd.toPre.P.A := Dd.toPre.P.isAb
  haveI : CompactSpace Dd.toPre.P.A.left := by
    have := hab.proper; exact QuasiCompact.compactSpace_of_compactSpace Dd.toPre.P.A.hom
  obtain ⟨κ, hκ, W, c, hWa, hWc, hWcov⟩ :=
    FinAffineCharts.exists_finite_affine_cover Dd.toPre.P.L Dd.toPre.P.isLB
  have hL' := FinAffineCharts.refineLB_isLB Dd.toPre.P.isLB W c hWc hWcov
  have hiso := FinAffineCharts.iso_refineLB Dd.toPre.P.isLB W c hWc
  have hK' := MulDescent.kTriv_of_lbIso Dd.toPre.P.isLB hL' hiso Dd.toPre.P.ktriv
  have hA' : RelAmple Dd.toPre.P.A (FinAffineCharts.refineLB Dd.toPre.P.L W c hWc) := by
    obtain ⟨w0, hw0⟩ : LBIso (FinAffineCharts.refineLB Dd.toPre.P.L W c hWc)
        (Dd.toPre.P.L.pull (𝟙 Dd.toPre.P.A.left)) :=
      hiso.symm.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Dd.toPre.P.L (𝟙 _) (𝟙 _) rfl)
    exact relAmple_pull IsPullback.of_id_fst Dd.toPre.P.isLB hL' ((isGen_iff w0).1 hw0) ⊤
      (isAffineOpen_top _) (fun _ => trivial) Dd.toPre.P.ample
  obtain ⟨bs⟩ := _root_.GlobalTheory.TanBasisDim.basis_tanM_abelian R Dd.toPre.P.A Dd.toPre.P.g hab Dd.toPre.P.smoothDim
  obtain ⟨e, he⟩ := _root_.GlobalTheory.exists_subfamily_unique_repr_of_spanning_localRing R _ Dd.toPre.P.g g ⟨bs⟩ w hspan
  have hI := _root_.GlobalTheory.DlogBasis.main R Dd.toPre.P.A Dd.toPre.P.g _ hab Dd.toPre.P.smoothDim hL' hA' hK' hWa hκ
    (fun a => w (e a)) (fun a => dd' (e a)) (fun a => hinv (e a)) he
  obtain ⟨z', b, hz'c, hR1, hR2⟩ := _root_.GlobalTheory.CechMixed.exists_cocycle_on_affine _ J κ V W hV hWa z hz
  obtain ⟨cc, ⟨y', hy'⟩, -⟩ := hI z' hz'c

  obtain ⟨φV, hφV⟩ : ∃ φV : Fin g → C1 V, φV = fun a i i' => rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a)
      (j i) (j i') (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i'))) (V i ⊓ V i') := ⟨_, rfl⟩
  obtain ⟨φU, hφU⟩ : ∃ φU : Fin g → C1 W, φU = fun a k k' => dlg Dd.toPre.P.A (𝟙 _)
      (FinAffineCharts.refineLB Dd.toPre.P.L W c hWc) (dd' a) k k' (W k ⊓ W k') := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : Fin g → ∀ i k, Γ(Dd.toPre.P.A.left, V i ⊓ W k), β = fun a i k =>
      rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) (j i) (c k)
        (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (c k))) (V i ⊓ W k) := ⟨_, rfl⟩

  have hm1 : ∀ a i i' k, rsT (φV a i i') (V i ⊓ V i' ⊓ W k) =
      rsT (β a i k) (V i ⊓ V i' ⊓ W k) - rsT (β a i' k) (V i ⊓ V i' ⊓ W k) := by
    intro a i i' k
    subst hφV hβ
    have t1 : V i ⊓ V i' ⊓ W k ≤ V i ⊓ V i' := inf_le_left
    have t2 : V i ⊓ V i' ⊓ W k ≤ V i ⊓ W k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have t3 : V i ⊓ V i' ⊓ W k ≤ V i' ⊓ W k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    simp only
    rw [GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i) (hVj i')) t1, GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i) (hWc k)) t2,
      GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i') (hWc k)) t3,
      ← dlg_tri _ _ Dd.toPre.P.isLB (dd' a) (hinv a).1 (j i) (j i') (c k)
        (t1.trans (inf_le_inf (hVj i) (hVj i'))) (t3.trans (inf_le_inf (hVj i') (hWc k)))
        (t2.trans (inf_le_inf (hVj i) (hWc k)))]
    abel
  have hm2 : ∀ a i k k', rsT (φU a k k') (V i ⊓ W k ⊓ W k') =
      rsT (β a i k') (V i ⊓ W k ⊓ W k') - rsT (β a i k) (V i ⊓ W k ⊓ W k') := by
    intro a i k k'
    subst hφU hβ
    have t1 : V i ⊓ W k ⊓ W k' ≤ W k ⊓ W k' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have t2 : V i ⊓ W k ⊓ W k' ≤ V i ⊓ W k := inf_le_left
    have t3 : V i ⊓ W k ⊓ W k' ≤ V i ⊓ W k' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    simp only
    rw [dlg_refine _ _ (dd' a) (hinv a).1 W c hWc k k' t1, GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i) (hWc k)) t2,
      GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i) (hWc k')) t3,
      ← dlg_tri _ _ Dd.toPre.P.isLB (dd' a) (hinv a).1 (j i) (c k) (c k')
        (t2.trans (inf_le_inf (hVj i) (hWc k))) (t1.trans (inf_le_inf (hWc k) (hWc k')))
        (t3.trans (inf_le_inf (hVj i) (hWc k')))]
    abel

  set q := Dd.toPre.P.A.hom
  have hmix := _root_.GlobalTheory.KS.isCob_of_mixed _ J κ V W hWcov
    (fun i i' => z i i' - ∑ a, constFn q _ (cc a) * φV (e a) i i')
    (fun k k' => z' k k' - ∑ a, constFn q _ (cc a) * φU (e a) k k')
    (fun i k => b i k - ∑ a, constFn q _ (cc a) * β (e a) i k)
    (fun i i' k => by
      simp only [GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_sum, rsT_cmul, hR1, hm1, mul_sub, Finset.sum_sub_distrib]; abel)
    (fun i k k' => by
      simp only [GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_sum, rsT_cmul, hR2, hm2, mul_sub, Finset.sum_sub_distrib]; abel)
    ⟨y', fun k k' => by subst hφU; exact hy' k k'⟩
  obtain ⟨y, hy⟩ := hmix
  refine ⟨fun a => ∑ b, if e b = a then cc b else 0, y, fun i i' => ?_⟩
  have h := hy i i'
  rw [sum_reindex q _ cc e (fun a => rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) (j i) (j i')
    (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i'))) (V i ⊓ V i'))]
  simp only at h
  rw [← h]
  subst hφV
  simp only
  abel

end GlobalTheory.CoverRefinementPullback
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldCommutesPointTranslationStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantVectorField_commutes_pointTranslation : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left), IsInv G v dd → ∀ (x : 𝟙_ (Over (Sp R)) ⟶ G) (O O' : G.left.Opens), O' ≤ GlobalTheory.HeatTrans.tr G x ⁻¹ᵁ O → ∀ f : Γ(G.left, O), dd O' (pbT (GlobalTheory.HeatTrans.tr G x) f O') = pbT (GlobalTheory.HeatTrans.tr G x) (dd O f) O' := by
  first | exact @GlobalTheory.Heat.IsInv.pbT_tr | exact GlobalTheory.Heat.IsInv.pbT_tr | (intros; apply GlobalTheory.Heat.IsInv.pbT_tr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldOfTangentVectorLinearCombina
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.InvComb

open TrivSqZeroExt (inl inr)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem tv_finsum {κ : Type} (s : Finset κ) (f : κ → TanM (𝟙 (Sp R)) G) :
    tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty]; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, PullbackSections.tv_add, ih]

theorem isField_comb (g : ℕ) (e : Fin g → Fld G.left) (he : ∀ c, IsField ⊤ (e c)) (a : Fin g → R) :
    IsField ⊤ (fun O f => ∑ c, constFn G.hom O (a c) * e c O f) := by
  refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW f => ?_⟩
  · have h1 := fun c => (he c).1 W hW f f'
    simp only [h1, mul_add, Finset.sum_add_distrib]
  · have h1 := fun c => (he c).2.1 W hW f f'
    simp only [h1, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun c _ => by ring
  · have h1 := fun c => (he c).2.2 W W' h hW f
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [h1, map_sum, map_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← GlobalTheory.ArcPts.SecValue.res_constFn G.hom h (a c)]

theorem isInv_comb : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g : ℕ)
    (w : Fin g → TanM (𝟙 (Sp R)) G) (e : Fin g → Fld G.left), (∀ c, IsInv G (w c) (e c)) →
    ∀ a : Fin g → R, IsInv G (∑ c, a c • w c) (fun O f => ∑ c, constFn G.hom O (a c) * e c O f) := by
  intro R _ G _ _ g w e hw a
  refine ⟨isField_comb g e (fun c => (hw c).1) a, ?_⟩
  intro S _ φ x w' O f hx hO htr
  letI : Algebra R S := φ.toAlgebra
  have hG := GlobalTheory.Heat.CoeffWt.isGrpPullback_self G
  choose u hu using fun c => PullbackSections.push_surj hG (tv (w c))
  have hul : ∀ c, (u c).left = (tv (w c)).left := fun c =>
    (Category.comp_id _).symm.trans (congrArg (fun q => q.left) (hu c))
  have ht : ∀ c, IsTangent (u c) := fun c => (PullbackSections.isTangent_iff hG _).2 (by rw [hu c]; exact PullbackSections.tv_mem _)
  let z0 : Chart.sp (R₀ := R) S ⟶ G := Over.homMk x hx
  let z : Chart.sp (R₀ := R) (DualNumber S) ⟶ G := Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z0
  let ee : Fin g → DualNumber S := fun c => inr (φ (a c))
  have hee : ∀ i j, ee i * ee j = 0 := fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _
  obtain ⟨a₁, a₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (GlobalTheory.SqZero.inlS R S).toRingHom x O hO
  obtain ⟨b₁, b₂⟩ := GlobalTheory.Heat.CoeffWt.valR_prod hul ht hw ee hee z O a₁ Finset.univ

  choose U hU using PullbackSections.push_surj hG (tv (∑ c, a c • w c))
  have hU' : U = ∏ c, PullbackSections.scK (a c) (u c) := by
    refine PullbackSections.push_inj hG ?_
    rw [hU, map_prod, tv_finsum]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [PullbackSections.push_scK, hu c, PullbackSections.tv_smul]
  have hUl : U.left = (tv (∑ c, a c • w c)).left :=
    (Category.comp_id _).symm.trans (congrArg (fun q => q.left) hU)
  obtain ⟨g', v', hg', hv', rfl⟩ := htr
  let ρ : Chart.sp (R₀ := R) (DualNumber S) ⟶ tEpsG (x ≫ G.hom) := Over.homMk (𝟙 _) (by
    rw [hx]
    refine (Category.id_comp _).trans ?_
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap S (DualNumber S)))).symm)
  have k₁ : ρ ≫ g' = z := Over.OverMorphism.ext ((Category.id_comp _).trans hg')
  have k₂ : ρ ≫ v' = ∏ c, (Chart.spMap (GlobalTheory.SqZero.epsTo R (ee c) (hee c c)) ≫ u c :
      Chart.sp (R₀ := R) (DualNumber S) ⟶ G) := by
    have k₃ : ρ ≫ v' = Chart.spMap (GlobalTheory.SqZero.dualMap (Algebra.ofId R S)) ≫ U := by
      refine Over.OverMorphism.ext ((Category.id_comp _).trans (hv'.trans ?_))
      show _ = _ ≫ U.left
      rw [hUl]
      refine congrArg (fun q : DualNumber R →+* DualNumber S => spMap q ≫ _) (RingHom.ext fun r => ?_)
      ext <;> simp [dualMap, Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl] <;> rfl
    rw [k₃, hU', comp_prodT]
    refine Finset.prod_congr rfl fun c _ => Over.OverMorphism.ext ?_
    show _ ≫ spMap (epsScaleR (a c)) ≫ (u c).left = _ ≫ (u c).left
    rw [← Category.assoc]
    refine congrArg (· ≫ (u c).left) ?_
    simp only [Chart.spMap_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r <;> simp [epsScaleR, GlobalTheory.SqZero.epsTo, GlobalTheory.SqZero.dualTo_apply, ee, Algebra.smul_def] <;> rfl
  have key : (g' * v').left = ((∏ c, (Chart.spMap (GlobalTheory.SqZero.epsTo R (ee c) (hee c c)) ≫ u c :
      Chart.sp (R₀ := R) (DualNumber S) ⟶ G)) * z).left := by
    rw [← k₂, ← k₁, _root_.mul_comm, ← MonObj.comp_mul]
    exact (Category.id_comp _).symm
  rw [key, b₂ f]
  have a₃ : ∀ h, valR z.left O h = inl (valR x O h) := a₂
  simp only [a₃]
  show _ = valR x O (∑ c, constFn G.hom O (a c) * e c O f)
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [GlobalTheory.ZH.CrdCalc.valR_eq x O hO, map_sum]
  simp only [map_mul, ← GlobalTheory.ZH.CrdCalc.valR_eq x O hO]
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, zero_add, TrivSqZeroExt.snd_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [GlobalTheory.ZH.CrdCalc.valR_mul x O hO, GlobalTheory.ArcPts.SecValue.valR_constFn G.hom φ x hx O hO]
  simp [ee, mul_comm]

end GlobalTheory.Heat.InvComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrameChart
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

variable {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
  {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ}

theorem isFrame_chart (h : IsGrpPullback H G x ψ) (j : PUnit → (hodge G g).ι) :
    IsFrame fun i => (omegaBase h).app (LB.wchart (hodge G g) (fun _ => x) j)
      (pullbackSections x (omega G) (LB.wchart_le (hodge G g) (fun _ => x) j PUnit.unit) ((j PUnit.unit).e i)) :=
  (GlobalTheory.BadPt.Fibre.frame_pb x (j PUnit.unit).isFrame _).map_iso (omegaBase h)

def gen (h : IsGrpPullback H G x ψ) {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a) : LB.Gen ((hodge G g).pull x) where
  s j := (isFrame_chart h j).detUnit ha le_rfl le_top

end GlobalTheory.HodgeFrameGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor GlobalTheory.EndLoc

variable {O : Type} [Ring O]

def ActPB {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    (z' : SiegPre h M ζ s') (act' : O → (z'.A ⟶ z'.A)) (z : SiegPre h M ζ s) (act : O → (z.A ⟶ z.A))
    (f : S' ⟶ S) : Prop :=
  ∃ (φ : z'.A.left ⟶ z.A.left) (φ₂ : (G2 z'.A).left ⟶ (G2 z.A).left),
    IsGrpPullback z'.A z.A f φ ∧ IsSquare φ φ₂ ∧ LBIso z'.P (z.P.pull φ₂) ∧
      (∀ a, (z'.lev a).left ≫ φ = f ≫ (z.lev a).left) ∧ ∀ o, (act' o).left ≫ φ = φ ≫ (act o).left

theorem ActPB.trans {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B}
    {s' : S' ⟶ Sp B} {s'' : S'' ⟶ Sp B} {z : SiegPre h M ζ s} {z' : SiegPre h M ζ s'} {z'' : SiegPre h M ζ s''}
    {act : O → (z.A ⟶ z.A)} {act' : O → (z'.A ⟶ z'.A)} {act'' : O → (z''.A ⟶ z''.A)} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m' : ActPB z'' act'' z' act' f') (m : ActPB z' act' z act f) :
    ActPB z'' act'' z act (f' ≫ f) := by
  obtain ⟨φ, φ₂, hφ, hs, hw, hl, ha⟩ := m
  obtain ⟨ψ, ψ₂, hψ, hs', hw', hl', ha'⟩ := m'
  refine ⟨ψ ≫ φ, ψ₂ ≫ φ₂, hψ.comp hφ, GlobalTheory.TChart.AbPol.isSquare_comp hs' hs,
    GlobalTheory.TChart.AbLevel.lbIso_comp z.isLB z'.isLB z''.isLB hw hw', fun a => ?_, fun o => ?_⟩
  · rw [← Category.assoc, hl' a, Category.assoc, hl a, Category.assoc]
  · rw [← Category.assoc, ha' o, Category.assoc, ha o, Category.assoc]

def ZRel {h h' M : ℕ} {B : Type} [CommRing B] {ζ : B} {S : Scheme.{0}} {t : S ⟶ Sp B} (e : O)
    (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) {n : ℕ} (o : Fin n → O)
    (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (c : SiegPre h M ζ t) (z : SiegPre h' M ζ t)
    (act : O → (z.A ⟶ z.A)) : Prop :=
  ∃ (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 c.A ∧ pr ≫ inc = act e ∧
    LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) ∧ (∀ a, c.lev a ≫ inc = z.lev (jl a)) ∧
    ∀ a, z.lev a = (List.ofFn fun k => c.lev (κ k a) ≫ inc ≫ act (o k)).prod

theorem isQProjOver_comp_immersion {R : Type} [CommRing R] {X Y : Scheme.{0}} (j : X ⟶ Y) (s : Y ⟶ Sp R)
    (hj : IsImmersion j) (hq : QuasiCompact j) (hs : IsQProjOver s) : IsQProjOver (j ≫ s) := by
  obtain ⟨N, i, hi, hiq, rfl⟩ := hs
  exact ⟨N, j ≫ i, inferInstance, inferInstance, (Category.assoc _ _ _).symm⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueOfSectionPullbackScalarMultipleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointValue_of_section_pullback_scalar_multiple : ∀ (X₂ Y : Scheme.{0}) (L₂ : LB X₂) (f₂ : Y ⟶ X₂) (k : ℕ) (σ : SecM (𝟙 X₂) L₂ k) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))) (c : Γ(Y, ⊤)), GeneratorPullback.SecScal L₂ (fun _ : Fin 1 => f₂) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 X₂) (fun _ => (k : ℤ)) σ f₂ c → ∀ (F : Type) [CommRing F] (ξ : Sp F ⟶ Y) (i : L₂.ι), ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ L₂.U i → valR (ξ ≫ f₂) _ (σ.f fun _ => i) = valR ξ ⊤ c * valR ξ _ (s.f fun _ => i) := by
  first | exact @GlobalTheory.SecScalVal.val_of_secScal | exact GlobalTheory.SecScalVal.val_of_secScal | (intros; apply GlobalTheory.SecScalVal.val_of_secScal <;> assumption)
end

