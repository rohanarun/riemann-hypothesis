module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitsOfPullEqZero
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SmallGlue

theorem exists_units_of_pull_eq_zero {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (q : Y ⟶ X)
    (h : GlobalTheory.CechPic.pull q (cls L hL) = 0) :
    ∃ a : ∀ j, Γ(Y, q ⁻¹ᵁ L.U j)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (i j : L.ι),
      q (f z) ∈ L.U i → q (f z) ∈ L.U j →
      gm f z (q ⁻¹ᵁ L.U i) (a i) = gm (f ≫ q) z (L.U i ⊓ L.U j) (L.g i j) * gm f z (q ⁻¹ᵁ L.U j) (a j) := by
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff (pull_isLB hL q)).1 h
  have le : ∀ j, q ⁻¹ᵁ L.U j ≤ (L.pull q).U (fun _ => j) := fun j y hy => mem_pull.2 hy
  refine ⟨fun j => res (le j) (t.s (fun _ => j)), fun Z f z i j hi hj => ?_⟩
  have hm : f z ∈ (L.pull q).U (fun _ => i) ⊓ (L.pull q).U (fun _ => j) := ⟨mem_pull.2 hi, mem_pull.2 hj⟩
  have := congrArg (gm f z _) (ht (fun _ => i) (fun _ => j))
  rw [map_mul, gm_res _ z _ hm, gm_res _ z _ hm] at this
  rw [gm_res f z (le i) hi, gm_res f z (le j) hj]
  exact this.trans (congrArg (· * _) (gm_pull_g L q f z (fun _ => i) (fun _ => j) hm.1 hm.2))

theorem pullU_isGen_of_germ {X Y : Scheme.{0}} {L : LB X} (q : Y ⟶ X) (d : ∀ j, Γ(X, L.U j)ˣ) (i j : L.ι)
    (h : ∀ y : Y, q y ∈ L.U i → q y ∈ L.U j →
      gm (𝟙 Y) y (q ⁻¹ᵁ L.U i) (pullU q _ (d i)) =
        gm (𝟙 Y ≫ q) y (L.U i ⊓ L.U j) (L.g i j) * gm (𝟙 Y) y (q ⁻¹ᵁ L.U j) (pullU q _ (d j))) :
    pullU q (L.U i ⊓ L.U j) (res inf_le_left (d i)) =
      pullU q (L.U i ⊓ L.U j) (L.g i j * res inf_le_right (d j)) := by
  refine unit_ext fun y hy => ?_
  have hm : q ((𝟙 Y : Y ⟶ Y) y) ∈ L.U i ⊓ L.U j := hy
  have e := h y hm.1 hm.2
  rw [gm_pull (𝟙 Y) q y _ hm.1, gm_pull (𝟙 Y) q y _ hm.2] at e
  rw [gm_pull (𝟙 Y) q y _ hm, gm_pull (𝟙 Y) q y _ hm, map_mul, gm_res (𝟙 Y ≫ q) y _ hm,
    gm_res (𝟙 Y ≫ q) y _ hm]
  exact e

theorem cech_patching : ∀ {X X₁ X₂ X₀ : Scheme.{0}} (ι₁ : X₁ ⟶ X) (ι₂ : X₂ ⟶ X) (ρ₁ : X₀ ⟶ X₁) (ρ₂ : X₀ ⟶ X₂), ρ₁ ≫ ι₁ = ρ₂ ≫ ι₂ →
    (∀ u : Γ(X₀, ⊤)ˣ, ∃ v : Γ(X₁, ⊤)ˣ, ∀ x : X₀, gm ρ₁ x ⊤ v = gm (𝟙 X₀) x ⊤ u) →
    (∀ (U : X.Opens) (a₁ : Γ(X₁, ι₁ ⁻¹ᵁ U)ˣ) (a₂ : Γ(X₂, ι₂ ⁻¹ᵁ U)ˣ),
      (∀ x : X₀, ρ₁ x ∈ ι₁ ⁻¹ᵁ U → gm ρ₁ x (ι₁ ⁻¹ᵁ U) a₁ = gm ρ₂ x (ι₂ ⁻¹ᵁ U) a₂) →
      ∃ d : Γ(X, U)ˣ, pullU ι₁ U d = a₁ ∧ pullU ι₂ U d = a₂) →
    (∀ (U : X.Opens) (d d' : Γ(X, U)ˣ), pullU ι₁ U d = pullU ι₁ U d' → pullU ι₂ U d = pullU ι₂ U d' → d = d') →
    ∀ c : Pic X, GlobalTheory.CechPic.pull ι₁ c = 0 → GlobalTheory.CechPic.pull ι₂ c = 0 → c = 0 := by
  intro X X₁ X₂ X₀ ι₁ ι₂ ρ₁ ρ₂ hsq hlift hpatch huniq c h₁ h₂
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨α, hα⟩ := exists_units_of_pull_eq_zero hL ι₁ h₁
  obtain ⟨β, hβ⟩ := exists_units_of_pull_eq_zero hL ι₂ h₂
  have pt : ∀ x : X₀, ι₂ (ρ₂ x) = ι₁ (ρ₁ x) := fun x => congrArg (fun g => g x) hsq.symm
  have le : ∀ j, ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j) ≤ ρ₂ ⁻¹ᵁ (ι₂ ⁻¹ᵁ L.U j) := fun j x hx => by
    show ι₂ (ρ₂ x) ∈ L.U j
    rw [pt]; exact hx
  have hu : ∀ j (x : X₀), ι₁ (ρ₁ x) ∈ L.U j →
      gm (𝟙 X₀) x (ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j)) (pullU ρ₁ _ (α j) * (res (le j) (pullU ρ₂ _ (β j)))⁻¹) =
        gm ρ₁ x _ (α j) * (gm ρ₂ x _ (β j))⁻¹ := fun j x hx => by
    rw [map_mul, map_inv, gm_res (𝟙 X₀) x (le j) hx, gm_pull (𝟙 X₀) ρ₁ x _ hx,
      gm_pull (𝟙 X₀) ρ₂ x _ (le j hx), Category.id_comp, Category.id_comp]
  obtain ⟨w, hw⟩ := glue_unit (⊤ : X₀.Opens) (fun j => ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j)) (fun _ => le_top)
    (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (ι₁ (ρ₁ x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj⟩)
    (fun j => pullU ρ₁ _ (α j) * (res (le j) (pullU ρ₂ _ (β j)))⁻¹)
    (fun i j x hx => by
      refine (hu i x hx.1).trans (Eq.trans ?_ (hu j x hx.2).symm)
      rw [hα _ ρ₁ x i j hx.1 hx.2, hβ _ ρ₂ x i j (le i hx.1) (le j hx.2), hsq, mul_inv, _root_.mul_mul_mul_comm,
        mul_inv_cancel, _root_.one_mul])
  obtain ⟨v, hv⟩ := hlift w
  have hd : ∀ j, ∃ d : Γ(X, L.U j)ˣ, pullU ι₁ _ d = α j * (res le_top v)⁻¹ ∧ pullU ι₂ _ d = β j := fun j =>
    hpatch _ _ _ fun x hx => by
      have e : gm (𝟙 X₀) x ⊤ w = gm ρ₁ x _ (α j) * (gm ρ₂ x _ (β j))⁻¹ :=
        (gm_res (𝟙 X₀) x (le_top : ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j) ≤ ⊤) hx w).symm.trans
          ((congrArg _ (hw j)).trans (hu j x hx))
      rw [map_mul, map_inv, gm_res ρ₁ x _ hx, hv, e, mul_inv, inv_inv, mul_inv_cancel_left]
  choose d hd₁ hd₂ using hd
  refine (cls_eq_zero_iff hL).2 ⟨⟨d⟩, fun i j => huniq _ _ _ ?_ ?_⟩
  · refine pullU_isGen_of_germ ι₁ d i j fun y hi hj => ?_
    rw [hd₁, hd₁, map_mul, map_mul, map_inv, map_inv, gm_res (𝟙 X₁) y _ hi, gm_res (𝟙 X₁) y _ hj,
      hα _ (𝟙 X₁) y i j hi hj, _root_.mul_assoc]
  · refine pullU_isGen_of_germ ι₂ d i j fun y hi hj => ?_
    rw [hd₂, hd₂]
    exact hβ _ (𝟙 X₂) y i j hi hj

end GlobalTheory.SmallGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsRootLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilRootLocal

theorem exists_weilIs_root_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A],
    IsAbelianScheme A → ∀ (PP : RigLB A), CubicalStr A PP → ∀ (R : Type) [CommRing R] [IsLocalRing R]
    (t : Sp R ⟶ S) (n : ℕ) (g h : Over.mk t ⟶ A), g ^ n = 1 → h ^ n = 1 →
    ∃ u : Rˣ, u ^ n = 1 ∧ Out.WeilIs A PP.L (n : ℤ) g h (unitOn u) := by
  intro S A _ _ hA PP cub R _ _ t n g h hg hh
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have loc : ∀ z : Over.mk t ⟶ A, z ^ n = 1 → ∀ p : (Over.mk t).left, ∃ V : (Over.mk t).left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp A PP.L (n : ℤ) (Out.overRes V), θ.pt = Out.overResι V ≫ z := fun z hz p => by
    obtain ⟨θ, hθ⟩ := TorsionThetaLocal.exists_theta_of_pow_eq_one S A PP cub R t n z hz
    obtain ⟨θ', hθ'⟩ := CommutatorPairing.exists_pull PP.isLB θ (Out.overResι ⊤)
    exact ⟨⊤, trivial, θ', by rw [hθ', hθ]⟩
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_weilIs hG hA PP.isLB (loc g hg) (loc h hh)
  have pw : ∀ m : ℕ, Out.WeilIs A PP.L (n : ℤ) (g ^ (m + 1)) h (c ^ (m + 1)) := fun m => by
    induction m with
    | zero => rw [zero_add, pow_one, pow_one]; exact hc
    | succ m ih =>
      rw [pow_succ g (m + 1), pow_succ c (m + 1)]
      exact DiagPairing.weilIs_mul_left hG hA PP.isLB ih hc
  have e := pw n
  rw [pow_succ g, hg, _root_.one_mul] at e
  have hcn := CommutatorPairing.weilIs_unique hG hA PP.isLB e hc
  rw [pow_succ, mul_eq_right] at hcn
  obtain ⟨u, rfl⟩ : ∃ u : Rˣ, unitOn u = c :=
    (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toMulEquiv).surjective c
  refine ⟨u, unitOn_injective_of_commRing ?_, hc⟩
  show unitOn (u ^ n) = unitOn 1
  rw [unitOn, unitOn, map_pow, map_one]
  exact hcn

end GlobalTheory.WeilRootLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsXPowMulSubMemVanishingIdealReduction
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.FormalAlg.PolyLoc

open MvPolynomial

theorem exists_homogeneous_coeff_mem {σ R : Type} [CommRing R] (J : Ideal R) (i : σ) (g : MvPolynomial σ R)
    (hg : ∀ m, AddMonoidAlgebra.coeff g m ∈ J) : ∃ e : ℕ, ∀ d, e ≤ d → ∃ G : MvPolynomial σ R, G.IsHomogeneous d ∧
      (∀ m, AddMonoidAlgebra.coeff G m ∈ J) ∧ (X i - 1 : MvPolynomial σ R) ∣ G - g := by
  let Q : MvPolynomial σ R → Prop := fun p => ∃ e : ℕ, ∀ d, e ≤ d → ∃ G : MvPolynomial σ R, G.IsHomogeneous d ∧
      (∀ m, AddMonoidAlgebra.coeff G m ∈ J) ∧ (X i - 1 : MvPolynomial σ R) ∣ G - p
  have h0 : Q 0 := ⟨0, fun d _ => ⟨0, isHomogeneous_zero _ _ _, fun m => by exact J.zero_mem,
    by rw [sub_zero]; exact dvd_zero _⟩⟩
  have hadd : ∀ p q, Q p → Q q → Q (p + q) := by
    rintro p q ⟨e, he⟩ ⟨e', he'⟩
    refine ⟨max e e', fun d hd => ?_⟩
    obtain ⟨G, hG, hGJ, hGd⟩ := he d (le_of_max_le_left hd)
    obtain ⟨G', hG', hGJ', hGd'⟩ := he' d (le_of_max_le_right hd)
    refine ⟨G + G', hG.add hG', fun m => by rw [MvPolynomial.coeff_add]; exact J.add_mem (hGJ m) (hGJ' m), ?_⟩
    rw [add_sub_add_comm]
    exact hGd.add hGd'
  have hmon : ∀ v (c : R), c ∈ J → Q (monomial v c) := by
    intro v c hc
    refine ⟨v.degree, fun d hd => ⟨monomial v c * X i ^ (d - v.degree), ?_, fun m => ?_, ?_⟩⟩
    · have := (isHomogeneous_monomial (R := R) c (rfl : v.degree = v.degree)).mul (isHomogeneous_X_pow i (d - v.degree))
      rwa [Nat.add_sub_cancel' hd] at this
    · classical
      rw [X_pow_eq_monomial, monomial_mul, coeff_monomial, _root_.mul_one]
      split_ifs
      · exact hc
      · exact J.zero_mem
    · rw [← mul_sub_one]
      exact (sub_one_dvd_pow_sub_one _ _).mul_left _
  rw [g.as_sum]
  exact Finset.sum_induction _ Q hadd h0 fun v _ => hmon v _ (hg v)

theorem exists_X_pow_mul_mem_vanIdeal {X : Scheme.{0}} {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {H : LB X} {m : ℕ} {s : Fin (m + 1) → LB.Sec H} (hc : ⨆ j, nonzeroLocus (s j) = ⊤)
    (ha : ∀ j, IsAffineOpen (nonzeroLocus (s j))) (r : ∀ j, Fin (m + 1) → Γ(X, nonzeroLocus (s j)))
    (hr : ∀ j, IsRatioFamily s j (r j)) (i : Fin (m + 1)) {Q : MvPolynomial (Fin (m + 1)) R} {e : ℕ}
    (hQ : Q.IsHomogeneous e) (h0 : eval₂Hom (cst f _) (r i) Q = 0) :
    ∃ c : ℕ, MvPolynomial.X i ^ c * Q ∈ vanIdeal f s := by
  have hn : ∀ j, ∃ n, r j i ^ n * eval₂Hom (cst f _) (r j) Q = 0 := fun j => by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X (ha j) _ _ (fn_ext fun y hy => ?_)
    have hj : y ∈ nonzeroLocus (s j) := X.basicOpen_le _ hy
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hj
    have uj := (mem_nonzeroLocus_iff_isUnit _ hk).1 hj
    have hi : y ∈ nonzeroLocus (s i) := by
      rw [mem_nonzeroLocus_iff_isUnit _ hk, (hr j).gs_eq hj hk i]
      exact ((LBGerm.isUnit_gs_iff (𝟙 X) y _ hj _).2 hy).mul uj
    have e₁ := ((hr j).gs_form f hj hk hQ).symm.trans ((hr i).gs_form f hi hk hQ)
    rw [h0, LBGerm.gs_zero _ y _ hi, mul_zero] at e₁
    rw [LBGerm.gs_zero _ y _ hy]
    exact (gs_res _ y (X.basicOpen_le _) hy _).trans ((uj.pow e).mul_right_eq_zero.1 e₁)
  choose n hn using hn
  refine ⟨Finset.univ.sup n, (mem_vanIdeal _ _ _).2 ?_⟩
  refine (mem_vanishingForms_of_ratios f hc r hr ((isHomogeneous_X_pow i _).mul hQ) fun j => ?_).2
  have hle : n j ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ j)
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le' hle
  rw [hb, map_mul, map_pow, eval₂Hom_X', pow_add, _root_.mul_assoc, hn j, mul_zero]

theorem app_eval_eq_zero {R : Type} [CommRing R] {X X' : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (β : X' ⟶ X) {H : LB X} {H' : LB X'} {w : LB.Iso H' (H.pull β)} {m : ℕ} {s : Fin (m + 1) → LB.Sec H}
    {s' : Fin (m + 1) → LB.Sec H'} (hH : H.IsLB) (hH' : H'.IsLB) (hrel : ∀ j, Rel β w (s j) (s' j))
    (i : Fin (m + 1)) (r : Fin (m + 1) → Γ(X, nonzeroLocus (s i))) (hr : IsRatioFamily s i r)
    {F : MvPolynomial (Fin (m + 1)) R} {t : ℕ} (hF : F.IsHomogeneous t) (h0 : F ∈ vanIdeal (β ≫ f) s') :
    (β.app (nonzeroLocus (s i))).hom (eval₂Hom (cst f _) r F) = 0 := by
  refine fn_ext fun z hz => ?_
  rw [gs_pull (𝟙 X') β z _ hz, Category.id_comp, LBGerm.gs_zero _ z _ hz]
  obtain ⟨k, hk⟩ := exists_chart hH (β z)
  obtain ⟨k', hk'⟩ := exists_chart hH' z
  have e₁ := Rel.form hrel f hF z k k' hk hk'
  rw [(mem_vanIdeal _ _ _).1 h0 k', LBGerm.gs_zero _ z _ hk', mul_zero] at e₁
  have e₂ := congrArg (β.stalkMap z).hom (hr.gs_form f hz hk hF)
  rw [map_mul, map_pow, gs_stalkMap_comp β (𝟙 X) z _ hk, gs_stalkMap_comp β (𝟙 X) z _ hk,
    gs_stalkMap_comp β (𝟙 X) z _ hz] at e₂
  simp only [Category.comp_id] at e₂
  rw [e₁] at e₂
  have u := (mem_nonzeroLocus_iff_pull (s i) β z hk).1 hz
  exact ((u.pow t).mul_right_eq_zero.1 e₂.symm)

end GlobalTheory.FormalAlg.PolyLoc


open GlobalTheory.FormalAlg.PolyLoc MvPolynomial in
theorem GlobalTheory.FormalAlg.exists_X_pow_mul_sub_mem_vanIdeal : ∀ (R : Type) [CommRing R] (J : Ideal R) (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (β : X' ⟶ X) (q : X' ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback β q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → ∀ (H : LB X) (H' : LB X') (w : LB.Iso H' (H.pull β)) (n : ℕ) (s : Fin (n + 1) → LB.Sec H) (s' : Fin (n + 1) → LB.Sec H'), H.IsLB → H'.IsLB → w.IsGen → (∀ j, Rel β w (s j) (s' j)) → VeryAmpleBy f H s → ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ vanIdeal (β ≫ f) s' → ∀ i, ∃ (N : ℕ) (G : MvPolynomial (Fin (n + 1)) R), G.IsHomogeneous (t + N) ∧ (∀ m, AddMonoidAlgebra.coeff G m ∈ J) ∧ MvPolynomial.X i ^ N * F - G ∈ vanIdeal f s := by
  open MvPolynomial GlobalTheory.FormalAlg.PolyLoc in
    intro R _ J X X' f β q hpb H H' w n s s' hH hH' _ hrel hva t F hF h0 i
    obtain ⟨hc, hva⟩ := hva
    choose ha r hr hsur using hva
    have hR : ∀ j, IsRatioFamily s j (r j) := hr
    set φ := MvPolynomial.eval₂Hom (AbLaw.cst f (nonzeroLocus (s i))) (r i) with hφ
    have hker := ((_root_.GlobalTheory.FormalAlg.baseChange_quotient R J X X' f β q hpb).2.2 _ (ha i)).2
    have hβ : (β.app (nonzeroLocus (s i))).hom (φ F) = 0 := app_eval_eq_zero f β hH hH' hrel i (r i) (hR i) hF h0
    have hJ : φ F ∈ (Ideal.map (C : R →+* MvPolynomial (Fin (n + 1)) R) J).map φ := by
      have h2 : φ F ∈ J.map (AbLaw.cst f (nonzeroLocus (s i))) := hker ▸ (RingHom.mem_ker.2 hβ)
      have h3 : AbLaw.cst f (nonzeroLocus (s i)) = φ.comp C := by
        ext a
        simp [hφ]
      rwa [h3, ← Ideal.map_map] at h2
    obtain ⟨g, hg, hgF⟩ := (Ideal.mem_map_iff_of_surjective φ (hsur i)).1 hJ
    rw [MvPolynomial.mem_map_C_iff] at hg
    obtain ⟨e, he⟩ := exists_homogeneous_coeff_mem J i g hg
    obtain ⟨G₁, hG₁, hG₁J, hdvd⟩ := he (t + e) (Nat.le_add_left e t)
    have hQ : (MvPolynomial.X i ^ e * F - G₁).IsHomogeneous (t + e) := by
      have := (isHomogeneous_X_pow i e).mul hF
      rw [Nat.add_comm e t] at this
      exact this.sub hG₁
    have hφQ : φ (MvPolynomial.X i ^ e * F - G₁) = 0 := by
      obtain ⟨P, hP⟩ := hdvd
      have hx : φ (MvPolynomial.X i) = 1 := by rw [hφ, eval₂Hom_X']; exact (hR i).self_eq_one
      have hG : G₁ = g + (MvPolynomial.X i - 1) * P := by rw [← hP]; ring
      rw [hG, map_sub, map_mul, map_pow, hx, one_pow, _root_.one_mul, map_add (f := _), map_mul, map_sub, hx, map_one, sub_self,
        zero_mul, add_zero, hgF, sub_self]
    obtain ⟨c, hc'⟩ := exists_X_pow_mul_mem_vanIdeal f hc ha r hR i hQ hφQ
    refine ⟨c + e, MvPolynomial.X i ^ c * G₁, ?_, fun m => ?_, ?_⟩
    · have := (isHomogeneous_X_pow i c).mul hG₁
      convert this using 1
      ring
    · have h4 : MvPolynomial.X i ^ c * G₁ ∈ Ideal.map (C : R →+* MvPolynomial (Fin (n + 1)) R) J :=
        Ideal.mul_mem_left _ _ (mem_map_C_iff.2 hG₁J)
      exact mem_map_C_iff.1 h4 m
    · convert hc' using 1
      ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartPowEqOneLocal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

theorem push_pow {S' S₀ : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S₀} [GrpObj G] {f : S' ⟶ S₀}
    {π : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f π) {T : Over S'} (x : T ⟶ G')
    (x₀ : Over.mk (T.hom ≫ f) ⟶ G) (h : x₀.left = x.left ≫ π) (n : ℕ) :
    (x₀ ^ n).left = (x ^ n).left ≫ π := by
  have h1 : (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ π := by
    let e : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ π) (by
      show ((1 : T ⟶ G').left ≫ π) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, hg.1.w, ← Category.assoc, Over.w])
    have he : e * e = e := Over.OverMorphism.ext ((hg.2 T 1 1 e e rfl rfl).trans (by rw [_root_.mul_one]; rfl))
    have he1 : e = 1 := mul_eq_left.1 he
    exact (congrArg (fun z => z.left) he1).symm
  induction n with
  | zero => simpa using h1
  | succ n ih => rw [pow_succ, pow_succ]; exact hg.2 T _ _ _ _ ih h

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g := by
  have := congrArg (fun z => (Spec.preimage z).hom) h
  simpa using this

theorem lift_of_residue : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X} {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q) {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left} (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (h : aH P' x0 hu hg.1 ^ q = 1) (S : Type) [CommRing S] [hS : IsLocalRing S] (y : Sp S ⟶ (torsion G' q).left), (∃ s : Sp (IsLocalRing.ResidueField S) ⟶ (Hs P' x0 hu).left, s ≫ (jH P' x0 hu hg.1 h).left = spMap (IsLocalRing.residue S) ≫ y) → ∃ s : Sp S ⟶ (Hs P' x0 hu).left, s ≫ (jH P' x0 hu hg.1 h).left = y := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu G' _ π hg h S _ hS y hy
  obtain ⟨s0, hs0⟩ := hy
  let o : O →+* S := (Spec.preimage (y ≫ (torsion G' q).hom)).hom
  have ho : spMap o = y ≫ (torsion G' q).hom := Spec.map_preimage _
  let φ : R →+* S := o.comp x0
  have hu' : IsUnit (φ P'.f) := hu.map o
  have hw : (y ≫ (torsion.ι G' q).left ≫ π) ≫ t.G.hom = spMap φ ≫ ξ := by
    rw [Category.assoc, Category.assoc, hg.1.w, ← Category.assoc (torsion.ι G' q).left, Over.w (torsion.ι G' q),
      ← Category.assoc, ← ho, GlobalTheory.HTMap.spc_assoc]
  let w : Over.mk (spMap φ ≫ ξ) ⟶ t.G := GlobalTheory.HTMap.mkPt _ hw
  let T : Over (Sp O) := Over.mk (y ≫ (torsion G' q).hom)
  let yt : T ⟶ torsion G' q := Over.homMk y rfl
  let x : T ⟶ G' := yt ≫ torsion.ι G' q
  have hx : x ^ q = 1 := by
    show (yt ≫ torsion.ι G' q) ^ q = 1
    rw [← MonObj.comp_pow, GlobalTheory.KernelNoTorsion.torsionι_pow, MonObj.comp_one]
  let x₀ : Over.mk (T.hom ≫ (spMap x0 ≫ ξ)) ⟶ t.G := Over.homMk (x.left ≫ π) (by
    show (x.left ≫ π) ≫ t.G.hom = T.hom ≫ spMap x0 ≫ ξ
    rw [Category.assoc, hg.1.w, ← Category.assoc, Over.w x])
  have hx₀ : x₀ ^ q = 1 := by
    refine Over.OverMorphism.ext ?_
    rw [push_pow hg x x₀ rfl q, hx]
    have := push_pow hg x x₀ rfl 0
    simp only [pow_zero] at this
    exact this.symm
  have hwq : w ^ q = 1 := GlobalTheory.HTMap.tors_of (g := 𝟙 _) (w := x₀) (by
    rw [Category.id_comp]
    show y ≫ (torsion.ι G' q).left ≫ π = (y ≫ (torsion.ι G' q).left) ≫ π
    rw [Category.assoc]) hx₀
  obtain ⟨β0, hβ0⟩ : ∃ β, P'.At φ w.left β := by
    refine GlobalTheory.HTMap.FP.at_open hu' rfl w hwq fun 𝔪 h𝔪 => ?_
    obtain rfl := IsLocalRing.eq_maximalIdeal h𝔪
    let gm : Bt P' x0 hu →+* IsLocalRing.ResidueField S := (Spec.preimage s0).hom
    have hgm : spMap gm = s0 := Spec.map_preimage _
    have e1 : spMap (gm.comp (algebraMap O (Bt P' x0 hu))) = spMap ((IsLocalRing.residue S).comp o) := by
      rw [← GlobalTheory.HTMap.spc (algebraMap O (Bt P' x0 hu)) gm, hgm, ← GlobalTheory.HTMap.spc o (IsLocalRing.residue S), ho]
      show s0 ≫ (Hs P' x0 hu).hom = _
      rw [← Over.w (jH P' x0 hu hg.1 h), ← Category.assoc, hs0, Category.assoc]
    have e2 := spMap_inj e1
    refine ⟨gm.comp (inB P' x0 hu), ?_, ?_⟩
    · show (gm.comp (inB P' x0 hu)).comp P'.str = (IsLocalRing.residue S).comp φ
      rw [RingHom.comp_assoc, inB_str, ← RingHom.comp_assoc, e2]
      rfl
    · show spMap (gm.comp (inB P' x0 hu)) ≫ P'.u.left = spMap (IsLocalRing.residue S) ≫ y ≫ (torsion.ι G' q).left ≫ π
      rw [← GlobalTheory.HTMap.spc_assoc, hgm, ← aH_left_π P' x0 hu hg.1, ← jH_ι P' x0 hu hg.1 h, Over.comp_left,
        ← Category.assoc, ← Category.assoc, hs0, Category.assoc, Category.assoc]
  letI : Algebra O S := o.toAlgebra
  have hβ : β0.comp P'.str = (algebraMap O S).comp x0 := hβ0.1
  refine ⟨(ptOf P' x0 hu β0 hβ).left, ?_⟩
  let b : T ⟶ torsion G' q := Over.homMk ((ptOf P' x0 hu β0 hβ).left ≫ (jH P' x0 hu hg.1 h).left) (by
    show ((ptOf P' x0 hu β0 hβ).left ≫ (jH P' x0 hu hg.1 h).left) ≫ (torsion G' q).hom = y ≫ (torsion G' q).hom
    rw [Category.assoc, Over.w (jH P' x0 hu hg.1 h), Over.w (ptOf P' x0 hu β0 hβ)]
    exact ho)
  have hb : b = yt := by
    refine GlobalTheory.KernelNoTorsion.torsion_hom_ext (Over.OverMorphism.ext (hg.1.hom_ext ?_ ?_))
    · have e1 : (b ≫ torsion.ι G' q).left = (ptOf P' x0 hu β0 hβ ≫ aH P' x0 hu hg.1).left := by
        show (ptOf P' x0 hu β0 hβ).left ≫ (jH P' x0 hu hg.1 h).left ≫ (torsion.ι G' q).left = _
        rw [← Over.comp_left, jH_ι]
        rfl
      rw [e1, ptOf_aH_π, hβ0.2]
      show y ≫ (torsion.ι G' q).left ≫ π = (y ≫ (torsion.ι G' q).left) ≫ π
      rw [Category.assoc]
    · rw [Over.w (b ≫ torsion.ι G' q), Over.w (yt ≫ torsion.ι G' q)]
  exact congrArg (fun z => z.left) hb
end GlobalTheory.FinPartAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetsInAffineOpenFiniteCoproduct
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem finAff_sigma : ∀ {κ : Type} [Finite κ] (B : κ → Scheme.{0}), (∀ i, FinAff (B i)) → FinAff (∐ B) := by
  intro κ _ B hB F
  classical
  have hfin : ∀ i, {y : B i | Sigma.ι B i y ∈ F}.Finite := fun i =>
    (F.finite_toSet).preimage (Sigma.ι B i).isOpenEmbedding.injective.injOn
  choose V hV hFV using fun i => hB i (hfin i).toFinset
  refine ⟨⨆ i, Sigma.ι B i ''ᵁ V i, IsAffineOpen.iSup_of_disjoint
    (fun i => (hV i).image_of_isOpenImmersion _) fun i j hij => ?_, fun x hx => ?_⟩
  · exact (disjoint_opensRange_sigmaι B i j hij).mono (Scheme.Hom.image_le_opensRange _ _)
      (Scheme.Hom.image_le_opensRange _ _)
  · obtain ⟨i, y, rfl⟩ := (sigmaOpenCover B).exists_eq x
    have hy : y ∈ V i := hFV i y ((Set.Finite.mem_toFinset _).2 hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, ⟨y, hy, rfl⟩⟩

end GlobalTheory.DualCon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
section
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SiegelTor GlobalTheory.ZM

namespace GlobalTheory.SiegelTor


open CategoryTheory AlgebraicGeometry _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits NumberField in
theorem _root_.GlobalTheory.SiegelTor.finiteType_cycAway (n : ℕ) : Algebra.FiniteType ℤ (_root_.GlobalTheory.SiegelTor.cycAway n) := by
  have hfg : (Algebra.adjoin ℤ ({_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n, (n : ℂ)⁻¹} : Set ℂ)).FG := by
    rw [show ({_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n, (n : ℂ)⁻¹} : Set ℂ) = ↑({_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n, (n : ℂ)⁻¹} : Finset ℂ) by simp]
    exact Subalgebra.fg_adjoin_finset _
  have h := (Subalgebra.fg_iff_finiteType _).1 hfg
  rw [Algebra.adjoin_int] at h
  exact h


open CategoryTheory AlgebraicGeometry _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits NumberField in
theorem _root_.GlobalTheory.SiegelTor.arBase_cycAway : ∀ n : ℕ, n ≠ 0 → _root_.GlobalTheory.ZM.ArBase (_root_.GlobalTheory.SiegelTor.cycAway n).subtype := by
  intro n _
  exact ⟨_root_.GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n, _root_.GlobalTheory.SiegelTor.finiteType_cycAway n,
    Subtype.val_injective⟩

end GlobalTheory.SiegelTor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatPreimageContainsCodimLeOnePoints
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatCodimOne

theorem coheight_map_le_one {X Y : Scheme.{0}} (q : Y ⟶ X) (hq : GeneralizingMap q) (y : Y)
    (hy : Order.coheight y ≤ 1) : Order.coheight (q y) ≤ 1 := by
  have hy' := (Order.coheight_le_coe_iff (n := 1)).1 hy
  refine (Order.coheight_le_coe_iff (n := 1)).2 fun z hz ↦ ?_
  obtain ⟨y', h₁, rfl⟩ := hq (show z ⤳ q y from hz.le)
  have hlt : y < y' := ⟨h₁, fun h ↦ hz.not_ge (Specializes.map h q.continuous)⟩
  have hm : IsMax y' := by simpa using hy' y' hlt
  have : IsMax (q y') := fun w hw ↦ by
    obtain ⟨y'', h₂, rfl⟩ := hq (show w ⤳ q y' from hw)
    exact Specializes.map (hm (show y' ≤ y'' from h₂)) q.continuous
  simpa using this

theorem preimage_contains_codim_le_one : ∀ (X Y : Scheme.{0}) (q : Y ⟶ X) [Flat q] (W : X.Opens), (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → (∀ z : Y, ringKrullDim ((Y).presheaf.stalk z) ≤ 1 → z ∈ q ⁻¹ᵁ W) := by
  intro X Y q _ W hW y hy
  show q y ∈ W
  apply hW
  rw [ringKrullDim_stalk_eq_coheight] at hy ⊢
  have h1 : Order.coheight y ≤ 1 := by exact_mod_cast hy
  have := coheight_map_le_one q (Flat.generalizingMap q) y h1
  exact_mod_cast this

end GlobalTheory.FlatCodimOne
end

