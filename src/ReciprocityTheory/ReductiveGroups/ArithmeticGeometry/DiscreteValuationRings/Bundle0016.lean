module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenPf
section
set_option autoImplicit false
set_option linter.overlappingInstances false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing TG

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem isTheta_of_nonzeroOnSpecial' (hLaws : Laws) (hL4 : Laws4) (hR : CLND R)
    [IsDiscreteValuationRing R] (hI : I = maximalIdeal R) (U : Unif I D A G) (s : H0 U.LG.L 1)
    (hs : NonzeroOnSpecial U s) : IsTheta U s := by
  have := flat_G U.toUnifPre
  have := flat_B (D := D)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hIϖ : I = Ideal.span {ϖ} := by
    rw [hI, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
  obtain ⟨F, hF, -⟩ := (U.expand 1 le_rfl).1 (secK U.toUnifPre s)
  obtain ⟨r, hr0, σ, f, hσ, hfK, hexp⟩ := hF
  have hσr := sec_eq_of_secScal U.toUnifPre s σ (secK U.toUnifPre s) r (secK_rel U.toUnifPre s) hσ
  obtain ⟨n, u, hru⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ
  let τ : H0 U.LG.L 1 := SecOps.secScale (scal G.hom (u : R)) s
  have hστ : ∀ j, σ.f j = toW G.hom _ (ϖ ^ n) * τ.f j := fun j => by
    rw [hσr, hru]
    show _ = _ * (toW G.hom _ (u : R) * s.f j)
    rw [map_mul, mul_comm (toW G.hom _ (u : R)), _root_.mul_assoc]
  obtain ⟨g, hfg, hexpg⟩ := expand_div_pow U.toUnifPre hL4.weightIndep hϖ.ne_zero hIϖ n σ τ hστ f hexp
  let g' : ∀ α, D.toPre.SecB 1 α := fun α => SecOps.secScale (scal D.toPre.P.A.hom ((u⁻¹ : Rˣ) : R)) (g α)
  have hexp' : ∀ e, U.ExpandsAt e 1 s g' := fun e =>
    _root_.ReciprocityTheory.ChartRestriction.G.DVR.TG.expandsAt_scale U.toUnifPre ((u⁻¹ : Rˣ) : R) τ s (fun j => by
      show _ = _ * (toW G.hom _ (u : R) * s.f j)
      rw [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]) g g' (fun α j => rfl) e (hexpg e)
  have hgF : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε 1) (F.s α)
      (D.toPre.famφB α) (DegPre.famε 1) (g' α) (DegPre.prB D.toPre (FractionRing R)).left 1 := by
    intro α j₁ j₂ hc
    have e := hfK α j₁ j₂ hc
    have hf' : (f α).f j₂ = toW D.toPre.P.A.hom _ r * (g' α).f j₂ := by
      rw [hfg α j₂]
      show _ = _ * (toW _ _ ((u⁻¹ : Rˣ) : R) * (g α).f j₂)
      rw [← _root_.mul_assoc, ← map_mul, hru, mul_comm (u : R), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    have hBF : (DegPre.BF D.toPre (FractionRing R)).hom =
        (pullback.fst _ _ ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
      simp [DegPre.BF, TF]
    have hw : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom = (DegPre.BF D.toPre (FractionRing R)).hom :=
      Over.w _
    erw [hf', map_mul, app_toW, map_mul, toW_res, resTop_scal, toW_congr hw] at e
    have hu := isUnit_toW_of_K (pullback.fst _ _ ≫ jFK (R := R) (FractionRing R))
      (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) j₁ ⊓
        LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB α k) j₂) hr0
    rw [← toW_congr hBF] at hu
    have e2 := hu.mul_left_cancel e
    have h1 : resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) j₁ ⊓
        LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB α k) j₂)
        (1 : Γ((DegPre.BF D.toPre (FractionRing R)).left, ⊤)) = 1 := map_one _
    rw [h1, _root_.one_mul]
    exact e2
  have hv := terms_vanish hϖ hI F g' hgF
  have h0 := leading_expansion_term_ne_zero hI U s hs g' (hexp' 0) hv
  exact fun e => ⟨g', hexp' e, generates_of_ne hLaws hI (g' 0) h0⟩

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationAtUnit
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.ValuationAtUnit

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem exists_glue_ratio {Y : Scheme.{0}} {M : LB Y} (hc : ⨆ j, M.U j = ⊤) (s : LB.Sec M) (τ : LB.Gen M)
    (hτ : τ.IsGen) : ∃ a : Γ(Y, ⊤), ∀ j, s.f j = (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom a * (τ.s j).val := by
  let r : ∀ j, Γ(Y, M.U j) := fun j => s.f j * ((τ.s j)⁻¹ : Γ(Y, M.U j)ˣ).val
  have compat : ∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : M.U i ⊓ M.U j ≤ M.U i)).op).hom (r i) =
      (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom (r j) := by
    intro i j
    have hs := s.compat i j
    have hti : (Y.presheaf.map (homOfLE (inf_le_left : M.U i ⊓ M.U j ≤ M.U i)).op).hom ((τ.s i)⁻¹ : Γ(Y, M.U i)ˣ).val =
        (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom ((τ.s j)⁻¹ : Γ(Y, M.U j)ˣ).val *
          ((M.g i j)⁻¹ : Γ(Y, M.U i ⊓ M.U j)ˣ).val := by
      have := congrArg (fun u => (u⁻¹ : Γ(Y, M.U i ⊓ M.U j)ˣ).val) (hτ i j)
      simp only [mul_inv_rev, Units.val_mul] at this
      exact this
    have hg : (M.g i j : Γ(Y, M.U i ⊓ M.U j)ˣ).val * ((M.g i j)⁻¹ : Γ(Y, M.U i ⊓ M.U j)ˣ).val = 1 := by
      rw [← Units.val_mul, _root_.mul_inv_cancel, Units.val_one]
    simp only [r, map_mul]
    rw [hs, hti]
    linear_combination ((Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom (s.f j) *
      (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom ((τ.s j)⁻¹ : Γ(Y, M.U j)ˣ).val) * hg
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' M.U ⊤ (fun j => homOfLE le_top) hc.ge r compat
  have ha' : ∀ j, (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom a = r j := ha
  refine ⟨a, fun j => ?_⟩
  rw [ha' j]
  simp only [r]
  rw [_root_.mul_assoc, ← Units.val_mul, _root_.inv_mul_cancel, Units.val_one, _root_.mul_one]

end ReciprocityTheory.ChartRestriction.G.DVR.ValuationAtUnit
end
end

