module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordLambdaBilinearIntegralCombinations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExtensionSecPull
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2435
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2414

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoPullbackCommSquare
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.SquareIso

theorem lbIso_pull_further {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem iso_pull_of_square : ∀ {X Y Z Y' : Scheme.{0}} (LA' : LB X) (LA : LB Y) (L₁ : LB Z) (L₂ : LB Y') (ψ : X ⟶ Y) (φ₁ : Y ⟶ Z) (φ₂ : X ⟶ Y') (τ : Y' ⟶ Z), LA'.IsLB → LA.IsLB → L₁.IsLB → L₂.IsLB → ψ ≫ φ₁ = φ₂ ≫ τ → (∃ w : LB.Iso LA' (LA.pull ψ), w.IsGen) → (∃ w : LB.Iso LA (L₁.pull φ₁), w.IsGen) → LBIso L₂ (L₁.pull τ) → ∃ w : LB.Iso LA' (L₂.pull φ₂), w.IsGen := by
  intro X Y Z Y' LA' LA L₁ L₂ ψ φ₁ φ₂ τ hA' hA h₁ h₂ e w₁ w₂ w₃
  have a : LBIso (LA.pull ψ) (L₁.pull (φ₂ ≫ τ)) := lbIso_pull_further w₂ ψ e.symm
  have b : LBIso (L₂.pull φ₂) (L₁.pull (φ₂ ≫ τ)) := lbIso_pull_further w₃ φ₂ rfl
  exact LBIso.trans hA' (pull_isLB h₁ _) (pull_isLB h₂ _) (LBIso.trans hA' (pull_isLB hA _) (pull_isLB h₁ _) w₁ a) b.symm

end GlobalTheory.Poinc.SquareIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoPullbackOfCoprodJoin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.JoinPull

section Helpers

variable {X X₁ Z : Scheme.{0}} {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι}

theorem part_g_of_eq (h : IsPart N M e π) (ψ : Z ⟶ X₁) (χ : Z ⟶ X) (hχ : χ = ψ ≫ e) (z : Z) (i j : N.ι)
    (hi : ψ z ∈ M.U (π i)) (hj : ψ z ∈ M.U (π j)) :
    gm χ z (N.U i ⊓ N.U j) (N.g i j) = gm ψ z (M.U (π i) ⊓ M.U (π j)) (M.g (π i) (π j)) := by
  subst hχ; exact h.g _ ψ z i j hi hj

theorem part_g_eq_one (h : IsPart N M e π) (hM : M.IsLB) (ψ : Z ⟶ X₁) (χ : Z ⟶ X) (hχ : χ = ψ ≫ e) (z : Z)
    (i j : N.ι) (e₀ : π i = π j) (hi : ψ z ∈ M.U (π i)) : gm χ z (N.U i ⊓ N.U j) (N.g i j) = 1 := by
  rw [part_g_of_eq h ψ χ hχ z i j hi (e₀ ▸ hi)]
  have : ∀ b, π i = b → gm ψ z (M.U (π i) ⊓ M.U b) (M.g (π i) b) = 1 := by
    rintro _ rfl; exact gm_self hM _ z hi
  exact this _ e₀

end Helpers

theorem exists_iso_of_joinGen : ∀ {X₁ X₂ : Scheme.{0}} (M : LB X₁) (M' : LB X₂), M.IsLB → M'.IsLB → Nonempty X₁ → Nonempty X₂ → ∀ (F : X₂ ⟶ X₁) (t : LB.Gen (LB.LinComb (join M' M) (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl)) (Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ))))), t.IsGen → ∃ w : LB.Iso M' (M.pull F), w.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ X₂) (z : Z) (J : (Z ⟶ X₂ ⨿ X₁) → (join M' M).ι), Good (join M' M) z J → gw w f z (rr J (f ≫ F)) (rl J f) = val t f z J := by
  intro X₁ X₂ M M' hM hM' h₁ h₂ F t ht
  obtain ⟨i₀⟩ := @nonempty_idx _ _ hM h₁
  obtain ⟨k₀⟩ := @nonempty_idx _ _ hM' h₂
  have hl := isPart_inl M' M
  have hr := isPart_inr M' M
  have le : ∀ a : (PUnit.{1} → M.ι) × M'.ι, (LB.div (M.pull F) M').U a ≤
      LB.wchart (join M' M) (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl))
        (Sum.elim (fun _ => (k₀, a.1 PUnit.unit)) (fun _ => (a.2, i₀))) := fun a y hy =>
    Set.mem_iInter.2 fun k => by
      rcases k with u | u
      · exact (hr.mem (k₀, a.1 PUnit.unit) (F y)).2 (mem_pull.1 hy.1)
      · exact (hl.mem (a.2, i₀) y).2 hy.2
  let c : ChartPull (LB.div (M.pull F) M')
      (LB.LinComb (join M' M) (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl))
        (Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ)))) (𝟙 X₂) :=
    { idx := fun a => Sum.elim (fun _ => (k₀, a.1 PUnit.unit)) (fun _ => (a.2, i₀))
      le := le
      g := fun y a b ha hb => by
        refine (gm_div M' (M.pull F) (𝟙 X₂) y a b ⟨ha, hb⟩).trans ?_
        refine Eq.trans ?_ (gm_linComb (join M' M) _ _ (𝟙 X₂) y _ _ (le a ha) (le b hb)).symm
        rw [Fintype.prod_sum_type, Fintype.prod_unique, Fintype.prod_unique]
        exact congrArg₂ (· * ·)
          ((gm_pull_g M F (𝟙 X₂) y a.1 b.1 ha.1 hb.1).trans ((part_g_of_eq hr (𝟙 X₂ ≫ F) _
            (Category.assoc _ _ _).symm y (k₀, a.1 PUnit.unit) (k₀, b.1 PUnit.unit) (mem_pull.1 ha.1)
            (mem_pull.1 hb.1)).symm.trans (zpow_one _).symm))
          ((congrArg (·⁻¹) (part_g_of_eq hl (𝟙 X₂) _ rfl y (a.2, i₀) (b.2, i₀) ha.2 hb.2).symm).trans
            (zpow_neg_one _).symm) }
  refine ⟨cGen c t, cGen_isGen c ht, fun Z f z J hJ => ?_⟩
  have m : f z ∈ (LB.div (M.pull F) M').U (fun _ => rr J (f ≫ F), rl J f) :=
    ⟨mem_pull.2 (hr.good hJ (f ≫ F)), hl.good hJ f⟩
  have n := hJ.mem (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl)) f
  refine (gm_res f z _ m _).trans ((gen_trans ht f z (le _ m) n).trans ?_)
  have e₁ : trF (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl))
      (Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ))) f z
      (Sum.elim (fun _ => (k₀, rr J (f ≫ F))) (fun _ => (rl J f, i₀)))
      (fun k => J (f ≫ Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl) k)) = 1 := by
    rw [trF, Fintype.prod_sum_type, Fintype.prod_unique, Fintype.prod_unique]
    exact (congrArg₂ (· * ·)
      ((congrArg (· ^ _) (part_g_eq_one hr hM (f ≫ F) _ (Category.assoc _ _ _).symm z
        (k₀, rr J (f ≫ F)) (J (f ≫ F ≫ coprod.inr))
        (congrArg (fun q => (J q).2) (Category.assoc _ _ _)) (hr.good hJ (f ≫ F)))).trans (one_zpow _))
      ((congrArg (· ^ _) (part_g_eq_one hl hM' f _ rfl z (rl J f, i₀) (J (f ≫ coprod.inl)) rfl
        (hl.good hJ f))).trans (one_zpow _))).trans (mul_one 1)
  exact (congrArg (· * _) e₁).trans (one_mul _)

end GlobalTheory.JoinPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoRestrictAlongSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

noncomputable section

namespace GlobalTheory.IsoRes

variable {XG XT Pb : Scheme.{0}} {LG : LB XG} {LT : LB XT} {c : Pb ⟶ XG} {g : Pb ⟶ XT} {gi : XT ⟶ Pb}

theorem comp_pt {A B C : Scheme.{0}} (f : A ⟶ B) (h : B ⟶ C) (x : A) : (f ≫ h) x = h (f x) := by
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply]

theorem sec_apply (hgi : gi ≫ g = 𝟙 XT) (x : XT) : g (gi x) = x := by
  rw [← comp_pt, hgi]; rfl

theorem chart_le (hgi : gi ≫ g = 𝟙 XT) (J : PUnit → LG.ι) (k : LT.ι) :
    (LG.pull (gi ≫ c)).U J ⊓ LT.U k ≤ gi ⁻¹ᵁ ((LG.pull c).U J ⊓ (LT.pull g).U (fun _ => k)) := by
  intro x hx
  refine ⟨mem_pull.2 ?_, mem_pull.2 ?_⟩
  · have := mem_pull.1 hx.1
    rwa [comp_pt] at this
  · rw [sec_apply hgi]; exact hx.2

def resIso (hgi : gi ≫ g = 𝟙 XT) (w₀ : LB.Iso (LT.pull g) (LG.pull c)) : LB.Iso LT (LG.pull (gi ≫ c)) where
  s := fun p => res (chart_le hgi p.1 p.2) (pullU gi _ (w₀.s (p.1, fun _ => p.2)))

theorem gw_resIso (hgi : gi ≫ g = 𝟙 XT) (w₀ : LB.Iso (LT.pull g) (LG.pull c)) {Z : Scheme.{0}} (r : Z ⟶ XT) (z : Z)
    (j : LG.ι) (k : LT.ι) : gw (resIso hgi w₀) r z j k = gw w₀ (r ≫ gi) z j (fun _ => k) := by
  by_cases h : r z ∈ (LG.pull (gi ≫ c)).U (fun _ => j) ⊓ LT.U k
  · have h' : gi (r z) ∈ (LG.pull c).U (fun _ => j) ⊓ (LT.pull g).U (fun _ => k) := chart_le hgi _ _ h
    exact (gm_res r z _ h _).trans (gm_pull r gi z _ h' _)
  · have h' : ¬ (r ≫ gi) z ∈ (LG.pull c).U (fun _ => j) ⊓ (LT.pull g).U (fun _ => k) := by
      intro hm
      apply h
      rw [comp_pt] at hm
      refine ⟨mem_pull.2 ?_, ?_⟩
      · rw [comp_pt]; exact mem_pull.1 hm.1
      · have := mem_pull.1 hm.2
        rwa [sec_apply hgi] at this
    show gm r z _ _ = gm (r ≫ gi) z _ _
    rw [gm, gm, dite_eq_right h, dite_eq_right h']; rfl

theorem resIso_pgen (hgi : gi ≫ g = 𝟙 XT) (w₀ : LB.Iso (LT.pull g) (LG.pull c)) (hw₀ : PGen w₀) :
    PGen (resIso hgi w₀) := by
  intro Y f y j j' k k' hj hj' hk hk'
  rw [gw_resIso, gw_resIso]
  rw [comp_pt] at hj hj'
  have hj0 : c ((f ≫ gi) y) ∈ LG.U j := by rw [comp_pt]; exact hj
  have hj0' : c ((f ≫ gi) y) ∈ LG.U j' := by rw [comp_pt]; exact hj'
  have hk0 : (f ≫ gi) y ∈ (LT.pull g).U (fun _ => k) := mem_pull.2 (by rw [comp_pt, sec_apply hgi]; exact hk)
  have hk0' : (f ≫ gi) y ∈ (LT.pull g).U (fun _ => k') := mem_pull.2 (by rw [comp_pt, sec_apply hgi]; exact hk')
  have e := hw₀ Y (f ≫ gi) y j j' (fun _ => k) (fun _ => k') hj0 hj0' hk0 hk0'
  have e2 : gm (f ≫ gi) y ((LT.pull g).U (fun _ => k) ⊓ (LT.pull g).U (fun _ => k'))
      ((LT.pull g).g (fun _ => k) (fun _ => k')) = gm f y _ (LT.g k k') := by
    show gm (f ≫ gi) y _ (∏ _k : PUnit, (res _ (pullU g _ (LT.g k k'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    refine (gm_res (f ≫ gi) y _
      (show (f ≫ gi) y ∈ (LT.pull g).U (fun _ => k) ⊓ (LT.pull g).U (fun _ => k') from ⟨hk0, hk0'⟩) _).trans
      ((gm_pull (f ≫ gi) g y (LT.U k ⊓ LT.U k') ⟨mem_pull.1 hk0, mem_pull.1 hk0'⟩ _).trans ?_)
    rw [Category.assoc, hgi, Category.comp_id]
  rw [e, e2, Category.assoc]

theorem exists_iso_restrict : ∀ {XG XT Pb : Scheme.{0}} {LG : LB XG} {LT : LB XT} (hG : LG.IsLB) (hT : LT.IsLB) {c : Pb ⟶ XG} {g : Pb ⟶ XT} {gi : XT ⟶ Pb} (hgi : gi ≫ g = 𝟙 XT) (w₀ : LB.Iso (LT.pull g) (LG.pull c)) (hw₀ : w₀.IsGen), ∃ w : LB.Iso LT (LG.pull (gi ≫ c)), w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ XT) (z : Z) (j : LG.ι) (k : LT.ι), gw w r z j k = gw w₀ (r ≫ gi) z j (fun _ => k) := by
  intro XG XT Pb LG LT hG hT c g gi hgi w₀ hw₀
  exact ⟨resIso hgi w₀, (isGen_iff _).2 (resIso_pgen hgi w₀ ((isGen_iff _).1 hw₀)),
    fun Z r z j k => gw_resIso hgi w₀ r z j k⟩

end GlobalTheory.IsoRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivExtensionFieldBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.FieldBaseChange

def basisOfIsExtension {K F V W : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module F W] {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) {I : Type}
    (B : Module.Basis I K V) : Module.Basis I F W :=
  Module.Basis.mk (GlobalTheory.ConstFam.linearIndependent_of_isExtension ha B.linearIndependent) (by
    have h : Submodule.span K (Set.range B) ≤
        Submodule.comap a (Submodule.span F (Set.range fun i => a (B i))) :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨i, rfl⟩)
    rw [← ha.span, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span K (Set.range B) := B.span_eq ▸ Submodule.mem_top
    exact h hv)

theorem basisOfIsExtension_apply {K F V W : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module F W] {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) {I : Type}
    (B : Module.Basis I K V) (i : I) : basisOfIsExtension ha B i = a (B i) := by
  simp [basisOfIsExtension]

theorem exists_bijective_extension : ∀ (K F V V' W W' : Type) [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] [AddCommGroup W] [Module F W] [AddCommGroup W'] [Module F W'] (a : V →ₛₗ[algebraMap K F] W) (d : V' →ₛₗ[algebraMap K F] W'), GlobalTheory.FieldBaseChange.IsExtension a → GlobalTheory.FieldBaseChange.IsExtension d → ∀ e : V →ₗ[K] V', Function.Bijective e → ∃ e' : W →ₗ[F] W', Function.Bijective e' ∧ ∀ v, e' (a v) = d (e v) := by
  intro K F V V' W W' _ _ _ _ _ _ _ _ _ _ _ a d ha hd e he
  let B := Module.Basis.ofVectorSpace K V
  let B' := B.map (LinearEquiv.ofBijective e he)
  let C := basisOfIsExtension ha B
  let C' := basisOfIsExtension hd B'
  let E := C.equiv C' (Equiv.refl _)
  refine ⟨E.toLinearMap, E.bijective, fun v => ?_⟩
  have key : (E.toLinearMap.comp a : V →ₛₗ[algebraMap K F] W') = d.comp e := B.ext fun i => by
    have h1 : a (B i) = C i := (basisOfIsExtension_apply ha B i).symm
    have h2 : d (e (B i)) = C' i := by
      rw [basisOfIsExtension_apply hd B' i]; simp [B']
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1, h2, E, Module.Basis.equiv_apply, Equiv.refl_apply]
  exact LinearMap.congr_fun key v

end GlobalTheory.FieldBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalOfSymmetricMultiadditive
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.PolForm

def expv {ι : Type} {n : ℕ} (c : Fin n → ι) : ι →₀ ℕ := ∑ a, Finsupp.single (c a) 1

theorem prod_X_eq {ι : Type} {n : ℕ} (c : Fin n → ι) :
    (∏ a, X (c a) : MvPolynomial ι ℝ) = monomial (expv c) 1 := by
  rw [expv, monomial_sum_one]; rfl

theorem expv_apply {ι : Type} [DecidableEq ι] {n : ℕ} (c : Fin n → ι) (i : ι) :
    expv c i = Fintype.card {a // c a = i} := by
  rw [expv, Finsupp.finsetSum_apply, Fintype.card_subtype]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_boole]
  simp

theorem weight_expv {ι : Type} {n : ℕ} (c : Fin n → ι) : Finsupp.weight 1 (expv c) = n := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [expv, map_sum, Finsupp.weight_apply, Finsupp.sum_single_index]

theorem exists_perm_of_expv_eq {ι : Type} {n : ℕ} {c c' : Fin n → ι} (h : expv c = expv c') :
    ∃ e : Equiv.Perm (Fin n), ∀ a, c' a = c (e a) := by
  classical
  have hc : ∀ i, Fintype.card {a // c' a = i} = Fintype.card {a // c a = i} := fun i => by
    have := congrArg (fun s => s i) h
    simp only [expv_apply] at this
    convert this.symm
  let E : ∀ i, {a // c' a = i} ≃ {a // c a = i} := fun i => Fintype.equivOfCardEq (hc i)
  refine ⟨(Equiv.sigmaFiberEquiv c').symm.trans ((Equiv.sigmaCongrRight E).trans (Equiv.sigmaFiberEquiv c)),
    fun a => ?_⟩
  show c' a = c (E (c' a) ⟨a, rfl⟩).1
  exact (E (c' a) ⟨a, rfl⟩).2.symm

end GlobalTheory.MixHt.PolForm

namespace GlobalTheory.MixHt


open _root_.GlobalTheory.MixHt.PolForm _root_.GlobalTheory.MixHt.PolForm in
theorem exists_linear_of_multiadditive : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (d : ℕ) (F : (Fin (d + 1) → HermLB p) → ℝ), (∀ L M, (∀ a, (L a).Isometric (M a)) → F L = F M) → (∀ L (e : Equiv.Perm (Fin (d + 1))), F (fun a => L (e a)) = F L) → (∀ (A B : HermLB p) (L : Fin d → HermLB p), F (Fin.cons (A.tens B) L) = F (Fin.cons A L) + F (Fin.cons B L)) → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), ∃ Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, (∀ n : Fin (d + 1) → ι → ℤ, Φ (∏ a, lin fun i => (n a i : ℝ)) = F fun a => comb L (n a)) ∧ ∀ (P : MvPolynomial ι ℝ) (e : ℕ), e ≠ d + 1 → P.IsHomogeneous e → Φ P = 0 := by
  intro k _ X p d F hiso hsymm hadd ι _ L
  classical
  let rep : HermLB.IsomClass p → HermLB p := fun x => Quotient.out (s := HermLB.isometrySetoid p) x
  have hrepcls : ∀ x, (rep x).icls = x := fun x => Quotient.out_eq (s := HermLB.isometrySetoid p) x
  let G' : (Fin (d + 1) → HermLB.IsomClass p) → ℝ := fun v => F fun a => rep (v a)
  have hG : ∀ M : Fin (d + 1) → HermLB p, G' (fun a => (M a).icls) = F M :=
    fun M => hiso _ _ fun a => HermLB.icls_eq_iff.1 (hrepcls _)
  have hGs : ∀ v (e : Equiv.Perm (Fin (d + 1))), G' (fun a => v (e a)) = G' v :=
    fun v e => hsymm (fun a => rep (v a)) e
  have hG0 : ∀ (x y : HermLB.IsomClass p) (w : Fin d → HermLB.IsomClass p),
      G' (Fin.cons (x + y) w) = G' (Fin.cons x w) + G' (Fin.cons y w) := by
    intro x y w
    have hc : ∀ z, (fun a => rep ((Fin.cons z w : Fin (d + 1) → HermLB.IsomClass p) a)) =
        Fin.cons (rep z) (fun a => rep (w a)) := fun z => by
      funext a; exact Fin.cases rfl (fun _ => rfl) a
    show F (fun a => rep ((Fin.cons (x + y) w : Fin (d + 1) → HermLB.IsomClass p) a)) =
      F (fun a => rep ((Fin.cons x w : Fin (d + 1) → HermLB.IsomClass p) a)) +
        F (fun a => rep ((Fin.cons y w : Fin (d + 1) → HermLB.IsomClass p) a))
    rw [hc, hc, hc, ← hadd]
    refine hiso _ _ fun a => Fin.cases ?_ (fun b => ?_) a
    · simp only [Fin.cons_zero]
      exact HermLB.icls_eq_iff.1 (by rw [HermLB.icls_tens, hrepcls, hrepcls, hrepcls])
    · simp only [Fin.cons_succ]; exact HermLB.Isometric.refl _
  have h0 : ∀ (q : Fin (d + 1) → HermLB.IsomClass p) (x y : HermLB.IsomClass p),
      G' (Function.update q 0 (x + y)) = G' (Function.update q 0 x) + G' (Function.update q 0 y) := by
    intro q x y
    rw [← Fin.cons_self_tail q, Fin.update_cons_zero, Fin.update_cons_zero, Fin.update_cons_zero]
    exact hG0 x y _
  have hGi : ∀ (m : Fin (d + 1) → HermLB.IsomClass p) (i : Fin (d + 1)) (x y : HermLB.IsomClass p),
      G' (Function.update m i (x + y)) = G' (Function.update m i x) + G' (Function.update m i y) := by
    intro m i x y
    have key : ∀ z, G' (Function.update m i z) = G' (Function.update (m ∘ Equiv.swap 0 i) 0 z) := fun z => by
      rw [← hGs (Function.update m i z) (Equiv.swap 0 i)]
      show G' (Function.update m i z ∘ Equiv.swap 0 i) = _
      rw [Function.update_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_right]
    rw [key, key, key]
    exact h0 _ x y
  let Mlt : MultilinearMap (RingHom.id ℤ) (fun _ : Fin (d + 1) => HermLB.IsomClass p) ℝ :=
    { toFun := G'
      map_update_add' := by
        intro inst m i x y
        obtain rfl : inst = instDecidableEqFin _ := Subsingleton.elim _ _
        exact hGi m i x y
      map_update_smul' := by
        intro inst m i c x
        obtain rfl : inst = instDecidableEqFin _ := Subsingleton.elim _ _
        exact map_zsmul (AddMonoidHom.mk' (fun z => G' (Function.update m i z)) (hGi m i)) c x }
  let g : ι → HermLB.IsomClass p := fun i => (L i).icls
  let f : (Fin (d + 1) → ι) → ℝ := fun c => G' fun a => g (c a)
  have hf : ∀ c (e : Equiv.Perm (Fin (d + 1))), f (fun a => c (e a)) = f c := fun c e => hGs (fun a => g (c a)) e
  have hF : ∀ n : Fin (d + 1) → ι → ℤ, F (fun a => comb L (n a)) =
      ∑ c : Fin (d + 1) → ι, (∏ a, (n a (c a) : ℝ)) * f c := by
    intro n
    rw [← hG]
    simp only [icls_comb]
    have e1 := Mlt.map_sum (fun a i => n a i • g i)
    have e2 : ∀ c : Fin (d + 1) → ι, Mlt (fun a => n a (c a) • g (c a)) = (∏ a, (n a (c a) : ℝ)) * f c := by
      intro c
      rw [Mlt.map_smul_univ (fun a => n a (c a)) (fun a => g (c a)), zsmul_eq_mul, Int.cast_prod]
      rfl
    simp only [e2] at e1
    exact e1
  let φ : (ι →₀ ℕ) → ℝ := fun s => if h : ∃ c : Fin (d + 1) → ι, expv c = s then f h.choose else 0
  have hφ : ∀ c, φ (expv c) = f c := by
    intro c
    have h : ∃ c' : Fin (d + 1) → ι, expv c' = expv c := ⟨c, rfl⟩
    simp only [φ, dif_pos h]
    obtain ⟨e, he⟩ := exists_perm_of_expv_eq h.choose_spec
    rw [← hf h.choose e]
    exact congrArg f (funext fun a => (he a).symm)
  let Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ := (basisMonomials ι ℝ).constr ℝ φ
  have hΦ : ∀ s, Φ (monomial s 1) = φ s := by
    intro s
    have := (basisMonomials ι ℝ).constr_basis ℝ φ s
    rwa [coe_basisMonomials] at this
  refine ⟨Φ, fun n => ?_, fun P e he hP => ?_⟩
  · rw [hF]
    simp only [lin]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.prod_mul_distrib, ← map_prod, prod_X_eq, C_mul', map_smul, hΦ, hφ, smul_eq_mul]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [P.as_sum, map_sum]
    refine Finset.sum_eq_zero fun s hs => ?_
    have hm : monomial s (AddMonoidAlgebra.coeff P s) = AddMonoidAlgebra.coeff P s • monomial s (1 : ℝ) := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hm, map_smul, hΦ, smul_eq_mul]
    refine mul_eq_zero_of_right _ (dif_neg ?_)
    rintro ⟨c, rfl⟩
    have := hP (mem_support_iff.1 hs)
    rw [weight_expv] at this
    exact he this.symm

end GlobalTheory.MixHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearMapThetaGroupActionSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

noncomputable section

namespace GlobalTheory.Mum.Desc

open GlobalTheory.FieldBaseChange

theorem exists_linear_isActOf : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), ∃ b : SecF A F N →ₗ[F] SecF A F N, ∀ t t' : SecF A F N, IsActOf A.A A.L N θ t t' ↔ t' = b t := by
  intro R _ _ A F _ _ N θ
  have hex : ∀ t : SecF A F N, ∃ u : SecF A F N, IsActOf A.A A.L N θ t u :=
    fun t => GlobalTheory.VVCompare.exists_isActOf A.A A.isLB θ t
  choose Θ hΘ using hex
  have hb : (translT A.A θ.pt).left ≫ (fst (TFK (R := R) F) A.A).left = (fst (TFK (R := R) F) A.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : translT A.A θ.pt ≫ fst _ _ = _)
  have hv := fun (t u : SecF A F N) (h : IsActOf A.A A.L N θ t u) y J hJ =>
    GlobalTheory.VVCompare.sv_of_isTwistPull A.A h (𝟙 _) y (J := J) hJ
  refine ⟨⟨⟨Θ, fun s s' => sec_ext' A.isLB fun y J hJ => ?_⟩,
    fun c s => sec_ext' A.isLB fun y J hJ => ?_⟩, fun t t' => ⟨fun h => sec_ext' A.isLB fun y J hJ => ?_, ?_⟩⟩
  · refine (hv _ _ (hΘ _) y J hJ).trans ?_
    refine Eq.symm ((sval_add' hJ _ _ _).trans (Eq.trans ?_ (congrArg _ (sval_add' hJ _ s s')).symm))
    exact (congrArg₂ (· + ·) (hv _ _ (hΘ s) y J hJ) (hv _ _ (hΘ s') y J hJ)).trans (mul_add _ _ _).symm
  · refine (hv _ _ (hΘ _) y J hJ).trans ?_
    refine Eq.symm ((sval_smul' hJ _ _ _).trans (Eq.trans ?_ (congrArg _ (sval_smul' hJ _ c s)).symm))
    rw [Category.assoc, hb]
    exact (congrArg _ (hv _ _ (hΘ s) y J hJ)).trans (mul_left_comm _ _ _)
  · exact (hv _ _ h y J hJ).trans (hv _ _ (hΘ t) y J hJ).symm
  · rintro rfl
    exact hΘ t

end GlobalTheory.Mum.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultiplicationPullbackGenericSectionCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multiplicationPullback_genericSection_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ θ₀ : SecK C.P.L.L C.α 1, ∃ S : SecK C.P.L.L C.α (m ^ 2), MulSecK C m θ₀ S := by
  first | exact @GlobalTheory.Mum.exists_mulSecK | exact GlobalTheory.Mum.exists_mulSecK | (intros; apply GlobalTheory.Mum.exists_mulSecK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatTransLiftsOverAffinePairs
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem exists_lift_pair_natTrans (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R)
    (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ)
    (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (hi : φ₀ ≫ D.i = D'.i ≫ φ) :
    ∃ θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G, ∀ (p : (Pair φ)ᵒᵖ) a,
      (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
        Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a) := by
  choose θ hθ using GlobalTheory.T.exists_smoothLift_hom_affinePair D D' Λ Λ' σ φ φ₀ hφ m hi
  refine ⟨⟨fun p ↦ θ p.unop, fun p q a ↦ ?_⟩, fun p a ↦ hθ p.unop a⟩
  apply Thick.Hom.ext'
  apply AlgHom.ext
  intro b
  obtain ⟨x, rfl⟩ := (Λ.e (Opposite.op p.unop.1.2)).surjective b
  have h1 := Λ.nat ((pairSnd φ).map a) x
  have h2 := hθ q.unop (mp (OAff D.s) ((pairSnd φ).map a) x)
  have h3 := hθ p.unop x
  have h4 := Λ'.nat ((pairFst φ).map a) (GlobalTheory.CechDR.secPull D.s D'.s p.unop x)
  have h5 := (pairPull hφ).naturality a x
  exact ((congrArg (θ q.unop).φ h1.symm).trans h2).trans
    ((congrArg (Λ'.e (Opposite.op q.unop.1.1)) h5).trans
      (h4.trans (congrArg (Λ'.L.map ((pairFst φ).map a)).φ h3.symm)))

end GlobalTheory.PDForm
end

