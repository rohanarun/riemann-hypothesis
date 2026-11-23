module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2054
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2622
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2714
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2492
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2659
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesVanishingNoetherianAbelian
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh.AxesSq

theorem surj_of_comp {R R' : Type} [CommRing R] [CommRing R'] {X X' X₀ : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R}
    {s₀ : X₀ ⟶ Sp R'} {σ : R →+* R'} (e : X ⟶ X') (ψ : X₀ ⟶ X)
    (he : e ≫ s' = s ≫ spMap (RingHom.id R)) (hψ : ψ ≫ s = s₀ ≫ spMap σ) (hc : (ψ ≫ e) ≫ s' = s₀ ≫ spMap σ) :
    (Function.Surjective (pullHO1 hc) → Function.Surjective (pullHO1 hψ)) ∧
    (Function.Surjective (pullHO2 hc) → Function.Surjective (pullHO2 hψ)) := by
  have H := (_root_.GlobalTheory.AbCoh.pull_comp_cup_id.1 R R X' X s' s (RingHom.id R) e he R' X₀ s₀ σ ψ hψ σ (ψ ≫ e) hc rfl (fun _ ↦ rfl))
  refine ⟨fun h y ↦ ?_, fun h y ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := h y
    exact ⟨pullHO1 he a, H.1 a⟩
  · obtain ⟨a, rfl⟩ := h y
    exact ⟨pullHO2 he a, H.2.1 a⟩

theorem fp_bc1 (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom)) ∧ StructureSheafH1BaseChange A.hom := by
  haveI : Smooth A.hom := hA.smooth
  haveI : IsProper A.hom := hA.proper
  obtain ⟨h1, -, h3, -⟩ := _root_.GlobalTheory.AbCoh.CohBaseChange.main R A.left A.hom inferInstance inferInstance (_root_.GlobalTheory.AbCoh.uConst_of_isAbelianScheme R A hA)
    (by
      intro R' _ _ _ _ k _ _ α hα X' s' φ X₀ s₀ ψ hφ w
      obtain ⟨B, _, pr, -, hB, hBg, hpb, -⟩ := _root_.GlobalTheory.AbBaseChangeSq.exists_baseChange_and_sq R R' A g hA hg
      let e : B.left ≅ X' := IsPullback.isoIsPullback _ _ hpb hφ
      have he2 : e.hom ≫ s' = B.hom := IsPullback.isoIsPullback_hom_snd A.left (Sp R') hpb hφ
      have he : e.inv ≫ B.hom = s' ≫ spMap (RingHom.id R') := by
        rw [← he2, Iso.inv_hom_id_assoc]
        first | (rw [spMap_id, Category.comp_id]) | (simp [spMap, CommRingCat.ofHom_id]) | (rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id])
      have w' : IsPullback (ψ ≫ e.inv) s₀ B.hom (spMap (α : R' →+* k)) := by
        refine IsPullback.of_iso w (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp [← he2]
      obtain ⟨s1, s2⟩ := _root_.GlobalTheory.AbCoh.artinian_pullHO_surjective R' B g hB hBg k α hα X₀ s₀ (ψ ≫ e.inv) w'
      have hc := surj_of_comp (s := s') (s' := B.hom) e.inv ψ he w.w w'.w
      exact ⟨hc.1 s1, hc.2 s2⟩)
  exact ⟨h1, h3⟩

theorem pull1_congr {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'}
    {σ : R →+* R'} {φ₁ φ₂ : X' ⟶ X} (hφ : φ₁ = φ₂) (h₁ : φ₁ ≫ s = s' ≫ spMap σ) (h₂ : φ₂ ≫ s = s' ≫ spMap σ)
    (c : HO1 s) : pullHO1 h₁ c = pullHO1 h₂ c := by
  subst hφ; rfl

def axesMap {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] :
    HO1 (A ⊗ A).hom →ₗ[R] HO1 A.hom × HO1 A.hom :=
  LinearMap.prod (pO1 (lift (𝟙 A) (toUnit A ≫ η[A]))) (pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)))

theorem pO1_bc {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {A Y : Over (Sp R)} {B Z : Over (Sp K)}
    (f : Y ⟶ A) (f' : Z ⟶ B) (pr : Z.left ⟶ Y.left) (pr' : B.left ⟶ A.left)
    (hpb : pr ≫ Y.hom = Z.hom ≫ spMap (algebraMap R K)) (hpb' : pr' ≫ A.hom = B.hom ≫ spMap (algebraMap R K))
    (hc : f'.left ≫ pr' = pr ≫ f.left) (c : HO1 A.hom) :
    pO1 f' (pullHO1 hpb' c) = pullHO1 hpb (pO1 f c) := by
  have h1 : (f'.left ≫ pr') ≫ A.hom = Z.hom ≫ spMap (algebraMap R K) := by
    rw [Category.assoc, hpb', ← Category.assoc, Over.w]
  have h2 : (pr ≫ f.left) ≫ A.hom = Z.hom ≫ spMap (algebraMap R K) := by rw [← hc]; exact h1
  have E1 := (_root_.GlobalTheory.AbCoh.pull_comp_cup_id.1 R K A.left B.left A.hom B.hom (algebraMap R K) pr' hpb' K Z.left Z.hom (RingHom.id K)
    f'.left (ovw f') (algebraMap R K) (f'.left ≫ pr') h1 rfl (fun _ ↦ rfl)).1 c
  have E2 := (_root_.GlobalTheory.AbCoh.pull_comp_cup_id.1 R R A.left Y.left A.hom Y.hom (RingHom.id R) f.left (ovw f) K Z.left Z.hom (algebraMap R K)
    pr hpb (algebraMap R K) (pr ≫ f.left) h2 rfl (fun _ ↦ rfl)).1 c
  unfold pO1
  rw [E1, E2]
  exact pull1_congr hc h1 h2 c

theorem axesMap_baseChange_injective (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A]
    (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (K : Type) [Field K] [IsAlgClosed K] [Algebra R K] :
    Function.Injective ((axesMap A).baseChange K) := by
  obtain ⟨hsq, hsqg⟩ := (GlobalTheory.Obs.sq_abelian_and_affine_H1 R).1 A g hA hg
  obtain ⟨B, _, pr, pr', hB, hBg, hpb, hpb', -, -, -, h1, h2⟩ := _root_.GlobalTheory.AbBaseChangeSq.exists_baseChange_and_sq R K A g hA hg
  obtain ⟨eS, heS⟩ := (fp_bc1 R (A ⊗ A) (g + g) hsq hsqg).2 K _ _ pr' hpb'
  obtain ⟨eA, heA⟩ := (fp_bc1 R A g hA hg).2 K _ _ pr hpb
  have key : ∀ (f : A ⟶ A ⊗ A) (f' : B ⟶ B ⊗ B), f'.left ≫ pr' = pr ≫ f.left →
      ∀ z, pO1 f' (eS z) = eA ((pO1 f).baseChange K z) := by
    intro f f' hc z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c =>
      have : a ⊗ₜ[R] c = a • ((1 : K) ⊗ₜ[R] c) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [this, map_smul, map_smul, map_smul, LinearMap.baseChange_tmul, map_smul, heS, heA]
      congr 1
      exact pO1_bc f f' pr pr' hpb.w hpb'.w hc c
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  obtain ⟨-, -, -, -, hax⟩ := _root_.GlobalTheory.AbCoh.structureSheafCoh_abelianVariety_algClosed K B g hB hBg
  intro z z' hzz
  rw [← sub_eq_zero] at hzz ⊢
  rw [← map_sub] at hzz
  generalize z - z' = w at hzz ⊢
  have hfst : (pO1 (lift (𝟙 A) (toUnit A ≫ η[A]))).baseChange K w = 0 := by
    have := congrArg ((LinearMap.fst R (HO1 A.hom) (HO1 A.hom)).baseChange K) hzz
    rwa [map_zero, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp] at this
  have hsnd : (pO1 (lift (toUnit A ≫ η[A]) (𝟙 A))).baseChange K w = 0 := by
    have := congrArg ((LinearMap.snd R (HO1 A.hom) (HO1 A.hom)).baseChange K) hzz
    rwa [map_zero, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp] at this
  have e0 : eS w = 0 := by
    apply hax
    · have k1 := key (lift (𝟙 A) (toUnit A ≫ η[A])) (lift (𝟙 B) (toUnit B ≫ η[B])) h1 w
      rw [k1, hfst, map_zero]
    · have k2 := key (lift (toUnit A ≫ η[A]) (𝟙 A)) (lift (toUnit B ≫ η[B]) (𝟙 B)) h2 w
      rw [k2, hsnd, map_zero]
  simpa using congrArg eS.symm e0

theorem axesO1_of_isAbelianScheme : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → AxesVanishingStructureSheafDegOne A := by
  intro R _ _ A _ g hA hg
  obtain ⟨hsq, hsqg⟩ := (GlobalTheory.Obs.sq_abelian_and_affine_H1 R).1 A g hA hg
  obtain ⟨⟨hS1, hS2⟩, -⟩ := fp_bc1 R (A ⊗ A) (g + g) hsq hsqg
  obtain ⟨⟨hA1, hA2⟩, -⟩ := fp_bc1 R A g hA hg
  let e1 : ULift.{1} (HO1 (A ⊗ A).hom) ≃ₗ[R] HO1 (A ⊗ A).hom := ULift.moduleEquiv
  let e2 : ULift.{1} (HO1 A.hom × HO1 A.hom) ≃ₗ[R] HO1 A.hom × HO1 A.hom := ULift.moduleEquiv
  let f : ULift.{1} (HO1 (A ⊗ A).hom) →ₗ[R] ULift.{1} (HO1 A.hom × HO1 A.hom) :=
    e2.symm.toLinearMap ∘ₗ axesMap A ∘ₗ e1.toLinearMap
  haveI : Module.Finite R (ULift.{1} (HO1 (A ⊗ A).hom)) := Module.Finite.equiv e1.symm
  haveI : Module.Projective R (ULift.{1} (HO1 (A ⊗ A).hom)) := Module.Projective.of_equiv e1.symm
  haveI : Module.Finite R (ULift.{1} (HO1 A.hom × HO1 A.hom)) := Module.Finite.equiv e2.symm
  haveI : Module.Projective R (ULift.{1} (HO1 A.hom × HO1 A.hom)) := Module.Projective.of_equiv e2.symm
  obtain ⟨r, hr⟩ := GlobalTheory.split_injective_of_forall_prime_baseChange_field_injective R _ _ f (by
    intro P
    refine ⟨AlgebraicClosure P.asIdeal.ResidueField, inferInstance, inferInstance, ?_, ?_⟩
    · have hk : RingHom.ker (algebraMap P.asIdeal.ResidueField (AlgebraicClosure P.asIdeal.ResidueField)) = ⊥ :=
        (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap P.asIdeal.ResidueField _).injective
      rw [IsScalarTower.algebraMap_eq R P.asIdeal.ResidueField (AlgebraicClosure P.asIdeal.ResidueField),
        ← RingHom.comap_ker, hk]
      exact Ideal.ker_algebraMap_residueField _
    · have hi := axesMap_baseChange_injective R A g hA hg (AlgebraicClosure P.asIdeal.ResidueField)
      simp only [f, LinearMap.baseChange_comp]
      exact (e2.symm.baseChange R _ _ _).injective.comp (hi.comp (e1.baseChange R _ _ _).injective))
  have hf : Function.Injective f := fun x y hxy ↦ by
    have := congrArg r hxy
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, hr, LinearMap.id_apply, LinearMap.id_apply] at this
  intro y hy1 hy2
  have h0 : f (e1.symm y) = f 0 := by
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, map_zero]
    simp [axesMap, hy1, hy2]
  simpa using congrArg e1 (hf h0)

end GlobalTheory.AbCoh.AxesSq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalIsoHodgeFiltrationEqRangeInvariantFormsStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_iso_hodge_filtration_eq_range_invariant_forms : ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (L : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), Function.Surjective L → (∀ c, IsCan t c (L c)) → (PrimitiveSubmodule A).map L = LinearMap.range G.rigOfOmega := by
  first | exact @GlobalTheory.PtExt.map_F1prim_eq_range_rigOfOmega | exact GlobalTheory.PtExt.map_F1prim_eq_range_rigOfOmega | (intros; apply GlobalTheory.PtExt.map_F1prim_eq_range_rigOfOmega <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormFieldDbarCohomologousTwoConnections
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem dbarCoh_chernFld : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r]
    [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ j, DbarCoh A (chernFld A G j) (chernFld A G' j) := by
  intro M _ n A r _ _ G G' hG j
  obtain ⟨h1, -, halg⟩ := _root_.GlobalTheory.ChernCalc.dbarCoh_algebra M n A
  have hpow := _root_.GlobalTheory.ChernCalc.PowCoh.dbarCoh_powFld M n A r G G' hG
  have hzero : DbarCoh A 0 0 := by
    have := (halg 0 1 1 1 1 h1 h1).1
    simpa using this
  have hsum : ∀ (s : Finset ℕ) (w w' : ℕ → A.Pt → Ev n), (∀ i ∈ s, DbarCoh A (w i) (w' i)) →
      DbarCoh A (∑ i ∈ s, w i) (∑ i ∈ s, w' i) := by
    intro s w w' h
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (halg 0 _ _ _ _ (h a (Finset.mem_insert_self _ _))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).2.1
  have key : ∀ (H : M → M → Matrix r r ℂ) (j : ℕ), 0 < j → chernFld A H j = (j : ℂ)⁻¹ • ((-1 : ℂ) •
      ∑ i ∈ Finset.range j, (-kappa) ^ (i + 1) • (powFld A H (i + 1) * chernFld A H (j - 1 - i))) := by
    intro H j hj
    funext x
    have := (_root_.GlobalTheory.ChernCalc.chernAt_newton n r (fun v => H x.pt (x.ch.symm v)) x.crd).2 j
    simp only [Pi.smul_apply, Finset.sum_apply, Pi.mul_apply, chernFld, powFld, HolAtlas.chern]
    rw [neg_one_smul, ← this, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hj.ne'), one_smul]
  have key0 : ∀ H : M → M → Matrix r r ℂ, chernFld A H 0 = 1 := by
    intro H; funext x
    exact (_root_.GlobalTheory.ChernCalc.chernAt_newton n r _ x.crd).1
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [key0, key0]; exact h1
    · rw [key G j hj, key G' j hj]
      refine (halg _ _ _ _ _ ?_ h1).1
      refine (halg _ _ _ _ _ ?_ h1).1
      refine hsum _ _ _ fun i hi => ?_
      refine (halg _ _ _ _ _ ?_ h1).1
      exact (halg 0 _ _ _ _ (hpow (i + 1)) (ih _ (by simp at hi; omega))).2.2

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationOfMarkedPeriodsFamily
section
noncomputable section

namespace GlobalTheory.PELU

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem isPeriod_comp_isometry_symm {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    (D D' : PLat O bar) (w : D.La ≃ₗ[O] D'.La) (hw : IsIsom D D' w) (P : D.La →+ (Fin g → ℂ))
    (hP : IsPeriod D ρ P) : IsPeriod D' ρ (P.comp w.symm.toLinearMap.toAddMonoidHom) := by
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, him⟩ := hP
  have hrange : (P.comp w.symm.toLinearMap.toAddMonoidHom).range = P.range := by
    ext v
    simp only [AddMonoidHom.mem_range, AddMonoidHom.comp_apply]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨w x, by simp⟩
  have hrange' : Set.range (P.comp w.symm.toLinearMap.toAddMonoidHom) = Set.range P := by
    have := congrArg (fun S : AddSubgroup (Fin g → ℂ) => (S : Set (Fin g → ℂ))) hrange
    simpa [AddMonoidHom.coe_range] using this
  refine ⟨fun a x => ?_, ?_, ?_, ?_, Hm, hH, hpos, fun x y => ?_⟩
  · simp [hlin]
  · intro x y hxy
    have := hinj hxy
    simpa using this
  · rw [hrange]; exact hdisc
  · rw [hrange']; exact hspan
  · have := hw (w.symm x) (w.symm y)
    simp only [LinearEquiv.apply_symm_apply] at this
    simp [him, this]

theorem unif_of_fineAt : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type)
    (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ), 3 ≤ N → (∀ a, F.eta a ^ N = 1) →
    SmoothOfRelativeDimension d F.s → QuasiCompact F.s → (∀ D' t, C D' t → FullMark N D' t) →
    FineAt F (RingHom.id ℂ) ρ N C → Nonempty (Unif F (RingHom.id ℂ) ρ N C) := by
  intro O _ bar g ρ Λ F N C d hN heta hsm hqc hfull hF
  have hN0 : 0 < N := by omega
  have hlft : LocallyOfFiniteType F.s := by
    haveI := hsm
    haveI : Smooth F.s := SmoothOfRelativeDimension.smooth d F.s
    infer_instance
  obtain ⟨n, Di, t, hmem, hall, hdist⟩ := _root_.GlobalTheory.PELU.exists_finite_representatives O bar g ρ Λ F N C d hN0 heta hsm hqc hF
  have hQ : ∀ i (P : (Di i).La →+ (Fin g → ℂ)), ∃ Q, IsPeriod (Di i) ρ Q ∧ (IsPeriod (Di i) ρ P → Q = P) := by
    intro i P
    by_cases hP : IsPeriod (Di i) ρ P
    · exact ⟨P, hP, fun _ => rfl⟩
    · obtain ⟨Q, hQ⟩ := (hmem i).2
      exact ⟨Q, hQ, fun h => absurd h hP⟩
  choose Q hQp hQe using hQ
  have hex : ∀ i P, ∃ y e, UnifAt F (RingHom.id ℂ) ρ N (Di i) (t i) (Q i P) y e :=
    fun i P => hF.occ _ _ _ (hmem i).1 (hQp i P)
  choose u ex hu using hex
  have hunif : ∀ i P, IsPeriod (Di i) ρ P → UnifAt F (RingHom.id ℂ) ρ N (Di i) (t i) P (u i P) (ex i P) := by
    intro i P hP
    have := hu i P
    rwa [hQe i P hP] at this
  have hrefl : ∀ i, IsMarkedIsom N (Di i) (Di i) (t i) (t i) (LinearEquiv.refl O _) :=
    fun i => ⟨fun x y => rfl, fun a => ⟨0, by simp⟩⟩
  have cmpEq : ∀ (D' D'' : PLat O bar) (t' : Λ → D'.La) (t'' : Λ → D''.La) (P : D'.La →+ (Fin g → ℂ))
      (P' : D''.La →+ (Fin g → ℂ)) (y y' : Sp ℂ ⟶ F.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ F.A))
      (e' : (Fin g → ℂ) → (Over.mk y' ⟶ F.A)), y = y' →
      UnifAt F (RingHom.id ℂ) ρ N D' t' P y e → UnifAt F (RingHom.id ℂ) ρ N D'' t'' P' y' e' →
      ∃ (w : D'.La ≃ₗ[O] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
        IsMarkedIsom N D' D'' t' t'' w ∧ ∀ x, P' (w x) = h (P x) := by
    intro D' D'' t' t'' P P' y y' e e' hy h1 h2
    subst hy
    obtain ⟨w, h, hw, hP, -⟩ := _root_.GlobalTheory.PELU.unifAt_cmp O bar g ρ ℂ (RingHom.id ℂ) Λ F N D' D'' t' t'' P P' y e e' hN0 h1 h2
    exact ⟨w, h, hw, hP⟩
  refine ⟨{
      n := n
      Di := Di
      t := t
      mem := fun i => (hmem i).1
      ne := fun i => (hmem i).2
      all := hall
      distinct := hdist
      u := u
      ex := ex
      unif := hunif
      onto := ?_
      disj := ?_
      fibre := ?_
      hol := ?_
      lift := ?_ }⟩
  · intro y hy
    obtain ⟨D', t', P, e, hC, hU⟩ := hF.pts y hy
    obtain ⟨i, w, hw⟩ := hall D' t' hC ⟨P, hU.2.1⟩
    have hP' := isPeriod_comp_isometry_symm D' (Di i) w hw.1 P hU.2.1
    refine ⟨i, _, hP', ?_⟩
    exact (hF.sep D' (Di i) t' (t i) P _ y _ e (ex i _) hU (hunif i _ hP') w (LinearEquiv.refl ℂ _) hw
      (fun x => by simp)).symm
  · intro i j P P' hP hP' huu
    obtain ⟨w, h, hw, -⟩ := cmpEq _ _ _ _ _ _ _ _ _ _ huu (hunif i P hP) (hunif j P' hP')
    exact hdist i j w hw
  · intro i P P' hP hP'
    constructor
    · intro huu
      exact cmpEq _ _ _ _ _ _ _ _ _ _ huu (hunif i P hP) (hunif i P' hP')
    · rintro ⟨w, h, hw, hPw⟩
      exact hF.sep _ _ _ _ _ _ _ _ _ _ (hunif i P hP) (hunif i P' hP') w h hw hPw
  · intro i m B P hB hHol
    exact _root_.GlobalTheory.PELUHol.isHolTo_point_and_exp O bar g ρ Λ F N C d (Di i) (t i) m B P (fun b => u i (P b)) (fun b => ex i (P b)) hN heta hsm
      hqc hF (hmem i).1 (hfull _ _ (hmem i).1) hB hHol (fun b hb => hunif i (P b) (hHol.1 b hb))
  · intro m B y hB hy hhol b₀ hb₀
    obtain ⟨D', t', P, e, hC, hU⟩ := hF.pts (y b₀) (hy b₀ hb₀)
    obtain ⟨i, w, hw⟩ := hall D' t' hC ⟨P, hU.2.1⟩
    have hP' := isPeriod_comp_isometry_symm D' (Di i) w hw.1 P hU.2.1
    have hU' := _root_.GlobalTheory.PELU.unifAt_transport O bar g ρ ℂ (RingHom.id ℂ) Λ F N D' (Di i) t' (t i) P _ (y b₀) e w
      (LinearEquiv.refl ℂ _) hN0 hU hw (fun x => by simp) hP'
    obtain ⟨B', P₁, e₁, hB', hb₀', hBB, -, hHol, -, hU₁⟩ :=
      _root_.GlobalTheory.PELU.holomorphic_map_lifts_to_periods O bar g ρ Λ F N (Di i) (t i) m B y b₀ _ _ hN0 heta hlft hB hb₀ hy hhol hU'
    refine ⟨B', i, P₁, hB', hb₀', hBB, hHol, fun b hb => ?_⟩
    exact hF.sep _ _ _ _ _ _ _ _ _ _ (hunif i (P₁ b) (hHol.1 b hb)) (hU₁ b hb) (LinearEquiv.refl O _)
      (LinearEquiv.refl ℂ _) (hrefl i) (fun x => rfl)

end GlobalTheory.PELU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupChartSemilinearHomIsFormalGrou
section
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem isHom_map_of_semiHom_ev (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k')
    (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e)
    (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k)
    (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k') (φ : Fin d → MvPowerSeries (Fin e) k')
    (hμ : c.IsLawOf μ) (hν : c'.IsLawOf ν) (hφ : ∀ n j, c'.ev n (φ j) = s.app n (c.x n j))
 :
    IsHom ν (fun i => MvPowerSeries.map σ (μ i)) φ := by
  have hL := (GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k' e G' c').2 ν hν
  have h2 := _root_.GlobalTheory.Katz.semiHom_ev₂_pull2 p k k' σ d e G G' c c' s φ hφ
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have h0 := (GlobalTheory.Katz.counit_dUnit_evA k' e (G'.A 0) (c'.x 0) (c'.nil 0) (c'.aug 0) (φ j)).1
    change Coalgebra.counit (R := k') (c'.ev 0 (φ j)) = _ at h0
    rw [← h0, hφ 0 j, (s.app 0).counit_map, c.aug 0 j, map_zero]
  · let z : ∀ n, G'.A n ⊗[k'] G'.A n := fun n => Coalgebra.comul (R := k') (s.app n (c.x n j))
    have hz : ∀ n, pullbackTwo (G'.res n) (z (n + 1)) = z n := fun n => by
      simp only [z]
      rw [pullTwo_comul, s.res_app, c.res]
    have hl : ∀ n, c'.ev₂ n (subst ν (φ j)) = z n := fun n => by
      rw [(hL.2 n (φ j)).1, hφ n j]
    have hr : ∀ n, c'.ev₂ n (pull2 φ (MvPowerSeries.map σ (μ j))) = z n := fun n => by
      rw [h2 n (μ j), hμ n j, SemiBialgHom.two_comul]
    exact ((_root_.GlobalTheory.chart_square_presents p k' e G' c').2 z hz).unique hl hr

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentKernelEqCokerOmegaMap
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

noncomputable section

namespace GlobalTheory.PDivGroup

theorem cotMap_comp_eq_zero_of_kerIdeal_le {k A B C : Type} [Field k] [CommRing A] [CommRing B]
    [CommRing C] [Bialgebra k A] [Bialgebra k B] [Bialgebra k C] (g : B →ₐc[k] A)
    (π : A →ₐc[k] C) (h : kerIdeal g ≤ RingHom.ker π) (x : Cot k B) :
    cotMap π (cotMap g x) = 0 := by
  rw [← LinearMap.comp_apply, ← cotMap_comp]
  obtain ⟨b, rfl⟩ := AugCot.d_surjective _ x
  rw [cotMap_d]
  have h' := (kerIdeal_le_ker_iff g (π : A →ₐ[k] C)).1 h b
  change dUnit (R := k) ((π : A →ₐ[k] C) (g b)) = 0
  rw [h']
  exact AugCot.d_algebraMap _ _

theorem cot_kernel_eq_coker_omegaMap : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H) (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (π : G.A 1 →ₐc[k] C), Function.Surjective π → (kerIdeal (q.app 1) ≤ RingHom.ker π → ∀ w ∈ LinearMap.range (omegaMap G H q), cotMap π (w.1 1) = 0) ∧ (RingHom.ker π ≤ kerIdeal (q.app 1) ⊔ augIdeal k (G.A 1) ^ 2 → kerIdeal (q.app 1) ≤ RingHom.ker π → Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) = Module.finrank k (Cot k C)) ∧ ∀ (H' : PDivGroup p k) (f : G ⟶ H'), (∀ w ∈ LinearMap.range (omegaMap G H' f), cotMap π (w.1 1) = 0) → cotMap (π.comp (f.app 1)) = 0 := by
  intro p _ k _ _ G H q C _ _ _ _ π hπ
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  have part1 : kerIdeal (q.app 1) ≤ RingHom.ker π →
      ∀ w ∈ LinearMap.range (omegaMap G H q), cotMap π (w.1 1) = 0 := by
    rintro h w ⟨v, rfl⟩
    exact cotMap_comp_eq_zero_of_kerIdeal_le (q.app 1) π h (v.1 1)
  refine ⟨part1, fun h1 h2 => ?_, fun H' f hf => ?_⟩
  ·
    let Φ : G.omega →ₗ[k] Cot k C := cotMap π ∘ₗ G.omegaLevel 1
    have hΦ : Function.Surjective Φ :=
      (cotMap_surjective hπ).comp (G.omegaLevel_one_bijective hp).2
    have hker : LinearMap.ker Φ = LinearMap.range (omegaMap G H q) := by
      ext w
      rw [LinearMap.mem_ker]
      constructor
      · intro hw
        have hw' : AugCot.map (π : G.A 1 →ₐ[k] C) (BialgHomClass.counitAlgHom_comp π) (w.1 1) = 0 :=
          hw
        obtain ⟨x, hx⟩ := (AugCot.exact_kerMap_map (π : G.A 1 →ₐ[k] C)
          (BialgHomClass.counitAlgHom_comp π) hπ (w.1 1)).1 hw'
        have hx2 : dUnit (R := k) (x : G.A 1) = w.1 1 := by
          rw [← hx]; exact (AugCot.kerMap_apply _ _ x).symm
        have hxm : (x : G.A 1) ∈ kerIdeal (q.app 1) ⊔ augIdeal k (G.A 1) ^ 2 := h1 x.2
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hxm
        have hz0 : dUnit (R := k) z = 0 := by
          have hzI : z ∈ augIdeal k (G.A 1) := Ideal.pow_le_self two_ne_zero hz
          have hεz : counitAlgHom k (G.A 1) z = 0 := hzI
          rw [dUnit, AugCot.d_eq_zero_iff, hεz, map_zero, sub_zero]
          exact hz
        obtain ⟨u, hu⟩ := dUnit_mem_range_of_mem_kerIdeal (q.app 1) hy
        obtain ⟨v, rfl⟩ := (H.omegaLevel_one_bijective hp).2 u
        refine ⟨v, (G.omegaLevel_one_bijective hp).1 ?_⟩
        change cotMap (q.app 1) (H.omegaLevel 1 v) = w.1 1
        rw [hu, ← hx2, ← hyz]
        change dUnit (R := k) y = dUnit (R := k) (y + z)
        rw [show dUnit (R := k) (y + z) = dUnit (R := k) y + dUnit (R := k) z from map_add _ y z, hz0, add_zero]
      · intro hw
        exact part1 h2 w hw
    rw [← hker]
    exact (Φ.quotKerEquivOfSurjective hΦ).finrank_eq
  · rw [cotMap_comp]
    refine LinearMap.ext fun u => ?_
    obtain ⟨v, rfl⟩ := (H'.omegaLevel_one_bijective hp).2 u
    exact hf _ ⟨v, rfl⟩

end GlobalTheory.PDivGroup
end
end

