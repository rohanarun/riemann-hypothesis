module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0124
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0170
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfAssociated
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueSpecializes
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValFGeneric
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsVeryAmplePower
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Algebraise

theorem exists_veryAmple_h1Zero_pull : ∀ (A : Type) [CommRing A] (X : Over (Spec (CommRingCat.of A))) (L : LB X.left), L.IsLB → RelAmple X L → ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (g₀ : A →+* K) (X₀ : Scheme.{0}) (π : X₀ ⟶ X.left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ X.hom (Spec.map (CommRingCat.ofHom g₀)) → ∃ d : ℕ, 1 ≤ d ∧ FirstCohomologyVanishes ((AbLaw.pw L d).pull π) ∧ ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (AbLaw.pw L d)), VeryAmpleBy X.hom (AbLaw.pw L d) s := by
  intro A _ X L hL h K _ _ g₀ X₀ π f₀ hπ
  obtain ⟨d₀, hd₀, n₀, s₀, hs₀⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy A X L hL).1 h
  have isLB_pw {Y : Scheme.{0}} {H : LB Y} (hH : H.IsLB) (t : ℤ) :
      (AbLaw.pw H t).IsLB := by
    refine ⟨hH.cover, ?_, ?_⟩
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simp only [one_zpow, ← map_zpow] at h
      exact h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simp only [mul_zpow, ← map_zpow] at h
      exact h
  have hH := isLB_pw hL (d₀ : ℤ)
  have hH₀ := LB.isLB_pull hH π
  let s' := fun j => GlobalTheory.Cartier.secPull (s₀ j) π
  haveI : IsClosedImmersion (pullback.lift π f₀ hπ.w) := by
    have e : pullback.lift π f₀ hπ.w = hπ.isoPullback.hom := by
      apply pullback.hom_ext
      · exact (pullback.lift_fst _ _ _).trans hπ.isoPullback_hom_fst.symm
      · exact (pullback.lift_snd _ _ _).trans hπ.isoPullback_hom_snd.symm
    rw [e]
    infer_instance
  have hva : VeryAmpleBy f₀ _ s' := by
    haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) hπ.flip inferInstance
    have loc (i : Fin (n₀ + 1)) : nonzeroLocus (s' i) = π ⁻¹ᵁ nonzeroLocus (s₀ i) :=
      GlobalTheory.Cartier.nonzeroLocus_secPull (s₀ i) π
    have restrict_app {U : X.left.Opens} {V W : X₀.Opens}
        (e : V ≤ π ⁻¹ᵁ U) (hWV : W ≤ V) (a : Γ(X.left, U)) :
        rs X₀ hWV ((π.appLE U V e).hom a) = (π.appLE U W (hWV.trans e)).hom a :=
      congrArg (fun q => q.hom a) (π.appLE_map e (homOfLE hWV).op)
    refine ⟨GlobalTheory.ProjSpace.iSup_nonzeroLocus_secPull hs₀.1 π, fun i => ?_⟩
    obtain ⟨haff, r, hr, hsurj⟩ := hs₀.2 i
    refine ⟨by rw [loc]; exact haff.preimage π, fun j => (π.appLE _ _ (loc i).le).hom (r j), ?_, ?_⟩
    · intro j k
      have e := GlobalTheory.Cartier.pull_U (AbLaw.pw L (d₀ : ℤ)) π k
      change rs X₀ inf_le_right ((π.appLE _ _ e.le).hom ((s₀ j).f (k ⟨⟩))) =
        rs X₀ inf_le_left ((π.appLE _ _ (loc i).le).hom (r j)) *
          rs X₀ inf_le_right ((π.appLE _ _ e.le).hom ((s₀ i).f (k ⟨⟩)))
      rw [restrict_app, restrict_app, restrict_app]
      exact Segre.ap_ratio π (hr j (k ⟨⟩)) (inf_le_left.trans (loc i).le)
        (inf_le_right.trans e.le)
    · intro x
      refine VeryAmplePull.closure_eq_top hπ.w haff (loc i) (RingHom.range _) (fun d => ?_)
        (fun c => ?_) x
      · obtain ⟨p, rfl⟩ := hsurj d
        refine ⟨MvPolynomial.map g₀ p, ?_⟩
        rw [MvPolynomial.eval₂Hom_map_hom, MvPolynomial.map_eval₂Hom]
        exact congrArg (fun q => MvPolynomial.eval₂Hom q _ p)
          (RingHom.ext fun c => (VeryAmplePull.appLE_cst hπ.w _ _ _ c).symm)
      · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩
  obtain ⟨t₀, ht₀⟩ := _root_.GlobalTheory.AbLaw.serre_h1Zero_and_sections_polynomial.1 K X₀ f₀ _ n₀ s' hH₀ hva _ hH₀
  have h1 := ht₀ (t₀.toNat : ℤ) (Int.self_le_toNat t₀)
  obtain ⟨w, hw⟩ := lbIso_tw hH₀ (t₀.toNat : ℤ)
  have h2 := H1Iso.firstCohomologyVanishes_of_iso_of_isGen (isLB_tw hH₀ hH₀ _).cover (isLB_pw hH₀ _) w hw h1
  have h3 := veryAmpleBy_pw A X.left X.hom _ n₀ s₀ hH hs₀ (t₀.toNat + 1) (Nat.le_add_left _ _)
  have e : AbLaw.pw (AbLaw.pw L (d₀ : ℤ)) ((t₀.toNat + 1 : ℕ) : ℤ) =
      AbLaw.pw L ((d₀ * (t₀.toNat + 1) : ℕ) : ℤ) := by
    rw [pw_pw, Nat.cast_mul]
  refine ⟨d₀ * (t₀.toNat + 1), Nat.mul_pos hd₀ (Nat.succ_pos _), ?_, ?_⟩
  · rw [← e, pw_pull, Nat.cast_add, Nat.cast_one]
    exact h2
  · rw [← e]
    exact h3

end GlobalTheory.Algebraise
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrobeniusCountsIntegralTorsionSpecialFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.SpecialCount

theorem transfer {M N : Type} [CommGroup M] [Group N] (H : Subgroup M) (r : H →* N) (Φ : MulAut M)
    (φ : ℕ → N → N) (hφ : ∀ (j : ℕ) (x : H), ∃ h : Φ^[j] x ∈ H, r ⟨_, h⟩ = φ j (r x)) (l e : ℕ)
    (hinj : ∀ n (x : H), x ^ l ^ n = 1 → r x = 1 → x = 1) (V : Subgroup N)
    (hV : ∀ x ∈ V, φ 1 x = x ^ e) (hfin : ∀ n, Finite {x : N // x ^ l ^ n = 1}) (Q : Polynomial ℤ)
    (hQ : ∀ (x : N) n, x ^ l ^ n = 1 →
      ((List.range (Q.natDegree + 1)).map fun j => φ j x ^ Q.coeff j).prod ∈ V) :
    ∃ U : Subgroup M,
      (∀ n, Nat.card {x : H // x ^ l ^ n = 1} ≤ Nat.card {x : N // x ^ l ^ n = 1} ∧
        Nat.card {x : U // x ^ l ^ n = 1} ≤ Nat.card {x : V // x ^ l ^ n = 1}) ∧
      (∀ n, ∀ x ∈ U, x ^ l ^ n = 1 → Φ x = x ^ e) ∧
      ∀ n, ∀ x ∈ H, x ^ l ^ n = 1 → ∏ j ∈ Finset.range (Q.natDegree + 1), (Φ^[j] x) ^ Q.coeff j ∈ U := by
  have inj : ∀ n (x y : H), x ^ l ^ n = 1 → y ^ l ^ n = 1 → r x = r y → x = y := by
    intro n x y hx hy h
    have := hinj n (x * y⁻¹) (by rw [mul_pow, inv_pow, hx, hy]; simp) (by rw [map_mul, map_inv, h]; simp)
    exact mul_inv_eq_one.1 this
  have memU : ∀ x : M, x ∈ (V.comap r).map H.subtype ↔ ∃ h : x ∈ H, r ⟨x, h⟩ ∈ V := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨h, hx⟩
      exact ⟨⟨x, h⟩, hx, rfl⟩
  refine ⟨(V.comap r).map H.subtype, fun n => ⟨?_, ?_⟩, fun n x hx hn => ?_, fun n x hx hn => ?_⟩
  · have := hfin n
    refine Nat.card_le_card_of_injective
      (fun x => ⟨r x.1, by rw [← map_pow, x.2, map_one]⟩) fun x y h => ?_
    exact Subtype.ext (inj n _ _ x.2 y.2 (congrArg Subtype.val h))
  · have := hfin n
    have : Finite {x : V // x ^ l ^ n = 1} :=
      Finite.of_injective (β := {x : N // x ^ l ^ n = 1})
        (fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩) fun x y h =>
          Subtype.ext (Subtype.ext (by exact congrArg (fun z : {x : N // x ^ l ^ n = 1} => z.1) h))
    have tor : ∀ x : {x : (V.comap r).map H.subtype // x ^ l ^ n = 1},
        (⟨x.1.1, ((memU _).1 x.1.2).1⟩ : H) ^ l ^ n = 1 := fun x =>
      Subtype.ext (by exact congrArg (fun z : (V.comap r).map H.subtype => z.1) x.2)
    refine Nat.card_le_card_of_injective
      (fun x => ⟨⟨r ⟨x.1.1, ((memU _).1 x.1.2).1⟩, ((memU _).1 x.1.2).2⟩, Subtype.ext (by
        change r _ ^ l ^ n = 1
        rw [← map_pow, tor x, map_one])⟩) fun x y h => ?_
    have := inj n _ _ (tor x) (tor y) (congrArg (fun z => z.1.1) h)
    exact Subtype.ext (Subtype.ext (by exact congrArg (fun z : H => z.1) this))
  · obtain ⟨h, hv⟩ := (memU x).1 hx
    obtain ⟨h', e'⟩ := hφ 1 ⟨x, h⟩
    have := inj n ⟨_, h'⟩ (⟨x, h⟩ ^ e) (Subtype.ext (by
        change Φ x ^ l ^ n = 1
        rw [← map_pow, hn, map_one])) (Subtype.ext (by
        change (x ^ e) ^ l ^ n = 1
        rw [← pow_mul, mul_comm, pow_mul, hn, one_pow])) (by rw [e', hV _ hv, map_pow])
    exact congrArg Subtype.val this
  · choose h e' using fun j => hφ j ⟨x, hx⟩
    have hr := hQ (r ⟨x, hx⟩) n (by
      rw [← map_pow, show (⟨x, hx⟩ : H) ^ l ^ n = 1 from Subtype.ext hn, map_one])
    refine ⟨((List.range (Q.natDegree + 1)).map fun j => (⟨_, h j⟩ : H) ^ Q.coeff j).prod, ?_, ?_⟩
    · change r _ ∈ V
      rw [map_list_prod, List.map_map]
      have : (r ∘ fun j => (⟨_, h j⟩ : H) ^ Q.coeff j) = fun j => φ j (r ⟨x, hx⟩) ^ Q.coeff j := by
        funext j
        simp only [Function.comp, map_zpow, e']
      rw [this]
      exact hr
    · rw [map_list_prod, List.map_map]
      rfl

theorem exists_restrict {R Ω : Type} [CommRing R] [IsLocalRing R] [Field Ω] [Algebra R Ω]
    (hi : Function.Injective (algebraMap R Ω)) (q : ℕ) (ψ : Ω →+* Ω)
    (h : ∀ x : R, ∃ y : R, algebraMap R Ω y = ψ (algebraMap R Ω x) ∧ y - x ^ q ∈ IsLocalRing.maximalIdeal R) :
    ∃ σ : R →+* R, (∀ x, algebraMap R Ω (σ x) = ψ (algebraMap R Ω x)) ∧
      ∀ x, IsLocalRing.residue R (σ x) = IsLocalRing.residue R x ^ q := by
  choose f hf hf' using h
  refine ⟨{ toFun := f
            map_one' := hi (by simp [hf])
            map_mul' := fun x y => hi (by simp [hf])
            map_zero' := hi (by simp [hf])
            map_add' := fun x y => hi (by simp [hf]) }, hf, fun x => ?_⟩
  have := (IsLocalRing.residue_eq_zero_iff _).2 (hf' x)
  rw [map_sub, map_pow, sub_eq_zero] at this
  exact this

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem smConn_pullback {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] (h : SmConn G) :
    SmConn ((Over.pullback f).obj G) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · show Smooth (pullback.snd _ _); infer_instance
  · show IsSeparated (pullback.snd _ _); infer_instance
  · show QuasiCompact (pullback.snd _ _); infer_instance
  · show GeometricallyConnected (pullback.snd _ _); infer_instance

end GlobalTheory.SS.SpecialCount

namespace GlobalTheory.SS
open SpecialCount

theorem frobenius_on_integral_torsion : ∀ (W R Ω : Type) [CommRing W] [CommRing R] [IsDomain R] [IsLocalRing R] [Field Ω] [Algebra W R] [Algebra R Ω] [Algebra W Ω] [IsScalarTower W R Ω], Function.Injective (algebraMap R Ω) → IsAlgClosed (IsLocalRing.ResidueField R) → ∀ (p r l : ℕ), p.Prime → CharP (IsLocalRing.ResidueField R) p → 1 ≤ r → l.Prime → IsUnit (l : R) → (∀ c : IsLocalRing.ResidueField R, ∃ m, 1 ≤ m ∧ c ^ ((p ^ r) ^ m) = c) → ∀ ψ : Ω →+* Ω, (∀ w : W, ψ (algebraMap W Ω w) = algebraMap W Ω w) → (∀ x : R, ∃ y : R, algebraMap R Ω y = ψ (algebraMap R Ω x) ∧ y - x ^ (p ^ r) ∈ IsLocalRing.maximalIdeal R) → ∀ (G : Over (Sp W)) [GrpObj G], SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ L : LB ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G).left, AmpleCub ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G) L → ∀ (M : Type) [CommGroup M] (θ : M ≃* (Over.mk (spMap (algebraMap W Ω)) ⟶ G)) (Ψ : MulAut M), (∀ x, (θ (Ψ x)).left = spMap ψ ≫ (θ x).left) → ∃ (t a m C : ℕ) (Q : Polynomial ℤ) (H U : Subgroup M), 1 ≤ m ∧ (∀ x, x ∈ H ↔ ∃ s : Sp R ⟶ G.left, s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R Ω) ≫ s = (θ x).left) ∧ (∀ n, Nat.card {x : H // x ^ l ^ n = 1} ≤ C * l ^ (n * (t + 2 * a)) ∧ Nat.card {x : U // x ^ l ^ n = 1} ≤ C * l ^ (n * t)) ∧ (∀ β : ℂ, Polynomial.aeval β Q = 0 → ‖β‖ < (((p ^ r) ^ m : ℕ) : ℝ)) ∧ (∀ n, ∀ x ∈ U, x ^ l ^ n = 1 → (Ψ ^ m) x = x ^ ((p ^ r) ^ m)) ∧ (∀ n, ∀ x ∈ H, x ^ l ^ n = 1 → ∏ j ∈ Finset.range (Q.natDegree + 1), ((Ψ ^ m : MulAut M)^[j] x) ^ Q.coeff j ∈ U) ∧ (g ≤ t + a → Nonempty (TorusExtension ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G))) := by
  intro W R Ω _ _ _ _ _ _ _ _ _ hi hac p r l hp hch hr hl hlu hfin ψ hψW hψR G _ hG g hg L hL M _ θ Ψ hΨ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ, hσ, hσ'⟩ := exists_restrict hi (p ^ r) ψ hψR
  have hσW : ∀ w, σ (algebraMap W R w) = algebraMap W R w := fun w => hi (by
    rw [hσ, ← IsScalarTower.algebraMap_apply, hψW])
  obtain ⟨F, hF, hFx⟩ := GlobalTheory.SS.exists_frobG_baseChange W (IsLocalRing.ResidueField R)
    ((IsLocalRing.residue R).comp (algebraMap W R)) p r hr (fun w => by
      rw [RingHom.comp_apply, ← hσ', hσW]) hfin G hG
  have hlp : l ≠ p := by
    rintro rfl
    have := hlu.map (IsLocalRing.residue R)
    rw [map_natCast, CharP.cast_eq_zero] at this
    exact not_isUnit_zero this
  have hq : 2 ≤ p ^ r := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  obtain ⟨t, a, m, C, Q, V, hm, hroot, hV, hcount, hQ, hT⟩ := GlobalTheory.SS.frobenius_on_torsion _ p l hl hlp _
    (smConn_pullback _ G hG) g (by
      show SmoothOfRelativeDimension g (pullback.snd _ _)
      exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback _ _) hg) L hL F (p ^ r) hq hF
  obtain ⟨H₀, red, hH, hred, hinj⟩ := GlobalTheory.RedPts.exists_reduction W R Ω hi G hG
  let H : Subgroup M := H₀.comap θ.toMonoidHom
  let κ : H →* H₀ := (θ.toMonoidHom.subgroupComap H₀)
  have step : ∀ x : H, ∃ h : Ψ x ∈ H, red (κ ⟨_, h⟩) = red (κ x) ≫ F.asHom := by
    intro x
    obtain ⟨s, hs, hs'⟩ := (hH _).1 x.2
    have a1 : (spMap σ ≫ s) ≫ G.hom = spMap (algebraMap W R) := by
      rw [Category.assoc, hs, sp_comp]
      congr 1
      exact RingHom.ext hσW
    have a2 : spMap (algebraMap R Ω) ≫ spMap σ ≫ s = (θ (Ψ x)).left := by
      rw [hΨ, ← Category.assoc, sp_comp, show (algebraMap R Ω).comp σ = ψ.comp (algebraMap R Ω) from
        RingHom.ext hσ, ← sp_comp, Category.assoc, hs']
      rfl
    have hx : Ψ x ∈ H := (hH _).2 ⟨_, a1, a2⟩
    refine ⟨hx, ?_⟩
    have b1 := hred (κ ⟨_, hx⟩) _ a1 a2
    have b2 := hred (κ x) s hs hs'
    have b3 := hFx (red (κ x)) (iterateFrobenius _ p r) (fun c => rfl)
    ext1
    apply pullback.hom_ext
    · refine b1.trans (Eq.trans ?_ b3.symm)
      erw [b2]
      rw [← Category.assoc, ← Category.assoc, sp_comp, sp_comp]
      congr 2
      exact RingHom.ext hσ'
    · exact (Over.w _).trans (Over.w _).symm
  have iter : ∀ (n : ℕ) (x : H), ∃ h : (Ψ ^ n) x ∈ H,
      red (κ ⟨_, h⟩) = red (κ x) ≫ (F ^ n).asHom := by
    intro n
    induction n with
    | zero => exact fun x => ⟨x.2, (Category.comp_id _).symm⟩
    | succ n ih =>
      intro x
      obtain ⟨h, e⟩ := step x
      obtain ⟨h', e'⟩ := ih ⟨_, h⟩
      rw [pow_succ, pow_succ]
      refine ⟨h', e'.trans ?_⟩
      rw [e, Category.assoc]
      rfl
  obtain ⟨U, hU1, hU2, hU3⟩ := transfer H (red.comp κ) (Ψ ^ m)
    (fun j x => x ≫ ((F ^ m) ^ j).asHom) (fun j x => by
      have e : (Ψ ^ m : MulAut M)^[j] x = (Ψ ^ (m * j)) x := by
        rw [pow_mul]
        generalize (x : M) = y
        induction j generalizing y with
        | zero => rfl
        | succ j ih => rw [pow_succ, Function.iterate_succ_apply, ih]; rfl
      rw [e, ← pow_mul]
      exact iter (m * j) x) l ((p ^ r) ^ m) (fun n x hx h => by
      have := hinj (l ^ n) (κ x) (by rw [Nat.cast_pow]; exact hlu.pow n)
        (by rw [← map_pow, hx, map_one]) h
      exact Subtype.ext (θ.injective ((congrArg Subtype.val this).trans (map_one θ).symm))) V
    (fun x hx => by rw [pow_one]; exact hV x hx) (fun n => (hcount n).1) Q hQ
  refine ⟨t, a, m, C, Q, H, U, hm, fun x => hH _, fun n => ⟨(hU1 n).1.trans (hcount n).2.1,
    (hU1 n).2.trans (hcount n).2.2⟩, fun β hβ => ?_, hU2, hU3, hT⟩
  rw [Nat.cast_pow]
  exact hroot β hβ

end GlobalTheory.SS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIntegrallyClosedOverring
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.GoodOut

open GlobalTheory.Points

theorem exists_hom_ker {R : Type} [CommRing R] (z : PrimeSpectrum R) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (f : R →+* K), ∀ t, f t = 0 ↔ t ∈ z.asIdeal :=
  ⟨AlgebraicClosure z.asIdeal.ResidueField, inferInstance, inferInstance,
    (algebraMap z.asIdeal.ResidueField _).comp (algebraMap R z.asIdeal.ResidueField), fun _ =>
    (map_eq_zero_iff (algebraMap z.asIdeal.ResidueField _) (RingHom.injective _)).trans
      Ideal.algebraMap_residueField_eq_zero⟩

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}


theorem exists_th_notMem (hL : Laws) (hL₂ : Laws2) (ρ : S.Real) (z : PrimeSpectrum S.R) (a : S.Gam) :
    ∃ c : S.Gam, ρ.n • c = 0 ∧ (⟨S.th (a + c), S.th_mem _⟩ : S.R) ∉ z.asIdeal := by
  obtain ⟨K, _, _, f, hf⟩ := exists_hom_ker z
  let x : Sp K ⟶ Sp S.R := spMap f
  obtain ⟨j, hj, hr⟩ := ρ.r_eq
  have hM : S.r * S.N = ρ.n * ρ.n ^ (j - 1 + ρ.k * 2) := by
    rw [hr, ρ.N_eq, ← pow_mul, ← pow_add, ← pow_succ']
    congr 1
    omega
  have hn : (ρ.n : K) ≠ 0 := by
    have h := (S.unit.map (f.comp (algebraMap o S.R))).ne_zero
    rw [map_natCast, hM, Nat.cast_mul] at h
    exact left_ne_zero_of_mul h
  obtain ⟨θ, hθ, hv⟩ := UnitTheta.exists_sec_of_baseOver S.R ρ.P ρ.th₁
  obtain ⟨y₀, hy₀, e₀⟩ := ThetaFibre.exists_mem_nonzeroLocus_fibre hL₂.secBaseChangeAny S.R ρ.P ρ.th₁ ρ.th₁_basis
    (x (IsLocalRing.closedPoint K))
  let u : Over.mk x ⟶ baseOver (Sp S.R) := Over.homMk x (by simp)
  obtain ⟨y, hy, H⟩ := UnitTheta.exists_good_point_of_sec hL.polBaseChange hL.goodPt _ ρ.P θ K x ρ.n
    ρ.n_prime.two_le hn ⟨_, hθ y₀ hy₀, _, e₀.symm⟩ (u ≫ ρ.pt a)
  have := ρ.P.isAb.comm
  obtain ⟨h0, hsm⟩ := ThetaReal.pt_nsmul ρ.pt ρ.pt_add
  obtain ⟨c, hc, -⟩ := ρ.pt_bij K x y (by rw [hM, pow_mul, hy, one_pow])
  obtain ⟨a₀, -, uniq⟩ := ρ.pt_bij K x 1 (one_pow _)
  refine ⟨c, (uniq _ (by beta_reduce; rw [hsm, MonObj.comp_pow, hc, hy])).trans
    (uniq _ (by beta_reduce; rw [h0, MonObj.comp_one])).symm, fun h => ?_⟩
  have e : (u ≫ ρ.pt a * y).left = spMap f ≫ (ρ.pt (a + c)).left := by
    rw [← hc, ρ.pt_add]
    exact congrArg CommaMorphism.left (MonObj.comp_mul u _ _).symm
  rw [e] at H
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (H (x := IsLocalRing.closedPoint K) trivial)
  have hk' := (le_preimage_iff _ _).2 hk
  have hU := le_preimage_mono _ (Scheme.basicOpen_le _ _) hk'
  refine ((le_preimage_basicOpen_iff _ hU _).1 hk').ne_zero ?_
  rw [hv _ _ _ (ρ.th_val (a + c)) K f k hU, (hf _).2 h, zero_mul]

section Comb

variable {X Z : Scheme.{0}} (p : X ⟶ Z) {B : LB X} {J : Type} [Fintype J] (s : J → B.Sec) (W : Z.Opens)

variable [DecidableEq J] (b c : Matrix J J Γ(Z, W)) (hc : c * b = 1)
include hc

end Comb

section Transfer

variable {Z : Scheme.{0}} (P : PolAV Z)

end Transfer

variable (ρ : S.Real) (c : CubicalStr ρ.P.A ⟨ρ.P.L, ρ.rig, ρ.P.isLB, ρ.rig_gen⟩)


section Support

include ρ

end Support


end GlobalTheory.ZH.GoodOut

end
end

