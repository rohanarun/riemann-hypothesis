module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIntegralOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfInfLeInfRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2316
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1857
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfAssociated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1952
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2134
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2481
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPrincipalPolarisationExtendsSemiAbelian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.SymExtend

open GlobalTheory.CechPic

theorem stalkMap_comp_base {R : Type} [CommRing R] {G : Over (Sp R)} (f : G ⟶ G) (x : G.left) :
    (f.left.stalkMap x).hom.comp ((G.left.presheaf.germ ⊤ (f.left x) trivial).hom.comp ((G.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) =
      (G.left.presheaf.germ ⊤ x trivial).hom.comp ((G.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) := by
  ext a
  have e := Scheme.Hom.germ_stalkMap_apply f.left ⊤ x trivial
    (G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
  refine e.trans ?_
  conv_rhs => rw [← Over.w f]
  rfl

theorem exists_open_unit_mul_sq (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hA : AdmBase R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (L2 : LB G.left) (h2 : L2.IsLB) (h : L2.Sec)
    (Lθ : LB (pullback G.hom (jK R))) (hθ : Lθ.IsLB) (θ : Lθ.Sec) (hc : (∀ j i, ∃ w : Γ(pullback G.hom (jK R), pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i)ˣ, ((pullback G.hom (jK R)).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G.hom (jK R), pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i)) * ((pullback G.hom (jK R)).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G.hom (jK R)).app (L2.U j)).hom (h.f j)))) (hs : (∀ (x' : G.left) (k : L2.ι), ((𝟙 G) ^ 2 : G ⟶ G).left x' ∈ L2.U k → gs ((𝟙 G) ^ 2 : G ⟶ G).left x' (L2.U k) (h.f k) ≠ 0 ∧ ∃ (u : (G.left.presheaf.stalk x')ˣ) (g : G.left.presheaf.stalk x'), gs ((𝟙 G) ^ 2 : G ⟶ G).left x' (L2.U k) (h.f k) = u * g ^ 2))
    (x : G.left) (hx : G.hom x = closedPoint R) :
    ∃ V : G.left.Opens, x ∈ V ∧ ∃ a : Γ(G.left, V), a ≠ 0 ∧ ∀ j, ∃ u : Γ(G.left, V ⊓ L2.U j)ˣ, (G.left.presheaf.map (homOfLE inf_le_right).op).hom (h.f j) = (u : Γ(G.left, V ⊓ L2.U j)) * (G.left.presheaf.map (homOfLE inf_le_left).op).hom a ^ 2 := by
  have hfl := (GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow _ G hG 2 two_ne_zero).1
  have hsu := GlobalTheory.SemiAbSurj.surjective_pow _ G hG 2 two_ne_zero
  generalize ((𝟙 G) ^ 2 : G ⟶ G) = f at hs hfl hsu
  obtain ⟨x', rfl⟩ := f.left.surjective x
  have hx' : G.hom x' = closedPoint R := by
    rw [← hx, ← Scheme.Hom.comp_apply, Over.w f]
  obtain ⟨hD, hN, hIC⟩ := GlobalTheory.SquareNear.stalk_props R hA G hG (f.left x')
  obtain ⟨hD', hN', hIC'⟩ := GlobalTheory.SquareNear.stalk_props R hA G hG x'
  obtain ⟨k, hk⟩ := exists_chart h2 (f.left x')
  obtain ⟨hne, u, g, hug⟩ := hs x' k hk
  rw [gs_stalkMap _ _ _ hk, gs_eq (𝟙 G.left) (f.left x') _ hk] at hne hug
  let _ := (f.left.stalkMap x').hom.toAlgebra
  have : Module.Flat (G.left.presheaf.stalk (f.left x')) (G.left.presheaf.stalk x') := Flat.stalkMap f.left x'
  have : IsLocalHom (algebraMap (G.left.presheaf.stalk (f.left x')) (G.left.presheaf.stalk x')) :=
    inferInstanceAs (IsLocalHom (f.left.stalkMap x').hom)
  have : Module.FaithfullyFlat (G.left.presheaf.stalk (f.left x')) (G.left.presheaf.stalk x') :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hne₀ : (G.left.presheaf.germ (L2.U k) (f.left x') hk).hom (h.f k) ≠ 0 := fun e =>
    hne ((congrArg (f.left.stalkMap x').hom e).trans (map_zero _))
  have hsq : ∃ (u : (G.left.presheaf.stalk x')ˣ) (g : G.left.presheaf.stalk x'),
      algebraMap (G.left.presheaf.stalk (f.left x')) (G.left.presheaf.stalk x')
        ((G.left.presheaf.germ (L2.U k) (f.left x') hk).hom (h.f k)) = u * g ^ 2 := ⟨u, g, hug⟩
  have hinj := GlobalTheory.Mum.LocalInj.base_to_stalk_injective R hA G hG (f.left x')
  have hpr := GlobalTheory.Mum.ideal_map_stalk_isPrime_of_closedPoint R hA G hG (f.left x') hx
  have hpr' := GlobalTheory.Mum.ideal_map_stalk_isPrime_of_closedPoint R hA G hG x' hx'
  have hhor := GlobalTheory.SqHorizontal.horizontal R hA G hG L2 h Lθ hθ θ hc (f.left x') k hk
  rw [← stalkMap_comp_base f x'] at hpr'
  generalize ((G.left.presheaf.germ ⊤ (f.left x') trivial).hom.comp ((G.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) = σ at hinj hpr hpr' hhor
  have Hp : ∀ p : Ideal (G.left.presheaf.stalk (f.left x')), p.IsPrime → p.height = 1 →
      ∃ a b c : G.left.presheaf.stalk (f.left x'), b ∉ p ∧ c ∉ p ∧
        b * (G.left.presheaf.germ (L2.U k) (f.left x') hk).hom (h.f k) = c * a ^ 2 := by
    intro p hp h1
    by_cases hq : Ideal.comap σ p = ⊥
    · exact hhor p hp hq
    · have hqp : (Ideal.comap σ p).IsPrime := Ideal.comap_isPrime _ p
      have hP := hpr _ hqp
      have heq : Ideal.map σ (Ideal.comap σ p) = p := by
        by_contra hne'
        have hlt := lt_of_le_of_ne (Ideal.map_comap_le (f := σ) (K := p)) hne'
        have h1' : (Ideal.map σ (Ideal.comap σ p)).height < 1 :=
          (Ideal.height_strict_mono_of_isPrime hlt).trans_le h1.le
        rw [ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1'
        exact hq ((Ideal.map_eq_bot_iff_of_injective hinj).1 h1')
      refine _root_.GlobalTheory.Mum.exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime _ _ _ hne₀ hsq p hp h1 ?_
      have := hpr' _ hqp
      rwa [← Ideal.map_map, heq] at this
  obtain ⟨u₀, a, hua⟩ := isUnit_mul_sq_of_faithfullyFlat _ (G.left.presheaf.stalk x') _ hne₀ hsq Hp
  have ha : a ≠ 0 := by
    rintro rfl
    apply hne₀
    rw [hua]
    simp
  exact GlobalTheory.Mum.unit_mul_sq_spread G.left L2 h (f.left x') k hk u₀ a ha hua

theorem exists_unit_mul_of_sq_sec {X : Scheme.{0}} [IsIntegral X] [GlobalTheory.IsNormalScheme X] (W : X.Opens)
    {s t : Γ(X, W)} (c : Γ(X, W)ˣ) (ht : Nonempty W → t ≠ 0) (h : s ^ 2 = c * t ^ 2) :
    ∃ w : Γ(X, W)ˣ, s = w * t := by
  by_cases hW : Nonempty W
  · have ht := ht hW
    have h1 : t ∣ s := (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 ⟨c, by rw [h, mul_comm]⟩
    have h2 : s ∣ t := (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1
      ⟨(c⁻¹ : Γ(X, W)ˣ), by rw [h, mul_right_comm, Units.mul_inv, _root_.one_mul]⟩
    obtain ⟨w, hw⟩ := associated_of_dvd_dvd h1 h2
    exact ⟨w, by rw [← hw, mul_comm]⟩
  · obtain rfl : W = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hW ⟨⟨x, hx⟩⟩
    exact ⟨1, Subsingleton.elim _ _⟩

theorem res_ne_zero {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} (hW : W ≤ V) {a : Γ(X, V)} (ha : a ≠ 0)
    [Nonempty W] : (X.presheaf.map (homOfLE hW).op).hom a ≠ 0 := fun h0 =>
  ha (map_injective_of_isIntegral X (homOfLE hW) (h0.trans (map_zero _).symm))

theorem res_mem_nonZeroDivisors {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} (hW : W ≤ V) {a : Γ(X, V)}
    (ha : a ≠ 0) : (X.presheaf.map (homOfLE hW).op).hom a ∈ nonZeroDivisors Γ(X, W) := by
  by_cases hn : Nonempty W
  · exact mem_nonZeroDivisors_of_ne_zero (res_ne_zero hW ha)
  · obtain rfl : W = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hn ⟨⟨x, hx⟩⟩
    rw [Subsingleton.elim ((X.presheaf.map (homOfLE hW).op).hom a) 1]
    exact Submonoid.one_mem _

theorem extends_near (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hA : AdmBase R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (L2 : LB G.left) (h2 : L2.IsLB) (h : L2.Sec)
    (Lθ : LB (pullback G.hom (jK R))) (hθ : Lθ.IsLB) (θ : Lθ.Sec) (hc : (∀ j i, ∃ w : Γ(pullback G.hom (jK R), pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i)ˣ, ((pullback G.hom (jK R)).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G.hom (jK R), pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i)) * ((pullback G.hom (jK R)).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G.hom (jK R)).app (L2.U j)).hom (h.f j)))) (hs : (∀ (x' : G.left) (k : L2.ι), ((𝟙 G) ^ 2 : G ⟶ G).left x' ∈ L2.U k → gs ((𝟙 G) ^ 2 : G ⟶ G).left x' (L2.U k) (h.f k) ≠ 0 ∧ ∃ (u : (G.left.presheaf.stalk x')ˣ) (g : G.left.presheaf.stalk x'), gs ((𝟙 G) ^ 2 : G ⟶ G).left x' (L2.U k) (h.f k) = u * g ^ 2)) :
    ∃ (O : G.left.Opens) (N : LB O.toScheme), (∀ g : G.left, G.hom g = closedPoint R → g ∈ O) ∧ N.IsLB ∧
      LBIso (N.pull (pullback.fst O.ι (pullback.fst G.hom (jK R)))) (Lθ.pull (pullback.snd O.ι (pullback.fst G.hom (jK R)))) := by
  have hY := fun (x : {x : G.left // G.hom x = closedPoint R}) =>
    exists_open_unit_mul_sq R hA G hG L2 h2 h Lθ hθ θ hc hs x.1 x.2
  choose V hxV a ha hu using hY
  obtain ⟨hsq, hθa⟩ := GlobalTheory.SqGlue.main R hA G hG L2 h2 h _ θ hc _ V a ha hu
  haveI : IsIntegrallyClosed R := hA.2.2.1
  haveI : IsNoetherianRing R := hA.1
  haveI : Smooth G.hom := hG.smooth
  haveI : GeometricallyConnected G.hom := hG.geomConnected
  haveI : IsIntegral G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G
  haveI : GlobalTheory.IsNormalScheme G.left := GlobalTheory.isNormalScheme_of_smooth G.hom
  haveI : IsIntegral (pullback G.hom (jK R)) := GlobalTheory.isIntegral_pullback_of_smooth G.hom (jK R)
  haveI : GlobalTheory.IsNormalScheme (pullback G.hom (jK R)) := GlobalTheory.isNormalScheme_of_smooth (pullback.snd G.hom (jK R))
  have hgen : ∀ k, ((pullback.fst G.hom (jK R)).app (V k)).hom (a k) ≠ 0 := fun k h0 =>
    ha k (GlobalTheory.ExpInt.generic_app_injective G (V k) (h0.trans (map_zero _).symm))
  obtain ⟨O, N, hO, hN, hiso⟩ := GlobalTheory.LocalEqGlue.exists_lb_of_localEq G.left _ (pullback.fst G.hom (jK R)) Lθ θ _ V a
    (fun k W hW => res_mem_nonZeroDivisors hW (ha k)) (fun k W hW => res_mem_nonZeroDivisors hW (hgen k))
    (fun k l => by
      obtain ⟨c, hc⟩ := hsq k l
      exact exists_unit_mul_of_sq_sec _ c (fun _ => res_ne_zero _ (ha l)) hc)
    (fun k i => by
      obtain ⟨w, hw⟩ := hθa k i
      exact exists_unit_mul_of_sq_sec _ w (fun _ => res_ne_zero _ (hgen k)) hw)
  exact ⟨O, N, fun g hg => hO ⟨g, hg⟩ (hxV ⟨g, hg⟩), hN, hiso⟩

theorem exists_odd_sec {X : Scheme.{0}} [Nonempty X] {L : LB X} (hL : GlobalTheory.IsAmpleLB L) :
    ∃ (t : ℕ) (θ : (lbPow L (2 * t + 1)).Sec) (i : (lbPow L (2 * t + 1)).ι), θ.f i ≠ 0 := by
  obtain ⟨t, ht⟩ := Filter.eventually_atTop.1 (GlobalTheory.CutOutSections.eventually_isGenerated_lbPow hL)
  obtain ⟨θ, hθ⟩ := (ht (2 * t + 1) (by omega)).exists_mem (Classical.arbitrary X)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hθ
  refine ⟨t, θ, i, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hi
  exact hi

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ L₁ : LB G.left, L₁.IsLB ∧ LBIso (L₁.pull (pullback.fst G.hom (jK R))) (A.L.pull gen.hom.left) := by
  intro R _ _ _ hA G _ _ hG A gen hgen PP hext
  have hL : (A.L.pull gen.hom.left).IsLB := LB.isLB_pull A.isLB _
  have hP : (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left).IsLB := LB.isLB_pull hext.1 _
  obtain ⟨h2c, φ, hφ, h4c⟩ := _root_.GlobalTheory.Mum.two_smul_cls_eq_pull_diag_and_pull_sq R G A gen hgen PP hext _ _ hL hP rfl rfl
  haveI : Smooth G.hom := hG.smooth
  haveI : GeometricallyConnected G.hom := hG.geomConnected
  haveI : IsIntegral (pullback G.hom (jK R)) := GlobalTheory.isIntegral_pullback_of_smooth G.hom (jK R)
  haveI : IsIso gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map gen.hom))
  have hamp : GlobalTheory.IsAmpleLB (X := pullback G.hom (jK R)) (A.L.pull gen.hom.left) :=
    (GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A.A A.isLB A.ample).pull_of_isAffineHom gen.hom.left
  have hK : Function.Surjective (pullback.snd G.hom (jK R)).appTop.hom := by
    have e : pullback.snd G.hom (jK R) = gen.hom.left ≫ A.A.hom := (Over.w gen.hom).symm
    haveI : IsIso gen.hom.left.appTop := inferInstanceAs (IsIso (gen.hom.left.app ⊤))
    rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso gen.hom.left.appTop).2.comp (GlobalTheory.ExpansionTotal.globalFns _ A.A A.isAb).2
  obtain ⟨t, θ, hθ⟩ := exists_odd_sec hamp
  generalize (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left) = P at hP h2c
  have hLθ := GlobalTheory.isLB_lbPow hL (2 * t + 1)
  have hL2 := GlobalTheory.isLB_lbPow hP (2 * t + 1)
  have eθ := cls_lbPow hL (2 * t + 1) hLθ
  obtain ⟨h, hc, hs⟩ := exists_sec_sq_of_double R hA G hG hK _ hLθ θ hθ _ hL2
    (by rw [cls_lbPow hP, map_nsmul, ← h2c, smul_comm]; exact congrArg (2 • ·) eθ) φ hφ
    (by
      refine (congrArg (pull φ) eθ).trans (Eq.trans ?_ (congrArg (4 • ·) eθ).symm)
      rw [map_nsmul, smul_comm]
      exact congrArg ((2 * t + 1) • ·) h4c)
  obtain ⟨O, N, hO, hN, hiso⟩ := extends_near R hA G hG _ hL2 h _ hLθ θ hc hs
  obtain ⟨N', hN', eN'⟩ := cls_surj (cls N hN - t • pull O.ι (cls P hP))
  have e₁ := (cls_eq_iff (LB.isLB_pull hN _) (LB.isLB_pull hLθ _)).2 hiso
  rw [cls_pull hN, cls_pull hLθ] at e₁
  obtain ⟨L', hL', hI⟩ := GlobalTheory.Mum.lb_extends_of_extLam R hA G hG _ PP hL hext O hO N' hN'
    ((cls_eq_iff (LB.isLB_pull hN' _) (LB.isLB_pull hL _)).1 (by
      rw [cls_pull hN', eN', map_sub, e₁, map_nsmul, ← pull_comp, pullback.condition, pull_comp, ← h2c]
      refine Eq.trans ?_ (cls_pull hL _ _).symm
      refine (congrArg (fun z => pull (pullback.snd O.ι (pullback.fst G.hom (jK R))) z - _) eθ).trans ?_
      rw [map_nsmul, map_nsmul, smul_smul, add_smul, one_smul, mul_comm t 2, add_sub_cancel_left]))
  exact ⟨L', hL', hI.symm⟩

end GlobalTheory.SymExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelOverCyclotomic
section
noncomputable section

namespace GlobalTheory.HTSympCover

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem exists_galoisCover_of_geom {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] (b : Base D R)
    (N h M : ℕ) (h1 : 1 ≤ h) (hM0 : 0 < M) (hodd : Odd M) (hMp : M.Coprime p)
    (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)) (huniv : HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev)
    (ρ : sympSimGrp h M → (X ⟶ X)) (hρ : SympActs s s₁ u lev ρ) (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t)
    (geo : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), ∃ (t₁ : Sp K ⟶ Sp (cycAway M))
      (lv : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ o.A)), SympCond o h M (Over.mk x) t₁ lv) :
    ∃ (S₁ : Scheme.{0}) (π₁ : S₁ ⟶ S) (ρ₁ : sympSimGrp h M → (S₁ ⟶ S₁)) (y : S₁ ⟶ X) (o' : Obj b N (π₁ ≫ t)),
      GlobalTheory.ZM.IsGaloisCover (sympSimGrp h M) ρ₁ π₁ ∧ (∀ a, ρ₁ a ≫ y = y ≫ ρ a) ∧
      y ≫ s = π₁ ≫ t ∧ Nonempty (ObjMap o' o π₁) ∧ Nonempty (ObjMap o' u y) := by
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨Y, t₁, lu, hYf, hYe, hY⟩ := GlobalTheory.T.exists_finiteEtale_symplecticLevel_scheme p D R b N h M hM0 hMp S t o
  have hAu : SympCond o h M Y t₁ lu := (hY Y t₁ lu).2 ⟨𝟙 Y, by simp, fun a => Category.id_comp _⟩
  have uniqY : ∀ {T : Over S} (f g : T ⟶ Y), f.left ≫ t₁ = g.left ≫ t₁ → (∀ c, f ≫ lu c = g ≫ lu c) → f = g :=
    fun {T} f g e1 e2 => ((hY T (g.left ≫ t₁) (fun c => g ≫ lu c)).1 ((hY T _ _).2 ⟨g, rfl, fun _ => rfl⟩)).unique
      ⟨e1, e2⟩ ⟨rfl, fun _ => rfl⟩
  obtain ⟨o', ⟨m⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N S Y.left t Y.hom o
  have hlift : ∀ c, ∃ g : 𝟙_ (Over Y.left) ⟶ o'.A, g.left ≫ m.φ = (lu c).left := fun c => by
    have w : (lu c).left ≫ o.A.hom = 𝟙 Y.left ≫ Y.hom := by rw [Over.w (lu c), Category.id_comp]
    exact ⟨Over.homMk (m.cart.1.lift (lu c).left (𝟙 Y.left) w) (m.cart.1.lift_snd _ _ _),
      m.cart.1.lift_fst _ _ _⟩
  choose lv' hlv' using hlift
  choose n σ hn hσζ hσs using fun a => (hρ a).2.1
  have hTw : ∀ a, SympCond o h M Y (t₁ ≫ spMap (σ a)) (sympTwist a lu) := fun a =>
    _root_.GlobalTheory.HTSympCover.sympCond_twist p D R b N h M hM0 S t o Y t₁ lu hAu a (n a) (σ a) (hn a) (hσζ a)
  choose r hr using fun a => ((hY Y _ _).1 (hTw a)).exists
  have hlev' : IsSympLev o'.P h M (zetaAway M) t₁ lv' := _root_.GlobalTheory.HTSympCover.isSympLev_of_sympCond_pull p D R b N h M S t o Y t₁ o' m lv' lu hlv' hAu
  have hlevT : ∀ a, IsSympLev o'.P h M (zetaAway M) (t₁ ≫ spMap (σ a)) (sympTwist a lv') := fun a =>
    _root_.GlobalTheory.HTSympCover.isSympLev_of_sympCond_pull p D R b N h M S t o Y (t₁ ≫ spMap (σ a)) o' m (sympTwist a lv') (sympTwist a lu) (fun c => hlv' _) (hTw a)
  obtain ⟨y, ⟨hys, hys₁, my, hmy⟩, -⟩ := huniv Y.left (Y.hom ≫ t) t₁ o' lv' hlev'
  have hdet := (GlobalTheory.SiegelTor.cycAway_galois M (by omega)).2.1
  have hσ1 : σ 1 = RingHom.id _ := hdet _ (σ 1) (RingHom.id _) (by
    rw [hσζ, RingHom.id_apply]
    conv_rhs => rw [← pow_one (zetaAway M)]
    apply zetaAway_pow_eq M (by omega)
    have hm1 : IsMultOf (1 : sympSimGrp h M) 1 := fun x y => by simp
    exact_mod_cast isMultOf_unique h1 (hn 1) hm1)
  have hσmul : ∀ a c, (σ a).comp (σ c) = σ (a * c) := fun a c => hdet _ _ _ (by
    rw [RingHom.comp_apply, hσζ, map_pow, hσζ, hσζ, ← pow_mul]
    apply zetaAway_pow_eq M (by omega)
    have hm : IsMultOf (a * c) (n a * n c) := fun x y => by
      show omegaMod M ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
        ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) x))
        ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
        ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) y)) = _
      rw [hn a, hn c]
      push_cast
      ring
    exact isMultOf_unique h1 hm (hn (a * c)))
  have hsm : ∀ (k : ℕ) w, lu (k • w) = lu w ^ k := by
    have h0 : lu 0 = 1 := by
      have e0 := hAu.1 0 0
      rw [add_zero] at e0
      exact (by simpa using congrArg (· * (lu 0)⁻¹) e0 : (1 : Y ⟶ o.A) = lu 0).symm
    intro k w
    induction k with
    | zero => rw [zero_smul, h0, pow_zero]
    | succ k ih => rw [succ_nsmul, hAu.1, ih, pow_succ]
  have hper : ∀ c, lu (liftMod (reduceMod M c)) = lu c := by
    intro c
    have hw : liftMod (reduceMod M c) = c + M • (fun i => -(c i / M)) := by
      funext i
      simp only [liftMod, reduceMod, ZMod.val_intCast, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply,
        Pi.natCast_apply]
      rw [Int.emod_def]
      ring
    rw [hw, hAu.1, hsm, hAu.2.1, _root_.mul_one]
  have hsp1 : spMap (RingHom.id (cycAway M)) = 𝟙 _ := Spec.map_id _
  have hr1 : r 1 = 𝟙 Y := uniqY _ _ (by rw [(hr 1).1, hσ1, hsp1]; simp) (fun c => by
    rw [(hr 1).2, Category.id_comp]
    exact hper c)
  have hrmul : ∀ a c, r (a * c) = r a ≫ r c := fun a c => uniqY _ _ (by
      rw [(hr _).1, Over.comp_left, Category.assoc, (hr c).1, ← Category.assoc, (hr a).1, Category.assoc,
        ← spMap_comp, hσmul])
    (fun d => by
      rw [(hr _).2, Category.assoc, (hr c).2]
      change sympTwist (a * c) lu d = r a ≫ lu (liftMod
        ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M d)))
      rw [(hr a).2]
      change lu (liftMod (((a * c : sympSimGrp h M) : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
          (reduceMod M d))) = lu (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
          (reduceMod M (liftMod ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
            (reduceMod M d))))))
      rw [reduceMod_liftMod]
      rfl)
  refine ⟨Y.left, Y.hom, fun a => (r a).left, y, o', ⟨sympSimGrp_finite h M, ?_, ?_, ?_, hYf, hYe, ?_, ?_⟩,
    ?_, hys, ⟨m⟩, ⟨my⟩⟩
  · show (r 1).left = _
    rw [hr1]
    rfl
  · intro a c
    show (r (a * c)).left = _
    rw [hrmul]
    rfl
  · intro a
    exact Over.w (r a)
  · refine ⟨fun pt => ?_⟩
    obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point S pt
    obtain ⟨t₀, lv, hlv⟩ := geo k x
    obtain ⟨f, -, -⟩ := (hY (Over.mk x) t₀ lv).1 hlv
    obtain ⟨q, hq⟩ : pt ∈ Set.range x := by rw [hx]; rfl
    exact ⟨f.left q, by rw [← Scheme.Hom.comp_apply, Over.w f]; exact hq⟩
  · intro K _ _ y₁ y₂ h12
    let P1 : Over.mk (y₁ ≫ Y.hom) ⟶ Y := Over.homMk y₁ rfl
    let P2 : Over.mk (y₁ ≫ Y.hom) ⟶ Y := Over.homMk y₂ h12.symm
    have c1 : SympCond o h M (Over.mk (y₁ ≫ Y.hom)) (y₁ ≫ t₁) (fun c => P1 ≫ lu c) :=
      (hY _ _ _).2 ⟨P1, rfl, fun _ => rfl⟩
    have c2 : SympCond o h M (Over.mk (y₁ ≫ Y.hom)) (y₂ ≫ t₁) (fun c => P2 ≫ lu c) :=
      (hY _ _ _).2 ⟨P2, rfl, fun _ => rfl⟩
    obtain ⟨a, ⟨ha1, ha2⟩, hu⟩ := _root_.GlobalTheory.HTSympCover.sympCond_fibre_existsUnique p D R b N h M hM0 hodd h1 σ (fun a => ⟨n a, hn a, hσζ a⟩) S t o K
      (y₁ ≫ Y.hom) _ _ _ _ c1 c2
    refine ⟨a, ?_, fun a' ha' => hu a' ?_⟩
    · have : P1 ≫ r a = P2 := uniqY _ _ (by
          show y₁ ≫ (r a).left ≫ t₁ = y₂ ≫ t₁
          rw [(hr a).1, ← Category.assoc]
          exact ha1)
        (fun c => by rw [Category.assoc, (hr a).2]; exact ha2 c)
      exact congrArg (fun q => q.left) this
    · have e' : P1 ≫ r a' = P2 := Over.OverMorphism.ext ha'
      refine ⟨?_, fun c => ?_⟩
      · rw [Category.assoc, ← (hr a').1, ← Category.assoc]
        exact congrArg (· ≫ t₁) ha'
      · show P1 ≫ lu _ = P2 ≫ lu c
        rw [← e', Category.assoc, (hr a').2]
        rfl
  · exact fun a => _root_.GlobalTheory.HTSympCover.classify_equivariant p D R b N h M X s s₁ u lev huniv ρ hρ σ hσs S t o Y t₁ lu o' m lv' hlv' hlevT y my hmy
      hys hys₁ r (fun a => (hr a).1) (fun a => (hr a).2) a

theorem exists_galoisCover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
  (N M e : ℕ),
  3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e →
  (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin (Module.finrank ℤ D.La / 2) ⊕ Fin (Module.finrank ℤ D.La / 2) → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P (Module.finrank ℤ D.La / 2) M (zetaAway M) s₁ lev →
    HarrisTaylorSymplecticLevelFamilyUniversalProperty b N (Module.finrank ℤ D.La / 2) M s s₁ u lev →
    ∀ ρ : sympSimGrp (Module.finrank ℤ D.La / 2) M → (X ⟶ X), SympActs s s₁ u lev ρ →
    ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t),
      ∃ (S₁ : Scheme.{0}) (π₁ : S₁ ⟶ S) (ρ₁ : sympSimGrp (Module.finrank ℤ D.La / 2) M → (S₁ ⟶ S₁)) (y : S₁ ⟶ X)
        (o' : Obj b N (π₁ ≫ t)),
        GlobalTheory.ZM.IsGaloisCover (sympSimGrp (Module.finrank ℤ D.La / 2) M) ρ₁ π₁ ∧ (∀ a, ρ₁ a ≫ y = y ≫ ρ a) ∧
        y ≫ s = π₁ ≫ t ∧ Nonempty (ObjMap o' o π₁) ∧ Nonempty (ObjMap o' u y) := by
  intro p _ D R _ b N M e _ _ hM hodd hMp _ hMe hperf X s s₁ u lev _ huniv ρ hρ S t o
  have h1 : 1 ≤ Module.finrank ℤ D.La / 2 := by have := D.two_le_finrank_La; omega
  exact exists_galoisCover_of_geom b N _ M h1 (by omega) hodd hMp X s s₁ u lev huniv ρ hρ S t o
    (fun K _ _ x => GlobalTheory.T.exists_symplectic_level_geometric_point_harrisTaylor p D R b N M e hM hodd hMp hMe hperf S t o K x)

end GlobalTheory.HTSympCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoIntegralLogAddInv
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem tendsto_integral_log_add_inv : ∀ (T : Type) [MeasurableSpace T] (μ : Measure T) [IsFiniteMeasure μ] (w : T → ℝ) (C : ℝ), Measurable w → (∀ x, 0 ≤ w x ∧ w x ≤ C) → (∀ᵐ x ∂μ, 0 < w x) → Integrable (fun x => Real.log (w x) / 2) μ → Tendsto (fun n : ℕ => ∫ x, Real.log (w x + 1 / ((n : ℝ) + 1)) ∂μ) atTop (𝓝 (2 * ∫ x, Real.log (w x) / 2 ∂μ)) := by
  intro T _ μ _ w C hw hwC hpos hint
  have hint' : Integrable (fun x => Real.log (w x)) μ := by
    refine (hint.const_mul 2).congr (Eventually.of_forall fun x => ?_)
    simp only; ring
  have hlim : 2 * ∫ x, Real.log (w x) / 2 ∂μ = ∫ x, Real.log (w x) ∂μ := by
    rw [← integral_const_mul]; congr 1; ext x; ring
  rw [hlim]
  refine tendsto_integral_of_dominated_convergence (fun x => |Real.log (w x)| + |Real.log (C + 1)|) ?_ ?_ ?_ ?_
  · intro n
    exact (Real.measurable_log.comp (hw.add_const _)).aestronglyMeasurable
  · exact hint'.abs.add (integrable_const _)
  · intro n
    filter_upwards [hpos] with x hx
    have hd : 0 < 1 / ((n:ℝ) + 1) := by positivity
    have hd1 : 1 / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    have h1 : Real.log (w x) ≤ Real.log (w x + 1 / ((n:ℝ)+1)) := Real.log_le_log hx (by linarith)
    have h2 : Real.log (w x + 1 / ((n:ℝ)+1)) ≤ Real.log (C + 1) :=
      Real.log_le_log (by linarith) (by linarith [(hwC x).2])
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le (Real.log (w x)), abs_nonneg (Real.log (C+1))]
    · linarith [le_abs_self (Real.log (C+1)), abs_nonneg (Real.log (w x))]
  · filter_upwards [hpos] with x hx
    have h : Tendsto (fun n : ℕ => w x + 1 / ((n:ℝ) + 1)) atTop (𝓝 (w x + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h
    exact (Real.continuousAt_log hx.ne').tendsto.comp h

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFixedUnramifiedCompleteTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_fixed_unramified_complete_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → spMap φ (closedPoint V) ∈ W → ∀ n : ℕ, 2 ≤ n → IsUnit (n : V) → ∀ j : ℕ, ∃ (T' : Subring (AlgebraicClosure (FractionRing V))) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v : V, (f v : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ σ : AlgebraicClosure (FractionRing V) ≃+* AlgebraicClosure (FractionRing V), (∀ z ∈ T', σ z = z) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  first | exact @GlobalTheory.UnramTorsPull.torsion_fixed_unramified | exact GlobalTheory.UnramTorsPull.torsion_fixed_unramified | (intros; apply GlobalTheory.UnramTorsPull.torsion_fixed_unramified <;> assumption)
end

