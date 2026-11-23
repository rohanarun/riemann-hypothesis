module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2448
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreConstOfSpecialisationInvariant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory

theorem fibre_exists_finite_generizing {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] [T0Space Z] (q : Y → Z)
    (hq : Continuous q) (z : Z) :
    ∃ T : Set Y, T.Finite ∧ (∀ e ∈ T, q e = z) ∧ ∀ w, q w = z → ∃ e ∈ T, e ⤳ w := by
  have hfin : (irreducibleComponents (q ⁻¹' {z})).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have key : ∀ C : irreducibleComponents (q ⁻¹' {z}),
      ∃ e : Y, q e = z ∧ ∀ c ∈ C.1, e ⤳ (c : Y) := by
    intro C
    have hC : IsIrreducible C.1 := C.2.1
    have hCi : IsIrreducible (((↑) : q ⁻¹' {z} → Y) '' C.1) :=
      hC.image _ continuous_subtype_val.continuousOn
    have hgen := hCi.isGenericPoint_genericPoint_closure
    refine ⟨hCi.genericPoint, ?_, ?_⟩
    · obtain ⟨c, hc⟩ := hC.nonempty
      have hcz : q c = z := c.2
      have h1 : hCi.genericPoint ⤳ (c : Y) := hgen.specializes (subset_closure ⟨c, hc, rfl⟩)
      have h2 : hCi.genericPoint ∈ closure (((↑) : q ⁻¹' {z} → Y) '' C.1) := hgen.mem
      have h3 : closure (((↑) : q ⁻¹' {z} → Y) '' C.1) ⊆ q ⁻¹' closure {z} :=
        (closure_mono (by rintro _ ⟨d, -, rfl⟩; exact d.2)).trans (hq.closure_preimage_subset _)
      have h4 : z ⤳ q hCi.genericPoint := specializes_iff_mem_closure.2 (h3 h2)
      have h5 : q hCi.genericPoint ⤳ z := by
        have := h1.map hq
        rwa [hcz] at this
      exact (h5.antisymm h4).eq
    · intro c hc
      exact hgen.specializes (subset_closure ⟨c, hc, rfl⟩)
  choose f hf using key
  haveI : Finite (irreducibleComponents (q ⁻¹' {z})) := hfin.to_subtype
  refine ⟨Set.range f, Set.finite_range f, ?_, ?_⟩
  · rintro _ ⟨C, rfl⟩
    exact (hf C).1
  · intro w hw
    let w' : q ⁻¹' {z} := ⟨w, hw⟩
    refine ⟨f ⟨_, irreducibleComponent_mem_irreducibleComponents w'⟩, ⟨_, rfl⟩, ?_⟩
    exact (hf _).2 w' mem_irreducibleComponent

theorem fibre_const_of_specializes_invariant : ∀ (Y Z : Type) [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] [T0Space Z] (q : Y → Z), Continuous q → ∀ z : Z, _root_.IsPreconnected (q ⁻¹' {z}) → ∀ P : Y → Prop, (∀ a b, q a = z → q b = z → a ⤳ b → (P a ↔ P b)) → ∀ a b, q a = z → q b = z → P a → P b := by
  intro Y Z _ _ _ _ _ q hq z hpc P hP a b ha hb hPa
  obtain ⟨T, hTf, hTz, hTs⟩ := fibre_exists_finite_generizing q hq z
  by_contra hPb
  have closed : ∀ R : Y → Prop, IsClosed (⋃ e ∈ {e ∈ T | R e}, closure ({e} : Set Y)) :=
    fun R => (hTf.subset (show {e ∈ T | R e} ⊆ T from fun _ h => h.1)).isClosed_biUnion (fun _ _ => isClosed_closure)
  have mem : ∀ (R : Y → Prop) (e w : Y), e ∈ T → R e → e ⤳ w →
      w ∈ ⋃ e ∈ {e ∈ T | R e}, closure ({e} : Set Y) := by
    intro R e w he hR hs
    exact Set.mem_biUnion ⟨he, hR⟩ (specializes_iff_mem_closure.1 hs)
  have mem' : ∀ (R : Y → Prop) (w : Y), w ∈ ⋃ e ∈ {e ∈ T | R e}, closure ({e} : Set Y) →
      ∃ e, e ∈ T ∧ R e ∧ e ⤳ w := by
    intro R w hw
    obtain ⟨e, ⟨he, hR⟩, hc⟩ := Set.mem_iUnion₂.1 hw
    exact ⟨e, he, hR, specializes_iff_mem_closure.2 hc⟩
  obtain ⟨w, hwS, hwt, hwt'⟩ := isPreconnected_closed_iff.1 hpc _ _ (closed P) (closed (fun e => ¬ P e))
    (by
      intro w hw
      obtain ⟨e, he, hs⟩ := hTs w hw
      by_cases h : P e
      · exact Or.inl (mem P e w he h hs)
      · exact Or.inr (mem _ e w he h hs))
    (by
      obtain ⟨e, he, hs⟩ := hTs a ha
      exact ⟨a, ha, mem P e a he ((hP e a (hTz e he) ha hs).2 hPa) hs⟩)
    (by
      obtain ⟨e, he, hs⟩ := hTs b hb
      exact ⟨b, hb, mem (fun e => ¬ P e) e b he (fun h => hPb ((hP e b (hTz e he) hb hs).1 h)) hs⟩)
  have hwz : q w = z := hwS
  obtain ⟨e₁, h₁, hP₁, hs₁⟩ := mem' P w hwt
  obtain ⟨e₂, h₂, hP₂, hs₂⟩ := mem' _ w hwt'
  exact hP₂ ((hP e₂ w (hTz e₂ h₂) hwz hs₂).2 ((hP e₁ w (hTz e₁ h₁) hwz hs₁).1 hP₁))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatKernelSymmetricBirigidifiedBundle
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerFlatP

theorem flat_of_finite_rep : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (B : Over (Sp R)) [GrpObj B],
    IsAbelianScheme B → ∀ N : LB B.left, N.IsLB → Out.RelAmple B N → ∀ M : LB B.left, M.IsLB →
    ∀ (H : Over (Sp R)) (j : H ⟶ B), IsClosedImmersion j.left → IsFinite H.hom →
    (∀ (T : Over (Sp R)) (x : T ⟶ B), GlobalTheory.MemKL B M x ↔ ∃ z : T ⟶ H, z ≫ j = x) → Flat H.hom := by
  intro R _ _ B _ hB N hN hamp M hM H j hj hfin hrep
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  refine _root_.GlobalTheory.flat_of_isFinite_of_flat_localization_maximal R H hfin (fun m _ => ?_)
  set f := spMap (algebraMap R (Localization.AtPrime m)) with hf
  have hB' : IsAbelianScheme ((Over.pullback f).obj B) := GlobalTheory.isAbelianScheme_pullback_obj f B hB
  haveI := hB'.comm
  have hpb := IsPullback.of_hasPullback B.hom f
  obtain ⟨hP, -, -, -⟩ := GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ B N hB hN hamp
    (Localization.AtPrime m) f _ _ _ hpb
  have hML : (M.pull (pullback.fst B.hom f)).IsLB := pull_isLB hM _
  have hrep' := _root_.GlobalTheory.memKL_baseChange_rep _ _ f B M hM H j hrep
  have hth := GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy _root_.GlobalTheory.abelianSchemeLaws_all.1 _ ((Over.pullback f).obj B) hB' hP _ hML
  have hcl : IsClosedImmersion ((Over.pullback f).map j).left := by
    exact MorphismProperty.overPullbackMap (P := @IsClosedImmersion) f j hj
  have hfin' : IsFinite ((Over.pullback f).obj H).hom := by
    first
    | exact MorphismProperty.pullback_snd (P := @IsFinite) _ _ hfin
    | (haveI := hfin; exact (inferInstance : IsFinite (pullback.snd H.hom f)))
  exact _root_.GlobalTheory.StabFlatLocal.flat_of_isFinite hG (Localization.AtPrime m) ((Over.pullback f).obj B) hB' hP _ hML hth _ _ hcl hrep' hfin'

theorem exists_closed_rep : ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B], IsAbelianScheme B →
    ∀ N : LB B.left, N.IsLB → Out.RelAmple B N → ∀ M : LB B.left, M.IsLB →
    ∃ (H : Over (Sp R)) (j : H ⟶ B), IsClosedImmersion j.left ∧
      ∀ (T : Over (Sp R)) (x : T ⟶ B), GlobalTheory.MemKL B M x ↔ ∃ z : T ⟶ H, z ≫ j = x := by
  intro R _ B _ hB N hN hamp M hM
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hP : IsProjBy B.hom := GlobalTheory.WtTower.isProjBy_of_relAmple B hN hamp
  obtain ⟨h0, -, h2⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B M hM
  obtain ⟨H, j, hj, hrep⟩ := _root_.GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hG R B hB hP M (AbLaw.pw M 0) hM h0
  refine ⟨H, j, hj, fun T x => ?_⟩
  rw [← GlobalTheory.UU.inK_iff_memKL, h2 _ rfl T x]
  exact hrep T x

private theorem isFinite_of_closedImmersion_factor_through_finite {S : Scheme.{0}} {H F G : Over S} (j : H ⟶ G) (i : F ⟶ G)
    (m : H ⟶ F) (hm : m ≫ i = j) (hj : IsClosedImmersion j.left) (hF : IsFinite F.hom) : IsFinite H.hom := by
  haveI : IsSeparated (i.left ≫ G.hom) := by rw [Over.w i]; infer_instance
  haveI : IsSeparated i.left := IsSeparated.of_comp i.left G.hom
  haveI : IsClosedImmersion (m.left ≫ i.left) := by rw [← Over.comp_left, hm]; exact hj
  haveI : IsClosedImmersion m.left := IsClosedImmersion.of_comp m.left i.left
  rw [← Over.w m]; infer_instance

end GlobalTheory.KerFlatP

namespace GlobalTheory


open GlobalTheory.KerFlatP in
theorem kernel_finiteFlat : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G2 G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → Out.RelAmple G (P.pull (lift (𝟙 G) (𝟙 G)).left) → ∃ (H : Over (Sp R)) (i : H ⟶ G), IsClosedImmersion i.left ∧ IsFinite H.hom ∧ Flat H.hom ∧ ∀ (T : Over (Sp R)) (x : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) ↔ ∃ y : T ⟶ H, y ≫ i = x := by
  intro R _ _ G _ hG P hP h1 h2 hsym hamp
  have hL : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  obtain ⟨HL, _, iL, -, -, hfinL, -, hrepL⟩ := GlobalTheory.kernel_finiteFlat_subgroup R G hG _ hL hamp
  have hGG : IsAbelianScheme (G ⊗ G) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor G G hG hG
  haveI : IsProper G.hom := hG.proper
  haveI : IsProper (G ⊗ G).hom := by
    show IsProper (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  have hL1 := pull_isLB hL (fst G G).left
  have hL2 := pull_isLB hL (snd G G).left
  have hN := GlobalTheory.CechPic.isLB_tens hL1 hL2
  have hNamp : Out.RelAmple (G ⊗ G) (GlobalTheory.CechPic.tens _ _) :=
    GlobalTheory.MumProd.SumPol.relAmple_prod G G hL hL hN
      (by rw [GlobalTheory.CechPic.cls_tens hL1 hL2 hN, GlobalTheory.CechPic.cls_pull hL _ hL1, GlobalTheory.CechPic.cls_pull hL _ hL2])
      hamp hamp

  obtain ⟨K, k, hk, hrepK⟩ := exists_closed_rep R (G ⊗ G) hGG _ hN hNamp P hP

  have hmemK : GlobalTheory.MemKL (G ⊗ G) P (lift (k ≫ fst G G) (k ≫ snd G G)) := by
    rw [lift_comp_fst_snd]; exact (hrepK K k).2 ⟨𝟙 K, Category.id_comp _⟩
  obtain ⟨ha, hb⟩ := _root_.GlobalTheory.KerAxes.triv_of_memKL_pair R G hG P hP h1 h2 hsym K _ _ hmemK
  obtain ⟨za, hza⟩ := (hrepL K _).1 (_root_.GlobalTheory.AbDual.memKL_diag_of_triv_ev_of_symm R G hG P hP h1 h2 hsym K _ ha)
  obtain ⟨zb, hzb⟩ := (hrepL K _).1 (_root_.GlobalTheory.AbDual.memKL_diag_of_triv_ev_of_symm R G hG P hP h1 h2 hsym K _ hb)
  have hfinHL2 : IsFinite (HL ⊗ HL).hom := by
    haveI := hfinL
    show IsFinite (pullback.fst HL.hom HL.hom ≫ HL.hom)
    infer_instance
  have hfinK : IsFinite K.hom := by
    refine isFinite_of_closedImmersion_factor_through_finite k (lift (fst HL HL ≫ iL) (snd HL HL ≫ iL)) (lift za zb) ?_ hk hfinHL2
    apply CartesianMonoidalCategory.hom_ext <;> simp [hza, hzb]
  have hflatK : Flat K.hom := flat_of_finite_rep R (G ⊗ G) hGG _ hN hNamp P hP K k hk hfinK hrepK

  set e : G ⟶ G ⊗ G := lift (𝟙 G) (1 : G ⟶ G) with he
  have hxe : ∀ {T : Over (Sp R)} (x : T ⟶ G), x ≫ e = lift x (1 : T ⟶ G) := by
    intro T x
    apply CartesianMonoidalCategory.hom_ext <;> simp [e]
  let H : Over (Sp R) := Over.mk (pullback.snd k.left e.left ≫ G.hom)
  let i : H ⟶ G := Over.homMk (pullback.snd k.left e.left) rfl
  haveI := hk
  have hi : IsClosedImmersion i.left := by
    show IsClosedImmersion (pullback.snd k.left e.left)
    infer_instance
  have hwK : pullback.fst k.left e.left ≫ K.hom = H.hom := by
    show _ = pullback.snd k.left e.left ≫ G.hom
    rw [← Over.w k, pullback.condition_assoc, Over.w e]
  let s : H ⟶ K := Over.homMk (pullback.fst k.left e.left) hwK
  have hs : s ≫ k = i ≫ e :=
    Over.OverMorphism.ext (by rw [Over.comp_left, Over.comp_left]; exact pullback.condition)
  have hmemH : ∀ (T : Over (Sp R)) (x : T ⟶ G),
      (∃ t : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) ↔ ∃ y : T ⟶ H, y ≫ i = x := by
    intro T x
    constructor
    · intro htr
      obtain ⟨z, hz⟩ := (hrepK T _).1 (_root_.GlobalTheory.AbDual.memKL_lift_one_of_triv_ev R G hG P hP h1 h2 hsym T x htr)
      have hz' : z.left ≫ k.left = x.left ≫ e.left := by
        rw [← Over.comp_left, hz, ← hxe, Over.comp_left]
      refine ⟨Over.homMk (pullback.lift z.left x.left hz') ?_, ?_⟩
      · show pullback.lift z.left x.left hz' ≫ pullback.snd k.left e.left ≫ G.hom = T.hom
        rw [pullback.lift_snd_assoc, Over.w x]
      · exact Over.OverMorphism.ext (by rw [Over.comp_left]; exact pullback.lift_snd _ _ _)
    · rintro ⟨y, rfl⟩
      have hm : GlobalTheory.MemKL (G ⊗ G) P (lift (y ≫ i) (1 : T ⟶ G)) := by
        refine (hrepK T _).2 ⟨y ≫ s, ?_⟩
        rw [Category.assoc, hs, ← Category.assoc, hxe]
      exact (_root_.GlobalTheory.KerAxes.triv_of_memKL_pair R G hG P hP h1 h2 hsym T _ _ hm).1

  have hLi : GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) i :=
    _root_.GlobalTheory.AbDual.memKL_diag_of_triv_ev_of_symm R G hG P hP h1 h2 hsym H i ((hmemH H i).2 ⟨𝟙 H, Category.id_comp _⟩)
  obtain ⟨zH, hzH⟩ := (hrepL H i).1 hLi
  have hfinH : IsFinite H.hom := isFinite_of_closedImmersion_factor_through_finite i iL zH hzH hi hfinL

  obtain ⟨r, hr⟩ := (hmemH K (k ≫ fst G G)).1 ha
  have hsr : s ≫ r = 𝟙 H := by
    haveI : Mono i.left := by
      show Mono (pullback.snd k.left e.left)
      infer_instance
    have h3 : s ≫ r ≫ i = 𝟙 H ≫ i := by
      rw [hr, ← Category.assoc, hs, Category.assoc]; simp [e]
    apply Over.OverMorphism.ext
    exact (cancel_mono i.left).1 (by simpa [Over.comp_left] using congrArg CommaMorphism.left h3)
  exact ⟨H, i, hi, hfinH, GlobalTheory.T.flat_of_finite_retract_of_finite_flat R H K s r hsr hfinH hfinK hflatK, hmemH⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGenerationIntegralFamilySections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem finFam_finite : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsLocallyNoetherian S] {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)), (⨆ i, V i) = ⊤ →
    (∀ i, ∀ y ∈ t i, (gp.app (V i)).hom.IsIntegralElem y) → ∀ W : S.Opens, IsAffineOpen W →
    ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ W), (∀ y ∈ s, y ∈ finFam gp V t W) ∧
      ∀ x ∈ finFam gp V t W, ∃ c : Γ(Sp K, gp ⁻¹ᵁ W) → Γ(S, W), x = ∑ y ∈ s, (gp.app W).hom (c y) * y := by
  first
  | exact @_root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite
  | exact _root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite
  | (apply _root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite ..)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIntegerRingActionsPrincipallyPolarisedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_integerRing_actions_principallyPolarised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K)), letI := H.starRing; Set.Finite {act : 𝓞 E → (P.A ⟶ P.A) | ∃ ρ : P.OAct (𝓞 E), ∀ a, ρ.act a = act a} := by
  first | exact @GlobalTheory.UMin.FinAct.finite_oActs | exact GlobalTheory.UMin.FinAct.finite_oActs | (intros; apply GlobalTheory.UMin.FinAct.finite_oActs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMorphismValuativeLiftingNormalDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory

theorem finite_lift_fractionField (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (Z P : Scheme.{0}) (p : Z ⟶ P) (ξ₀ : Sp R ⟶ P) (y : Sp (FractionRing R) ⟶ Z)
    (hp : IsFinite p) (hy : y ≫ p = jK R ≫ ξ₀) :
    ∃ ξ : Sp R ⟶ Z, jK R ≫ ξ = y ∧ ξ ≫ p = ξ₀ := by
  first
  | exact @_root_.GlobalTheory.RetractionLiftSection.lift_finite
  | exact _root_.GlobalTheory.RetractionLiftSection.lift_finite
  | (apply _root_.GlobalTheory.RetractionLiftSection.lift_finite <;> assumption)
  | (intros; apply _root_.GlobalTheory.RetractionLiftSection.lift_finite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RetractionLiftSection.lift_finite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RetractionLiftSection.lift_finite ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStalkGermQuotientIntegralUnitDenominator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem GlobalTheory.Poinc.finite_stalk_quot_integral : ∀ (X Y : Scheme.{0}) (p : Y ⟶ X), IsFinite p → ∀ (y : Y) (a : Y.presheaf.stalk y), ∃ b s : Y.presheaf.stalk y, IsUnit s ∧ a * s = b ∧ (∃ P : Polynomial (X.presheaf.stalk (p y)), P.Monic ∧ P.eval₂ (p.stalkMap y).hom b = 0) ∧ ∃ Q : Polynomial (X.presheaf.stalk (p y)), Q.Monic ∧ Q.eval₂ (p.stalkMap y).hom s = 0 := by
  intro X Y p hp y a
  obtain ⟨U, hU', hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := p y) trivial
  have hV : IsAffineOpen (p ⁻¹ᵁ U) := hU'.preimage p
  have hyV : y ∈ p ⁻¹ᵁ U := hyU
  letI : Algebra Γ(Y, p ⁻¹ᵁ U) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk ⟨y, hyV⟩
  haveI := hV.isLocalization_stalk ⟨y, hyV⟩
  obtain ⟨⟨c, t⟩, hct⟩ := IsLocalization.mk'_surjective (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl a
  have hfin : (p.app U).hom.Finite := p.finite_app U hU'
  have hint := hfin.to_isIntegral
  have key : ∀ z : Γ(Y, p ⁻¹ᵁ U), ∃ P : Polynomial (X.presheaf.stalk (p y)), P.Monic ∧
      P.eval₂ (p.stalkMap y).hom (algebraMap Γ(Y, p ⁻¹ᵁ U) (Y.presheaf.stalk y) z) = 0 := by
    intro z
    obtain ⟨P', hm, hP'⟩ := hint z
    refine ⟨P'.map (X.presheaf.germ U (p y) hyU).hom, hm.map _, ?_⟩
    have hc : (p.stalkMap y).hom.comp (X.presheaf.germ U (p y) hyU).hom
        = (Y.presheaf.germ (p ⁻¹ᵁ U) y hyV).hom.comp (p.app U).hom := by
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap]
    rw [Polynomial.eval₂_map, hc]
    change Polynomial.eval₂ _ ((Y.presheaf.germ (p ⁻¹ᵁ U) y hyV).hom z) P' = 0
    rw [← Polynomial.hom_eval₂, hP', map_zero]
  refine ⟨algebraMap _ _ c, algebraMap _ _ (t : Γ(Y, p ⁻¹ᵁ U)), IsLocalization.map_units _ t, ?_, key c, key t⟩
  rw [← hct]
  exact IsLocalization.mk'_spec _ c t
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeFderivLtOfNotDominantCharts
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

theorem finrank_range_fderiv_lt_of_not_dominant : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (A : FinHolAtlas D (CxPts p σ)) (A' : FinHolAtlas D (CxPts q σ)), IsAlgAtlas A → IsAlgAtlas A' → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) ≠ genericPoint X → ∀ j l, ∀ y ∈ (A'.chart j).target, PtsOver.map π hπ (spMap σ) ((A'.chart j).symm y) ∈ (A.chart l).source → Module.finrank ℂ (LinearMap.range (fderiv ℂ (A.chart l ∘ PtsOver.map π hπ (spMap σ) ∘ (A'.chart j).symm) y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) < D := by
  intro k _ X Y _ _ p q σ D A A' hA hA' π hπ hgen j l y hy hyl
  set m := PtsOver.map π hπ (spMap σ) with hm_def
  have hm : ∀ z : CxPts q σ, (m z).1 = z.1 ≫ π := fun _ => rfl
  have hH := hA.holoMap hA' (f := π) hm
  set W := (A'.chart j).target ∩ (A'.chart j).symm ⁻¹' (m ⁻¹' (A.chart l).source) with hW_def
  have hWo : IsOpen W := (A'.chart j).isOpen_inter_preimage_symm
    ((A.chart l).open_source.preimage hH.1)
  have han : AnalyticOnNhd ℂ (A.chart l ∘ m ∘ (A'.chart j).symm) W := hH.2 j l
  set Z : Set X := closure {π (genericPoint Y)} with hZ_def
  have hZc : IsClosed Z := isClosed_closure
  have hZg : genericPoint X ∉ Z := by
    intro h
    have h1 : π (genericPoint Y) ⤳ genericPoint X := specializes_iff_mem_closure.2 h
    have h2 : genericPoint X ⤳ π (genericPoint Y) := genericPoint_specializes _
    exact hgen (h1.antisymm h2).eq
  have hZm : ∀ z : CxPts q σ, (m z).1 (IsLocalRing.closedPoint ℂ) ∈ Z := by
    intro z
    have hs : genericPoint Y ⤳ z.1 (IsLocalRing.closedPoint ℂ) := genericPoint_specializes _
    have := hs.map π.continuous
    rw [hm]
    exact specializes_iff_mem_closure.1 this
  obtain ⟨c, hc⟩ := hA l
  have hnull := _root_.GlobalTheory.ChernNull.chart_null_field k X p σ D Z hZc hZg c
  have hsub : (A.chart l ∘ m ∘ (A'.chart j).symm) '' W ⊆
      FinChart.toV D ⁻¹' (c.e '' (c.e.source ∩ {x : CxPts p σ | x.1 (IsLocalRing.closedPoint ℂ) ∈ Z})) := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨m ((A'.chart j).symm z), ⟨?_, hZm _⟩, ?_⟩
    · have := hz.2
      rw [hc] at this
      exact this
    · simp only [Function.comp_apply, hc]
      rfl
  have h0 : volume ((A.chart l ∘ m ∘ (A'.chart j).symm) '' W) = 0 :=
    measure_mono_null hsub (FinChart.measurePreserving_toV.quasiMeasurePreserving.preimage_null hnull)
  exact finrank_range_fderiv_lt_of_volume_image_eq_zero D _ W hWo han h0 y ⟨hy, hyl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusCanonicalLiftPrimitiveHodgeStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_primitiveSubmodule_of_isCan_of_rigToExt_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (x : G.RigExt),
      GlobalTheory.PtExt.IsCan t c x → G.rigToExt x = 0 → c ∈ PrimitiveSubmodule A :=
  @GlobalTheory.PtExt.mem_F1prim_of_rigToExt_eq_zero_of_pow_eq_zero
end

