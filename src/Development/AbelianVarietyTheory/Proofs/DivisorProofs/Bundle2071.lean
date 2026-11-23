module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRingHomLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1812
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1807
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealMultiplicationUniformization
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace GlobalTheory.RealMultChart

theorem comp_mulN {S : Scheme.{0}} (B : Over S) [GrpObj B] {T : Over S} (x : T ⟶ B) (n : ℕ) :
    x ≫ mulN B n = x ^ n := by
  induction n with
  | zero =>
    show x ≫ (toUnit B ≫ η[B]) = x ^ 0
    rw [pow_zero, Hom.one_def, ← Category.assoc, toUnit_unique (x ≫ toUnit B) (toUnit T)]
  | succ n ih =>
    show x ≫ (lift (mulN B n) (𝟙 B) ≫ μ[B]) = x ^ (n + 1)
    rw [pow_succ, Hom.mul_def, ← ih, ← Category.assoc, comp_lift, Category.comp_id]

theorem mulN_eq_mulA {S : Scheme.{0}} (B : Over S) [GrpObj B] (n : ℕ) : mulN B n = Out.mulA B n := by
  have h1 := comp_mulN B (𝟙 B) n
  rw [Category.id_comp] at h1
  rw [h1]

theorem exists_pow_eq (B : Over (Sp ℂ)) [GrpObj B] (hB : IsAbelianScheme B) (a₀ : 𝟙_ (Over (Sp ℂ)) ⟶ B)
    (n : ℕ) (hn : n ≠ 0) : ∃ b : 𝟙_ (Over (Sp ℂ)) ⟶ B, b ^ n = a₀ := by
  have hn' : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hsurj : Surjective (mulN B n).left := surjective_mulN_of_isAbelianScheme ℂ B hB n hn'
  have hfin : IsFinite (mulN B n).left := by
    rw [mulN_eq_mulA]
    exact MulFiniteAny.isFinite_mulA ℂ B hB n (Nat.one_le_iff_ne_zero.2 hn)
  obtain ⟨t, ht⟩ := H1.SectionDivision.exists_section (pullback.snd (mulN B n).left a₀.left)
  have hb' : (t ≫ pullback.fst (mulN B n).left a₀.left) ≫ (mulN B n).left = a₀.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
  have hw : (t ≫ pullback.fst (mulN B n).left a₀.left) ≫ B.hom = (𝟙_ (Over (Sp ℂ))).hom := by
    rw [← Over.w (mulN B n), ← Category.assoc, hb', Over.w a₀]
  refine ⟨Over.homMk _ hw, ?_⟩
  rw [← comp_mulN]
  exact Over.OverMorphism.ext hb'

theorem compactSpace_points (A : Over (Sp ℂ)) (L : LB A.left) (hL : Out.RelAmple A L) :
    @CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) (PointsCompact.pointTopology A) := by
  have h1 : PointsCompact.ValueRules := valAt'_rules
  have h2 : PointsCompact.AffinePoints := existsUnique_point_of_ringHom
  obtain ⟨N, -, M, s, hcov, H⟩ := hL ⊤ (isAffineOpen_top _)
  let Y : Over (Sp ℂ) := Over.mk ((A.hom ∣_ ⊤) ≫ (⊤ : (Sp ℂ).Opens).ι)
  let φ : Y ⟶ A := Over.homMk (A.hom ⁻¹ᵁ ⊤).ι (morphismRestrict_ι A.hom ⊤).symm
  let c₀ : ℂ →+* Γ((⊤ : (Sp ℂ).Opens).toScheme, ⊤) :=
    ((⊤ : (Sp ℂ).Opens).ι.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hc₀ : Function.Surjective c₀ := by
    have : IsIso (⊤ : (Sp ℂ).Opens).ι := inferInstanceAs (IsIso (Sp ℂ).topIso.hom)
    exact (ConcreteCategory.bijective_of_isIso ((⊤ : (Sp ℂ).Opens).ι.app ⊤)).2.comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2
  have hY : @CompactSpace _ (PointsCompact.pointTopology Y) := by
    refine PointsCompact.compact_of_sections h1 h2 Y (Out.powOver A L ⊤ N) s hcov fun i => ⟨(H i).1, ?_⟩
    obtain ⟨r, hr, hs⟩ := (H i).2
    refine ⟨r, hr, ((A.hom ∣_ ⊤).appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom.comp c₀,
      fun a => ?_, fun f => ?_⟩
    · have := Scheme.Hom.comp_appLE (A.hom ∣_ ⊤) (⊤ : (Sp ℂ).Opens).ι ⊤
        (Out.nonzeroLocus (s i)) le_top
      exact (congrArg (fun u => u.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) this).symm
    · obtain ⟨p, rfl⟩ := hs f
      obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective c₀ hc₀ p
      exact ⟨q, (MvPolynomial.eval₂_map c₀ r _ q).symm⟩
  letI := PointsCompact.pointTopology Y
  letI := PointsCompact.pointTopology A
  have hsurj : Function.Surjective fun x : 𝟙_ (Over (Sp ℂ)) ⟶ Y => x ≫ φ := by
    intro x
    have hrange : Set.range x.left ⊆ Set.range (A.hom ⁻¹ᵁ ⊤).ι := by
      rw [Scheme.Opens.range_ι]
      intro _ _
      trivial
    have hl := IsOpenImmersion.lift_fac (A.hom ⁻¹ᵁ ⊤).ι x.left hrange
    refine ⟨Over.homMk (IsOpenImmersion.lift (A.hom ⁻¹ᵁ ⊤).ι x.left hrange) ?_, ?_⟩
    · have := Over.w x
      rw [← hl, Category.assoc, ← morphismRestrict_ι] at this
      exact this
    · ext1
      exact hl
  exact hsurj.compactSpace (PointsCompact.continuous_comp h1 φ)

def trivLB (A : Over (Sp ℂ)) : LB A.left := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩


open AbelianExp in
theorem exists_holUnif_of_compact (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ)
    (hs : SmoothOfRelativeDimension g A.hom)
    (hcpt : @CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) (PointsCompact.pointTopology A))
    (hdiv : ∀ (a : 𝟙_ (Over (Sp ℂ)) ⟶ A) (n : ℕ), n ≠ 0 → ∃ b, b ^ n = a) :
    Nonempty (HolUnif A (trivLB A) g) := by
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  have hprod := @holFamily_lift hval
  have hchart := HolChart.exists_holomorphic_chart hval hvalaff exists_holomorphic_section_of_etale
  letI := pointTopology A
  have := isTopologicalGroup_complexPoints hval A
  have : CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) := hcpt
  have hpost := fun X x => (hval X x).2.2.2.1
  have hmulHol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E)
      (a b : E → (𝟙_ (Over (Sp ℂ)) ⟶ A)), HolOn W a → HolOn W b → HolOn W fun w => a w * b w :=
    fun E _ _ W a b ha hb => HolOn.post hpost (hprod E W _ _ a b ha hb) μ[A]
  obtain ⟨W, σ, U, t, hW, h0, hσ0, hU, hσ, ht, ho, hD⟩ := hchart A g hs 1
  let φ : OpenPartialHomeomorph (Additive (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Fin g → ℂ) :=
    chart t hW hσ ht ho
  have hU1 : ⊤ ≤ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left ⁻¹ᵁ U := hσ0 ▸ (ht 0 h0).1
  have hφ : IsAnalyticGroupChart φ := by
    refine ⟨⟨0, h0, hσ0⟩, funext fun i => ?_, ?_⟩
    · have := (ht 0 h0).2 i
      rwa [hσ0] at this
    · have hH := hmulHol _ (W ×ˢ W) _ _
        (HolOn.comp hσ (hW.prod hW) differentiableOn_fst fun p hp => hp.1)
        (HolOn.comp hσ (hW.prod hW) differentiableOn_snd fun p hp => hp.2)
      refine hH.analyticAt t (w := 0) ⟨h0, h0⟩ ?_
      simpa only [Prod.fst_zero, Prod.snd_zero, hσ0, _root_.mul_one] using hU1
  have hsurj : Function.Surjective hφ.exp := hφ.exp_surjective fun n hn x => hdiv x.toMul n hn
  obtain ⟨W', L, hW', h0', hL, hLm, hLe⟩ : ∃ (W' : Set (Fin g → ℂ))
      (L : (Fin g → ℂ) → (Fin g → ℂ)), IsOpen W' ∧ 0 ∈ W' ∧ DifferentiableOn ℂ L W' ∧
      Set.MapsTo L W' W ∧ ∀ᶠ v in 𝓝 0, (hφ.exp v).toMul = σ (L v) := by
    have ha := hφ.isLocalCommGroupLaw.analyticAt_logChart_symm
    have h1 : ∀ᶠ v in 𝓝 0, hφ.isLocalCommGroupLaw.logChart.symm v ∈ W :=
      ha.continuousAt.eventually (hW.mem_nhds (by simpa using h0))
    obtain ⟨W', h2, h3, h4⟩ := eventually_nhds_iff.mp (ha.eventually_analyticAt.and h1)
    exact ⟨W', _, h3, h4, fun v hv => (h2 v hv).1.differentiableAt.differentiableWithinAt,
      fun v hv => (h2 v hv).2, hφ.exp_eventuallyEq⟩
  refine ⟨⟨fun v => (hφ.exp v).toMul, fun z w => congrArg Additive.toMul (hφ.exp.map_add z w), hsurj,
    hφ.periodLattice, fun z => Iff.rfl, inferInstance, hφ.isZLattice_periodLattice.span_top,
    HolOn.of_local fun z => ?_, fun _ _ => 1, fun _ => differentiableOn_const _,
    fun _ _ _ => one_ne_zero, fun i j z hz => ?_⟩⟩
  · have hs : Continuous fun v : Fin g → ℂ => v - z := continuous_sub_right z
    have hWz : IsOpen ((fun v => v - z) ⁻¹' W') := hW'.preimage hs
    refine ⟨(fun v => v - z) ⁻¹' W', fun v => (hφ.exp z).toMul * σ (L (v - z)), by simpa using h0',
      hmulHol _ _ _ _ (HolOn.const hWz _) (HolOn.comp (HolOn.comp hσ hW' hL hLm) hWz
        (differentiableOn_id.sub_const z) fun v hv => hv), ?_⟩
    filter_upwards [(hs.tendsto' z 0 (sub_self z)).eventually hLe] with v hv
    rw [← hv, ← toMul_add, ← map_add (f := _), add_sub_cancel]
  · obtain ⟨e, he⟩ := (hval _ _).2.1 _ hz
    rw [he]
    show (1 : ℂ) = e (((1 : Γ(A.left, ⊤ ⊓ ⊤)ˣ)) : Γ(A.left, ⊤ ⊓ ⊤)) * 1
    rw [Units.val_one]
    exact ((_root_.mul_one _).trans e.map_one).symm

end GlobalTheory.RealMultChart

namespace GlobalTheory.RealMult


end GlobalTheory.RealMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularKodairaSpencerCoordinateAffineOffBo
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CompHS
open CategoryTheory AlgebraicGeometry TopologicalSpace _root_.CategoryTheory.Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open scoped Classical
open GlobalTheory.AllWt (exOf)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw))

theorem glue_field_cover {Z : Scheme.{0}} [IsReduced Z] (V : Z.Opens)
    (R : ∀ (L : Type) [Field L], (Sp L ⟶ Z) → L → Prop)
    (loc : ∀ p ∈ V, ∃ (W : Z.Opens) (a : Γ(Z, W)), p ∈ W ∧ W ≤ V ∧
      (∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ W), R L z (ev z W hz a)) ∧
      ∀ (L : Type) [Field L] (z : Sp L ⟶ Z), ⊤ ≤ z ⁻¹ᵁ W → ∀ x y, R L z x → R L z y → x = y) :
    ∃ a : Γ(Z, V), ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), R L z (ev z V hz a) := by
  choose! W a hp hWV ha hu using loc
  let I := {p // p ∈ V}
  have hc : ∀ p ∈ V, ∃ i : I, p ∈ W i.1 := fun p h => ⟨⟨p, h⟩, hp p h⟩
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => W i.1) V (fun i => homOfLE (hWV i.1 i.2))
    (fun p h => TopologicalSpace.Opens.mem_iSup.2 (hc p h)) (fun i => a i.1) (fun i j => by
      refine GlobalTheory.FlagMod.ext_ev_field (a := resG Z inf_le_left (a i.1)) (b := resG Z inf_le_right (a j.1)) fun L _ z hz => ?_
      have hi := le_preimage_mono inf_le_left hz
      have hj := le_preimage_mono inf_le_right hz
      rw [GlobalTheory.FlagMod.ev_res z _ hz hi, GlobalTheory.FlagMod.ev_res z _ hz hj]
      exact hu i.1 i.2 L z hi _ _ (ha i.1 i.2 L z hi) (ha j.1 j.2 L z hj))
  refine ⟨s, fun L _ z hz => ?_⟩
  obtain ⟨i, hi⟩ := hc (z (IsLocalRing.closedPoint L)) (hz (Set.mem_univ _))
  have hi' : ⊤ ≤ z ⁻¹ᵁ W i.1 := ((IsLocalRing.closed_point_mem_iff (U := z ⁻¹ᵁ W i.1)).1 hi).ge
  have e : ev z V hz s = ev z (W i.1) hi' (a i.1) :=
    (GlobalTheory.FlagMod.ev_res z (hWV i.1 i.2) hi' hz s).symm.trans (congrArg _ (hs i))
  exact e ▸ ha i.1 i.2 L z hi'

theorem exists_local (hP : GlobalTheory.Published.AbelianDeRham)
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    (i : M.K.bundle.ι) (k : X.F.J) (W : M.X.Opens) (hW : W ≤ ksOpen M i k) (p : M.X) (hp : p ∈ W) :
    ∃ (W' : M.X.Opens) (a : Γ(M.X, W')), p ∈ W' ∧ W' ≤ W ∧
      (∀ (L : Type) [Field L] (z : Sp L ⟶ M.X) (hz : ⊤ ≤ z ⁻¹ᵁ W'), KSRel M i k z (ev z W' hz a)) ∧
      ∀ (L : Type) [Field L] (z : Sp L ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ W' → ∀ x y, KSRel M i k z x → KSRel M i k z y → x = y := by
  have hWk : ksOpen M i k ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k := fun s hs =>
    ⟨hs.1, (((common₀ X Z).pull M.σ).mem _ _ _).1 hs.2.2⟩
  have hWi : ksOpen M i k ≤ M.K.bundle.U i := fun s hs => hs.2.1
  obtain ⟨V, f, hpV, hf⟩ := exists_isFrame_dOn M.str (dimFlag Dw) p
  obtain ⟨W₁, hW₁, hpW₁, hW₁V⟩ := Opens.isBasis_iff_nbhd.1 M.X.isBasis_affineOpens (show p ∈ W ⊓ V from ⟨hp, hpV⟩)
  obtain ⟨W', hW', eH, hpW', hWW', eH1, eH2⟩ := _root_.GlobalTheory.HorFrame.exists_horizontal_lift M hP hKS k W₁
    ((hW₁V.trans inf_le_left).trans (hW.trans hWk)) p hpW₁
  have hWV : W' ≤ W := hWW'.trans (hW₁V.trans inf_le_left)
  have hW'k : W' ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k := hWV.trans (hW.trans hWk)
  have hW'i : W' ≤ M.K.bundle.U i := hWV.trans (hW.trans hWi)
  obtain ⟨eV, eV1, eV2⟩ := GlobalTheory.T.exists_ringMaps_lift_vertical_deformations_affine M k W' hW' hW'k
  let e : TIx Dw (psiSet H) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W')) := Sum.elim eH eV
  have e1 : ∀ b s, (e b s).fst = s := by
    rintro (b | b) s
    · exact eH1 b s
    · exact eV1 b s

  have e2 : ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W') →+* K)
      (hk : ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
      X.F.ChartFr k _ hk Q → ∃ v, IsTanFrame (psiSet H) Q v ∧
        ∀ b, spMap ((dualMap ψ).comp (e b)) ≫ tau hW' ≫ toFlag M = X.ptY (v b) := by
    intro K _ _ ψ hk Q hQ
    choose w₁ hw₁ hw₁' hw₁'' using eH2 K ψ hk Q hQ
    choose w₂ hw₂ hw₂' using eV2 K ψ hk Q hQ
    refine ⟨Sum.elim w₁ w₂, ⟨fun b => ⟨hw₁ b, hw₁' b⟩, fun b => hw₂ b⟩, ?_⟩
    rintro (b | b)
    · exact hw₁'' b
    · exact hw₂' b
  let g : Fin (dimFlag Dw) → Γ(M.X, W') := fun a => resG M.X (hWW'.trans (hW₁V.trans inf_le_right)) (f a)
  have hu : IsUnit (M.K.jacobian i hW'i g) := (M.K.isUnit_jacobian_iff i hW' hW'i g).2 (by
    have := hf.res hW' (hWW'.trans (hW₁V.trans inf_le_right))
    rwa [resForm_dOn] at this)
  let A : Matrix (Fin (dimFlag Dw)) (Fin (dimFlag Dw)) Γ(M.X, W') :=
    Matrix.of fun a b => (e (tanOrd Dw b) (g a)).snd

  let zv : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X) :=
    fun ψ b => spMap ((dualMap ψ).comp (e b)) ≫ tau hW'
  have hzvW : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K) b, ⊤ ≤ zv ψ b ⁻¹ᵁ W' := fun ψ b =>
    le_preimage_comp _ (tau_le hW' le_rfl)
  have hred : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K) b,
      spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ zv ψ b = spMap ψ ≫ tau hW' := fun {K} _ ψ b => by
    simp only [zv]
    rw [← Category.assoc, ← spMap_comp]
    congr 2
    ext s
    simp [dualMap, e1]
  have hev : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K) a b,
      (evalPt (zv ψ b) W' (hzvW ψ b) (g a)).snd = ψ (e b (g a)).snd := fun ψ a b => by
    have := ev_spMap_tau hW' ((dualMap ψ).comp (e b)) (hzvW ψ b)
    have h2 : evalPt (zv ψ b) W' (hzvW ψ b) (g a) = ((dualMap ψ).comp (e b)) (g a) := congrFun (congrArg DFunLike.coe this) _
    rw [h2]
    simp [dualMap]
  have hdet : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K),
      (Matrix.of fun a b => (evalPt (zv ψ (tanOrd Dw b)) W' (hzvW ψ _) (g a)).snd).det = ψ A.det := fun ψ => by
    rw [RingHom.map_det]
    congr 1
    ext a b
    exact hev ψ a _
  have hzW : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ⊤ ≤ (spMap ψ ≫ tau hW') ⁻¹ᵁ W' := fun ψ =>
    le_preimage_comp _ (tau_le hW' le_rfl)
  have ho : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ⊤ ≤ (spMap ψ ≫ tau hW') ⁻¹ᵁ M.off := fun ψ =>
    le_preimage_comp _ (tau_le hW' (hW'k.trans inf_le_left))
  have hkk : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ X.F.U k :=
    fun ψ => by
      show ⊤ ≤ (spMap ψ ≫ tau hW') ⁻¹ᵁ (toFlag M ⁻¹ᵁ X.F.U k)
      exact le_preimage_comp _ (tau_le hW' (hW'k.trans inf_le_right))
  have chart : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ∃ (_ : Algebra c.F K) (Q : FrPt Xo c K),
      X.F.ChartFr k _ (hkk ψ) Q := fun ψ => by
    have hF : ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ flagOpen X := fun s _ => by
      have := ho ψ (Set.mem_univ s)
      rw [M.off_eq] at this
      exact this
    obtain ⟨a, h⟩ := exists_chartFr _ hF
    exact ⟨a, h k (hkk ψ)⟩
  have hJ : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), evalPt (spMap ψ ≫ tau hW') W' (hzW ψ) (M.K.jacobian i hW'i g) = ψ (M.K.jacobian i hW'i g) :=
    fun ψ => congrFun (congrArg DFunLike.coe (ev_spMap_tau hW' ψ (hzW ψ))) _
  have hl' : ∀ {K : Type} [Field K] [Algebra c.F K] (ψ : Γ(M.X, W') →+* K) {v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)},
      (∀ b, spMap ((dualMap ψ).comp (e b)) ≫ tau hW' ≫ toFlag M = X.ptY (v b)) → ∀ b, zv ψ b ≫ toFlag M = X.ptY (v b) :=
    fun ψ _ h b => (Category.assoc _ _ _).trans (h b)
  have hne : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ψ A.det ≠ 0 := fun {K} _ ψ => by
    obtain ⟨_, Q, hQ⟩ := chart ψ
    obtain ⟨v, hv, hl⟩ := e2 K ψ _ Q hQ
    have := _root_.GlobalTheory.CompHS.det_tanLift_ne_zero M hKS (spMap ψ ≫ tau hW') (ho ψ) (FlagCover.eq_ptY hQ.lies) hv (hl' ψ hl) i W' hW'i g (hzW ψ)
      (hzvW ψ) (by rw [hJ]; exact (hu.map ψ).ne_zero)
    rwa [hdet] at this
  have hAu : IsUnit A.det := by
    by_contra h
    obtain ⟨m, hm, hdm⟩ := exists_max_ideal_of_mem_nonunits h
    letI := Ideal.Quotient.field m
    exact hne (Ideal.Quotient.mk m) (Ideal.Quotient.eq_zero_iff_mem.2 hdm)
  let a : Γ(M.X, W') := M.K.jacobian i hW'i g * ↑(hAu.unit⁻¹)
  have hinv : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ψ A.det * ψ ↑(hAu.unit⁻¹) = 1 := fun ψ => by
    rw [← map_mul]
    have : A.det * ↑(hAu.unit⁻¹) = 1 := hAu.mul_val_inv
    rw [this, map_one]
  have rel : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), KSRel M i k (spMap ψ ≫ tau hW') (ψ a) := by
    intro K _ ψ _ P Q t v zv' O hO g' hz hzv hk hQ ht hv hl
    obtain ⟨v0, hv0, hl0⟩ := e2 K ψ hk Q hQ
    have hzO : ∀ b, ⊤ ≤ zv ψ b ⁻¹ᵁ O := fun b => le_preimage_of_dualNumber (TrivSqZeroExt.fstHom K K K).toRingHom _ O
      (by rw [hred]; exact hz)
    have tc := _root_.GlobalTheory.CompHS.det_der_frBor M hKS (spMap ψ ≫ tau hW') (ho ψ) t (FlagCover.eq_ptY hQ.lies) ht hv hv0 hl (hl' ψ hl0) O g' hzv hzO
    have jc := _root_.GlobalTheory.TanJac.det_mul_jacobian_comm M (spMap ψ ≫ tau hW') i (fun b => zv ψ (tanOrd Dw b)) (fun b => hred ψ _) O W' hO hW'i g' g hz
      (hzW ψ) (fun b => hzO _) (fun b => hzvW ψ _)
    rw [hJ, hdet] at jc
    rw [tc]
    generalize (Matrix.of fun a b => (evalPt (zv ψ (tanOrd Dw b)) O (hzO _) (g' a)).snd).det = D0 at jc ⊢
    generalize evalPt (spMap ψ ≫ tau hW') O hz (M.K.jacobian i hO g') = J1 at jc ⊢
    generalize ((∏ ix, t ix ^ exOf Dw (kap Dw) 0 ix : Kˣ) : K) = T
    have h1 := hinv ψ
    simp only [a, map_mul]
    generalize ψ ↑(hAu.unit⁻¹) = u at h1 ⊢
    generalize ψ A.det = d at jc h1
    generalize ψ (M.K.jacobian i hW'i g) = J0 at jc ⊢
    calc J0 * u * (T * D0) = T * u * (D0 * J0) := by ring
      _ = T * u * (d * J1) := by rw [jc]
      _ = (d * u) * (T * J1) := by ring
      _ = T * J1 := by rw [h1, one_mul]
  have uniq : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K) (x y : K), KSRel M i k (spMap ψ ≫ tau hW') x →
      KSRel M i k (spMap ψ ≫ tau hW') y → x = y := by
    intro K _ ψ x y hx hy
    obtain ⟨alg, Q, hQ⟩ := chart ψ
    obtain ⟨v0, hv0, hl0⟩ := e2 K ψ _ Q hQ
    have hb := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K).1 Q
    have a1 := @hx alg Q Q 1 v0 (zv ψ) W' hW'i g (hzW ψ) (hzvW ψ) _ hQ hb hv0 (hl' ψ hl0)
    have a2 := @hy alg Q Q 1 v0 (zv ψ) W' hW'i g (hzW ψ) (hzvW ψ) _ hQ hb hv0 (hl' ψ hl0)
    rw [hdet] at a1 a2
    exact mul_right_cancel₀ (hne ψ) (a1.trans a2.symm)
  refine ⟨W', a, hpW', hWV, fun L _ z hz => ?_, fun L _ z hz x y hx hy => ?_⟩
  · have e0 : spMap (ev z W' hz) ≫ tau hW' = z := spMap_ev z hW' hz
    have h : KSRel M i k (spMap (ev z W' hz) ≫ tau hW') (ev z W' hz a) := @rel L _ (ev z W' hz)
    rwa [e0] at h
  · have e0 : spMap (ev z W' hz) ≫ tau hW' = z := spMap_ev z hW' hz
    rw [← e0] at hx hy
    exact uniq _ x y hx hy

theorem exists_regular_ksRel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), GlobalTheory.Published.AbelianDeRham → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (i : M.K.bundle.ι) (k : X.F.J) (W : M.X.Opens), IsAffineOpen W → W ≤ ksOpen M i k → ∃ a : Γ(M.X, W), ∀ (K : Type) [Field K] (z : Sp K ⟶ M.X) (hz : ⊤ ≤ z ⁻¹ᵁ W), KSRel M i k z (GlobalTheory.FlagMod.ev z W hz a) := by
  intro E _ _ _ H Dw l Xo c Y X Z M hP hKS i k W _ hW
  haveI : Smooth M.str := SmoothOfRelativeDimension.smooth (dimFlag Dw) M.str
  haveI : IsReduced M.X := isReduced_of_smooth M.str
  exact glue_field_cover W (fun L _ z x => KSRel M i k z x) (exists_local M hP hKS i k W hW)

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRunModel
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Build

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem exists_runModel (p : PtAt ex Csz) (hm : More p) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (ho : OwnPin r)
    (i : Fin D.R.m) : ∃ (C : Type) (_ : Finite C) (_ : MulAction p.P.Gp C) (M : TwoLevels D.host.E D.R.r p.P.Gp C)
      (ka : Wt M.Ψ D.R.r), RunModel p r h i M ka := by
  classical
  obtain ⟨v⟩ := nonempty_place D
  have hne : Nonempty (uAt r v i).Comp := GlobalTheory.ModelLatticeCheck.comp_nonempty _ _ _
  have hcom := _root_.GlobalTheory.ShareOn.comps_share p hm r h ho i v
  have hchi := _root_.GlobalTheory.ShareOn.uAt_chi_eq_one p hm r h ho i v
  have hcong := _root_.GlobalTheory.ShareOn.sub_mem_half_smul_latP p hm r h ho i v
  obtain ⟨act, tr, h1, hmul, hmt, hconj, hcoc, hfaith, ⟨a, ha⟩, hd2⟩ := GlobalTheory.T.exists_levelGroup_transport_uniformisation_components p hm r h ho i v
  choose Xx hXd hXL using exists_dataX_latP p r h i v
  have hΓ : ∀ c, (Xx c).Γ = ((uAt r v i).X c).Γ := fun c => congrArg Data.Γ (hXd c)
  have hΛ : ∀ c, (Xx c).Λ = ((uAt r v i).X c).Λ := fun c => congrArg Data.Λ (hXd c)
  let k0 : (uAt r v i).Comp := hne.some
  letI inst : MulAction p.P.Gp (uAt r v i).Comp := { smul := act, one_smul := h1, mul_smul := hmul }
  let M : TwoLevels D.host.E D.R.r p.P.Gp (uAt r v i).Comp :=
    { Ψ := ((uAt r v i).X k0).Ψ
      Gm := ((uAt r v i).X k0).Gm
      p0 := ((uAt r v i).X k0).p0
      ξ0 := ((uAt r v i).X k0).ξ0
      comp := Xx
      comp_Ψ := fun c => (congrArg Data.Ψ (hXd c)).trans (hcom c k0).1
      comp_Gm := fun c => (congrArg Data.Gm (hXd c)).trans (hcom c k0).2.2.1
      comp_basePoint := fun c => (congrArg Data.p0 (hXd c)).trans (hcom c k0).2.1
      comp_ξ0 := fun c => (congrArg Data.ξ0 (hXd c)).trans (hcom c k0).2.2.2
      χ_one := fun c => chi_one_of_toData (Xx c) _ (hXd c) (hchi c)
      Γ_L' := fun c γ hγ w => by
        rw [hXL c]
        rw [hΓ c] at hγ
        exact mem_localLattice_iff_mulVec D _ (((uAt r v i).X c).Γ_stab γ hγ).2 w
      tr := tr
      tr_herm := fun u c w w' => by
        have e := (hmt u c).iso w w'
        rw [(hcom (act u c) k0).2.2.1, (hcom c k0).2.2.1] at e
        exact e
      tr_Λ := fun u c w => by
        rw [hΛ c, hΛ (u • c)]
        exact (hmt u c).lat w
      tr_L' := fun u c w => by
        rw [hXL c, hXL (u • c)]
        exact mem_localLattice_iff_mulVec D _ (hmt u c).lat w
      tr_conj := fun u c γ => by
        rw [hΓ c, hΓ (u • c)]
        exact hconj u c γ
      tr_mul := fun u u' c => by
        rw [hΓ]
        exact hcoc u u' c
      tr_faithful := fun u c hu ht => hfaith u c hu (by rw [hΓ c] at ht; exact ht) }
  let ka : Wt M.Ψ D.R.r := fun τ j => laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k0 τ j
  refine ⟨(uAt r v i).Comp, inferInstance, inst, M, ka, v, Equiv.refl _, fun c => hXd c, ?_, ⟨a, ?_⟩, ?_, ?_⟩
  · intro c τ h1 h2 j
    show laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k0 ⟨τ, h1⟩ j = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) c ⟨τ, h2⟩ j
    unfold laR laU
    rw [(hcom c k0).2.1]
  · intro F g c x hx h1 h2
    have hx' : castFrame h1 x ∈ ((uAt r v i).X c).dom := by
      show castFrame h1 x ∈ GG ((uAt r v i).X c).Ψ ((uAt r v i).X c).Gm ((uAt r v i).X c).p0
      rw [(hcom c k0).2.2.1, (hcom c k0).2.1]
      exact fun τ => hx ⟨τ.1, by rw [h1]; exact τ.2⟩
    have e := ha F g c (castFrame h1 x) hx' (h1.symm.trans h2)
    exact e
  · intro c γ hγ w hw
    rw [hXL c] at hw ⊢
    rw [hΓ c] at hγ
    exact hcong c γ hγ w hw
  · exact hd2 (fun c => (Xx c).L') hXL

end Build

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTensorOrderAlgEquivMatrixCharPStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_tensor_order_algEquiv_matrix_charP : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] [CharP k p] [Algebra (𝓞 D.F) k], Nonempty ((k ⊗[𝓞 D.F] D.O) ≃ₐ[k] Matrix (Fin D.m) (Fin D.m) k) := by
  first | (exact @GlobalTheory.UPel.HT.Datum.charP_tensor_matrix) | (exact GlobalTheory.UPel.HT.Datum.charP_tensor_matrix) | (intros; apply GlobalTheory.UPel.HT.Datum.charP_tensor_matrix  <;> assumption)
end

