module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenericFrameIntegralOffFinitelyManyFunctions
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0111
public import Formalism.LocalToGlobal.ProjectiveLattices.LocFld
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0060

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetIntegralOfDefinite
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.Frames GlobalTheory.AllWt

noncomputable section

namespace GlobalTheory.FlatLine.Spread

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def Spreads {R : Type} [Field R] [Algebra c.F R] (y : FrPt Xo c R) : Prop :=
  ∃ S : Finset R, (∀ s ∈ S, s ≠ 0) ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra
    ∀ ψ : R →ₐ[c.F] T.Fr, (∀ s ∈ S, vV T.V (ψ s) = 0) → ∀ z : FrPt Xo c T.Fr, FrMap ψ y z → Integral T io z

theorem discrete_XF (hq : Dw.q = 0) : DiscreteTopology (Xo.XF c) := by
  have hd : Dw.dim = 0 := by simp [Datum.dim, hq]
  have h0 : SmoothOfRelativeDimension 0 Xo.s := hd ▸ Xo.smooth
  have h1 : Etale Xo.s := (Etale.iff_smoothOfRelativeDimension_zero _).2 h0
  let f := pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)
  have h2 : Etale f := inferInstance
  have h3 : LocallyQuasiFinite f := GlobalTheory.TangentCrit.locallyQuasiFinite_of_formallyUnramified f
  have s₀ : Sp c.F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum c.F)
  have h4 := f.isDiscrete_preimage_singleton s₀
  have h5 : f ⁻¹' {s₀} = Set.univ :=
    Set.eq_univ_of_forall fun x => Subsingleton.elim (α := PrimeSpectrum c.F) _ _
  rw [h5] at h4
  exact isDiscrete_univ_iff.1 h4

theorem exists_genPt_eq (hq : Dw.q = 0) (ξ : Xo.XF c) : ∃ Z : Comp Xo c, genPt Z = ξ := by
  have := discrete_XF (Xo := Xo) (c := c) hq
  refine ⟨⟨irreducibleComponent ξ, irreducibleComponent_mem_irreducibleComponents ξ⟩, ?_⟩
  set Z : Comp Xo c := ⟨irreducibleComponent ξ, irreducibleComponent_mem_irreducibleComponents ξ⟩
  have h1 : IsGenericPoint (genPt Z) (Z : Set (Xo.XF c)) :=
    (Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2))
  exact (h1.specializes mem_irreducibleComponent).eq

theorem spreads_of_model (hq : Dw.q = 0) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) {R : Type} [Field R]
    [Algebra c.F R] (y : FrPt Xo c R) : Spreads y := by
  have hT := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hbc : FrBC Xo c := fun S K _ _ _ _ ψ y =>
    GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c S K ψ y
  obtain ⟨Z, hZ⟩ := exists_genPt_eq hq (ptF y (IsLocalRing.closedPoint R))
  obtain ⟨M, hM⟩ := GlobalTheory.GenericChart.exists_chart_genPt hT E H Dw l Xo c Y Z
  obtain ⟨f, hf, -⟩ := GlobalTheory.ModelPoints.existsUnique_chartHom M.hU R (ptF y ≫ Y.j) (by
    show Y.j (ptF y _) ∈ M.U
    rw [← hZ]; exact hM)
  have hs : ptF y ≫ pullback.snd _ _ = spMap (algebraMap c.F R) := pullback.lift_snd _ _ _
  obtain ⟨Λ⟩ := GlobalTheory.Reg.MChart.nonempty_lift E H Dw l Xo c _ _ Y M R f (ptF y) hs hf.symm
  have ex : ptF y ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _
  rw [ex] at Λ
  exact GenInt.exists_finset_of_lift hT hbc M f y Λ

theorem Spreads.of_x_eq {R : Type} [Field R] [Algebra c.F R] {y₀ y : FrPt Xo c R} (h : Spreads y₀)
    (hx : y.x = y₀.x) : Spreads y := by
  classical
  obtain ⟨S, hS, H₀⟩ := h
  obtain ⟨k, a, hk, hchg⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c R y₀ y).1 hx
  let S₀ : Finset R := S ∪
    Finset.univ.biUnion (fun τ : E →+* ℂ =>
      Finset.univ.image fun p : Fin (Dw.mult τ) × Fin (Dw.mult τ) => k τ p.1 p.2) ∪
    Finset.univ.image (fun τ : E →+* ℂ => (k τ).det) ∪ {(a : R)}
  refine ⟨S₀.filter (· ≠ 0), fun s hs => (Finset.mem_filter.1 hs).2, fun T io => ?_⟩
  let _ := io.toAlgebra
  intro ψ hψ z hz
  have hin : ∀ s ∈ S₀, ∃ v, algebraMap T.V T.Fr v = ψ s := fun s hs => by
    by_cases h0 : s = 0
    · exact ⟨0, by rw [h0, map_zero, map_zero]⟩
    · exact Formalism.L2.PjFree.mem_range_of_vV_nonneg (hψ s (Finset.mem_filter.2 ⟨hs, h0⟩)).ge
  have hun : ∀ s ∈ S₀, IsUnit s → ∀ v, algebraMap T.V T.Fr v = ψ s → IsUnit v := fun s hs h0 v hv =>
    GenInt.isUnit_of_vV T v (by rw [hv]; exact (h0.map ψ).ne_zero)
      (by rw [hv]; exact hψ s (Finset.mem_filter.2 ⟨hs, h0.ne_zero⟩))
  choose k₀ hk₀ using fun τ j i => hin (k τ j i) (by
    simp only [S₀, Finset.mem_union, Finset.mem_biUnion]
    exact .inl (.inl (.inr ⟨τ, Finset.mem_univ _, Finset.mem_image.2 ⟨(j, i), Finset.mem_univ _, rfl⟩⟩)))
  have ha : (a : R) ∈ S₀ := by simp [S₀]
  obtain ⟨a₀, ha₀⟩ := hin a ha
  obtain ⟨a₁, rfl⟩ := hun a ha a.isUnit a₀ ha₀
  have ek : ∀ τ, (Matrix.of (k₀ τ)).map (algebraMap T.V T.Fr) = (k τ).map ψ :=
    fun τ => Matrix.ext fun j i => hk₀ τ j i
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
    E H Dw l Xo c R T.Fr ψ y₀
  have hi₀ : Integral T io z₀ := H₀ T io ψ (fun s hs => hψ s (Finset.mem_filter.2 ⟨by
    simp only [S₀, Finset.mem_union]; exact .inl (.inl (.inl hs)), hS s hs⟩)) z₀ hz₀
  have hc := (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c R T.Fr ψ y₀ y z₀ z k a hchg hz₀).1 hz
  refine GenInt.integral_chg T io z₀ z (fun τ => Matrix.of (k₀ τ)) a₁ (fun τ => ?_) ?_ hi₀
  · refine hun (k τ).det ?_ (hk τ) _ ?_
    · simp only [S₀, Finset.mem_union]
      exact .inl (.inr (Finset.mem_image_of_mem _ (Finset.mem_univ τ)))
    · rw [RingHom.map_det, RingHom.mapMatrix_apply, ek]
      exact (ψ.toRingHom.map_det (k τ)).symm
  · rw [funext ek, ha₀]
    exact hc

theorem Spreads.of_frOver {n : ℕ} (d : DeltaDat Xo c n) {R : Type} [Field R] [Algebra c.F R] [Algebra d.c₂.F R]
    (hc : ∀ a : c.F, algebraMap d.c₂.F R (d.eF a) = algebraMap c.F R a) {y : FrPt Xo c R}
    {y₂ : FrPt d.Xo₂ d.c₂ R} (h : Spreads y) (ho : FrOver d y₂ y) : Spreads y₂ := by
  obtain ⟨S, hS, H₀⟩ := h
  refine ⟨S, hS, fun T io₂ => ?_⟩
  letI := io₂.toAlgebra
  intro ψ₂ hψ z₂ hz₂
  let io : c.F →+* T.Fr := io₂.comp d.eF.toRingEquiv.toRingHom
  letI := io.toAlgebra
  let ψ : R →ₐ[c.F] T.Fr :=
    { ψ₂.toRingHom with commutes' := fun a => (congrArg ψ₂ (hc a).symm).trans (ψ₂.commutes _) }
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
    E H Dw l Xo c R T.Fr ψ y
  have hi : Integral T io z := H₀ T io ψ hψ z hz
  have ho' : FrOver d z₂ z := GlobalTheory.FrameLift.frOver_map d (ψ := ψ) (ψ₂ := ψ₂) rfl ho hz hz₂
  exact GlobalTheory.PlaceInt.integral_of_frOver E H Dw l Xo c n d T io io₂
    ⟨z, GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c _ z, hi⟩
    (fun _ => rfl) z₂ ho'

theorem exists_coeff_of_dvd {l₁ : Level H} (hl : l₁.Dvd l) (c : Coeff l) : ∃ c₁ : Coeff l₁, c.F = c₁.F := by
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have h' : l₁.M' ∣ l.M' := Nat.lcm_dvd (hl.1.trans (Nat.dvd_lcm_left _ _)) (hl.2.2.trans (Nat.dvd_lcm_right _ _))
  have hp : 0 < l.M' := Nat.lcm_pos hM l.A_pos
  refine ⟨⟨c.F, c.fin, c.conj, ?_, ?_⟩, rfl⟩
  · rw [← Moduli.LevelAction.zeta_pow_div hp h']; exact pow_mem c.zeta_mem _
  · refine le_trans ?_ c.le
    rw [KA, IntermediateField.adjoin_le_iff]
    rintro x (rfl | rfl)
    · exact (baseKA l).ρ.2
    · rw [← Moduli.LevelAction.zeta_pow_div l.A_pos hl.2.2]
      exact pow_mem (baseKA l).ζ.2 _

theorem spreads (hq : Dw.q = 0) (hp : 1 ≤ Dw.p) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) {R : Type} [Field R]
    [Algebra c.F R] (y : FrPt Xo c R) : Spreads y := by
  have hr : 1 ≤ Dw.p + Dw.q := hp.trans (Nat.le_add_right _ _)
  let l₁ : Level H := { l with A := 1, A_pos := one_pos }
  have hl : l₁.Dvd l := ⟨dvd_rfl, le_rfl, one_dvd _⟩
  obtain ⟨Xo₁⟩ := GlobalTheory.Moduli.moduli_scheme_exists E H Dw l₁ hr
  obtain ⟨c₁, hF⟩ := exists_coeff_of_dvd hl c
  obtain ⟨-, ⟨Y⟩⟩ := GlobalTheory.Reg.modelAt_and_nonempty_global_model E H Dw l₁ Xo₁ c₁ hr hg rfl
  obtain ⟨r, jK, m, hj, hrs, -⟩ := GlobalTheory.levelMaps_closed GlobalTheory.abelianSchemeLaws_all.1 E H Dw hr l₁ l Xo₁ Xo hl
  let d : DeltaDat Xo₁ c₁ 0 :=
    { pd := 1, I := ⊤, l₂ := l, Xo₂ := Xo, c₂ := c, hF := hF, r := r, m := m,
      nab₂ := fun _ _ _ _ => 0, cδ := 0, φδ := 0 }
  letI : Algebra d.c₂.F R := ‹Algebra c.F R›
  letI : Algebra c₁.F R := ((algebraMap c.F R).comp d.eF.toRingEquiv.toRingHom).toAlgebra
  obtain ⟨y₁, hy₁⟩ := exists_frPt_local (Xo := Xo₁) (c := c₁) (L := R) GlobalTheory.abelianSchemeLaws_all.2.secTwist
    (y.x ≫ r) (by
      rw [Category.assoc, hrs, ← Category.assoc, y.x_over, sOf, sOf, Formalism.L2.PjFree.spMap_comp']
      refine congrArg spMap (RingHom.ext fun a => ?_)
      exact congrArg (algebraMap c.F R) (Subtype.ext (hj a)))
  obtain ⟨y₂, hx, ho⟩ := GlobalTheory.FrameLift.exists_frOver d (fun _ => rfl) y₁ y.x hy₁.symm y.x_over
  exact (Spreads.of_frOver d (fun _ => rfl) (spreads_of_model hq Y y₁) ho).of_x_eq hx.symm

end GlobalTheory.FlatLine.Spread

namespace GlobalTheory.FlatLine


open ReciprocityTheory.ChartRestriction.G.FD in
theorem exists_finset_integral_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.q = 0 → 1 ≤ Dw.p → (∀ p : ℕ, p.Prime → l.GoodAt p) → ∀ y₀ : FrPt Xo c c.F, ∃ S : Finset c.F, (∀ s ∈ S, s ≠ 0) ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; (∀ s ∈ S, vV T.V (io s) = 0) → ∀ z : FrPt Xo c T.Fr, FrMap (Algebra.ofId c.F T.Fr) y₀ z → Integral T io z := by
  intro E _ _ _ H Dw l Xo c hq hp hg y₀
  obtain ⟨S, hS, h⟩ := Spread.spreads hq hp hg y₀
  exact ⟨S, hS, fun T io => letI := io.toAlgebra; fun hs z hz => h T io (Algebra.ofId c.F T.Fr) hs z hz⟩

end GlobalTheory.FlatLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
section
noncomputable section

namespace GlobalTheory.FlatLine

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.AllWt

theorem exists_finite_point {K : Type} [Field K] {X : Scheme.{0}} (s : X ⟶ Sp K) [LocallyOfFiniteType s]
    {Z : Set X} (hZ : IsOpen Z) (hne : Z.Nonempty) :
    ∃ (L : Type) (_ : Field L) (j : K →+* L) (g : Sp L ⟶ X), j.Finite ∧ g ≫ s = spMap j ∧ ∀ p, g p ∈ Z := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨U, hU, hxU, hUZ⟩ :=
    (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⟨Z, hZ⟩ : X.Opens) from hx)
  have hU' : IsAffineOpen U := hU
  obtain ⟨y, -⟩ : x ∈ Set.range hU'.fromSpec := by rw [hU'.range_fromSpec]; exact hxU
  let R := Γ(X, U)
  let φ : CommRingCat.of K ⟶ R := Spec.preimage (hU'.fromSpec ≫ s)
  have hφ : Spec.map φ = hU'.fromSpec ≫ s := Spec.map_preimage _
  have hft : LocallyOfFiniteType (Spec.map φ) := by
    rw [hφ]; exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  have hφft : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft
  let : Algebra K R := φ.hom.toAlgebra
  have : Algebra.FiniteType K R := hφft
  let p : PrimeSpectrum R := y
  obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  let L := R ⧸ m
  let fL : Field L := Ideal.Quotient.field m
  have : Algebra.FiniteType K L :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective _ _)
  have hf : Module.Finite K L := finite_of_finite_type_of_isJacobsonRing K L
  refine ⟨L, fL, algebraMap K L, spMap (Ideal.Quotient.mk m) ≫ hU'.fromSpec, RingHom.finite_algebraMap.2 hf, ?_,
    fun q => hUZ ?_⟩
  · rw [Category.assoc, ← hφ]
    exact (Spec.map_comp _ _).symm
  · show _ ∈ (U : Set X)
    rw [← hU'.range_fromSpec, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

abbrev prX (Xo : Moduli Dw l) (c : Coeff l) : Xo.XF c ⟶ Xo.X :=
  pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)

theorem exists_numberField_point (Z : Comp Xo c) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (j : c.F →+* L) (g : Sp L ⟶ Xo.XF c),
      g ≫ strK = spMap j ∧ ∀ p, g p ∈ (Z : Set (Xo.XF c)) := by
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have : LocallyOfFiniteType (strK (Xo := Xo) (c := c)) := inferInstance
  obtain ⟨L, _, j, g, hj, hg, hZ⟩ := exists_finite_point (strK (Xo := Xo) (c := c))
    (CompSplitPfB.cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z).isOpen
    (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).nonempty
  let _ : Algebra c.F L := j.toAlgebra
  have : Module.Finite c.F L := hj
  exact ⟨L, inferInstance, NumberField.of_module_finite c.F L, j, g, hg, hZ⟩

theorem prX_over {S : Type} [CommRing S] [Algebra c.F S] {g : Sp S ⟶ Xo.XF c}
    (hg : g ≫ strK = spMap (algebraMap c.F S)) : (g ≫ prX Xo c) ≫ Xo.s = sOf c S := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, hg, sOf, ← Spec.map_comp]
  rfl

theorem ptF_eq {S : Type} [CommRing S] [Algebra c.F S] {g : Sp S ⟶ Xo.XF c}
    (hg : g ≫ strK = spMap (algebraMap c.F S)) {y : FrPt Xo c S} (hy : y.x = g ≫ prX Xo c) : ptF y = g := by
  apply pullback.hom_ext
  · rw [ptF, pullback.lift_fst, hy]
  · rw [ptF, pullback.lift_snd]
    exact hg.symm

theorem point_ext {Z : Comp Xo c} {L S : Type} [CommRing L] [CommRing S] {j : c.F →+* L} {g : Sp L ⟶ Xo.XF c}
    (hg : g ≫ strK = spMap j) (hZ : ∀ p, g p ∈ (Z : Set (Xo.XF c))) (k : L →+* S) :
    (spMap k ≫ g) ≫ strK = spMap (k.comp j) ∧ ∀ p, (spMap k ≫ g) p ∈ (Z : Set (Xo.XF c)) := by
  refine ⟨?_, fun p => ?_⟩
  · rw [Category.assoc, hg, ← Spec.map_comp]
    rfl
  · rw [Scheme.Hom.comp_apply]
    exact hZ _

theorem framesOn_nonempty {r : ℕ} {σ : c.F →+* ℂ} {U : Unf Xo c σ r} (hU : IsUnf U) (Z : Comp Xo c) :
    (framesOn U Z).Nonempty := by
  obtain ⟨L, _, _, j, g, hg, hZ⟩ := exists_numberField_point Z
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  letI : Algebra c.F L := j.toAlgebra
  let k : L →ₐ[c.F] CAt σ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  obtain ⟨h1, h2⟩ := point_ext hg hZ k.toRingHom
  have e : k.toRingHom.comp j = algebraMap c.F (CAt σ) := k.comp_algebraMap
  rw [e] at h1
  obtain ⟨y, hy⟩ := exists_frPt_local (c := c) GlobalTheory.abelianSchemeLaws_all.2.secTwist _ (prX_over h1)
  obtain ⟨i, z, t, ht⟩ := hU.2.2.1 y
  refine ⟨⟨i, z.1⟩, z.2, fun p => ?_⟩
  have := ptF_eq h1 (ht.1.symm.trans hy)
  exact this ▸ h2 p

theorem valOn_nonempty (hE : IntFrExt Xo c) (Z : Comp Xo c) (w : HeightOneSpectrum (𝓞 c.F)) :
    (valOn Z w).Nonempty := by
  obtain ⟨L, _, _, j, g, hg, hZ⟩ := exists_numberField_point Z
  obtain ⟨T, k, e, ho, hfin⟩ := locFld c.F L j w
  obtain ⟨h1, h2⟩ := point_ext hg hZ k
  obtain ⟨T', i, r, hr, hi, hfin', y, hy⟩ := hE T (k.comp j) hfin ((spMap k ≫ g) ≫ prX Xo c)
    (letI := (k.comp j).toAlgebra; prX_over h1)
  obtain ⟨h3, h4⟩ := point_ext h1 h2 i
  letI := (i.comp (k.comp j)).toAlgebra
  have h5 : ptF y.1 = spMap i ≫ spMap k ≫ g := ptF_eq h3 (hy.trans (Category.assoc _ _ _).symm)
  exact ⟨_, PtV.mk w (ho.bc i hr hi) y ⟨hfin', fun p => h5 ▸ h4 p⟩ () trivial, rfl⟩

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

theorem hasPts (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (Z : Comp Xo c) : HasPts U Z := by
  obtain ⟨⟨-, -, -, -, hA, -⟩, h⟩ := GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c
  refine ⟨fun σ => ⟨framesOn_nonempty (hU _ (goodEmb_goodOf c σ)) Z, fun z _ hz => ?_⟩,
    valOn_nonempty ((h hpq).2.2 hg).1 Z⟩
  haveI : _root_.IsReduced (CAt (goodOf c σ)) := inferInstanceAs (_root_.IsReduced ℂ)
  exact hA _ _

end GlobalTheory.FlatLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
section
noncomputable section

namespace GlobalTheory.FlatLine

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.AllWt
  Formalism.L2.Pj.CompSplitPfB

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_of_frMap_test {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) {p : TRing c.F} {S : Type}
    [CommRing S] [Algebra c.F S] {φ : p.R →ₐ[c.F] S} {y : FrPt Xo c p.R} {z : FrPt Xo c S} (h : FrMap φ y z) :
    evR Xo c f z = φ (f p y) := by
  have ht : Tested z := ⟨p, φ, y, h⟩
  unfold evR evalAt
  rw [dite_eq_left ht]
  exact GlobalTheory.TransferCompare.evalWD_framed Xo c f hf S _ p _ φ _ y z ht.choose_spec.choose_spec.choose_spec h

theorem idem_notMem_iff (Z : Comp Xo c) {p : TRing c.F} (y : FrPt Xo c p.R) (q : PrimeSpectrum p.R) :
    idem Z p y ∉ q.asIdeal ↔ ptF y q ∈ (Z : Set (Xo.XF c)) :=
  cspB_idem_spec _ (cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z) y.x y.x_over q

theorem liesOff_of_map_idem {Z : Comp Xo c} {p : TRing c.F} {S : Type} [CommRing S] [Algebra c.F S]
    {φ : p.R →ₐ[c.F] S} {y : FrPt Xo c p.R} {z : FrPt Xo c S} (h : FrMap φ y z) (h0 : φ (idem Z p y) = 0) :
    LiesOff Z z := fun q hq => by
  have hC := cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z
  have h1 : cspB_idem _ hC z.x z.x_over = 0 := (cspB_idem_map _ hC φ y.x_over z.x_over h.1).symm.trans h0
  exact (cspB_idem_spec _ hC z.x z.x_over q).2 hq (h1 ▸ q.asIdeal.zero_mem)

theorem mem_suppOn_iff_idem_mul_of_natural {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) (Z : Comp Xo c) :
    f ∈ suppOn Z ↔ idem Z * f = f := by
  refine ⟨fun h => funext fun p => funext fun y => ?_, fun h => ?_⟩
  · obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _
      (Ideal.Quotient.mkₐ c.F (Ideal.span {idem Z p y})) y
    have h0 := h _ z (liesOff_of_map_idem hz (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)))
    rw [evR_of_frMap_test hf hz] at h0
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    have h1 : idem Z p y * idem Z p y = idem Z p y := congrFun (congrFun (idem_mul_idem Z) p) y
    show idem Z p y * f p y = f p y
    rw [← ha, mul_left_comm, h1]
  · rw [← h, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)

theorem mem_suppOn_iff_idem_mul {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (Z : Comp Xo c) :
    f ∈ suppOn Z ↔ idem Z * f = f := mem_suppOn_iff_idem_mul_of_natural hf.1 Z

theorem idem_mul_eq {e : Ix Dw → ℤ} {Z : Comp Xo c} {f : Rul Xo c} (hf : f ∈ secZ Xo c e ⊓ suppOn Z) :
    idem Z * f = f := (mem_suppOn_iff_idem_mul hf.1 Z).1 hf.2

theorem idem_mul_mem {e : Ix Dw → ℤ} (Z : Comp Xo c) {f : Rul Xo c} (hf : f ∈ secZ Xo c e) :
    idem Z * f ∈ secZ Xo c e ⊓ suppOn Z :=
  ⟨zero_add e ▸ mul_mem_secZ (idem_mem_secZ Z) hf, mul_comm f (idem Z) ▸ mul_mem_suppOn f (idem_mem_suppOn Z)⟩

theorem eq_zero_of_forall_prime {K : Type} [Field K] {p : TRing K} {a : p.R}
    (h : ∀ q : PrimeSpectrum p.R, a ∈ q.asIdeal) : a = 0 := by
  have : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  exact (nilpotent_iff_mem_prime.2 fun J hJ => h ⟨J, hJ⟩).eq_zero

theorem idem_mul_idem_of_ne {Z Z' : Comp Xo c} (h : Z ≠ Z') : idem Z * idem Z' = 0 :=
  funext fun p => funext fun y => eq_zero_of_forall_prime fun q => by
    show idem Z p y * idem Z' p y ∈ q.asIdeal
    by_contra hn
    have h1 := not_or.1 (mt q.isPrime.mul_mem_iff_mem_or_mem.2 hn)
    exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c Z Z' h) ((idem_notMem_iff Z y q).1 h1.1)
      ((idem_notMem_iff Z' y q).1 h1.2)


variable (Xo c) in
theorem sum_idem [Fintype (Comp Xo c)] : ∑ Z : Comp Xo c, idem Z = 1 := by
  classical
  refine funext fun p => funext fun y => ?_
  rw [Finset.sum_apply, Finset.sum_apply]
  show _ = (1 : p.R)
  refine sub_eq_zero.1 (eq_zero_of_forall_prime fun q => ?_)
  have hall : ptF y q ∈ ⋃₀ irreducibleComponents (Xo.XF c) := by
    rw [sUnion_irreducibleComponents]; trivial
  obtain ⟨W, hW, hq⟩ := Set.mem_sUnion.1 hall
  let Z₀ : Comp Xo c := ⟨W, hW⟩
  have h1 : idem Z₀ p y ∉ q.asIdeal := (idem_notMem_iff Z₀ y q).2 hq
  refine (q.isPrime.mem_or_mem (x := idem Z₀ p y) ?_).resolve_left h1
  have h2 : idem Z₀ p y * ∑ Z : Comp Xo c, idem Z p y = idem Z₀ p y := by
    rw [Finset.mul_sum]
    exact (Finset.sum_eq_single Z₀ (fun Z _ h => congrFun (congrFun (idem_mul_idem_of_ne h.symm) p) y)
      (fun h => absurd (Finset.mem_univ _) h)).trans (congrFun (congrFun (idem_mul_idem Z₀) p) y)
  rw [mul_sub, h2, mul_one, sub_self]
  exact q.asIdeal.zero_mem


theorem sum_idem_mul [Fintype (Comp Xo c)] (f : Rul Xo c) : ∑ Z : Comp Xo c, idem Z * f = f := by
  rw [← Finset.sum_mul, sum_idem, one_mul]

namespace ConstSec

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {Z : Comp Xo c} {la : Weight Dw}
  {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s : ConstSec U x Z la δ)

end ConstSec

end GlobalTheory.FlatLine
end
end

