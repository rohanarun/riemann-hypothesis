module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsOpenSameModel
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FlagChartsCoverFramedFieldPoints
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0080
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicGermValueChartIndependent
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsComponentOfModelCharts
section
open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.Reg
open scoped Matrix

noncomputable section

namespace GlobalTheory.OneComp

open GlobalTheory.CompModel GlobalTheory.SupGeneric

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem wchar_zero {S : Type} [CommRing S] (t : Ix Dw → Sˣ) : wchar (ex Dw 0 0) t = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  have : ex Dw 0 0 i = 0 := by rcases i with _ | ⟨τ, i⟩ <;> simp [ex]
  rw [this, pow_zero]

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem evR_eq_natCast (hL : EvLaws Xo c) {h : GenFrEx Xo c} {χ : Rul Xo c} (hχ : χ ∈ sec Xo c 0 0) (C : FChart h)
    {L : Type} [Field L] [Algebra c.F L] (ψ : C.R →ₐ[c.F] L) {z w : FrPt Xo c L} {t : Ix Dw → Lˣ}
    (hz : FrMap ψ C.y z) (hb : FrBor t z w) (n : ℕ) (hn : evC h C.Z χ = n) : evR Xo c χ w = n := by
  have h1 : evR Xo c χ C.yg = n := by
    rw [hL.wt 0 0 χ hχ _ C.t _ _ (hL.test _ _) (hL.test _ _) C.bor, wchar_zero]
    unfold evC at hn
    rw [hn]
    simp
  have h2 : evR Xo c χ C.y = n := by
    rw [evR_of_frMap hL hχ C.R.val C.gen] at h1
    exact Subtype.ext (h1.trans (map_natCast C.R.val n).symm)
  have h3 : evR Xo c χ z = n := by rw [evR_of_frMap hL hχ ψ hz, h2, map_natCast]
  rw [hL.wt 0 0 χ hχ _ t _ _ (hL.test _ _) (hL.test _ _) hb, wchar_zero, h3]
  simp

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem exists_comp_of_charts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.IsUnf U → ∀ (h : GenFrEx Xo c) (k : U.Comp), ∃ Z : Comp Xo c, ∀ (x : (U.X k).dom) (C : FChart h) (ψ : C.R →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap ψ C.y z → FrBor t z (U.un k x) → C.Z = Z := by
  intro E _ _ _ H Dw l Xo c σ r U hU h k
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨x₀, hx₀⟩ := (GlobalTheory.frames_isConnected E r (U.X k)).nonempty
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨C₀, ψ₀, z₀, t₀, hz₀, hb₀⟩ := hA h (CAt σ) (U.un k ⟨x₀, hx₀⟩)
  refine ⟨C₀.Z, fun x C ψ z t hz hb => ?_⟩
  by_contra hne
  obtain ⟨χ, hχ, hi, h1, h0⟩ := exists_idem_section E H Dw l Xo c hL h (hA h) C₀.Z
  have hD : Dom (E := E) 0 0 := ⟨fun τ _ _ _ => le_rfl, Even.zero⟩
  have hs := hU.2.2.2.2.1 0 0 hD χ hχ k
  rw [IdemCusp.laU_zero] at hs
  have hid : IdemCusp.IsIdemFn (U.X k) (Formalism.L2.PjFree.rdU U χ k) := by
    refine IdemCusp.isIdemFn_of_isSec _ hs ?_
    have := congrFun (IdemCusp.rdU_mul U χ χ) k
    rw [hi] at this
    exact this.symm
  have hT : Set.MapsTo (Formalism.L2.PjFree.rdU U χ k) (U.X k).dom ({0, 1} : Set ℂ) := by
    intro s hs
    rcases hid.1 _ hs with h | h <;> simp [h]
  have hc := (GlobalTheory.frames_isConnected E r (U.X k)).isPreconnected.constant_of_mapsTo
    (Set.toFinite ({0, 1} : Set ℂ)).isDiscrete hid.2.1.continuousOn hT x.2 hx₀
  have e0 := evR_eq_natCast hL hχ C ψ hz hb 0 ((h0 _ hne).trans Nat.cast_zero.symm)
  have e1 := evR_eq_natCast hL hχ C₀ ψ₀ hz₀ hb₀ 1 (h1.trans Nat.cast_one.symm)
  rw [rdU_apply, rdU_apply U χ k ⟨x₀, hx₀⟩, e0, e1] at hc
  have hc' : ((0 : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := hc
  simp at hc'

end GlobalTheory.OneComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCountableFlagSpaceAtlas
section
noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

attribute [local instance 1100] Subalgebra.algebra in
theorem exists_countable_atlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (h : GenFrEx Xo c), ∃ (ι : Type) (_ : Countable ι) (C : ι → FChart h),
      ∀ (L : Type) [Field L] [Algebra c.F L] (y : FrPt Xo c L),
        ∃ (i : ι) (ψ : (C i).R →ₐ[c.F] L) (z : FrPt Xo c L) (t : Ix Dw → Lˣ),
          FrMap ψ (C i).y z ∧ FrBor t z y := by
  intro E _ _ _ H Dw l Xo c h
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hBC : FrBC Xo c := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1.bc
  choose A iA dA aA j yA hj hp hjs hsm hyA using
    GlobalTheory.LocalFrame.exists_integral_chart_frame hS E H Dw l Xo c
  haveI : IsNoetherian (Xo.XF c) := CompFin.isNoetherian_XF Xo c
  obtain ⟨T, -, hT⟩ := (isCompact_univ (X := Xo.XF c)).elim_nhds_subcover (fun p => Set.range (j p))
    (fun p _ => by
      haveI := hj p
      exact (IsOpenImmersion.isOpen_range (j p)).mem_nhds (hp p))
  choose C hC using fun (p : Xo.XF c) (σ : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) =>
    GlobalTheory.Reg.exists_fChart_cell E H Dw l Xo c hBC h (A p) (j p) (yA p) (hj p) (hjs p) (hsm p) (hyA p) σ
  refine ⟨T × (∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))), inferInstance, fun i => C i.1 i.2, ?_⟩
  intro L _ _ y
  have hcond : y.x ≫ Xo.s =
      spMap (algebraMap c.F L) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [y.x_over, spMap_comp_ring]
    rfl
  let q : Sp L ⟶ Xo.XF c := pullback.lift y.x (spMap (algebraMap c.F L)) hcond
  obtain ⟨p, hpT, hq⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ (q (IsLocalRing.closedPoint L))))
  haveI := hj p
  obtain ⟨f, hf⟩ := exists_algHom_of_mem_range (pullback.snd _ _) (j p) (hjs p) q (pullback.lift_snd _ _ _) hq
  obtain ⟨z₀, hz₀⟩ := hBC (A p) L f (yA p)
  have hx : y.x = z₀.x := by
    rw [hz₀.1, hyA, ← Category.assoc, hf]
    exact (pullback.lift_fst _ _ _).symm
  obtain ⟨g, ⟨hgu, hg⟩, -⟩ := (_root_.GlobalTheory.Reg.ReframeEx.reframe_exists_unique E H Dw l Xo c L z₀).2 y hx
  choose σ u b h0 h1 hb e using fun τ => exists_perm_lower_upper (g τ) (hgu τ)
  let x : FlagVar Dw → L := fun v => u v.1 (σ v.1 v.2.1.2) v.2.1.1
  have hu : ∀ τ, (lowM x τ).submatrix (σ τ).symm id = u τ := by
    intro τ
    ext i k
    obtain ⟨i, rfl⟩ := (σ τ).surjective i
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, id, lowM]
    split_ifs with h₁ h₂
    · rfl
    · rw [h₂, h1]
    · exact (h0 τ i k (lt_of_le_of_ne (not_lt.mp h₁) (Ne.symm h₂))).symm
  refine ⟨(⟨p, hpT⟩, σ), hC p σ L f z₀ y x b hz₀ hb ?_⟩
  have : (fun τ => (lowM x τ).submatrix (σ τ).symm id * b τ) = g := funext fun τ => by rw [hu τ, ← e τ]
  rw [this]
  exact hg

end GlobalTheory.Reg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCuspFormNonzeroEveryComponent
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

noncomputable section

namespace GlobalTheory.RunJoin

theorem eval_ne_zero_of_nonZeroComp {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
    (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ Z, gF Z (X.inc u F) = 0) → F = 0)
    {u v : WeightFamilies.Wt D j} (g : B.Cusp j u) (hg : X.NonZeroComp u g) (Z : ι) (g' : B.Cusp j v)
    (h1 : gF Z (X.inc v g') ≠ 0) (h2 : ∀ Z', Z' ≠ Z → gF Z' (X.inc v g') = 0) : gF Z (X.inc u g) ≠ 0 := by
  intro h0
  obtain ⟨H, hH⟩ := X.inc_mul u v g g'
  have hz : H = 0 := by
    refine hinj _ H fun Z' => ?_
    rw [← hH, map_mul]
    by_cases e : Z' = Z
    · subst e
      rw [h0, zero_mul]
    · rw [h2 Z' e, mul_zero]
  have hg0 : g' = 0 := hg v g' (by rw [hH, hz, map_zero])
  exact h1 (by rw [hg0, map_zero, map_zero])

section Record

variable {D : D7} {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j)


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem generic_ne_zero_of_nonZeroComp (hG : GenFrEx (T.Q.Xo j) T.Q.c) {v u : WeightFamilies.Wt D j}
    (Z : Comp (T.Q.Xo j) T.Q.c) (w : (recB h.toLawsCore).Cusp j v) (hw : evC hG Z (w : T.R j) ≠ 0)
    (g : (recB h.toLawsCore).Cusp j u) (hg : (recPJ h j hj).NonZeroComp u g) : evC hG Z (g : T.R j) ≠ 0 := by
  have hT : GenFromTest (T.Q.Xo j) T.Q.c hG := fun Z => h.allTest j hj (Om Z) (genFr hG Z)
  have hV := GlobalTheory.Reg.genValInj_record D T h j hj hG
  obtain ⟨g', h1, h2⟩ := GlobalTheory.Reg.compSplit_record D T h j hj hG Z v w
  have := eval_ne_zero_of_nonZeroComp (recPlus h j hj) (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z)
    (fun Z => formsEvR j hG hT Z)
    (fun u F hF => hV u F fun Z => (formsEvR_inc h j hj hG hT Z u F).symm.trans (hF Z)) g hg Z g'
    (fun h0 => hw (h1.symm.trans ((formsEvR_inc h j hj hG hT Z v g').symm.trans h0)))
    (fun Z' e => (formsEvR_inc h j hj hG hT Z' v g').trans (h2 Z' e))
  exact fun h0 => this ((formsEvR_inc h j hj hG hT Z u g).trans h0)


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_cusp_reading_ne_zero (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ)
    (hN : ∀ k : (T.U j σ).Comp, ∃ x ∈ ((T.U j σ).X k).dom, ∃ f ∈ cutR T.C j w, rdU (T.U j σ) f k x ≠ 0) :
    ∃ F : (recB h.toLawsCore).Cusp j w, ∀ k : (T.U j σ).Comp, ∃ x ∈ ((T.U j σ).X k).dom,
      rdU (T.U j σ) (F.1 : T.R j) k x ≠ 0 := by
  choose x hx f hc hf0 using hN
  let p : (T.U j σ).Comp → Submodule T.Q.c.F (cutR T.C j w) := fun k =>
    { carrier := {F | rdU (T.U j σ) (F.1 : T.R j) k (x k) = 0}
      zero_mem' := by
        show rdU (T.U j σ) (0 : T.R j) k (x k) = 0
        rw [map_zero]; rfl
      add_mem' := by
        intro a b ha hb
        show rdU (T.U j σ) (a.1 + b.1 : T.R j) k (x k) = 0
        rw [map_add (f := _)]
        show rdU (T.U j σ) (a.1 : T.R j) k (x k) + rdU (T.U j σ) (b.1 : T.R j) k (x k) = 0
        rw [ha, hb, add_zero]
      smul_mem' := by
        intro c a ha
        show rdU (T.U j σ) (c • a.1 : T.R j) k (x k) = 0
        rw [LinearMap.map_smulₛₗ]
        show σ c * rdU (T.U j σ) (a.1 : T.R j) k (x k) = 0
        rw [ha, mul_zero] }
  have hne : ∀ k, p k ≠ ⊤ := by
    intro k htop
    have hm : (⟨f k, hc k⟩ : cutR T.C j w) ∈ p k := by rw [htop]; exact Submodule.mem_top
    exact hf0 k hm
  obtain ⟨F, hF⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hne
  exact ⟨F, fun k => ⟨x k, hx k, hF k⟩⟩

end Record


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_nonZeroComp_and_ne_zero : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (hG : GenFrEx (T.Q.Xo j) T.Q.c), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → (∃ g0 : (recB h.toLawsCore).Cusp j wF, (recPJ h j hj).NonZeroComp wF g0 ∧ ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z g0.1 ≠ 0) ∧ ∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u), (recPJ h j hj).NonZeroComp u F → (∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z F.1 ≠ 0) ∧ ∀ σ, GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp, ∃ x ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) F.1 k x ≠ 0 := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hG hOK
  have hP := hOK.hyp
  obtain ⟨hDF, -, hr, hl⟩ := (GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0
    hj.1 hP).1 wF (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hlp := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj wF hl
  have hg : ∀ i, 2 * WeightAlgebra.DF ka + 2 < D.host.g i := hP.2.2.2.1.2.2.2.2.2
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hdeg : 3 * WeightAlgebra.DF wF + 2 ≤ T.Q.l.M := by
    have h1 : (2 * WeightAlgebra.DF ka + 3) * 3 ≤ D.host.g 0 * D.host.g 1 :=
      Nat.mul_le_mul (hg 0) (by have := hg 1; omega)
    omega
  obtain ⟨g0, hg0⟩ := exists_cusp_reading_ne_zero h wF T.σ₀ fun k => by
    obtain ⟨x, hx⟩ := (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected _ ((T.U j T.σ₀).X k)).nonempty
    obtain ⟨f, hf, hf0⟩ := _root_.GlobalTheory.RunIn.exists_theta_ne_zero_record _root_.GlobalTheory.harmonicValue_chart_independent D T h j hj wF hr hdeg T.σ₀ T.good_σ₀ k x hx
    refine ⟨x, hx, f, ?_, hf0⟩
    rw [cutR_eq T.C hj]
    exact h.thCusp j hj _ _ (dom_wtA wF) hlp f hf
  have hZ : ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z g0.1 ≠ 0 := by
    intro Z hz
    obtain ⟨k, hk⟩ := (GlobalTheory.CompModel.comp_read_on_model D T h j hj hG T.σ₀ T.good_σ₀).1 Z
    obtain ⟨x, hx, hx0⟩ := hg0 k
    exact hx0 ((hk wF g0).1 hz x hx)
  refine ⟨⟨g0, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.nonzero_divisor_of_connected D T h j hj wF g0 T.σ₀ T.good_σ₀ hg0, hZ⟩, fun u F hF => ?_⟩
  have hFZ : ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z F.1 ≠ 0 := fun Z =>
    generic_ne_zero_of_nonZeroComp h hj hG Z g0 (hZ Z) F hF
  refine ⟨hFZ, fun σ hσ k => ?_⟩
  obtain ⟨Z, hk⟩ := (GlobalTheory.CompModel.comp_read_on_model D T h j hj hG σ hσ).2 k
  by_contra hno
  refine hFZ Z ((hk u F).2 fun x hx => ?_)
  by_contra h'
  exact hno ⟨x, hx, h'⟩

end GlobalTheory.RunJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.LinearDisjointAlgebraicClosure
section
noncomputable section

namespace GlobalTheory.GeomConn

section Algebra

open scoped TensorProduct IntermediateField
open Topology Filter

theorem linearDisjoint_algebraicClosure {K Ω L : Type} [Field K] [CharZero K] [Field Ω] [Field L] [Algebra K Ω]
    [Algebra Ω L] [Algebra K L] [IsScalarTower K Ω L]
    (h : ∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) : (algebraicClosure K L).LinearDisjoint Ω := by
  have : Algebra.IsIntegral K (algebraicClosure K L).toSubalgebra := (algebraicClosure.isAlgebraic K L).isIntegral
  refine Subalgebra.LinearDisjoint.of_linearDisjoint_finite_left _ _ fun B hB _ => ?_
  have halg : B.IsAlgebraic := fun x hx => (mem_algebraicClosure_iff (F := K)).1 (hB hx)
  let M : IntermediateField K L := halg.toIntermediateField
  haveI : FiniteDimensional K M := ‹Module.Finite K B›
  change M.LinearDisjoint Ω
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element K M
  have hi : IsIntegral K (θ : L) := (Algebra.IsIntegral.isIntegral (R := K) θ).map M.val
  have e : K⟮(θ : L)⟯ = M := by
    have := congrArg (IntermediateField.lift (F := M)) hθ
    simpa using this
  rw [← e]
  refine IntermediateField.LinearDisjoint.of_basis_left (IntermediateField.adjoin.powerBasis hi).basis ?_
  have hd := GlobalTheory.GeomIrr.natDegree_minpoly_eq (L := K) (F := Ω) (fun x hx => h x hx.isAlgebraic) hi
  have hl := linearIndependent_pow (K := Ω) (θ : L)
  rw [hd] at hl
  have he : (K⟮(θ : L)⟯.val ∘ (IntermediateField.adjoin.powerBasis hi).basis) =
      fun i : Fin (IntermediateField.adjoin.powerBasis hi).dim => (θ : L) ^ (i : ℕ) := by
    funext i
    simp
  rw [he]
  exact hl

theorem isDomain_tensor {K A Ω : Type} [Field K] [CharZero K] [CommRing A] [Field Ω] [Algebra K A] [Algebra K Ω]
    [Algebra.FiniteType K A] (j : A →ₐ[K] Ω) (hj : Function.Injective j)
    (h : ∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) (F : Type) [Field F] [Algebra K F] :
    IsDomain (F ⊗[K] A) := by
  let N := algebraicClosure K (AlgebraicClosure Ω)
  haveI : IsDomain (N ⊗[K] Ω) := (linearDisjoint_algebraicClosure h).isDomain
  haveI : IsAlgClosed N := IsAlgClosure.isAlgClosed K
  let φ := Algebra.TensorProduct.map (AlgHom.id K N) j
  have hφ : Function.Injective φ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := N) j.toLinearMap hj
  haveI : IsDomain (N ⊗[K] A) := Function.Injective.isDomain φ.toRingHom hφ
  exact GlobalTheory.GeomComp.isDomain_tensor_of_closure K N A F

theorem isPreconnected_points {K A : Type} [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    [Algebra K ℂ] [IsDomain (ℂ ⊗[K] A)] :
    IsPreconnected {x : A → ℂ | ∃ φ : A →ₐ[K] ℂ, ⇑φ = x} := by
  have hc := isConnected_basicOpen_complexPoints_of_dense
    (exists_isConnected_principalOpen noetherNormalization_primitive
      (isConnected_unramified_cover_of_irreducible isConnected_and_dense_compl_hypersurface
        exists_mvPolynomial_of_poly_bound_off_hypersurface))
    (principalOpen_dense_complexPoints noetherNormalization_primitive
      isConnected_and_dense_compl_hypersurface) (ℂ ⊗[K] A) 1 one_ne_zero
  have hf : Continuous fun (x : ℂ ⊗[K] A → ℂ) (a : A) => x (1 ⊗ₜ a) :=
    continuous_pi fun a => continuous_apply _
  convert hc.isPreconnected.image _ hf.continuousOn using 1
  ext x
  constructor
  · rintro ⟨φ, rfl⟩
    refine ⟨_, ⟨Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) φ fun _ _ => Commute.all _ _, rfl, by simp⟩, ?_⟩
    funext a
    simp
  · rintro ⟨_, ⟨φ, rfl, -⟩, rfl⟩
    exact ⟨(φ.restrictScalars K).comp Algebra.TensorProduct.includeRight, rfl⟩

theorem isPreconnected_points_over {K A Ω : Type} [Field K] [CharZero K] [CommRing A] [Field Ω] [Algebra K A]
    [Algebra K Ω] [Algebra.FiniteType K A] (j : A →ₐ[K] Ω) (hj : Function.Injective j)
    (h : ∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) (σ : K →+* ℂ) :
    IsPreconnected {g : A → ℂ | ∃ ρ : A →+* ℂ, ρ.comp (algebraMap K A) = σ ∧ ⇑ρ = g} := by
  letI : Algebra K ℂ := σ.toAlgebra
  haveI := isDomain_tensor j hj h ℂ
  convert isPreconnected_points (K := K) (A := A) using 1
  ext g
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    exact ⟨{ ρ with commutes' := fun a => RingHom.congr_fun hρ a }, rfl⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a, rfl⟩

end Algebra

open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.Reg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def ReadOn (U : Formalism.L2.PjFree.Unf Xo c σ r) {A : Type} [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A)
    (f : A → ℂ) (k : U.Comp) : Prop :=
  ∃ (ψ : A →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ)) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ),
    (∀ a, Formalism.L2.PjFree.toC (ψ a) = f a) ∧ FrMap ψ yA z ∧ FrBor t (U.un k x) z

theorem ReadOn.unique {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) {A : Type} [CommRing A]
    [Algebra c.F A] {yA : FrPt Xo c A} {f : A → ℂ} {k k' : U.Comp} (h : ReadOn U yA f k) (h' : ReadOn U yA f k') :
    k = k' := by
  obtain ⟨ψ, z, x, t, hψ, hz, ht⟩ := h
  obtain ⟨ψ', z', x', t', hψ', hz', ht'⟩ := h'
  obtain rfl : ψ = ψ' := AlgHom.ext fun a => (hψ a).trans (hψ' a).symm
  obtain rfl : z = z' := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c A (CAt σ) ψ yA).1 _ _ hz hz'
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)
  obtain ⟨ga, -, b, -, e⟩ := (hU.2.2.2.1 k k' x x').1 ⟨_, hmul _ _ _ _ _ ht (hinv _ _ _ ht')⟩
  exact (congrArg Sigma.fst e).symm

theorem ReadOn.eventually {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) {A : Type} [CommRing A] [Algebra c.F A] [Algebra.Smooth c.F A] {yA : FrPt Xo c A}
    {f : A → ℂ} {k : U.Comp} (h : ReadOn U yA f k) :
    ∀ᶠ g in 𝓝 f, (∃ ρ : A →+* ℂ, ρ.comp (algebraMap c.F A) = σ ∧ ⇑ρ = g) → ReadOn U yA g k := by
  classical
  obtain ⟨hL, -, -, -⟩ := _root_.GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨ψ₀, z₀, x₀, t₀, hf, hz₀, hb₀⟩ := h
  let φ₀ : A →+* ℂ := ψ₀.toRingHom
  obtain rfl : ⇑φ₀ = f := funext hf
  have hφ₀ : φ₀.comp (algebraMap c.F A) = σ := RingHom.ext fun a => ψ₀.commutes a
  obtain ⟨m, s, B, ψ, S, ε, hB, hε, hψ, hd, hnear⟩ :=
    GlobalTheory.SmoothPointFamily.exists_holomorphic_family c.F A σ φ₀ hφ₀
  let ψ' : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ) := fun b =>
    if hb : b ∈ B then
      { (show A →+* CAt σ from ψ b) with commutes' := fun a => RingHom.congr_fun (hψ b hb).1 a }
    else ψ₀
  have hψ' : ∀ b ∈ B, ∀ a, Formalism.L2.PjFree.toC (ψ' b a) = ψ b a := by
    intro b hb a
    simp only [ψ', dif_pos hb]
    rfl
  choose z hz using fun b => hL.bc _ _ (ψ' b) yA
  obtain ⟨h1, h2⟩ := hnear φ₀ hφ₀ (fun a _ => by simpa using hε)
  have e₀ : ψ' (fun i => φ₀ (s i)) = ψ₀ := AlgHom.ext fun a => by
    have := hψ' _ h1 a
    rw [h2] at this
    exact this
  have hz₀' : z₀ = z fun i => φ₀ (s i) :=
    (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c A (CAt σ) ψ₀ yA).1 _ _ hz₀ (e₀ ▸ hz _)
  obtain ⟨B₁, hB₁, hb₁, hloc⟩ := GlobalTheory.CompModel.exists_open_same_model U hσ hU yA ψ' z hB
    (fun a => (hd a).congr fun b hb => hψ' b hb a) (fun b _ => hz b) h1 (hz₀' ▸ hb₀)
  have e₁ : ∀ᶠ g : A → ℂ in 𝓝 ⇑φ₀, (fun i => g (s i)) ∈ B₁ :=
    (continuous_pi fun i => continuous_apply (s i)).continuousAt.eventually (hB₁.mem_nhds hb₁)
  have e₂ : ∀ᶠ g : A → ℂ in 𝓝 ⇑φ₀, ∀ a ∈ S, ‖g a - φ₀ a‖ < ε :=
    (eventually_all_finset S).2 fun a _ =>
      (((continuous_apply a).sub continuous_const).norm.continuousAt (x := ⇑φ₀)).eventually_lt
        continuousAt_const (by simpa using hε)
  filter_upwards [e₁, e₂] with g hg₁ hg₂
  rintro ⟨ρ, hρ, rfl⟩
  obtain ⟨h3, h4⟩ := hnear ρ hρ hg₂
  obtain ⟨x, t, ht⟩ := hloc _ hg₁
  exact ⟨ψ' _, z _, x, t, fun a => by rw [hψ' _ h3, h4], hz _, ht⟩

theorem ReadOn.eq_of_isPreconnected {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) {A : Type} [CommRing A] [Algebra c.F A] [Algebra.Smooth c.F A] {yA : FrPt Xo c A}
    (hc : IsPreconnected {g : A → ℂ | ∃ ρ : A →+* ℂ, ρ.comp (algebraMap c.F A) = σ ∧ ⇑ρ = g})
    {f f' : A → ℂ} {k k' : U.Comp} (h : ReadOn U yA f k) (h' : ReadOn U yA f' k') : k = k' := by
  obtain ⟨hL, -, -, -⟩ := _root_.GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hmem : ∀ {f k}, ReadOn U yA f k → ∃ ρ : A →+* ℂ, ρ.comp (algebraMap c.F A) = σ ∧ ⇑ρ = f := by
    rintro f k ⟨ψ, -, -, -, hψ, -⟩
    exact ⟨ψ.toRingHom, RingHom.ext fun a => ψ.commutes a, funext hψ⟩
  have key := hc.induction₂' (fun f g => ∀ k, ReadOn U yA f k → ReadOn U yA g k) (by
    rintro _ ⟨ρ, hρ, rfl⟩
    let ψ : A →ₐ[c.F] CAt σ := { (show A →+* CAt σ from ρ) with commutes' := fun a => RingHom.congr_fun hρ a }
    obtain ⟨z, hz⟩ := hL.bc _ _ ψ yA
    obtain ⟨k₀, x, t, ht⟩ := hU.2.2.1 z
    have h₀ : ReadOn U yA ρ k₀ := ⟨ψ, z, x, t, fun _ => rfl, hz, ht⟩
    filter_upwards [mem_nhdsWithin_of_mem_nhds (h₀.eventually hσ hU), self_mem_nhdsWithin] with g hg hgs
    exact ⟨fun k hk => h₀.unique hU hk ▸ hg hgs, fun k hk => (hg hgs).unique hU hk ▸ h₀⟩)
    (fun _ _ _ _ _ _ h₁ h₂ k hk => h₂ k (h₁ k hk)) (hmem h) (hmem h')
  exact (key k h).unique hU h'

theorem comp_eq_of_fnAlgClosed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → FnAlgClosed (Xo := Xo) (c := c) → ∀ (h : GenFrEx Xo c) (Z : Comp Xo c) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom), (∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y') → (∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k' x') y') → k = k' := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hac h Z k k' x x' hk hk'
  obtain ⟨hL, -, -, hA⟩ := _root_.GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)
  obtain ⟨C, ψ, z, t, hz, ht⟩ := hA h (Om Z) (genFr h Z)
  haveI := C.sm
  set_option synthInstance.maxHeartbeats 200000 in
  have hread : ∀ (k : U.Comp) (x : (U.X k).dom), (∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ))
      (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y') →
      ∃ f : C.R → ℂ, ReadOn (Formalism.L2.PjFree.Unf.ofPj U) (A := C.R) C.y f k := by
    rintro k x ⟨φ, y', t', hy', ht'⟩
    obtain ⟨w, hw⟩ := hL.bc _ _ φ z
    exact ⟨_, φ.comp ψ, w, x, _, fun _ => rfl, PullbackSections.frMap_trans _ _ hz hw,
      hmul _ _ _ _ _ ht' (hinv _ _ _ (GlobalTheory.SupGeneric.frBor_of_frMap φ ht hw hy'))⟩
  obtain ⟨f, hf⟩ := hread k x hk
  obtain ⟨f', hf'⟩ := hread k' x' hk'
  refine ReadOn.eq_of_isPreconnected (U := Formalism.L2.PjFree.Unf.ofPj U) hσ hU ?_ hf hf'
  exact isPreconnected_points_over C.R.val Subtype.val_injective (hac C.Z) σ

end GlobalTheory.GeomConn
end
end

