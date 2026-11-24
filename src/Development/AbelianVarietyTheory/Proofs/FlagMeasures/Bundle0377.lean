module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0375
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.NatSmulMulEq
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureFirst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0276
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0372

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ApproxGen
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GlobalApprox

theorem bcP_osmul (D : D7) (q : PlF D) (a : 𝓞 D.host.E) (m : (VS D).V) :
    baseChange₂ D q (a • m) = (D.s.atP q).ιE (a : D.host.E) • baseChange₂ D q m := by
  rw [← IsScalarTower.algebraMap_smul D.host.E a m]
  exact baseChange_smul₂ (D := D) q _ m

theorem osmul_mem (D : D7) (Z : LocDat D) (q : PlF D) (M : LV D) (m : (VS D).V) (hm : m ∈ M)
    (o : (D.s.atP q).Ep) (ho : o ∈ (D.s.atP q).O) : o • baseChange₂ D q m ∈ lattice₂ D Z.M q M := by
  have hO : (Z.M q).L.O = (D.s.atP q).O := (Z.agree q).2.2.2.1
  have ho' : o ∈ (Z.M q).L.O := by rw [hO]; exact ho
  have hgen : baseChange₂ D q m ∈ lattice₂ D Z.M q M := Submodule.subset_span ⟨m, hm, rfl⟩
  exact (lattice₂ D Z.M q M).smul_mem (⟨o, ho'⟩ : (Z.M q).L.O) hgen

theorem approx_gen (D : D7) (Z : LocDat D) (p : PlF D) (M : LV D) (m : (VS D).V) (hm : m ∈ M)
    (c : (D.s.atP p).Ep) (hc : c ∈ (D.s.atP p).O) :
    ∃ l ∈ M, (∃ w ∈ lattice₂ D Z.M p M, baseChange₂ D p l - c • baseChange₂ D p m = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • w) ∧
      ∀ p' : PlF D, p' ≠ p → ∃ w ∈ lattice₂ D Z.M p' M, baseChange₂ D p' l = (D.s.atP p').ιE ((gS D : ℕ) : D.host.E) • w := by
  obtain ⟨a, ⟨o, ho, hao⟩, hfar⟩ := _root_.GlobalTheory.CongrLoc.exists_int_congr_gS D p c hc
  refine ⟨a • m, M.smul_mem a hm, ⟨o • baseChange₂ D p m, osmul_mem D Z p M m hm o ho, ?_⟩, ?_⟩
  · rw [bcP_osmul, ← sub_smul, hao, mul_smul]
  · intro p' hp'
    obtain ⟨o', ho', hao'⟩ := hfar p' hp'
    exact ⟨o' • baseChange₂ D p' m, osmul_mem D Z p' M m hm o' ho', by rw [bcP_osmul, hao', mul_smul]⟩

theorem smul_step {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (g c : R) (b b' x w w' : V)
    (h : b - x = g • w) (h' : b' - c • b = g • w') : b' - c • x = g • (w' + c • w) := by
  rw [smul_add, ← h', smul_comm g c w, ← h, smul_sub]
  abel

theorem approx : ∀ (D : D7) (Z : LocDat D) (p : PlF D) (M : LV D) (x : Vp D p), x ∈ lattice₂ D Z.M p M → ∃ l ∈ M, (∃ w ∈ lattice₂ D Z.M p M, baseChange₂ D p l - x = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • w) ∧ ∀ p' : PlF D, p' ≠ p → ∃ w ∈ lattice₂ D Z.M p' M, baseChange₂ D p' l = (D.s.atP p').ιE ((gS D : ℕ) : D.host.E) • w := by
  intro D Z p M x hx
  have hO : (Z.M p).L.O = (D.s.atP p).O := (Z.agree p).2.2.2.1
  have hx' : x ∈ Submodule.span (Z.M p).L.O (baseChange₂ D p '' (M : Set (VS D).V)) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, hm, rfl⟩ := hy
    obtain ⟨l, hl, ⟨w, hw, hlw⟩, hfar⟩ := approx_gen D Z p M m hm 1 (Subring.one_mem _)
    rw [one_smul] at hlw
    exact ⟨l, hl, ⟨w, hw, hlw⟩, hfar⟩
  | zero =>
    refine ⟨0, M.zero_mem, ⟨0, (lattice₂ D Z.M p M).zero_mem, by simp⟩, fun p' _ => ?_⟩
    exact ⟨0, (lattice₂ D Z.M p' M).zero_mem, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨l₁, hl₁, ⟨w₁, hw₁, e₁⟩, f₁⟩ := hy
    obtain ⟨l₂, hl₂, ⟨w₂, hw₂, e₂⟩, f₂⟩ := hz
    refine ⟨l₁ + l₂, M.add_mem hl₁ hl₂, ⟨w₁ + w₂, (lattice₂ D Z.M p M).add_mem hw₁ hw₂, ?_⟩, ?_⟩
    · rw [map_add (f := _), smul_add, ← e₁, ← e₂]
      abel
    · intro p' hp'
      obtain ⟨v₁, hv₁, g₁⟩ := f₁ p' hp'
      obtain ⟨v₂, hv₂, g₂⟩ := f₂ p' hp'
      exact ⟨v₁ + v₂, (lattice₂ D Z.M p' M).add_mem hv₁ hv₂, by rw [map_add (f := _), g₁, g₂, smul_add]⟩
  | smul r y _ hy =>
    obtain ⟨l, hl, ⟨w, hw, e⟩, _⟩ := hy
    have hr : (r : (D.s.atP p).Ep) ∈ (D.s.atP p).O := by rw [← hO]; exact r.2
    obtain ⟨l', hl', ⟨w', hw', e'⟩, hfar'⟩ := approx_gen D Z p M l hl (r : (D.s.atP p).Ep) hr
    refine ⟨l', hl', ⟨w' + r • w, (lattice₂ D Z.M p M).add_mem hw' ((lattice₂ D Z.M p M).smul_mem r hw), ?_⟩, hfar'⟩
    exact smul_step _ (r : (D.s.atP p).Ep) (baseChange₂ D p l) (baseChange₂ D p l') y w w' e e'

end GlobalTheory.GlobalApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EvalConvGroupAlg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.SRe.ConvStep
variable {D : D7}

theorem kset_one (X : HidaSetting D) : (1 : X.B.I.Gf) ∈ X.B.I.Kset := by
  show ((1 : X.B.I.Gf) : GL _ _) ∈ Formalism.UG.stabGL X.B.I.Lf
  rw [OneMemClass.coe_one]
  exact (Formalism.UG.stabGL X.B.I.Lf).one_mem

theorem kset_mul (X : HidaSetting D) {x y : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hy : y ∈ X.B.I.Kset) :
    x * y ∈ X.B.I.Kset := by
  show ((x * y : X.B.I.Gf) : GL _ _) ∈ Formalism.UG.stabGL X.B.I.Lf
  rw [Subgroup.coe_mul]
  exact mul_mem hx hy

theorem kset_inv (X : HidaSetting D) {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) : x⁻¹ ∈ X.B.I.Kset := by
  show ((x⁻¹ : X.B.I.Gf) : GL _ _) ∈ Formalism.UG.stabGL X.B.I.Lf
  rw [Subgroup.coe_inv]
  exact inv_mem hx

theorem red_one (X : HidaSetting D) {red : X.B.I.Gf → G0g D.nd} (hr : IsRedHom X red) : red 1 = 1 := by
  have h := hr.2.1 1 (kset_one X) 1 (kset_one X)
  rw [one_mul] at h
  exact mul_left_cancel (a := red 1) (by rw [mul_one]; exact h.symm)

theorem fibre_iff (X : HidaSetting D) {red : X.B.I.Gf → G0g D.nd} (hr : IsRedHom X red) {s : X.B.I.Gf}
    (hs : s ∈ X.B.I.Kset) (x : X.B.I.Gf) :
    (x ∈ X.B.I.Kset ∧ red x = red s) ↔ s⁻¹ * x ∈ X.B.I.Kg X.B.g := by
  have hsi : s⁻¹ ∈ X.B.I.Kset := kset_inv X hs
  have hinv : red s⁻¹ = (red s)⁻¹ := by
    have h1 := hr.2.1 s⁻¹ hsi s hs
    rw [inv_mul_cancel, red_one X hr] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  constructor
  · rintro ⟨hx, hrx⟩
    have hk : s⁻¹ * x ∈ X.B.I.Kset := kset_mul X hsi hx
    refine (hr.2.2.2 _ hk).1 ?_
    rw [hr.2.1 _ hsi _ hx, hinv, hrx, inv_mul_cancel]
  · intro hk
    have hkK : s⁻¹ * x ∈ X.B.I.Kset := hk.1
    have hr1 : red (s⁻¹ * x) = 1 := (hr.2.2.2 _ hkK).2 hk
    have h2 := kset_mul X hs hkK
    rw [mul_inv_cancel_left] at h2
    refine ⟨h2, ?_⟩
    have h3 := hr.2.1 _ hs _ hkK
    rw [mul_inv_cancel_left, hr1, mul_one] at h3
    exact h3

theorem one_le_g (X : HidaSetting D) : 1 ≤ X.B.g := by
  rw [X.g_eq]
  exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)

theorem kg_open (X : HidaSetting D) : IsOpen (X.B.I.Kg X.B.g) := X.B.I.topf_open X.B.g (one_le_g X)

theorem kg_pos_fin (X : HidaSetting D) : 0 < X.B.μf (X.B.I.Kg X.B.g) ∧ X.B.μf (X.B.I.Kg X.B.g) < ⊤ := by
  have hne : (X.B.I.Kg X.B.g).Nonempty := ⟨1, by
    refine ⟨kset_one X, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
    simp [Formalism.MainNotions.S.AutInst.fmat]⟩
  refine ⟨(kg_open X).measure_pos X.B.μf hne, ?_⟩
  exact lt_of_le_of_lt (measure_mono fun x hx => hx.1) (PI.WAU.Cpt.isCompact_Kset X.B.I).measure_lt_top

theorem fibre_meas (X : HidaSetting D) {red : X.B.I.Gf → G0g D.nd} (hr : IsRedHom X red) {s : X.B.I.Gf}
    (hs : s ∈ X.B.I.Kset) :
    MeasurableSet {x | x ∈ X.B.I.Kset ∧ red x = red s} ∧
      X.B.μf {x | x ∈ X.B.I.Kset ∧ red x = red s} = X.B.μf (X.B.I.Kg X.B.g) := by
  have e : {x | x ∈ X.B.I.Kset ∧ red x = red s} = (fun x => s⁻¹ * x) ⁻¹' (X.B.I.Kg X.B.g) := by
    ext x; exact fibre_iff X hr hs x
  rw [e]
  refine ⟨((kg_open X).preimage (continuous_const_mul s⁻¹)).measurableSet, ?_⟩
  exact measure_preimage_mul X.B.μf s⁻¹ _

open scoped InnerProductSpace in
theorem top_expand [Fintype (G0g D.nd)] (X : HidaSetting D) {red : X.B.I.Gf → G0g D.nd} (hr : IsRedHom X red)
    (s0 : G0g D.nd → X.B.I.Gf) (hs0 : ∀ γ, s0 γ ∈ X.B.I.Kset ∧ red (s0 γ) = γ) (a : G0g D.nd → ℂ)
    (Top : L2X X →L[ℂ] L2X X)
    (hT : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R
      (fun x => if x ∈ X.B.I.Kset then a (red x) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) else 0) Top)
    (y : L2X X) (hy : ∀ k ∈ X.B.I.Kset, X.B.R (1, k) y = X.B.R (1, s0 (red k)) y) :
    Top y = ∑ γ, a γ • X.B.R (1, s0 γ) y := by
  apply ext_inner_left ℂ
  intro x
  rw [hT.2 x y, inner_sum]
  simp only [inner_smul_right]
  set V : ℝ := (X.B.μf (X.B.I.Kg X.B.g)).toReal with hV
  have hVpos : 0 < V := ENNReal.toReal_pos (kg_pos_fin X).1.ne' (kg_pos_fin X).2.ne
  have hV0 : (V : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hVpos.ne'
  let Fb : G0g D.nd → Set X.B.I.Gf := fun γ => {z | z ∈ X.B.I.Kset ∧ red z = γ}
  have hFb : ∀ γ, MeasurableSet (Fb γ) ∧ X.B.μf (Fb γ) = X.B.μf (X.B.I.Kg X.B.g) := by
    intro γ
    have := fibre_meas X hr (hs0 γ).1
    rw [(hs0 γ).2] at this
    exact this
  let cf : G0g D.nd → ℂ := fun γ => a γ / (V : ℂ) * ⟪x, X.B.R (1, s0 γ) y⟫_ℂ
  have hpt : ∀ g : X.B.I.Gf,
      (if g ∈ X.B.I.Kset then a (red g) / (V : ℂ) else 0) * ⟪x, X.B.R (1, g) y⟫_ℂ =
        ∑ γ, (Fb γ).indicator (fun _ => cf γ) g := by
    intro g
    by_cases hg : g ∈ X.B.I.Kset
    · rw [if_pos hg, Finset.sum_eq_single (red g)]
      · rw [Set.indicator_of_mem (show g ∈ Fb (red g) from ⟨hg, rfl⟩), hy g hg]
      · intro b _ hb
        exact Set.indicator_of_notMem (by exact fun hm => hb hm.2.symm) _
      · intro h1; exact absurd (Finset.mem_univ _) h1
    · rw [if_neg hg, zero_mul]
      symm
      refine Finset.sum_eq_zero fun b _ => ?_
      exact Set.indicator_of_notMem (by exact fun hm => hg hm.1) _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun γ _ => ?_
    rw [integral_indicator_const _ (hFb γ).1, measureReal_def, (hFb γ).2, ← hV]
    simp only [cf, Complex.real_smul]
    field_simp
  · intro γ _
    refine (integrable_indicator_iff (hFb γ).1).2 ?_
    refine integrableOn_const ?_
    rw [(hFb γ).2]; exact (kg_pos_fin X).2.ne

end GlobalTheory.Mem.SRe.ConvStep

namespace GlobalTheory.Mem.SRe

end GlobalTheory.Mem.SRe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueMultMap
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntertwMult

theorem contRep_facts (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (hF : I.IsFundDom (I.muA μf) fund)
    (hR : I.IsRightReg μf fund R) (y : I.L2 μf fund) (f : I.GA → ℂ) (hc : Continuous f)
    (hi : ∀ γ ∈ I.GFset, ∀ x, f (γ * x) = f x) (he : ∀ᵐ x ∂(I.muA μf), f x = I.ext y x) :
    (∀ f' : I.GA → ℂ, Continuous f' → (∀ᵐ x ∂(I.muA μf), f' x = I.ext y x) → f' = f) ∧
    (I.IsCuspFn (I.muA μf) (I.ext y) → I.IsCuspFn (I.muA μf) f) ∧
    ∀ (k : I.GA) (c : ℂ), R k y = c • y → ∀ x, f (x * k) = c * f x := by
  classical
  have hH : I.IsHilbTensor (H := fun _ => ℂ) (fun _ _ => ContinuousLinearMap.id ℂ ℂ)
      (fun _ => ContinuousLinearMap.id ℂ ℂ) (fun x => ∏ v, x v) := by
    refine ⟨fun x y => ?_, fun _ _ => rfl, ?_⟩
    · simp only [RCLike.inner_apply, map_prod, ← Finset.prod_mul_distrib]
    · have hspan : Submodule.span ℂ (Set.range fun x : (∀ _ : InfinitePlace I.F, ℂ) => ∏ v, x v) = ⊤ := by
        refine eq_top_iff.2 fun z _ => ?_
        have h1 : (1 : ℂ) ∈ Set.range fun x : (∀ _ : InfinitePlace I.F, ℂ) => ∏ v, x v :=
          ⟨fun _ => 1, by simp⟩
        simpa using Submodule.smul_mem _ z (Submodule.subset_span h1)
      rw [hspan, Submodule.top_coe]
      exact dense_univ
  let B : RowsAut := GlobalTheory.RepSmooth.bundle I μf fund R (fun _ => ℂ) (fun _ => inferInstance)
    (fun _ _ => ContinuousLinearMap.id ℂ ℂ) ℂ (fun _ => ContinuousLinearMap.id ℂ ℂ) (fun x => ∏ v, x v) hF hR hH 1
  have hy : GlobalTheory.Dec.IsContRep B y f := GlobalTheory.RepSmooth.isContRep_of_ae B hc hi he
  obtain ⟨-, -, htr, hfin⟩ := GlobalTheory.ExtContRep.ext_ae_eq_contRep B y f hy
  obtain ⟨huniq, hlin, -, -⟩ := GlobalTheory.ContRepUniq.contRep_unique_linear B
  refine ⟨fun f' hc' he' => ?_, fun hcu W hW ν hν => ?_, fun k c hk x => ?_⟩
  · have hae : ∀ᵐ x ∂(I.muA μf), f' x = f x := by
      filter_upwards [he', he] with x h1 h2
      rw [h1, h2]
    exact GlobalTheory.RepSmooth.eq_of_ae B hc' hc hae
  · haveI : IsFiniteMeasure ν := hν.1
    filter_upwards [hcu W hW ν hν, hfin ν inferInstance] with x h1 h2
    have h2' : ∀ᵐ m ∂ν, I.ext y (m * x) = f (m * x) := h2
    rw [← h1]
    exact integral_congr_ae (h2'.mono fun m hm => hm.symm)
  · have h3 : GlobalTheory.Dec.IsContRep B (R k y) (fun x => f (x * k)) := htr k
    rw [hk] at h3
    have h4 := hlin y y f f (c - 1) hy hy
    have e1 : y + (c - 1) • y = c • y := by
      rw [sub_smul, one_smul, add_sub_cancel]
    rw [e1] at h4
    have h5 : f (x * k) = f x + (c - 1) * f x := congrFun (huniq _ _ _ h3 h4) x
    rw [h5]
    ring

end GlobalTheory.IntertwMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedTermFrameAdmissibleIntegral
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.AdmGlued

theorem gS_pos (D : D7) : 0 < gS D :=
  Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos

theorem mem_localization_of_mem' {D : D7} (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) {L : LV D} {x : (VS D).V}
    (hx : x ∈ L) : x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L) :=
  ⟨1, P.asIdeal.primeCompl.one_mem, by simpa using hx⟩

theorem localization_mono {D : D7} (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) {L M : LV D} (h : L ≤ M) :
    (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L) ≤ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M) := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, h hx⟩

theorem frame_mem_locP {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LV D) (h : IsRowLat D F0 Λ)
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (a : Fin (D.R.rS + 1)) : frame (lf D F0) a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
  obtain ⟨-, ⟨-, -, hlift, hconv⟩, -⟩ := h
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have hz : (lf D F0).fl.z ∈ Λ := hlift.1
    have e : frame (lf D F0) (Fin.last D.R.rS) = (lf D F0).fl.z := by simp [frame, FlagG.fvec]
    rw [e]
    exact mem_localization_of_mem' P hz
  · obtain ⟨c, -, hc1, heq⟩ := hconv.1 P
    have e : frame (lf D F0) i.castSucc = (lf D F0).fl.e i := by simp [frame, FlagG.fvec]
    rw [e]
    have hmem : (lf D F0).fl.e i ∈ Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • (lf D F0).fl.e a) := by
      have := Submodule.subset_span (R := 𝓞 D.host.E) ⟨i, rfl⟩ (s := Set.range fun a => c a • (lf D F0).fl.e a)
      simpa [hc1 hP i] using this
    have h1 := mem_localization_of_mem' P hmem
    rw [← heq] at h1
    exact localization_mono P inf_le_left h1

theorem glued_frame_PD : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ g g', Adapt g (lf D (X.Fu u)) F → Adapt g' (lf D (X.Fu u')) F' → IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) → IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap g'⁻¹ Λ) → Formalism.L2.SG.TermDef.PD D (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D (X.Fu u)) u' (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) := by
  intro D X Y u u' F F' w hw hG Z FP hB hR Λ y hL g g' hA hA' hr hr'
  have hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hA.1
  have hg' : g' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hA'.1
  have hβ : g⁻¹ * g' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (inv_mem hg) hg'
  have hmap : Formalism.HermitianLatticesTheory.gmap (g⁻¹ * g') (Formalism.HermitianLatticesTheory.gmap g'⁻¹ Λ) = Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ := by
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [← Submodule.map_comp]
    congr 1
    ext x
    simp
  have hmapL : mapLF (g⁻¹ * g') (lf D (X.Fu u')) = Formalism.L2.SG.Saturated.mapL (g⁻¹ * g') hβ (lf D (X.Fu u')) := by
    unfold mapLF; rw [dite_eq_left hβ]; rfl
  obtain ⟨-, ⟨-, -, hlift', hconv'⟩, hX'⟩ := id hr'
  refine ⟨?_, ?_, ?_⟩
  · have h1 := (Formalism.L2.SG.Pf.IsLift_mapL (g⁻¹ * g') hβ _ _).2 hlift'
    rw [hmap, ← hmapL] at h1
    exact h1
  · exact GlobalTheory.T.glue_frame_congruences_unitriangular_integral (VS D) D.R.rS _ (gS D) (gS_pos D) _ _
      (fun P hP a => frame_mem_locP _ _ hr P hP a)
      (fun P hP => GlobalTheory.T.gluedFrame_congruent_unitriangular_at_primes D X Y u u' F F' w hw hG Z FP hB hR Λ y hL g g' hA hA' hr hr' P hP)
  · exact GlobalTheory.FrameIsom.frameOK_mapLF D (g⁻¹ * g') hβ _ _ hmap _ _ ⟨hconv', hX'⟩

end GlobalTheory.Unfold.AdmGlued
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermNoDefectPrimeToInvariants
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocNoDef
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

section Gen

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem N_unitary (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) : ∀ n ∈ Fr.N, IsUnitary H n := by
  intro n hn
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact hx.1
  | one => intro a b; rfl
  | mul x y _ _ hx hy => intro a b; rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx, hy]
  | inv x _ hx =>
    intro a b
    have hxx : ∀ v, x (x⁻¹ v) = v := fun v => by rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
    rw [← hx (x⁻¹ a) (x⁻¹ b), hxx, hxx]

theorem frame_mem_lamStd (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f))
    (hL : Fr.IsInner L) (b : Fin (r + 1)) : Fr.f b ∈ Fr.LamStd L := by
  apply Submodule.subset_span
  obtain ⟨-, -, xz, hxz, hxzL, -⟩ := hL
  induction b using Fin.lastCases with
  | last =>
    have h1 : ∀ a, H.h (Fr.f (Fin.last r)) (Fr.es a) = 0 := fun a => by
      rw [H.h_herm (Fr.es a), Fr.h_sz, map_zero]
    have h2 : ∀ a : Fin r, H.h (Fr.f (Fin.last r)) (Fr.e a) = 0 := fun a =>
      Fr.h_iso _ _ (Or.inr (Fin.castSucc_lt_last a).ne)
    refine ⟨fun a => by rw [h1]; exact M.L.O.zero_mem, fun a => by rw [h2]; exact M.L.O.zero_mem, xz, ?_, hxzL⟩
    simp [FrameD.prF, h1, h2, hxz, FrameD.z]
  | cast a =>
    have h1 : ∀ c, H.h (Fr.f a.castSucc) (Fr.es c) = if a = c then 1 else 0 := fun c => Fr.h_es a c
    have h2 : ∀ c : Fin r, H.h (Fr.f a.castSucc) (Fr.e c) = 0 := fun c =>
      Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)
    refine ⟨fun c => ?_, fun c => by rw [h2]; exact M.L.O.zero_mem, 0, ?_, by simp⟩
    · rw [h1]; split_ifs
      · exact M.L.O.one_mem
      · exact M.L.O.zero_mem
    · have h2' : ∀ c : Fin r, H.h (Fr.f a.castSucc) (Fr.f c.castSucc) = 0 := h2
      simp [FrameD.prF, h1, h2', FrameD.e]

theorem noDefect_gen (H : HermSp M V) {r : ℕ} (P : FPair H r) (hR : P.RelG (theta M)) (hP : P.PrimeTo)
    (d : Datum P) (t : Term V M r) (ht : IsTermOver P d t) : ¬ BBne (H := H) t := by
  rintro ⟨v, hvΛ, hvE, hvO⟩
  have hs : M.split = none := hP.1
  have hMM : H.MMfam t = Sum.elim t.f t.f' := by
    unfold HermSp.MMfam; rw [hs]
  rw [hMM] at hvE hvO
  obtain ⟨hT, hT', ⟨n, hn, hf, hΛ⟩, ⟨n', hn', hf', hΛ'⟩, -⟩ := ht
  have hu := N_unitary H P.A n hn
  have hu' := N_unitary H P.B n' hn'

  have hint : ∀ x ∈ t.abelian₂, ∀ y ∈ t.abelian₂, H.h x y ∈ M.L.O := by
    intro x hx y hy
    rw [hΛ] at hx hy
    obtain ⟨x0, hx0, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨y0, hy0, rfl⟩ := Submodule.mem_map.mp hy
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    rw [hu]
    exact _root_.GlobalTheory.LocStdInt.lamStd_integral H P.A d.L d.hL x0 hx0 y0 hy0
  have hmem : ∀ i, Sum.elim t.f t.f' i ∈ t.abelian₂ := by
    rintro (b | b)
    · simp only [Sum.elim_inl, hf]
      rw [hΛ]
      exact Submodule.mem_map_of_mem (f := ((n : V →ₗ[E] V).restrictScalars M.L.O))
        (frame_mem_lamStd H P.A d.L d.hL b)
    · simp only [Sum.elim_inr, hf']
      rw [hΛ']
      exact Submodule.mem_map_of_mem (f := ((n' : V →ₗ[E] V).restrictScalars M.L.O))
        (frame_mem_lamStd H P.B d.L' d.hL' b)
  have hDl : ∀ l, H.Dl t.f t.f' l = H.Dl P.A.f P.B.f l := by
    intro l
    rw [hf, hf']
    exact GlobalTheory.T.pairingLeadingMinor_eq_of_unitriangular_changes H _ _ _ _ (GlobalTheory.T.isFamilyUnitriangularChange_of_mem_frameUnipotent H P.A n hn) (GlobalTheory.T.isFamilyUnitriangularChange_of_mem_frameUnipotent H P.B n' hn') l
  have hG : H.Gdet t.f t.f' t.T t.T' = P.Gv := by
    simp only [HermSp.Gdet, hDl, hT, hT', FPair.Gv]
  have hfr : ∀ (Fr : FrameD H r) (g : V ≃ₗ[E] V), IsUnitary H g → ∀ a b,
      H.h (g (Fr.f a)) (g (Fr.f b)) =
        if a = Fin.last r ∧ b = Fin.last r then -(algebraMap F E Fr.T) else 0 := by
    intro Fr g hg a b
    rw [hg]
    split_ifs with hab
    · rw [hab.1, hab.2]; exact Fr.h_zz
    · apply Fr.h_iso
      tauto
  have hdet := _root_.GlobalTheory.GramDet.det_gram_sum_elim H t.f t.f' t.T t.T'
    (by intro a b; rw [hf, hT]; exact hfr P.A n hu a b)
    (by intro a b; rw [hf', hT']; exact hfr P.B n' hu' a b)
    (by rw [hDl]; exact hR.2.1)
  rw [hG] at hdet
  have hU : IsUnitO M (H.gram (Sum.elim t.f t.f')).det := by
    obtain ⟨h1, y, hy, hxy⟩ := hP.2.1
    rcases hdet with h | h
    · rw [h]; exact ⟨h1, y, hy, hxy⟩
    · rw [h]
      refine ⟨M.L.O.neg_mem h1, -y, M.L.O.neg_mem hy, ?_⟩
      rw [neg_mul_neg]; exact hxy
  exact hvO (_root_.GlobalTheory.satur_of_gram_det_unit H t.abelian₂ hint (Sum.elim t.f t.f') hmem hU v hvΛ hvE)

end Gen

theorem noDefect : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), (FP p).RelG (LocNG.theta (Z.M p)) → (FP p).PrimeTo → ∀ (d : LocNG.Datum (FP p)) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS), LocNG.IsTermOver (FP p) d t → ¬ LocNG.BBne (H := locH Z p) t :=
  fun _ _ FP p hR hP d t ht => noDefect_gen _ (FP p) hR hP d t ht

end GlobalTheory.LocNoDef

end
end

