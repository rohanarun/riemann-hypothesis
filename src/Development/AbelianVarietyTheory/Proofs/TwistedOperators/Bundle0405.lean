module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepConjSourceLineEqTargetLine
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0349

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatGlueLatIffDual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links
open Formalism.IndefR.Datum (IsSelfDualC)
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.AdIsom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents
open GlobalTheory.StdFrames hiding OA
open GlobalTheory.IdemSupport (cP cO)
open GlobalTheory.NormSum.AdLattice (lat)

variable {D : D7}

section Flat

variable {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V} {u : D.what₂.Word}

theorem vA_surj (V : HSp D) (x : Fin V.rank → D.host.E) : ∃ y : V.V, vA V y = fun i => inc D (x i) :=
  ⟨(Formalism.L2.Herm.crd V).symm x, funext fun i => by simp [vA]⟩

theorem eq_sum_vA_frame (x : Fin X.rank → EAf D) : x = ∑ i, x i • vA X (X.frame i) := by
  funext k
  have : ∀ i, vA X (X.frame i) k = if i = k then 1 else 0 := fun i => by
    change inc D (X.frame.repr (X.frame i) k) = _
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact map_one _
    · exact map_zero _
  simp [Finset.sum_apply, this]

theorem adelic_induction {p : (Fin X.rank → EAf D) → Prop} (h1 : ∀ x : X.V, p (vA X x)) (h0 : p 0)
    (hadd : ∀ x y, p x → p y → p (x + y)) (hsm : ∀ (a : EAf D) x, p x → p (a • x)) (x : Fin X.rank → EAf D) : p x := by
  rw [eq_sum_vA_frame x]
  exact Finset.sum_induction _ p hadd h0 fun i _ => hsm _ _ (h1 _)

theorem hA_zero_left (V : HSp D) (y : Fin V.rank → EAf D) : hA V 0 y = 0 := by simp [hA, Formalism.UG.hform]

theorem hA_zero_right (V : HSp D) (y : Fin V.rank → EAf D) : hA V y 0 = 0 := by simp [hA, Formalism.UG.hform]

theorem hA_mA_mA (h : HSpace.IsIsomEmb X Y ι) (x x' : Fin X.rank → EAf D) :
    hA Y (mA Y X ι *ᵥ x) (mA Y X ι *ᵥ x') = hA X x x' := by
  induction x using adelic_induction with
  | h1 x =>
    induction x' using adelic_induction with
    | h1 x' => rw [mA_mulVec_vA, mA_mulVec_vA, hA_vA, hA_vA, HSpace.hD, HSpace.hD, h]
    | h0 => rw [mulVec_zero, hA_zero_right, hA_zero_right]
    | hadd a b ha hb => rw [mulVec_add, hA_add_right, hA_add_right, ha, hb]
    | hsm c a ha => rw [mulVec_smul, hA_smul_right, hA_smul_right, ha]
  | h0 => rw [mulVec_zero, hA_zero_left, hA_zero_left]
  | hadd a b ha hb => rw [mulVec_add, hA_add_left, hA_add_left, ha, hb]
  | hsm c a ha => rw [mulVec_smul, hA_smul_left, hA_smul_left, ha]

theorem hA_mA_vA (h : IsLine Y X ι z u) (x : Fin X.rank → EAf D) : hA Y (mA Y X ι *ᵥ x) (vA Y z) = 0 := by
  induction x using adelic_induction with
  | h1 x => rw [mA_mulVec_vA, hA_vA, h.2.1, RingHom.map_zero]
  | h0 => rw [mulVec_zero, hA_zero_left]
  | hadd a b ha hb => rw [mulVec_add, hA_add_left, ha, hb, add_zero]
  | hsm c a ha => rw [mulVec_smul, hA_smul_left, ha, mul_zero]

theorem hA_flat (h : IsLine Y X ι z u) (x x' : Fin X.rank → EAf D) (a a' : EAf D) :
    hA Y (mA Y X ι *ᵥ x + a • vA Y z) (mA Y X ι *ᵥ x' + a' • vA Y z) = hA X x x' - a * cjA D a' * inc D (Tu D u) := by
  have h1 : hA Y (vA Y z) (mA Y X ι *ᵥ x') = 0 := by rw [← cjA_hA, hA_mA_vA h, RingHom.map_zero]
  rw [hA_add_left, hA_add_right, hA_add_right, hA_smul_left, hA_smul_left, hA_smul_right, hA_smul_right,
    hA_mA_mA h.1, hA_mA_vA h, h1, hA_vA, h.2.2, RingHom.map_neg]
  ring

theorem inc_inv_mul (u : D.what₂.Word) : inc D (Tu D u)⁻¹ * inc D (Tu D u) = 1 := by
  rw [← RingHom.map_mul, inv_mul_cancel₀ (Tu_ne_zero u), RingHom.map_one]

theorem cjA_inc_Tu (u : D.what₂.Word) : cjA D (inc D (Tu D u)) = inc D (Tu D u) := by rw [cjA_inc, star_natCast]

theorem cjA_inc_inv (u : D.what₂.Word) : cjA D (inc D (Tu D u)⁻¹) = inc D (Tu D u)⁻¹ := by
  rw [cjA_inc, star_inv₀, star_natCast]

theorem inc_Tu_mem (u : D.what₂.Word) : inc D (Tu D u) ∈ OA D := by
  rw [map_natCast]; exact natCast_mem _ _

theorem eq_zero_of_hA {V : HSp D} {x : Fin V.rank → EAf D} (h : ∀ y, hA V x y = 0) : x = 0 := by
  have h1 : V.gram.map (inc D) *ᵥ x = 0 := funext fun i => by
    rw [← Formalism.UG.P.sf_single (cjA D)]; exact h _
  exact Matrix.mulVec_injective_of_isUnit (isUnit_gram V) (h1.trans (mulVec_zero _).symm)

theorem flat_inj (h : IsLine Y X ι z u) {x x' : Fin X.rank → EAf D} {a a' : EAf D}
    (e : mA Y X ι *ᵥ x + a • vA Y z = mA Y X ι *ᵥ x' + a' • vA Y z) : x = x' ∧ a = a' := by
  constructor
  · rw [← sub_eq_zero]
    refine eq_zero_of_hA fun y => ?_
    have h1 := hA_flat h x y a 0
    rw [e, hA_flat h] at h1
    rw [hA_sub_left]
    simp only [RingHom.map_zero, mul_zero, zero_mul, sub_zero] at h1
    rw [h1, sub_self]
  · have h1 := hA_flat h x 0 a (inc D (Tu D u)⁻¹)
    rw [e, hA_flat h, hA_zero_right, hA_zero_right, cjA_inc_inv, mul_assoc, mul_assoc, inc_inv_mul] at h1
    linear_combination h1

theorem mem_glueLat {L₀ : Lat X} {x₀ : X.V} (y : Y.V) : y ∈ glueLat Y X ι z u L₀ x₀ ↔
    ∃ x : X.V, Formalism.L2.Herm.crd X x ∈ L₀ ∧ ∃ a : 𝓞 D.host.E, y = ι x + (a : D.host.E) • ((Tu D u)⁻¹ • z + ι x₀) := by
  rw [glueLat, Submodule.mem_sup]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, b, hb, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hb
    exact ⟨x, hx, a, by rw [← algebraMap_smul D.host.E a]; rfl⟩
  · rintro ⟨x, hx, a, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, Submodule.mem_span_singleton.2 ⟨a, rfl⟩, by rw [← algebraMap_smul D.host.E a]; rfl⟩


set_option maxHeartbeats 1600000 in
theorem mem_hat_glueLat {L₀ : Lat X} {x₀ : X.V} (y : Fin Y.rank → EAf D) :
    y ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) ↔ ∃ x ∈ hat L₀, ∃ a ∈ OA D,
      y = mA Y X ι *ᵥ (x + a • vA X x₀) + (a * inc D (Tu D u)⁻¹) • vA Y z := by
  constructor
  · intro hy
    refine hat_induction (p := fun y => ∃ x ∈ hat L₀, ∃ a ∈ OA D,
      y = mA Y X ι *ᵥ (x + a • vA X x₀) + (a * inc D (Tu D u)⁻¹) • vA Y z) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, a, rfl⟩ := (mem_glueLat y).1 hy
      refine ⟨vA X x, inc_mem_hat hx, inc D a, (inc_mem_iff _).2 ⟨a, rfl⟩, ?_⟩
      change vA Y _ = _
      rw [vA_add, vA_smul, vA_add, vA_smul, mulVec_add, mulVec_smul, mA_mulVec_vA, mA_mulVec_vA, smul_add, smul_smul]
      abel
    · exact ⟨0, zero_mem_hat, 0, zero_mem _, by rw [zero_smul, add_zero, mulVec_zero, zero_mul, zero_smul, add_zero]⟩
    · rintro _ _ ⟨x, hx, a, ha, rfl⟩ ⟨x', hx', a', ha', rfl⟩
      refine ⟨x + x', add_mem_hat hx hx', a + a', add_mem ha ha', ?_⟩
      rw [add_smul, add_mul, add_smul, add_add_add_comm x, mulVec_add _ (x + _)]
      abel
    · rintro c hc _ ⟨x, hx, a, ha, rfl⟩
      refine ⟨c • x, smul_mem_hat hc hx, c * a, mul_mem hc ha, ?_⟩
      rw [smul_add, ← mulVec_smul, smul_add, smul_smul, smul_smul, mul_assoc]
  · rintro ⟨x, hx, a, ha, rfl⟩
    have h1 : mA Y X ι *ᵥ x ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) := by
      refine hat_induction (p := fun x => mA Y X ι *ᵥ x ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)))
        ?_ ?_ ?_ ?_ hx
      · intro x hx
        obtain ⟨x, rfl⟩ := (Formalism.L2.Herm.crd X).surjective x
        change mA Y X ι *ᵥ vA X x ∈ _
        rw [mA_mulVec_vA]
        exact vA_mem_hat Y ((mem_glueLat _).2 ⟨x, hx, 0, by simp⟩)
      · rw [mulVec_zero]; exact zero_mem_hat
      · intro a b ha hb; rw [mulVec_add]; exact add_mem_hat ha hb
      · intro c hc a ha; rw [mulVec_smul]; exact smul_mem_hat hc ha
    have h2 := smul_mem_hat ha (vA_mem_hat Y ((mem_glueLat (ι := ι) (z := z) (u := u) (L₀ := L₀) (x₀ := x₀)
      ((Tu D u)⁻¹ • z + ι x₀)).2 ⟨0, by simp, 1, by simp⟩))
    convert add_mem_hat h1 h2 using 1
    rw [vA_add, vA_smul, mulVec_add, mulVec_smul, mA_mulVec_vA, smul_add, smul_smul]
    abel

theorem IsGlueVec.congr {L₀ : Lat X} {f f' : Fin X.rank → EAf D} (h : IsGlueVec X u L₀ f) (hf : f - f' ∈ hat L₀) :
    IsGlueVec X u L₀ f' := by
  obtain ⟨d, rfl⟩ : ∃ d, f' = f - d := ⟨f - f', (sub_sub_cancel _ _).symm⟩
  rw [sub_sub_cancel] at hf
  refine ⟨?_, h.int, fun y hy => ?_, ?_, fun y hy => ?_⟩
  · rw [smul_sub]; exact sub_mem_hat h.mul_mem (smul_mem_hat (inc_Tu_mem u) hf)
  · rw [hA_sub_left]; exact sub_mem (h.pair y hy) (h.int d hf y hy)
  · have h1 : hA X d f ∈ OA D := by rw [← cjA_hA]; exact cjA_mem (h.pair d hf)
    have := sub_mem (sub_mem h.norm (h.pair d hf)) (sub_mem h1 (h.int d hf d hf))
    rw [hA_sub_left, hA_sub_right, hA_sub_right]
    convert this using 1
    ring
  · obtain ⟨a, ha, H⟩ := h.dual y hy
    refine ⟨a, ha, ?_⟩
    convert add_mem_hat H (smul_mem_hat ha hf) using 1
    rw [smul_sub]; abel


set_option maxHeartbeats 1600000 in
theorem mem_hat_glueLat_iff_dual (h : IsLine Y X ι z u) {L₀ : Lat X} {x₀ : X.V} (hg : IsGlueVec X u L₀ (vA X x₀))
    (x : Fin X.rank → EAf D) (a : EAf D) :
    mA Y X ι *ᵥ x + a • vA Y z ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) ↔
      ∀ y ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)), hA Y y (mA Y X ι *ᵥ x + a • vA Y z) ∈ OA D := by
  simp only [mem_hat_glueLat]
  generalize vA X x₀ = f at hg
  have t := inc_inv_mul u
  constructor
  · rintro ⟨x₁, hx₁, a₁, ha₁, e⟩ _ ⟨x₂, hx₂, a₂, ha₂, rfl⟩
    have h1 : hA X x₂ f ∈ OA D := by rw [← cjA_hA]; exact cjA_mem (hg.pair _ hx₂)
    have := add_mem (add_mem (hg.int _ hx₂ _ hx₁) (mul_mem (cjA_mem ha₁) h1))
      (add_mem (mul_mem ha₂ (hg.pair _ hx₁)) (mul_mem (mul_mem ha₂ (cjA_mem ha₁)) hg.norm))
    rw [e, hA_flat h, hA_add_left, hA_add_right, hA_add_right, hA_smul_left, hA_smul_left, hA_smul_right, hA_smul_right,
      RingHom.map_mul, cjA_inc_inv]
    convert this using 1
    linear_combination (-(a₂ * cjA D a₁ * inc D (Tu D u)⁻¹)) * t
  · intro H
    obtain ⟨b, hb, hx⟩ := hg.dual x fun x' hx' => by
      have := H _ ⟨x', hx', 0, zero_mem _, rfl⟩
      rwa [hA_flat h, zero_smul, add_zero, zero_mul, zero_mul, zero_mul, sub_zero] at this
    have h1 := H _ ⟨0, zero_mem_hat, 1, one_mem _, rfl⟩
    rw [hA_flat h, zero_add, one_smul, one_mul] at h1
    have h2 := hg.pair _ hx
    rw [hA_sub_right, hA_smul_right] at h2
    have h3 : cjA D (a - b * inc D (Tu D u)⁻¹) ∈ OA D := by
      have := sub_mem (add_mem h2 (mul_mem (cjA_mem hb) hg.norm)) h1
      rw [RingHom.map_sub, RingHom.map_mul, cjA_inc_inv]
      convert this using 1
      linear_combination (-(cjA D a)) * t
    rw [cjA_mem_iff] at h3
    refine ⟨x - b • f - (a - b * inc D (Tu D u)⁻¹) • inc D (Tu D u) • f, sub_mem_hat hx (smul_mem_hat h3 hg.mul_mem),
      a * inc D (Tu D u), ?_, ?_⟩
    · convert add_mem (mul_mem h3 (inc_Tu_mem u)) hb using 1
      linear_combination b * t
    · congr 2
      · rw [smul_smul, sub_mul, mul_assoc b, t, mul_one, sub_smul]
        abel
      · linear_combination (-a) * t

end Flat

end GlobalTheory.AdIsom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedCoordinatePoincareSumHalfWittEqBump
section
namespace I195MixedCoordinates_fba5a936e8e43b62cb67e97a

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_fba5a936e8e43b62cb67e97a

public noncomputable abbrev _root_.I195MixedCoordinates_2b9c4e7ee460bdf0c3844320.source :=
  @_root_.I195MixedCoordinates_fba5a936e8e43b62cb67e97a.source

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

namespace GlobalTheory.BumpMixSum

variable {D : D7}

theorem finite_rat_mem {m n : ℕ} (K : Set (Mx D m n)) (hK : IsCompact K) :
    {γ : Matrix (Fin m) (Fin n) D.host.E | rat γ ∈ K}.Finite := by
  obtain ⟨hg, hlc, hsc, ht2, hdisc, -⟩ := lattice_Mx D m n
  haveI : T2Space (Mx D m n) := ht2
  haveI : T1Space (Mx D m n) := @T2Space.t1Space _ _ ht2
  have hcl : IsClosed (ratMx D m n : Set (Mx D m n)) := AddSubgroup.isClosed_of_discrete
  have hS : IsCompact ((Subtype.val : ratMx D m n → Mx D m n) ⁻¹' K) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hfin := (hS.finite_of_discrete.image Subtype.val).preimage (rat_injective (D := D) (m := m) (n := n)).injOn
  refine hfin.subset fun γ hγ => ?_
  exact ⟨⟨rat γ, γ, rfl⟩, hγ, rfl⟩

theorem mixS_poinX : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → ∀ x, (_root_.I195MixedCoordinates_fba5a936e8e43b62cb67e97a.source d) T ψ v.μ v.𝓕 (poinX ψ d T β) x 0 = β x := by
  intro D ψ hψ S S₀ T ρ d v β hβ x
  have h := v.covol
  have hψc : Continuous ψ := hψ.1.1
  have hn : ∀ t, ‖ψ t‖ = 1 := hψ.1.2.1
  have hY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  obtain ⟨i1, i2, i3, -⟩ := lattice_Mx D T.rank ρ
  haveI : BorelSpace (Mx D T.rank ρ) := ⟨rfl⟩
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h.2.2]; exact ENNReal.one_lt_top⟩
  haveI : Countable D.host.E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (Matrix (Fin T.rank) (Fin ρ) D.host.E) := inferInstanceAs (Countable (_ → _ → D.host.E))
  haveI : ContinuousSub (Mx D T.rank ρ) := @IsTopologicalAddGroup.to_continuousSub _ _ _ i1
  have hone : v.μ.real v.𝓕 = 1 := by rw [Measure.real, h.2.2, ENNReal.toReal_one]

  have hfin : {ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E | β (x + rat ξ) ≠ 0}.Finite := by
    refine (finite_rat_mem _ (hβ.supp.isCompact.image (continuous_sub_right x))).subset fun ξ hξ => ?_
    exact ⟨x + rat ξ, subset_tsupport β hξ, add_sub_cancel_left x (rat ξ)⟩

  have key : ∀ a, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T 0) (poinX ψ d T β))) 0 =
      ∑' ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E, ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) * β (x + rat ξ) := by
    intro a
    rw [d.integrandS_eq, poinX_coords, ← tsum_mul_left]
    refine tsum_congr fun ξ => ?_
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, symplOH_Y_X, ← d.symplOH_extX_extY T x a,
      ← d.symplOH_extX_extY T (x + 2 • rat ξ) a, map_add (d.extX T), two_nsmul, map_add (d.extX T), GlobalTheory.OrientedHeis.symplOH_add_left,
      GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.Core.Rk.ThetaOf.symplO_eq_add, neg_add_cancel_left]
  have hF := hasSum_integral_of_summable_integral_norm (μ := v.μ.restrict v.𝓕)
    (F := fun (ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E) a =>
      ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) * β (x + rat ξ)) (fun ξ => ?_) ?_
  · rw [_root_.I195MixedCoordinates_fba5a936e8e43b62cb67e97a.source]
    change (∫ a in v.𝓕, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x)
      (heisO ψ S T (d.ext0 T 0) (poinX ψ d T β))) 0 ∂v.μ) = β x
    simp_rw [key]
    refine hF.unique ?_
    have h0 : ∫ a in v.𝓕, ψ (symplO S T (d.extX T (rat 0)) (d.extY T a)) * β (x + rat 0) ∂v.μ = β x := by
      simp only [rat_zero, map_zero, GlobalTheory.Core.Rk.ThetaOf.symplO_eq_add, symplOH_zero_left, add_zero,
        AddChar.map_zero_eq_one, one_mul, setIntegral_const, hone, one_smul]
    rw [← h0]
    refine hasSum_single (f := fun ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E =>
      ∫ a in v.𝓕, ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) * β (x + rat ξ) ∂v.μ) 0 fun ξ hξ => ?_
    rw [integral_mul_const, GlobalTheory.Core.Rk.ThetaOf.integral_pair hψ d T h hξ, zero_mul]
  · refine Integrable.mul_const (Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun a => (hn _).le)) _
    exact (hψc.comp (GlobalTheory.Core.Rk.ThetaOf.continuous_symplO continuous_const hY)).measurable.aestronglyMeasurable
  · simp only [norm_mul, hn, one_mul, setIntegral_const, hone, one_smul]
    refine summable_of_hasFiniteSupport (hfin.subset fun ξ hξ => ?_)
    exact fun h0 => (Function.mem_support.1 hξ) (by simp only [h0, norm_zero])

end GlobalTheory.BumpMixSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeConjRead

open Classical

variable {D : D7}

def colMat {n : ℕ} (w : Fin n → Fin n → EAf D) : Matrix (Fin n) (Fin n) (EAf D) := Matrix.of fun i j => w j i

def pairAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) :
    Fin (Yc D 0).rank → Fin (Yc D 0).rank → EAf D :=
  if GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 then
    flagV D.R.rS D.R.k (Yc D 0).rank (f0T X h) (e0T X h) (bwdT X h) (z0T X h)
  else flagV D.R.rS D.R.k (Yc D 0).rank (f0T X h) (e0T X h) (fun i => bwT X h (Fin.rev i)) (z0T X h)

def hY (D : D7) (x y : Fin (Yc D 0).rank → EAf D) : EAf D :=
  Formalism.UG.hform (GlobalTheory.StdFrames.sg D) (GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM (Yc D 0).gram) x y

def SmallAt (PP : Pl D.host.E) (x : EAf D) : Prop := Valued.v (GlobalTheory.StdFrames.cpt PP x) < 1

def PairTable {M A : Type} [Ring A] (p : M → M → A) (sm : A → Prop) {ρ k : ℕ} (e f : Fin ρ → M) (b b' : Fin k → M)
    (z : M) : Prop :=
  (∀ a c, sm (p (f a) (e c) - if a = c then 1 else 0)) ∧ (∀ a j, sm (p (f a) (b j))) ∧ (∀ a, sm (p (f a) z)) ∧
  (∀ a c, sm (p (f a) (f c))) ∧
  (∀ i a, sm (p (b' i) (e a))) ∧ (∀ i j, sm (p (b' i) (b j) - if i = j then 1 else 0)) ∧ (∀ i, sm (p (b' i) z)) ∧
  (∀ i a, sm (p (b' i) (f a))) ∧
  (∀ a, sm (p z (e a))) ∧ (∀ j, sm (p z (b j))) ∧ sm (p z z + 1) ∧ (∀ a, sm (p z (f a))) ∧
  (∀ a c, sm (p (e a) (e c))) ∧ (∀ a j, sm (p (e a) (b j))) ∧ (∀ a, sm (p (e a) z)) ∧
  (∀ a c, sm (p (e a) (f c) - if a = c then 1 else 0))

def sgnD {A : Type} [Ring A] (ρ k : ℕ) {n : ℕ} (a : Fin n) : A := if a.1 = ρ + k then -1 else 1

end GlobalTheory.SeeConjRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAllDataProductsEqFourierJacobiPeriod
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.LinkProd

variable {D : D7}

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : star (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * star (ψ a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ a ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h2.trans h3.symm)

theorem heisO_at_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w f 0 = f w := by
  simp [heisO, symplOH_zero_left]

theorem lnk_point {L L' : HSp D} {ζ : Fin L.rank → D.host.E} {ζ' : Fin L'.rank → D.host.E} (l : Lnk L ζ L' ζ')
    {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (n : GA D W) :
    l.κ W₀ (ptS d L' (zEll L' ρ ζ') n) = ptT d L (yZero L ρ ζ) n ∧
      cenT d L (yZero L ρ ζ) n = -cenS d L' (zEll L' ρ ζ') n := by
  constructor
  · have h : (rat l.τ : Mx D L.rank L'.rank) ⬝ zEll L' ρ ζ' = yZero L ρ ζ := by
      have h0 : ratV (-ζ) = -ratV ζ := funext fun i => map_neg (incA D) _
      rw [yZero, zEll, zEll, Matrix.mul_vecMulVec, ← ratV_mulVec, l.map, h0, Matrix.neg_vecMulVec]
    rw [GlobalTheory.Unf.LinkPoint.ptT_eq, Lnk.κ, ptS, d.extX_apply, ← h]
    simp only [Matrix.mul_assoc]
  · have hN : D.host.xi0 * star D.host.xi0 ≠ 0 :=
      mul_ne_zero (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) (star_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
    rw [GlobalTheory.Unf.LinkPoint.cenT_eq, GlobalTheory.Unf.LinkPoint.neg_cenS_eq, yZero, adj_neg, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg, GlobalTheory.Unf.LinkPoint.gram_zEll, GlobalTheory.Unf.LinkPoint.gram_zEll,
      smul_smul, ← map_mul, l.norm, inv_mul_cancel_left₀ hN]

theorem perAll_box_eq_per : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), ∀ (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Lnk B.L B.ζ L' ζ') (χA χz χ' : (AE D)ˣ →* Circle) (oma : Om B.A J.W₀) (omz : Om J.W₀ L'), s.χV = χA * χz → IsWeilDatumO ψ B.A J.W₀ χA s.χW oma → IsWeilDatumO ψ J.W₀ L' χ' χz omz → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) Ξ₁ Ξ₂, IsThetaFunO ψ B.A J.W₀ Ξ₁ → IsThetaFunO ψ B.L J.W₀ Ξ₂ → J.perAll ψ B s.om₀ φ G (B.o.boxS J.W₀ Ξ₁ Ξ₂) = J.per ψ ζ' omz (liftT oma B.vA.μ B.vA.𝓕 φ Ξ₁) G (fun w => star (Ξ₂ (l.κ J.W₀ w))) := by
  intro D ψ ρ B J s L' ζ' hL' l χA χz χ' oma omz hχ hoa hoz φ G Ξ₁ Ξ₂ hΞ₁ hΞ₂
  have hψ := hoa.std
  have hrk : B.L.rank = L'.rank := B.line.1.trans hL'.1.symm
  have hres : ResEta D χz B.L.rank := by rw [hrk]; exact hoz.resT
  obtain ⟨omL, hoL⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D B.L J.W₀ ψ χz s.χW hψ hoz.hecT hoa.hecT hres hoa.resT
  obtain ⟨hg, -⟩ := _root_.GlobalTheory.LinkInvTheta.link_inv_theta D ψ hψ B.L L' J.W₀ B.ζ ζ' B.line hL' l
  have hg' : l.τᴴ ⬝ (B.L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram := by
    rw [Int.cast_one, one_mul]; exact hg
  have hcl := (GlobalTheory.ConjLine.conj_line D ψ B.L L' J.W₀ l.τ hrk hg' χz s.χW χ' omL omz hoL hoz Ξ₂ hΞ₂).2
  have hTS := GlobalTheory.TensorSrc.tensorSource D ψ hψ B.V₀ B.A B.L B.o J.W₀
  have hw0 : IsWeilDatumO ψ B.V₀ J.W₀ (χA * χz) s.χW s.om₀ := hχ ▸ s.weil₀
  have hbt : IsThetaFunO ψ B.V₀ J.W₀ (B.o.boxS J.W₀ Ξ₁ Ξ₂) := hTS.box_theta Ξ₁ Ξ₂ hΞ₁ hΞ₂
  have key : ∀ n ∈ flagN J.d, ∀ h, ∫ h₀ in B.vA.𝓕, φ h₀ * fjKer ψ J.d B.o B.ζ s.om₀ (B.o.boxS J.W₀ Ξ₁ Ξ₂) h₀ n h ∂B.vA.μ =
      liftT oma B.vA.μ B.vA.𝓕 φ Ξ₁ h * star (thetaJS ψ J.d ζ' omz (fun w => star (Ξ₂ (l.κ J.W₀ w))) n h) := by
    intro n _ h
    obtain ⟨hp, hc⟩ := lnk_point l J.d n
    have e1 : ∀ h₀, φ h₀ * fjKer ψ J.d B.o B.ζ s.om₀ (B.o.boxS J.W₀ Ξ₁ Ξ₂) h₀ n h =
        oma (h₀, h) Ξ₁ 0 * φ h₀ * (ψ (cenT J.d B.L (yZero B.L ρ B.ζ) n) * omL (1, h) Ξ₂ (ptT J.d B.L (yZero B.L ρ B.ζ) n)) := by
      intro h₀
      rw [GlobalTheory.Unf.fjKer_eq_om_apply D ψ J.W J.W₀ B.V₀ B.A B.L ρ J.d B.o B.ζ _ _ s.om₀ s.weil₀ _ hbt,
        hTS.om_box χA χz s.χW s.om₀ oma omL hw0 hoa hoL h₀ 1 h Ξ₁ Ξ₂ hΞ₁ hΞ₂]
      simp only [OrthDec.boxS, AddEquiv.apply_symm_apply]
      ring
    simp_rw [e1]
    rw [integral_mul_const, liftT_apply]
    congr 1
    have hcl' : omz (h, 1) (fun w => star (Ξ₂ (l.κ J.W₀ w))) = fun w => star (omL (1, h) Ξ₂ (l.κ J.W₀ w)) := hcl h
    rw [thetaJS, jacS, hcl', Pi.smul_apply, smul_eq_mul, heisO_at_zero, star_mul', star_star, star_psi hψ, hp, hc]
  unfold JacL.perAll JacL.per fjAll fjSrc
  congr 1
  funext h
  congr 1
  funext n
  rw [fjAllFun, fjSrcFun, key n.1 n.2 h]
  ring

end GlobalTheory.LinkProd

end
end

