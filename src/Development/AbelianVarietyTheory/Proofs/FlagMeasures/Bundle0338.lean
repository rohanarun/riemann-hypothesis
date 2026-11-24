module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFramesPerpendicularVectors
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedDualVectorPairingBoundedMajorant
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0328
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.FinalF

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearFormsBoundedRepresentatives
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.FunIdx

section Gen

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem exists_retraction (M0 L : Submodule (𝓞 E) V) (hL : L.FG) (h : IsPrimitiveSub M0 L) :
    ∃ r : L →ₗ[𝓞 E] M0, ∀ x : M0, r ⟨x, h.1 x.2⟩ = x := by
  exact _root_.GlobalTheory.ProjectiveRetraction.exists_retraction M0 L hL h

theorem exists_extend_fun (L : Submodule (𝓞 E) V) (hL : Submodule.span E (L : Set V) = ⊤)
    (ψ : L →ₗ[𝓞 E] 𝓞 E) : ∃ φ : V →ₗ[E] E, ∀ x : L, φ x = (ψ x : E) := by
  haveI : IsLocalizedModule (nonZeroDivisors (𝓞 E)) L.subtype := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      rw [Module.End.isUnit_iff]
      have ha0 : ((a : 𝓞 E) : E) ≠ 0 := by
        have := nonZeroDivisors.ne_zero a.2
        exact_mod_cast this
      have e : ⇑(algebraMap (𝓞 E) (Module.End (𝓞 E) V) a) = fun v => ((a : 𝓞 E) : E) • v := by
        funext v
        exact (algebraMap_smul E (a : 𝓞 E) v).symm
      rw [e]
      exact MulAction.bijective (Units.mk0 _ ha0)
    · intro y
      have hy : y ∈ Submodule.span E (L : Set V) := hL ▸ Submodule.mem_top
      obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ y hy
      rw [Submodule.span_eq] at ht
      exact ⟨(⟨_, ht⟩, t), rfl⟩
    · intro x y hxy
      exact ⟨1, by rw [Subtype.ext hxy]⟩
  let g : L →ₗ[𝓞 E] E := Algebra.linearMap (𝓞 E) E ∘ₗ ψ
  have hu : ∀ a : nonZeroDivisors (𝓞 E), IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) E) a) :=
    fun a => IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E)) (Algebra.linearMap (𝓞 E) E) a
  refine ⟨(IsLocalizedModule.lift (nonZeroDivisors (𝓞 E)) L.subtype g hu).extendScalarsOfIsLocalization
    (nonZeroDivisors (𝓞 E)) E, fun x => ?_⟩
  exact IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 E)) L.subtype g hu x

end Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem exists_vec (S : HSpace E) (φ : S.V →ₗ[E] E) : ∃ w, ∀ x, φ x = S.hT w x := by
  let G : S.V →ₗ[E] (Fin S.rank → E) := LinearMap.pi fun i => S.hT (S.frame i)
  have hG : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply S.nondeg.2 y
    intro x
    have : S.hT.flip y = 0 := S.frame.ext fun i => congrFun hy i
    exact LinearMap.congr_fun this x
  have hs : Function.Surjective G :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [S.rank_eq])).1 hG
  obtain ⟨w, hw⟩ := hs fun i => star (φ (S.frame i))
  refine ⟨w, fun x => LinearMap.congr_fun (S.frame.ext fun i => ?_ : φ = S.hT w) x⟩
  have h1 : S.hT (S.frame i) w = star (φ (S.frame i)) := congrFun hw i
  have h2 : star (S.hT (S.frame i) w) = S.hT w (S.frame i) := S.herm.eq _ _
  rw [← h2, h1, star_star]

theorem span_eq_top_of_unimodular {S : HSpace E} (L : Submodule (𝓞 E) S.V)
    (hL : Submodule.IsLattice E L)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT L) :
    Submodule.span E (L : Set S.V) = ⊤ := by
  by_contra hspan
  obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
  obtain ⟨μ, hμ⟩ := exists_vec S φ
  have hμ₀ : μ ≠ 0 := by
    intro h
    apply hφ₀
    ext y
    simpa [h] using hμ y
  have hline (a : E) : a • μ ∈ L := by
    rw [← hU]
    change a • μ ∈ Formalism.E.hdual S.hT L
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply]
    intro y hy
    have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
    simp [← S.herm.eq (a • μ) y, LinearMap.map_smulₛₗ, ← hμ, hy₀]
  obtain ⟨ψ, hψ, -⟩ := Submodule.exists_le_ker_of_notMem
    (show μ ∉ (⊥ : Submodule E S.V) by simpa using hμ₀)
  let f := ψ.restrictScalars (𝓞 E)
  have hmap (x : E) : x ∈ L.map f := by
    refine ⟨(x / ψ μ) • μ, hline _, ?_⟩
    change ψ ((x / ψ μ) • μ) = x
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hψ]
  obtain ⟨d, hd₀, hd⟩ := FractionalIdeal.isFractional_of_fg
    (S := nonZeroDivisors (𝓞 E)) (hL.fg.map f)
  have hinj := IsFractionRing.injective (𝓞 E) E
  have hne {a : 𝓞 E} (ha : a ≠ 0) : algebraMap (𝓞 E) E a ≠ 0 :=
    fun h => ha (hinj (h.trans (map_zero _).symm))
  have hinteger (x : E) : IsLocalization.IsInteger (𝓞 E) x := by
    have hx := hd _ (hmap ((algebraMap (𝓞 E) E d)⁻¹ * x))
    rwa [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ (hne (nonZeroDivisors.ne_zero hd₀)),
      one_mul] at hx
  apply RingOfIntegers.not_isField E
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨b, hb⟩ := hinteger ((algebraMap (𝓞 E) E a)⁻¹)
  refine ⟨b, hinj ?_⟩
  rw [map_mul, hb, map_one, mul_inv_cancel₀ (hne ha)]


theorem exists_dual_vec (S : HSpace E) (M0 L : Submodule (𝓞 E) S.V) (hL : Submodule.IsFullLattice E L)
    (h : IsPrimitiveSub M0 L) (ψ : M0 →ₗ[𝓞 E] 𝓞 E) :
    ∃ w : dualInH S.hT L, ∀ x : M0, (ψ x : E) = S.hT w x := by
  obtain ⟨r, hr⟩ := exists_retraction M0 L hL.fg h
  obtain ⟨φ, hφ⟩ := exists_extend_fun L (Submodule.IsFullLattice.span_eq_top (self := hL)) (ψ ∘ₗ r)
  obtain ⟨w, hw⟩ := exists_vec S φ
  refine ⟨⟨w, ?_, ?_⟩, fun x => ?_⟩
  · refine (Submodule.mem_iInf _).2 fun y => (Submodule.mem_iInf _).2 fun hy => ?_
    change S.hT y w ∈ (1 : Submodule (𝓞 E) E)
    have h2 : star (S.hT w y) = S.hT y w := S.herm.eq _ _
    have h3 : IsIntegral ℤ (S.hT y w) := by
      rw [← h2, ← hw, hφ ⟨y, hy⟩]
      exact (RingOfIntegers.isIntegral_coe _).map (starRingEnd E).toIntAlgHom
    exact Submodule.mem_one.2 ⟨⟨_, h3⟩, rfl⟩
  · change w ∈ Submodule.span E (L : Set S.V)
    rw [(Submodule.IsFullLattice.span_eq_top (self := hL))]; trivial
  · have := hφ ⟨x, h.1 x.2⟩
    rw [LinearMap.comp_apply, hr] at this
    rw [← this, hw]

theorem exists_reps (S : HSpace E) (M0 L : Submodule (𝓞 E) S.V) (hL : Submodule.IsFullLattice E L)
    (h : IsPrimitiveSub M0 L)
    (hfin : 1 ≤ Nat.card (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype)) :
    ∃ reps : Finset (M0 →ₗ[𝓞 E] 𝓞 E),
      reps.card ≤ Nat.card (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype) ∧
      ∀ ψ : M0 →ₗ[𝓞 E] 𝓞 E, ∃ ψ₀ ∈ reps, ∃ v ∈ L, ∀ x : M0, ((ψ x - ψ₀ x : 𝓞 E) : E) = S.hT v x := by
  choose w hw using exists_dual_vec S M0 L hL h
  haveI : Finite (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype) :=
    Nat.finite_of_card_ne_zero (by omega)
  letI := Fintype.ofFinite (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype)
  let g : (M0 →ₗ[𝓞 E] 𝓞 E) → (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype) :=
    fun ψ => Submodule.Quotient.mk (w ψ)
  refine ⟨Finset.univ.image (Function.invFun g), ?_, fun ψ => ?_⟩
  · rw [Nat.card_eq_fintype_card]; exact Finset.card_image_le
  · refine ⟨Function.invFun g (g ψ), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have h1 : g ψ = g (Function.invFun g (g ψ)) := (Function.invFun_eq ⟨ψ, rfl⟩).symm
    have h2 := (Submodule.Quotient.eq _).1 h1
    refine ⟨_, h2, fun x => ?_⟩
    rw [Submodule.subtype_apply, Submodule.coe_sub, map_sub, LinearMap.sub_apply, ← hw, ← hw]
    push_cast
    rfl

theorem funIdx : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ M0 : LatW D, IsPrimitiveSub M0 (L0X D Λ (lf D F0)) → ∃ reps : Finset (M0 →ₗ[𝓞 D.host.E] 𝓞 D.host.E), (reps.card : ℝ) ≤ NT D u ^ 2 ∧ ∀ ψ : M0 →ₗ[𝓞 D.host.E] 𝓞 D.host.E, ∃ ψ₀ ∈ reps, ∃ v ∈ L0X D Λ (lf D F0), ∀ x : M0, ((ψ x - ψ₀ x : 𝓞 D.host.E) : D.host.E) = (D.sp.X 0).hT v x := by
  intro D u u' F0 Λ hStand hB hR M0 hM
  obtain ⟨hWH, -, hpd, hlat, hint, hdet, -⟩ := _root_.GlobalTheory.LoopC.Base.main D u u' F0 Λ hStand hB hR
  have hfull : Submodule.IsFullLattice D.host.E (L0X D Λ (lf D F0)) := by
    refine { toIsLattice := hlat, span_eq_top := ?_ }
    apply eq_top_iff.mpr
    intro w _
    have hΛ : Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ :=
      span_eq_top_of_unimodular Λ hR.2.1.1 hR.2.1.2.1
    have hw : D.sp.iXY 0 w ∈ orth (hS D) F0.Xplus :=
      hWH.1.le (Submodule.mem_sup_left ⟨w, rfl⟩)
    have hwX : D.sp.iXY 0 w ∈ orth (hS D) F0.X :=
      (Formalism.MainNotions.mem_orth_iff _ _).2 fun x hx =>
        (Formalism.MainNotions.mem_orth_iff _ _).1 hw x (Submodule.mem_sup_left hx)
    have hwz : (hS D).hT F0.z (D.sp.iXY 0 w) = 0 :=
      (Formalism.MainNotions.mem_orth_iff _ _).1 hw _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 D.host.E)) D.host.E Λ (D.sp.iXY 0 w) (hΛ ▸ Submodule.mem_top)
    rw [Submodule.span_eq] at ht
    have ht0 : (algebraMap (𝓞 D.host.E) D.host.E t) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors t.2
    have hmem : (t : 𝓞 D.host.E) • w ∈ L0X D Λ (lf D F0) := by
      change D.sp.iXY 0 ((t : 𝓞 D.host.E) • w) ∈ L0sub Λ (lf D F0)
      rw [← algebraMap_smul D.host.E, map_smul, algebraMap_smul]
      have hort : (t : 𝓞 D.host.E) • D.sp.iXY 0 w ∈ toO (hS D) (orth (hS D) F0.X) := by
        change (t : 𝓞 D.host.E) • D.sp.iXY 0 w ∈ (orth (hS D) F0.X).restrictScalars (𝓞 D.host.E)
        exact Submodule.smul_mem _ _ hwX
      refine ⟨⟨Submodule.mem_sup_left ⟨ht, hort⟩, hort⟩, ?_⟩
      change (hS D).hT F0.z ((t : 𝓞 D.host.E) • D.sp.iXY 0 w) = 0
      rw [← algebraMap_smul D.host.E, map_smul, hwz, smul_zero]
    have hspan : (t : 𝓞 D.host.E) • w ∈ Submodule.span D.host.E ((L0X D Λ (lf D F0)) : Set (D.sp.X 0).V) :=
      Submodule.subset_span hmem
    have hspan' : (algebraMap (𝓞 D.host.E) D.host.E t) • w ∈
        Submodule.span D.host.E ((L0X D Λ (lf D F0)) : Set (D.sp.X 0).V) := by
      rw [algebraMap_smul]
      exact hspan
    have := (Submodule.span D.host.E ((L0X D Λ (lf D F0)) : Set (D.sp.X 0).V)).smul_mem (algebraMap (𝓞 D.host.E) D.host.E t)⁻¹ hspan'
    rw [smul_smul, inv_mul_cancel₀ ht0, one_smul] at this
    exact this
  obtain ⟨h1, h2, -⟩ := GlobalTheory.LoopC.DetCard.main D _ hlat.fg hpd hint
  obtain ⟨reps, hc, hr⟩ := exists_reps (D.sp.X 0) M0 _ hfull hM h1
  refine ⟨reps, ?_, hr⟩
  rw [← hdet, ← h2]
  exact_mod_cast hc

end GlobalTheory.LoopC.FunIdx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NongenericRowStatementsOfFamilyStatements
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SnFamNG

theorem ampQ_id {Cl Nu : Type} (L : PN.LocalNG Cl Nu) : ampQ id L = L.ampNG := by
  funext d
  unfold ampQ PN.LocalNG.ampNG
  simp only [id]

theorem hasPt_of_isPt {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}
    {νL νB : X.B.I.Ginf → Measure X.B.I.Ginf} {ng : PN.Pts D.host.E D.R.rS → ℝ} {γ : PN.Pts D.host.E D.R.rS}
    (h : PN.IsPt (Y.tO u u') (NOf2 Y u u' νL νB ng) γ) : HasPt Y u u' (Y.tO u u').ngSet γ := by
  obtain ⟨-, -, t, ht, hv, -, hp, -⟩ := h
  exact ⟨t, ht, hv, hp⟩

theorem leaves_of_fam : FamNG → (FamilyWeightSumUnfoldingIdentity → Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric) ∧ (WeightsFam → Formalism.L2.SG.FamDefs.WeightsNG) ∧
    (FamilyGroupSumFactorsWeightAmplitude → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric) ∧ (ExistFam → Formalism.L2.SG.FamDefs.ExistNG) := by
  intro hF
  refine ⟨fun hG => ?_, fun hW => ?_, fun hG4 => ?_, fun hE => ?_⟩
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨a2, b2, h2⟩ := hG Cg cb Cw cT CT C0
    refine ⟨max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc νL νB ng γ hγ S Fm hT => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    exact h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc _ id _ _ hQ γ
      (hasPt_of_isPt hγ) Fm hT
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨a2, b2, h2⟩ := hW Cg cb Cw cT CT C0
    refine ⟨max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire
      hbk νL νB ng γ hγ S Fm hT hRel hTerm hG5 => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    exact h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc hb X0 ψ hbt sd C Th F0 what₂ vR Q
      i0 i0' νq Irat Ire hbk _ id _ _ hQ γ (hasPt_of_isPt hγ) Fm hT hRel hTerm hG5
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨CSt, hCSt, a2, b2, h2⟩ := hG4 Cg cb Cw cT CT C0
    refine ⟨CSt, hCSt, max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0'
      νq Irat Ire hbk ν hν => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    obtain ⟨s, hs1, hs2, hs3, hs4⟩ := h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc hb X0
      ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hbk ν hν
    refine ⟨s, hs1, hs2, hs3, fun γ hγ S Fm hT x _ => ?_⟩
    have h := hs4 _ id _ _ hQ γ (hasPt_of_isPt hγ) Fm hT x.1 x.2
    rw [ampQ_id] at h
    exact h
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨a2, b2, h2⟩ := hE Cg cb Cw cT CT C0
    refine ⟨max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc νL νB ng γ hγ S => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    exact h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc _ id _ _ hQ γ (hasPt_of_isPt hγ)

end GlobalTheory.SnFamNG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OffBlockEntriesBoundedNormalFormPairOfFlags
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.NfComp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.NfOff

lemma exists_blockEnd {r : ℕ} {β : Fin r → ℕ} (hβ : Monotone β) (c : Fin r) :
    ∃ l, l ≤ r ∧ ∀ i : Fin r, i.val < l ↔ β i ≤ β c := by
  obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i : Fin r => β i ≤ β c) id
    ⟨c, by simp⟩
  refine ⟨d.val + 1, d.2, fun i => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact (hβ (show i ≤ d from Nat.le_of_lt_succ h)).trans (Finset.mem_filter.1 hd).2
  · exact Nat.lt_succ_of_le (hmax i (by simpa using h))

lemma minor_ne_zero {r l : ℕ} (hl : l ≤ r) (Z : Matrix (Fin r) (Fin r) ℂ) (hZ : Z.det ≠ 0)
    (h : ∀ i : Fin r, ¬ i.val < l → ∀ j : Fin r, j.val < l → Z i j = 0) :
    (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det ≠ 0 := by
  rw [Matrix.twoBlockTriangular_det Z (fun i => i.val < l) h] at hZ
  have h1 := left_ne_zero_of_mul hZ
  let e : Fin l ≃ {i : Fin r // i.val < l} :=
    ⟨fun i => ⟨Fin.castLE hl i, i.2⟩, fun i => ⟨i.1.val, i.2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [← Matrix.det_submatrix_equiv_self e] at h1
  exact h1

lemma Zr_mul_uEmb {k r : ℕ} (g : Mat k r) (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) :
    Zr k r (g * uEmb k r u) = Zr k r g * u := by
  ext a b
  have h := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1 u hu).2.2.1 b
  have h2 : Zr k r (g * uEmb k r u) a b = (g *ᵥ (uEmb k r u *ᵥ bvec (eI k r b))) (esI k r a) := by
    rw [Matrix.mulVec_mulVec]; simp [bvec, Zr]
  rw [h2, h, Matrix.mulVec_sum, Finset.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [bvec, Zr, Matrix.mulVec_smul, mul_comm]

lemma N_sub_S {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, ⟨(uHGroup _ _ (Hunit k r)).1, by simp, by simp⟩, _, hn, (one_mul _).symm⟩

theorem offBlock_le : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De R₀ : ℝ), TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (y : UToff β → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg k r z' (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) ≤ R₀ → Sg k r z (g₀ * (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → ∀ p, ‖y p‖ ≤ R₀ ^ (2 * r) * De := by
  intro k r z z' g₀ β De R₀ hT hN hDe hR m hm y q a ha hS' hS p
  obtain ⟨hz, hz', -⟩ := hT
  obtain ⟨hg, -, hβ, hdet, hblk, -⟩ := hN
  obtain ⟨⟨⟨c, b⟩, hcb⟩, hβcb⟩ := p
  simp only at hcb hβcb
  obtain ⟨hg1, he⟩ := levi_diag_middle_mem_bessel_unitary_eucl (r := r) hm a ha
  have hU1 : (upperOff β y).det = 1 := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.2 _).1
  have hUu : IsUnit (upperOff β y).det := by rw [hU1]; exact isUnit_one
  have hUN : uEmb k r (upperOff β y) ∈ Nset k r := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.2 _).2
  have hPN : pOf k r q ∈ Nset k r :=
    (((GlobalTheory.Amp.Rad.radical k r).1 _ _).2.2.2 ((GlobalTheory.Amp.Rad.radical k r).2.1 _ _)).1
  have hPe : ∀ d : Fin r, pOf k r q *ᵥ bvec (eI k r d) = bvec (eI k r d) := ((GlobalTheory.Amp.Rad.radical k r).1 _ _).1
  have hs : uEmb k r (upperOff β y) * pOf k r q ∈ Nset k r := (nSubgroup k r).2.1 _ hUN _ hPN
  rw [Matrix.mul_assoc (uEmb k r (upperOff β y) * pOf k r q)] at hS hS'
  have hlen : ∀ d : Fin r, (a d)⁻¹ ≤ R₀ := by
    intro d
    have h1 := (((GlobalTheory.Amp.LInv.lengths_basic k r z' hz').1 _ hg1 _ (N_sub_S z' hs) 1
      ⟨(uHGroup _ _ (Hunit k r)).1, one_mem _⟩).1 d.castSucc)
    rw [mul_one, (GlobalTheory.Amp.LInv.lengths_basic k r z' hz').2.1 a ha m hm] at h1
    rw [← h1]
    exact ((((GlobalTheory.Amp.LInv.lengths_basic k r z' hz').2.2 _).2.1 _).2).trans hS'
  set g₁ := uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m with hg₁
  set U := upperOff β y with hU
  obtain ⟨l, hl, hlβ⟩ := exists_blockEnd hβ c
  have hcl : c.val < l := (hlβ c).2 le_rfl
  have hZ0 : ∀ i j : Fin r, (i.val < l ↔ ¬ j.val < l) → Zr k r g₀ i j = 0 := by
    intro i j hij
    by_contra h
    have := hblk i j h
    rw [hlβ, hlβ, this] at hij
    tauto
  have hcr := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.cramerUpper ℂ r l hl 1 (Zr k r g₀) U (by simp)
    (fun i j h => Matrix.one_apply_ne h.ne) (fun i => by simp [hU, upperOff, upper])
    (fun i j h => by
      simp only [hU, upperOff, upper]
      rw [dite_eq_right (not_lt.2 h.le), if_neg h.ne'])
    (fun i j hi hj => hZ0 i j ⟨fun _ => not_lt.2 hj, fun _ => hi⟩) ⟨c.val, hcl⟩ b
    (fun c' hc' => by
      by_contra h
      rcases upperOff_ne hβ y _ _ h with h' | h'
      · exact hc'.ne (Fin.castLE_injective hl h')
      · exact absurd ((hlβ (Fin.castLE hl c')).1 c'.2) (not_le.2 h'))
  have hUcb : U (Fin.castLE hl ⟨c.val, hcl⟩) b = y ⟨⟨(c, b), hcb⟩, hβcb⟩ := by
    show upperOff β y c b = _
    simp only [upperOff, upper]
    rw [dite_eq_left hcb, dite_eq_left hβcb]
  rw [Matrix.one_mul, hUcb, ← Zr_mul_uEmb g₀ U hUu] at hcr
  have hD1 : ((Zr k r (g₀ * uEmb k r U)).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      Dmin k r z z' g₀ ⟨l, by omega⟩ := by
    have h1 := dInv k r z z' hz hz' 1 (N_sub_S z (nSubgroup k r).1) _ (N_sub_S z' hUN) g₀ ⟨l, by omega⟩
    rw [Matrix.one_mul] at h1
    rw [← h1, Dmin_eq le_rfl z z' _ l hl]
    rfl
  have hD0 : Dmin k r z z' g₀ ⟨l, by omega⟩ ≠ 0 := by
    rw [Dmin_eq le_rfl z z' _ l hl]
    exact minor_ne_zero hl _ hdet fun i hi j hj => hZ0 i j ⟨fun h => absurd h hi, fun h => absurd hj h⟩
  have hDb := hDe.2 ⟨l, by omega⟩ hl hD0
  rw [hD1] at hcr
  set σ : Fin l → Fin r := fun j => if j = ⟨c.val, hcl⟩ then b else Fin.castLE hl j with hσ
  have hx := G_mul hg (G_mul hs.1 hg1)
  have hp := pluck_flag hl z hz _ hx R₀ hS (fun i => g₁⁻¹ *ᵥ bvec (eI k r (σ i))) (fun i => by
    rw [he]; exact hlen _)
  have hmat : (Matrix.of fun i i' : Fin l =>
      herm (Hpk k r) ((g₀ * (uEmb k r U * pOf k r q * g₁))⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl i')))
        (g₁⁻¹ *ᵥ bvec (eI k r (σ i)))) = ((Zr k r (g₀ * uEmb k r U)).submatrix (Fin.castLE hl) σ)ᴴ := by
    ext i i'
    rw [Matrix.of_apply, herm_inv_left hx, herm_symm, herm_e, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (G_unit hg1), Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hPe]
    simp [bvec, Zr]
  rw [hmat, Matrix.det_conjTranspose, norm_star, hcr, norm_mul] at hp
  have hP0 : 0 < ‖Dmin k r z z' g₀ ⟨l, by omega⟩‖ := norm_pos_iff.2 hD0
  have hpow : R₀ ^ l * R₀ ^ l ≤ R₀ ^ (2 * r) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hR (by omega)
  calc _ ≤ R₀ ^ (2 * r) * ‖Dmin k r z z' g₀ ⟨l, by omega⟩‖⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀' hP0]; exact hp.trans hpow
    _ ≤ _ := mul_le_mul_of_nonneg_left hDb (by positivity)

end GlobalTheory.Amp.NfOff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneMemKg
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Dec.CuspAll

theorem one_mem_Kg (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨(Formalism.UG.stabGL I.Lf).one_mem, fun y _ => ⟨0, I.Lf.zero_mem, ?_⟩⟩
  have : I.fmat 1 = 1 := rfl
  simp [this]

theorem re_fixed (B : RowsAut) : ∀ k ∈ B.I.Kg B.g, (B.R (1, k)).comp B.Re = B.Re := by
  intro k hk
  obtain ⟨hT2, -, hsc, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨R1, Rm, Rn, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  obtain ⟨-, -, -, -, -, hinv, -⟩ := B.e_adm
  obtain ⟨-, hT⟩ := B.Re_spec
  have p1 : (fun g : B.I.Gf => B.R (1, g)) 1 = 1 := R1
  have pm : ∀ a b : B.I.Gf, B.R (1, a * b) = B.R (1, a) * B.R (1, b) := by
    intro a b; rw [← Rm]; simp
  have pn : ∀ (g : B.I.Gf) v, ‖B.R (1, g) v‖ = ‖v‖ := fun g v => Rn _ v
  exact GlobalTheory.IdemProj.op_fixed B.μf (fun g => B.R (1, g)) p1 pm pn B.e B.Re hT k
    (fun x => by simpa using hinv x k hk 1 (one_mem_Kg B.I B.g))

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d)
    (hl : LocDec B h) (hb : HBig B 40 h) : Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hc, hm, hi⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl
  have h0 := hi 0 le_rfl (fun v => by
    rcases Nat.eq_zero_or_pos (rkR (B.I.ε v)) with hq | hq
    · exact Or.inl hq
    · right
      have hle : rkR (B.I.ε v) ≤ B.I.n := by
        unfold rkR
        refine (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
      have h1 : (0 : ℝ) < rkR (B.I.ε v) := by exact_mod_cast hq
      have h2 : ((rkR (B.I.ε v) : ℕ) : ℝ) ≤ B.I.n := by exact_mod_cast hle
      have h3 := Real.sqrt_pos.2 h1
      have h4 := hb v
      have h5 : (0 : ℝ) < B.I.n := h1.trans_le h2
      have h6 : (B.I.n : ℝ) * rkR (B.I.ε v) ≤ (B.I.n : ℝ) ^ 2 := by nlinarith
      have h7 : 0 < (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h6 h3.le])
  simp only [zero_mul, Real.exp_zero, mul_one] at h0
  exact h0.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hm)

theorem cusp_all : GlobalTheory.DSId.StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, A ∈ B.I.HomS B.σs B.μf B.fund B.R ∧ ∀ u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A u)) ∧ ∀ k ∈ B.I.Kg B.g, B.R (1, k) (A u) = A u := by
  intro hS B d h hd hg hgap hl hb T hT
  obtain ⟨-, hcomm, ⟨Rφ, hR⟩, -⟩ := GlobalTheory.GlobProj.globalProj_holds B d hd (integrable_ph B d h hd hl hb)
  obtain ⟨-, hirr, -, hw, -⟩ := GlobalTheory.Dec.tensorRep B d hd
  have hle : B.I.eHom B.σs B.μf B.fund B.R B.Re ≤ B.I.HomS B.σs B.μf B.fund B.R := by
    rintro _ ⟨A, hA, rfl⟩ g
    show (B.Re.comp A).comp (B.σs g) = (B.R (g, 1)).comp (B.Re.comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  obtain ⟨S, hSm, hScl, hSst, -⟩ := GlobalTheory.CuspSubspace.cuspidal_closed_stable B
  refine ⟨hle hT, fun u => ⟨?_, fun k hk => ?_⟩⟩
  · have hw' : T (B.tens B.w) ∈ S := by
      rw [hSm]
      exact _root_.GlobalTheory.RowCusp.row_isCuspFn hS B d h hd hg hgap hl hb Rφ hR T hT
    have hcl : IsClosed ((S.comap (T : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) : Submodule ℂ B.Hs) : Set B.Hs) :=
      hScl.preimage T.continuous
    rcases hirr _ hcl (fun g v hv => by
      have e := congrArg (fun A : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => A v) (hle hT g)
      simp only [ContinuousLinearMap.comp_apply] at e
      show T (B.σs g v) ∈ S
      rw [e]
      exact hSst _ _ hv) with h0 | h0
    · have : B.tens B.w ∈ S.comap (T : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) := hw'
      rw [h0, Submodule.mem_bot] at this
      rw [this] at hw
      simp at hw
    · have : u ∈ S.comap (T : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) := by rw [h0]; trivial
      exact (hSm _).1 this
  · obtain ⟨A, -, hA⟩ := hT
    rw [← hA]
    exact congrArg (fun C : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => C (A u)) (re_fixed B k hk)

end GlobalTheory.Dec.CuspAll
end
end

