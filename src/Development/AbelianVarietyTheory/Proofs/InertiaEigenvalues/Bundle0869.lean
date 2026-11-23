module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0854
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0815
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0859
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
public import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLevelTypeFormsOfUniversalCoeffReading
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameCharacterParahoricInvariant
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.JacTypeVec

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.JacBlock GlobalTheory.JacBlockTwo ValuativeRel Matrix

theorem exists_irreducible_subquotient_rel (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (x : V) (hx : x ≠ 0) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y) (y : Y),
      τ.IsIrreducible ∧ GlobalTheory.SmGL.IsSubquotient τ ρ ∧ y ≠ 0 ∧
        ∀ (ι : Type) (s : Finset ι) (f : ι → G) (c : ι → ℂ) (b : ℂ),
          ∑ i ∈ s, c i • ρ (f i) x = b • x → ∑ i ∈ s, c i • τ (f i) y = b • y :=
  _root_.GlobalTheory.QuotientGenerator.exists_irreducible_subquotient G V ρ x hx

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem mulSingle_false_mem_KO {r t : ℕ} {g : GL (Fin r) F} (hg : g ∈ KO F (Fin r)) (a : Bool) :
    (Pi.mulSingle false g : Levi F (Two (Fin r) (Fin t))) a ∈ KO F (Two (Fin r) (Fin t) a) := by
  cases a
  · rw [Pi.mulSingle_eq_same]; exact hg
  · rw [Pi.mulSingle_eq_of_ne (by decide)]; exact one_mem _

theorem deltaHalf_mulSingle_false {r t : ℕ} {g : GL (Fin r) F} (hg : g ∈ KO F (Fin r)) :
    deltaHalf F (Two (Fin r) (Fin t)) (Pi.mulSingle false g) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => isUnram_absPow F _ _ ?_
  exact GlobalTheory.StepData.valuation_det_of_mem_KO (mulSingle_false_mem_KO (t := t) hg a)

theorem emb₂_one_eq {r t : ℕ} (g : GL (Fin r) F) :
    emb₂ F (stdSum (rfl : r + t = r + t)) (g, 1) =
      leviEmb F (two (stdSum (rfl : r + t = r + t))) (Pi.mulSingle false g : Levi F (Two (Fin r) (Fin t))) := by
  unfold emb₂
  rw [MonoidHom.comp_apply]
  congr 1
  funext a
  cases a <;> rfl

theorem jac_mulSingle_false {r t : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL (Fin (r + t)) F) W) {g : GL (Fin r) F} (hg : g ∈ KO F (Fin r)) (v : W) :
    GlobalTheory.SmGL.jac (two (stdSum (rfl : r + t = r + t))) π (Pi.mulSingle false g) (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (π (emb₂ F (stdSum (rfl : r + t = r + t)) (g, 1)) v) := by
  rw [jac_mk, deltaHalf_mulSingle_false hg, inv_one, Units.val_one, one_smul, emb₂_one_eq]

theorem act_mulSingle_false_KOne {r t : ℕ} {χ : Fˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) F) W} {v : W} (hv : IsBlockVec χ π v)
    {g : GL (Fin r) F} (hg : g ∈ KOne F (Fin r)) :
    π (emb₂ F (stdSum (rfl : r + t = r + t)) (g, 1)) v = v := by
  set h := emb₂ F (stdSum (rfl : r + t = r + t)) (g, 1) with hdef
  have hval : ∀ i j, h.val i j = Matrix.reindex (stdSum (rfl : r + t = r + t)) (stdSum (rfl : r + t = r + t))
      (Matrix.fromBlocks g.val 0 0 (1 : GL (Fin t) F).val) i j := fun i j => by
    rw [hdef]
    exact congrFun (congrFun (val_emb₂ F _ (g, 1)) i) j
  have hKO : h ∈ KO F (Fin (r + t)) := by
    have hg' : g ∈ KO F (Fin r) := GlobalTheory.StepData.KOne_le_KO hg
    have e : h = leviEmb F (two (stdSum (rfl : r + t = r + t)))
        (Pi.mulSingle false g : Levi F (Two (Fin r) (Fin t))) := by
      rw [hdef, emb₂_one_eq]
    rw [e]
    refine GlobalTheory.StepData.mem_KO.2 ⟨intM_leviEmb _ _ fun a =>
      GlobalTheory.StepData.intM_of_mem_KO (mulSingle_false_mem_KO hg' a), ?_⟩
    rw [← map_inv]
    exact intM_leviEmb _ _ fun a => GlobalTheory.StepData.intM_of_mem_KO (inv_mem (mulSingle_false_mem_KO hg' a))
  have h0 : ∀ (i : Fin t) (j : Fin r), h.val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := fun i j => by
    rw [hval, ← stdSum_inr', ← stdSum_inl']
    simp
  have h1 : ∀ i j : Fin r, h.val (Fin.castAdd t i) (Fin.castAdd t j) = g.val i j := fun i j => by
    rw [hval, ← stdSum_inl', ← stdSum_inl']
    simp
  have h2 : h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) = 1 := by
    ext i j
    rw [Matrix.submatrix_apply, hval, ← stdSum_inr', ← stdSum_inr']
    simp
  have hg1 := GlobalTheory.StepData.mem_KOne.1 hg
  have key := hv h hKO (fun i j => by simp [h0]) (fun i j => by
      rw [h1]; have := hg1 i j; simpa [Matrix.sub_apply, Matrix.one_apply] using this) 1
    (by rw [h2, det_one, Units.val_one])
  rw [key, map_one, Units.val_one, one_smul]

end Local

theorem exists_subquot_typeVec : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (r t : ℕ) (χ : Fˣ →* ℂˣ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) F) W) (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (y : W) (ℓ : GL (Fin r) (ZMod p) → GL (Fin r) F), resCard F = p → IsSmooth π → π.IsIrreducible → IsTame χ → y ≠ 0 → IsBlockVec χ π y → (∀ g, IsLift g (ℓ g)) → (z.coeff.sum fun g c => c • π (emb₂ F (stdSum (rfl : r + t = r + t)) (ℓ g, 1)) y) = y → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (Levi F (Two (Fin r) (Fin t))) Y), τ.IsIrreducible ∧ IsSubquotient τ (GlobalTheory.SmGL.jac (two (stdSum (rfl : r + t = r + t))) π) ∧ ∃ w : Y, w ≠ 0 ∧ (∀ g ∈ KO F (Fin t), τ (Pi.mulSingle true g) w = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • w) ∧ TypeVec (n := Fin r) (τ.comp (MonoidHom.mulSingle (fun j => GL (Two (Fin r) (Fin t) j) F) false)) z w := by
  intro hP F _ _ _ _ p _ r t χ W _ _ π z y ℓ hp hsm hirr hχ hy0 hy hℓ hz
  obtain ⟨hx0, hxt⟩ := jacquet_ne_zero_of_isBlockVec_two hP F r t χ W π y hsm hirr hχ hy0 hy
  set x : Jacquet π (unipRad F (two (stdSum (rfl : r + t = r + t)))) := Submodule.Quotient.mk y with hxdef
  obtain ⟨Y, _, _, τ, w, hτ, hsq, hw0, hrel⟩ :=
    exists_irreducible_subquotient_rel _ _ (GlobalTheory.SmGL.jac (two (stdSum (rfl : r + t = r + t))) π) x hx0
  refine ⟨Y, inferInstance, inferInstance, τ, hτ, hsq, w, hw0, fun g hg => ?_, ?_, ℓ, hℓ, ?_⟩
  · have := hrel Unit {()} (fun _ => Pi.mulSingle true g) (fun _ => 1) _ (by
      simpa using hxt g hg)
    simpa using this
  · intro h hh
    have := hrel Unit {()} (fun _ => Pi.mulSingle false h) (fun _ => 1) 1 (by
      simp only [Finset.sum_singleton, one_smul]
      rw [hxdef, jac_mulSingle_false π (GlobalTheory.StepData.KOne_le_KO hh), act_mulSingle_false_KOne hy hh])
    simpa using this
  · have hsum : ∑ g ∈ z.coeff.support, z.coeff g • GlobalTheory.SmGL.jac (two (stdSum (rfl : r + t = r + t))) π
        (Pi.mulSingle false (ℓ g)) x = (1 : ℂ) • x := by
      rw [one_smul, hxdef]
      have e : ∀ g ∈ z.coeff.support, z.coeff g • GlobalTheory.SmGL.jac (two (stdSum (rfl : r + t = r + t))) π
          (Pi.mulSingle false (ℓ g)) (Submodule.Quotient.mk y) =
          Submodule.Quotient.mk (z.coeff g • π (emb₂ F (stdSum (rfl : r + t = r + t)) (ℓ g, 1)) y) :=
        fun g _ => by rw [jac_mulSingle_false π ((hℓ g).mem_KO hp), Submodule.Quotient.mk_smul]
      rw [Finset.sum_congr rfl e]
      conv_rhs => rw [← hz, Finsupp.sum]
      exact (map_sum (Submodule.mkQ _) _ _).symm
    have := hrel _ z.coeff.support (fun g => Pi.mulSingle false (ℓ g)) z.coeff 1 hsum
    rw [one_smul] at this
    intro h0
    apply hw0
    rw [← this, ← h0, Finsupp.sum]
    rfl

end GlobalTheory.JacTypeVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIPEqStarL2
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.GoodModulus

theorem thetaInner_eq_star_l2 {D : D7} {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (x y : WO S T' → ℂ) :
    thetaIP μ 𝓕 x y = star (GlobalTheory.AdelicScalar.l2 μ 𝓕 x y) := by
  unfold thetaIP GlobalTheory.AdelicScalar.l2 Formalism.IndefR.Lift.pet
  show _ = (starRingEnd ℂ) _
  rw [← integral_conj]
  congr 1; funext w
  simp [mul_comm]

theorem goodMod : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, GoodMod R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ v f hf hoff k hk
  obtain ⟨a, rfl⟩ := _root_.GlobalTheory.RawLift.suppF_finIdem_mem_range D (Wc D i) v f hf k hk
  have hW := hL.thP.ωP i t
  have hvac := _root_.GlobalTheory.RawLift.vacFin_off D G Pl0 T A Ks R F hL i t v f hf hoff
  have hunr := _root_.GlobalTheory.GoodModUnr.chrTh_unrAt D G Pl0 T A Ks R F hL i t v f hf hoff
  obtain ⟨φ, hφ, hc⟩ := GlobalTheory.VacCoef.vac_coef D R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) hW μ 𝓕 hμ v hunr
  have hmod := _root_.GlobalTheory.LocKerMod.sq_norm_mul_latIndex D (Wc D i) (Vc D i).rank _ v φ hφ (fun w h => (hunr w h).1) a
  have h1 := hc a (R.vP i t) (R.vP i t) hvac hvac
  have hne := (vecNe D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ).1
  have hne' : GlobalTheory.AdelicScalar.l2 μ 𝓕 (R.vP i t) (R.vP i t) ≠ 0 := by
    intro h; apply hne; rw [thetaInner_eq_star_l2, h, star_zero]
  have e : coef R i t μ 𝓕 (GlobalTheory.FinZeta.embV (Wc D i) v a) = star (φ a) := by
    unfold coef
    rw [thetaInner_eq_star_l2, thetaInner_eq_star_l2, h1, star_mul', mul_div_assoc, div_self (star_ne_zero.2 hne'), mul_one]
  rw [e, norm_star]
  exact hmod

end GlobalTheory.RawLift.GoodModulus

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralUpperMspan
section
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.ThetaPoisson GlobalTheory.ShortVecDecay
open scoped ComplexConjugate nonZeroDivisors ENNReal
open GlobalTheory.RSTheta GroundTheory.Global.IdeleGroup

namespace GlobalTheory.RSThetaM

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def measSub (E : Type) [Field E] [NumberField E] (a : ℕ) : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | Measurable F}
  add_mem' hF hG := Measurable.add hF hG
  zero_mem' := measurable_const
  smul_mem' c _ hF := Measurable.const_smul hF c

theorem measurable_gl_of_matrix {X : Type} [MeasurableSpace X] {γ : X → GL (Fin a) (Cinf E)}
    (h : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) : Measurable γ := by
  have hu : Continuous fun q : invSet E a =>
      (IsUnit.unit (q.2 : IsUnit (Matrix.of q.1)) : GL (Fin a) (Cinf E)) := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have := GlobalTheory.ConstTermSmooth.contDiffOn_invM.continuousOn.comp_continuous
      (f := fun q : invSet E a => q.1) continuous_subtype_val fun q => q.2
    refine Continuous.congr this fun q => ?_
    simp only [Matrix.coe_units_inv]
    rfl
  have hm : Measurable fun x => (⟨toL (γ x).val, (γ x).isUnit⟩ : invSet E a) := h.subtype_mk
  convert hu.measurable.comp hm using 1
  funext x
  ext1
  rfl

theorem measurable_of_mem_mspanR (π : CuspSub E a) {F : GA E a → ℂ} (hF : F ∈ GlobalTheory.JSW.mspanR π) : Measurable F := by
  have hF' := hF
  unfold GlobalTheory.JSW.mspanR at hF'
  refine Submodule.mem_sInf.1 hF' (measSub E a) ⟨fun φ hφ => ?_, fun F hF h => ?_,
    fun F hF X _ ν _ k γ hk => ?_⟩
  · exact (continuous_of_mem_or (π := π) (Or.inl hφ)).measurable
  · exact (hF : Measurable F).comp (continuous_mul_const h).measurable
  · have hγ : Measurable fun p : GA E a × X => p.1 * infGL E a (γ p.2) :=
      measurable_fst.mul ((GlobalTheory.ConstTermSmooth.continuous_infGL.measurable.comp
        (measurable_gl_of_matrix hk.2.1)).comp measurable_snd)
    have h1 : StronglyMeasurable fun p : GA E a × X => k p.2 * F (p.1 * infGL E a (γ p.2)) :=
      ((hk.1.comp measurable_snd).mul ((hF : Measurable F).comp hγ)).stronglyMeasurable
    exact (h1.integral_prod_right' (ν := ν)).measurable

theorem measurable_rsInf {ℓ : Fin a} {φ φ' : GA E a → ℂ} {Φ : (Fin a → Cinf E) → ℂ} (h : Measurable φ)
    (h' : Measurable φ') (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) :
    Measurable fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ φ' Φ p.1 p.2 := by
  set s : Set (GA E a × (Fin a → Cinf E)) := Set.univ ×ˢ rowSet E ℓ with hsdef
  have hsm : MeasurableSet s := (isOpen_univ.prod (isOpen_rowSet ℓ)).measurableSet
  refine measurable_of_restrict_of_restrict_compl hsm ?_ ?_
  · have hc : Continuous fun p : s => p.1.1 * (infGL E a (rowGL ℓ p.1.2))⁻¹ := by
      have h2 : ContinuousOn (fun p : GA E a × (Fin a → Cinf E) => p.1 * (infGL E a (rowGL ℓ p.2))⁻¹) s :=
        continuous_fst.continuousOn.mul ((continuousOn_inv_rowGL ℓ).comp continuous_snd.continuousOn
          fun p hp => hp.2)
      exact h2.restrict
    have hm := hc.measurable
    exact ((h.comp hm).mul (Complex.continuous_conj.measurable.comp (h'.comp hm))).mul
      (hΦ.measurable.comp (measurable_snd.comp measurable_subtype_coe))
  · convert (measurable_const (a := (0 : ℂ)) : Measurable fun _ : (sᶜ : Set (GA E a × (Fin a → Cinf E))) => (0 : ℂ)) using 1
    funext p
    have hp : p.1.2 ∉ tsupport Φ := fun hp => p.2 ⟨trivial, hs hp⟩
    change rsInf ℓ φ φ' Φ p.1.1 p.1.2 = 0
    simp [rsInf, image_eq_zero_of_notMem_tsupport hp]

theorem measurable_rsPsi_vecMul {ℓ : Fin a} {φ φ' : GA E a → ℂ} {Φ : (Fin a → Cinf E) → ℂ} (h : Measurable φ)
    (h' : Measurable φ') (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (ξ : Fin a → E) :
    Measurable fun g : GA E a => rsPsi ℓ φ φ' Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) := by
  have hY : Continuous fun g : GA E a => (fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val :=
    continuous_const.matrix_vecMul Units.continuous_val
  have hI : Continuous fun g : GA E a => fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i) :=
    continuous_pi fun i => GlobalTheory.ShortVecDecay.continuous_pInf.comp ((continuous_apply i).comp hY)
  have hF : Continuous fun g : GA E a => (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)) - η :=
    (continuous_pi fun i => (continuous_snd : Continuous (pFin E)).comp ((continuous_apply i).comp hY)).sub
      continuous_const
  have h3 : Continuous ((latt a J).indicator (1 : (Fin a → Af E) → ℂ)) :=
    IsClopen.continuous_indicator ⟨isClosed_latt J, isOpen_latt J⟩ continuous_const
  exact ((measurable_rsInf h h' hΦ hs).comp (measurable_id.prodMk hI.measurable)).mul (h3.comp hF).measurable

theorem theta_integral_upper_mspan : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a)
    (π π' : CuspSub E a), π.IsUnitary → π'.IsUnitary → ∀ φ φ' : Sm E a,
    (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → (φ' ∈ π'.V ∨ φ'.1 ∈ GlobalTheory.JSW.mspanR π') →
    ∀ Φ : (Fin a → Cinf E) → ℂ, Continuous Φ → HasCompactSupport Φ → tsupport Φ ⊆ rowSet E ℓ →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ →
    (∀ g : GA E a, Summable fun ξ : {ξ : Fin a → E // ξ ≠ 0} =>
      ‖rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) ∧
    (∀ x : ℝ, IntegrableOn (fun g : GA E a =>
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) *
        (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x)
      (𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) μ) ∧
    (∀ s : ℂ, IntegrableOn (fun g : GA E a =>
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s)
      (𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) μ) ∧
    (Differentiable ℂ fun s : ℂ => ∫ g in 𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)},
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s ∂μ) ∧
    Continuous fun x : ℝ => ∫ g in 𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)},
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
        (((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x : ℝ) : ℂ) ∂μ := by
  intro E _ _ _ a ℓ π π' hπ hπ' φ φ' hφ hφ' Φ hΦ hc hs J η μ _ 𝓕 h𝓕
  have hdec : ∀ {ρ : CuspSub E a}, ρ.IsUnitary → ∀ {ψ : Sm E a}, (ψ ∈ ρ.V ∨ ψ.1 ∈ GlobalTheory.JSW.mspanR ρ) → Decays ψ.1 :=
    fun {ρ} hρ {ψ} hψ L hL C₀ hC₀ N => GlobalTheory.T.cuspFormSmoothSpan_norm_le_shortRationalVector E a ρ hρ ψ hψ [] L hL C₀ hC₀ N
  have hmeas : ∀ {ρ : CuspSub E a} {ψ : Sm E a}, (ψ ∈ ρ.V ∨ ψ.1 ∈ GlobalTheory.JSW.mspanR ρ) → Measurable ψ.1 :=
    fun {ρ} {ψ} hψ => hψ.elim (fun h => (continuous_of_mem_or (π := ρ) (Or.inl h)).measurable)
      (GlobalTheory.RSThetaM.measurable_of_mem_mspanR ρ)
  have hK := isSmallKernel_rsPsi (hdec hπ hφ) (hdec hπ' hφ') hΦ hc hs J η
  obtain ⟨C, hC⟩ := hK.tsum_le (N := 1) le_rfl
  obtain ⟨h1, h2, h3⟩ := hK.integrableOn μ h𝓕 fun ξ _ =>
    (GlobalTheory.RSThetaM.measurable_rsPsi_vecMul (hmeas hφ) (hmeas hφ') hΦ hs J η ξ).aestronglyMeasurable
  refine ⟨fun g => (hC g).1, h1, h2, h3, (h3.continuous.comp Complex.continuous_ofReal).congr fun x => ?_⟩
  refine integral_congr_ae (.of_forall fun g => ?_)
  exact congrArg _ (Complex.ofReal_cpow (ideleModule E _).2.le x).symm

end GlobalTheory.RSThetaM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTypeUnderSupportedLifts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TypeSupportLift

variable {D : D7}

theorem exists_isBaseFrame {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsFrame β Λ) (h : IsSelfDualC V Λ) :
    ∃ N, Lev.IsBaseFrame V β Λ N := by
  obtain ⟨_, N, hB⟩ := GlobalTheory.FinAdIdent.exists_baseFrame V Λ h
  exact ⟨N, hβ, hB.2⟩

theorem idem_add_conj_mul {P : Finset (Pl D.host.E)} (hP : SplitSet P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    (idem P + cA D (idem P)) * (idemAt PP + cA D (idemAt PP)) = idemAt PP + cA D (idemAt PP) := by
  have e1 : idem P * idemAt PP = idemAt PP := by
    rw [idem, Finset.sum_mul, Finset.sum_eq_single PP (fun q hq hne => hP.mul_eq_zero hq hPP fun e => hne e.symm)
      (fun h => absurd hPP h)]
    exact (hP.isIdemAt hPP).1.1
  have e2 : idem P * cA D (idemAt PP) = 0 := by
    rw [idem, Finset.sum_mul]
    exact Finset.sum_eq_zero fun q hq => hP.mul_conj hq hPP
  have e3 : cA D (idem P) * idemAt PP = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [idem, map_sum, Finset.sum_mul]
    exact Finset.sum_eq_zero fun q hq => by rw [mul_comm]; exact hP.mul_conj hPP hq
  have e4 : cA D (idem P) * cA D (idemAt PP) = cA D (idemAt PP) := by rw [← RingHom.map_mul, e1]
  rw [add_mul, mul_add, mul_add, e1, e2, e3, e4, add_zero, zero_add]

theorem suppAt_idem_of_mem {V : HSp D} {P : Finset (Pl D.host.E)} (hP : SplitSet P) {PP : Pl D.host.E} (hPP : PP ∈ P)
    {g : GA D V} (hg : SuppAt (idemAt PP) V g) : SuppAt (idem P) V g := fun i j => by
  rw [← hg i j, ← mul_assoc, idem_add_conj_mul hP hPP]

theorem exists_lift_supp {S T : HSp D} (B : Base S T) (hB : B.Good) (u : G0 B.G.Pg T.rank) :
    ∃ κ : GA D T, Lev.IsLevelLift T B.F.βT B.G.levT u κ ∧ SuppAt (idem B.G.Pg) T κ := by
  obtain ⟨N, hN⟩ := exists_isBaseFrame hB.frame.frT hB.frame.sdT
  obtain ⟨R, h1, -, hR⟩ := hB.places.split
  have hPg : SplitSet B.G.Pg := hR.mono h1
  obtain ⟨e, κ, hl, hall⟩ := GlobalTheory.ParahoricLift.exists_lift_prod T B.F.βT B.G.levT B.F.ΛT N hN
    (fun PP hP PP' hP' => by
      rcases hP' with hP' | hP'
      · exact GlobalTheory.ExportType.not_isConjPl_of_splitSet hR (h1 hP) (h1 hP')
      · exact absurd hP' (Finset.notMem_empty _))
    (Finset.disjoint_empty_right _) u
  refine ⟨_, (hall Finset.univ.toList (Finset.nodup_toList _) fun PP => Finset.mem_toList.2 (Finset.mem_univ PP)).1, ?_⟩
  refine List.prod_induction _ (fun a b ha hb => GlobalTheory.SplitLinear.suppAt_mul ha hb) (GlobalTheory.SplitLinear.suppAt_one _ _) ?_
  intro x hx
  obtain ⟨PP, -, rfl⟩ := List.mem_map.1 hx
  have hs := (hl PP).2.1
  rw [← idemAt_eq (hl PP).1] at hs
  exact suppAt_idem_of_mem hPg PP.2 hs


open Classical in
theorem series_type_supp : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ ω : PairRep S T, B.IsWeil 1 ω →
    ∀ (u : G0 B.G.Pg T.rank) (hu : u ∈ B.G.P.H), ∃ κ : GA D T, Lev.IsLevelLift T B.F.βT B.G.levT u κ ∧
      SuppAt (idem B.G.Pg) T κ ∧ ∀ (Q : Finset (Pl D.host.E)), B.admitted Q →
        ∀ (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T),
          series B.F ω (B.vecAt Q φ) h P (g * κ) = ((B.G.P.chi ⟨u, hu⟩ : ℂˣ) : ℂ) * series B.F ω (B.vecAt Q φ) h P g := by
  intro D S T B hB hS ω hω u hu
  obtain ⟨κ, hκ, hs⟩ := exists_lift_supp B hB u
  refine ⟨κ, hκ, hs, fun Q hQ φ h P g => ?_⟩
  have hred : ∀ PP : ↥Q, redFn B.F.βT PP.1 (Lev.finE T κ) = 1 := fun PP =>
    GlobalTheory.ExportSeries.redFn_eq_one_of_suppAt B.F.βT (GlobalTheory.ExportSeries.DualType.dualTypePlaces_isSplitNonconjugate_of_admissible hQ) Finset.subset_union_left
      (Finset.mem_union_right _ (Finset.mem_union_right _ PP.2))
      (fun h => Finset.disjoint_left.1 hQ.1.disj h (Finset.mem_union_right _ PP.2)) (parLev_St hκ.2.1) hs
  have := GlobalTheory.ExportType.series_type hB hS hQ hω hu (GlobalTheory.ExportType.lifts_of_isLiftG0 hκ) (φ := φ) (φ' := φ) (fun _ => 1)
    (fun PP y => by rw [hred PP, Units.val_one, Matrix.one_mul, Units.val_one, one_mul]) h P g
  rw [this, Finset.prod_const_one, inv_one, mul_one]

end GlobalTheory.TypeSupportLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VerticalStatementHolds
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

namespace GlobalTheory

theorem continuous_mul_norm_rpow_neg_half :
    Continuous fun z : ℂ => z * ((‖z‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    rw [ContinuousAt, zero_mul, tendsto_zero_iff_norm_tendsto_zero]
    have hfun : (fun z : ℂ => ‖z * ((‖z‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖)
        = fun z => ‖z‖ ^ (1 / 2 : ℝ) := by
      funext z
      rcases eq_or_ne z 0 with rfl | hz
      · simp [Real.zero_rpow (show (1 / 2 : ℝ) ≠ 0 by norm_num)]
      · have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        have h2 : ‖z‖ ^ (1 / 2 : ℝ) = ‖z‖ ^ (1 : ℝ) * ‖z‖ ^ (-(1 / 2) : ℝ) := by
          rw [← Real.rpow_add hp]; norm_num
        rw [h2, Real.rpow_one]
    rw [hfun]
    have hc : Continuous fun z : ℂ => ‖z‖ ^ (1 / 2 : ℝ) :=
      continuous_norm.rpow_const (fun _ => Or.inr (by norm_num))
    simpa [Real.zero_rpow (show (1 / 2 : ℝ) ≠ 0 by norm_num)] using hc.tendsto 0
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    apply ContinuousAt.mul continuousAt_id
    apply Complex.continuous_ofReal.continuousAt.comp
    exact continuous_norm.continuousAt.rpow_const (Or.inl hn)

end GlobalTheory
end

