module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0223
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0228

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondencePairingLawOfTensorLaw
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.PairOfTens

open GlobalTheory.InvPairingTensor (exists_real_parts)
open GlobalTheory.ArchRec.PairTensor

variable {p q r s : ℕ} {T : GrpData p q} (R : DSRep T)

theorem ctr_map {U U' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U'] (g : U →ₗ[ℂ] U')
    (v : R.HK.V) (z : R.HK.V ⊗[ℂ] U) :
    ctr R U' v (TensorProduct.map LinearMap.id g z) = g (ctr R U v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [TensorProduct.map_tmul, ctr_tmul, ctr_tmul, map_smul, LinearMap.id_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mem_hwSub {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ)
    (v : V) : v ∈ hwSub act μ ↔
      (∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) ∧ ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem ctr_ne_zero {U : Type} [AddCommGroup U] [Module ℂ U] (Λ : Ix p q → ℚ)
    (h1 : Module.finrank ℂ ↥(hwSub R.HK.act Λ) = 1) (z : R.HK.V ⊗[ℂ] U) (hz : z ≠ 0)
    (hw : ∀ a, TensorProduct.map (R.HK.act (Eab a a)) LinearMap.id z = ((Λ a : ℚ) : ℂ) • z)
    (hn : ∀ a b, posC a b → TensorProduct.map (R.HK.act (Eab a b)) LinearMap.id z = 0)
    (v : R.HK.V) (hv : IsHW R.HK.act Λ v) : ctr R U v z ≠ 0 := by
  intro h0
  apply hz
  refine eq_zero_of_ctr R U z fun w => ?_
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  let d : R.HK.V ⊗[ℂ] U →ₗ[ℂ] R.HK.V :=
    (TensorProduct.rid ℂ R.HK.V).toLinearMap ∘ₗ TensorProduct.map LinearMap.id l
  have hd : ∀ a b, d (a ⊗ₜ b) = l b • a := fun a b => by simp [d]
  have hdA : ∀ (A : Module.End ℂ R.HK.V) y, d (TensorProduct.map A LinearMap.id y) = A (d y) := by
    intro A y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [TensorProduct.map_tmul, hd, hd, map_smul, LinearMap.id_apply]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hdc : ∀ u y, l (ctr R U u y) = ⟪R.ι u, R.ι (d y)⟫_ℂ := by
    intro u y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [ctr_tmul, hd, map_smul, map_smul, inner_smul_right, smul_eq_mul, mul_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy, inner_add_right]
  have hmem : d z ∈ hwSub R.HK.act Λ := by
    rw [mem_hwSub]
    exact ⟨fun a => by rw [← hdA, hw, map_smul], fun a b hab => by rw [← hdA, hn a b hab, map_zero]⟩
  have hv0 : (⟨v, hv.2⟩ : hwSub R.HK.act Λ) ≠ 0 := fun h => hv.1 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hv0).1 h1 ⟨d z, hmem⟩
  have hc' : c • v = d z := congrArg Subtype.val hc
  have h2 := hdc v z
  rw [h0, map_zero, ← hc', map_smul, inner_smul_right] at h2
  have hvv : ⟪R.ι v, R.ι v⟫_ℂ ≠ 0 := fun h =>
    hv.1 (R.ι_inj (by rw [map_zero]; exact inner_self_eq_zero.1 h))
  have hc0 : c = 0 := (mul_eq_zero.1 h2.symm).resolve_right hvv
  rw [hdc, ← hc', hc0, zero_smul, map_zero, inner_zero_right]

variable {σ : Type} {a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)}
  {a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)}

theorem exists_tintw (h₁ : IsGK a₁) (hA : AdmGK R.HK) (M : GKMod r s)
    (B : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] M.V) (hB : PLift a₁ a₂ R (fun Z => M.act Z) B) :
    ∃ f, TIntw a₁ a₂ R.HK M f ∧ ∀ P v, B P v = ctr R M.V v (f P) := by
  obtain ⟨f, hf, hBf⟩ := exists_map R a₁ h₁ hA B hB.1
  refine ⟨f, ⟨hf, fun Z => ?_⟩, hBf⟩
  have hreal : ∀ X ∈ upq r s, ∀ P, f (a₂ X P) = TensorProduct.map LinearMap.id (M.act X) (f P) := by
    intro X hX P
    refine ext_ctr R _ _ _ fun y => ?_
    rw [ctr_map, ← hBf, ← hBf]
    exact hB.2 X hX P y
  obtain ⟨X, Y, hX, hY, -, rfl⟩ := exists_real_parts Z
  refine LinearMap.ext fun P => ?_
  simp only [LinearMap.comp_apply, map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    TensorProduct.map_add_right, TensorProduct.map_smul_right, hreal X hX, hreal Y hY]

theorem exists_tintw_inc (h₁ : IsGK a₁) (hA : AdmGK R.HK) (M : GKMod r s) {U : Type} [AddCommGroup U] [Module ℂ U]
    (b : Mat r s → Module.End ℂ U) (inc : M.V →ₗ[ℂ] U) (hi : Function.Injective inc)
    (he : ∀ Z ∈ upq r s, ∀ y, inc (M.act Z y) = b Z (inc y))
    (B : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U) (hB : PLift a₁ a₂ R b B)
    (hr : ∀ P v, B P v ∈ LinearMap.range inc) :
    ∃ f, TIntw a₁ a₂ R.HK M f ∧ ∀ P v, B P v = inc (ctr R M.V v (f P)) := by
  obtain ⟨g, hg⟩ := inc.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hi)
  let B₀ : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] M.V :=
    { toFun := fun P =>
        { toFun := fun v => g (B P v)
          map_add' := fun v w => by rw [map_add (f := _), map_add (f := _)]
          map_smul' := fun c v => by rw [LinearMap.map_smulₛₗ, map_smul] }
      map_add' := fun P Q => by ext v; simp
      map_smul' := fun c P => by ext v; simp }
  have h0 : ∀ P v, inc (B₀ P v) = B P v := by
    intro P v
    obtain ⟨y, hy⟩ := hr P v
    change inc (g (B P v)) = _
    rw [← hy]
    exact congrArg inc (LinearMap.congr_fun hg y)
  obtain ⟨f, hf, hBf⟩ := exists_tintw (a₂ := a₂) R h₁ hA M B₀
    ⟨fun Z hZ P v => hi (by rw [map_add (f := _), h0, h0, map_zero]; exact hB.1 Z hZ P v),
     fun Z hZ P v => hi (by rw [h0, he Z hZ, h0]; exact hB.2 Z hZ P v)⟩
  exact ⟨f, hf, fun P v => by rw [← hBf, h0]⟩

theorem exists_both (h₁ : IsGK a₁) (h₂ : IsGK a₂) (hA : AdmGK R.HK) {U : Type} [NormedAddCommGroup U]
    [InnerProductSpace ℂ U] (b : Mat r s → Module.End ℂ U) (hb : IsUAct b)
    (B B' : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U) (hB : PLift a₁ a₂ R b B) (hB' : PLift a₁ a₂ R b B') :
    ∃ (MM : UGKMod r s) (inc : MM.M.V →ₗ[ℂ] U) (f f' : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V ⊗[ℂ] MM.M.V),
      Function.Injective inc ∧ (∀ Z ∈ upq r s, ∀ y, inc (MM.M.act Z y) = b Z (inc y)) ∧
      TIntw a₁ a₂ R.HK MM.M f ∧ TIntw a₁ a₂ R.HK MM.M f' ∧
      (∀ P v, B P v = inc (ctr R _ v (f P))) ∧ ∀ P v, B' P v = inc (ctr R _ v (f' P)) := by
  obtain ⟨MM, inc, hi, hr, he⟩ := GlobalTheory.T.exists_unitary_module_onto_span_of_intertwining r s (MvPolynomial σ ℂ) U (R.HK.V ⊕ R.HK.V) a₂ b
    (Sum.elim (fun v => B.flip v) (fun v => B'.flip v)) h₂ hb (by
      rintro (v | v) Z hZ P
      · exact hB.2 Z hZ P v
      · exact hB'.2 Z hZ P v)
  obtain ⟨f, hf, hBf⟩ := exists_tintw_inc R h₁ hA MM.M b inc hi he B hB fun P v => by
    rw [hr]; exact Submodule.subset_span ⟨Sum.inl v, P, rfl⟩
  obtain ⟨f', hf', hBf'⟩ := exists_tintw_inc R h₁ hA MM.M b inc hi he B' hB' fun P v => by
    rw [hr]; exact Submodule.subset_span ⟨Sum.inr v, P, rfl⟩
  exact ⟨MM, inc, f, f', hi, he, hf, hf', hBf, hBf'⟩

theorem pairLaw_of_tensLaw : ∀ (p q r s : ℕ) (T₁ : GrpData p q) (σ : Type) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (R₁ : DSRep T₁) (T₂ : GrpData r s) (R₂ : DSRep T₂) (Λ₁ : Ix p q → ℚ) (Λ₂ : Ix r s → ℚ), IsGK a₁ → IsGK a₂ → AdmGK R₁.HK → Module.finrank ℂ ↥(hwSub R₁.HK.act Λ₁) = 1 → TensLaw a₁ a₂ R₁ R₂ Λ₁ Λ₂ → PairLaw a₁ a₂ R₁ R₂ Λ₁ Λ₂ := by
  intro p q r s T₁ σ a₁ a₂ R₁ T₂ R₂ Λ₁ Λ₂ h₁ h₂ hA h1 hT
  refine ⟨hT.ex, hT.uniq, fun U _ _ b hb B hB hB0 => ?_, ?_⟩
  · have hne : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (inc : M →ₗ[ℂ] U)
        (f : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V ⊗[ℂ] M), (∀ P v, B P v = inc (ctr R₁ _ v (f P))) → f ≠ 0 := by
      intro M _ _ inc f hf h0
      apply hB0
      refine LinearMap.ext fun P => LinearMap.ext fun v => ?_
      rw [hf, h0]
      simp
    refine ⟨?_, fun Φ hΦ => ⟨fun v hv => ?_, fun B' hB' hΦ' => ?_⟩⟩
    · obtain ⟨MM, inc, f, -, hi, he, hf, -, hBf, -⟩ := exists_both R₁ h₁ h₂ hA b hb B B hB hB
      obtain ⟨⟨N, e, hee, hrf⟩, -⟩ := hT.unit MM f hf (hne inc f hBf)
      refine ⟨inc ∘ₗ N.subtype ∘ₗ e.toLinearMap, hi.comp (Subtype.val_injective.comp e.injective),
        fun Z hZ x => ?_, le_antisymm ?_ ?_⟩
      · change inc (e (R₂.HK.act Z x) : N) = b Z (inc (e x : N))
        rw [hee, he Z hZ]
      · rintro _ ⟨x, rfl⟩
        haveI : Nontrivial (hwSub R₁.HK.act Λ₁) := Module.nontrivial_of_finrank_eq_succ h1
        obtain ⟨⟨v, hvm⟩, hv⟩ := exists_ne (0 : hwSub R₁.HK.act Λ₁)
        have hvv : ⟪R₁.ι v, R₁.ι v⟫_ℂ ≠ 0 := fun h =>
          hv (Subtype.ext (R₁.ι_inj (by rw [ZeroMemClass.coe_zero, map_zero]; exact inner_self_eq_zero.1 h)))
        have hm : TensorProduct.map LinearMap.id N.subtype (v ⊗ₜ[ℂ] e x) ∈ LinearMap.range f := by
          rw [hrf]; exact LinearMap.mem_range_self _ _
        obtain ⟨P, hP⟩ := hm
        have h3 : B P v = ⟪R₁.ι v, R₁.ι v⟫_ℂ • inc (e x : N) := by
          rw [hBf, hP, ctr_map, ctr_tmul, map_smul, map_smul]; rfl
        have h4 : (inc ∘ₗ N.subtype ∘ₗ e.toLinearMap) x = (⟪R₁.ι v, R₁.ι v⟫_ℂ)⁻¹ • B P v := by
          rw [h3, inv_smul_smul₀ hvv]; rfl
        rw [h4]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨P, v, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨P, v, rfl⟩
        have hm : f P ∈ LinearMap.range (TensorProduct.map LinearMap.id N.subtype) := by
          rw [← hrf]; exact LinearMap.mem_range_self _ _
        obtain ⟨z, hz⟩ := hm
        refine ⟨e.symm (ctr R₁ N v z), ?_⟩
        rw [hBf, ← hz, ctr_map]
        simp
    · obtain ⟨MM, inc, f, -, hi, he, hf, -, hBf, -⟩ := exists_both R₁ h₁ h₂ hA b hb B B hB hB
      obtain ⟨-, hj⟩ := hT.unit MM f hf (hne inc f hBf)
      have hΦw := (mem_hwSub _ _ _).1 hΦ.2.1.2
      have hcomm : ∀ X, TensorProduct.map (R₁.HK.act X) LinearMap.id (f Φ) = f (a₁ X Φ) :=
        fun X => (LinearMap.congr_fun (hf.1 X) Φ).symm
      rw [hBf, ← map_zero inc]
      exact hi.ne (ctr_ne_zero R₁ Λ₁ h1 (f Φ) (hj Φ hΦ).1 (fun a => by rw [hcomm, hΦw.1, map_smul])
        (fun a c hac => by rw [hcomm, hΦw.2 a c hac, map_zero]) v hv.1)
    · obtain ⟨MM, inc, f, f', hi, he, hf, hf', hBf, hBf'⟩ := exists_both R₁ h₁ h₂ hA b hb B B' hB hB'
      obtain ⟨-, hj⟩ := hT.unit MM f hf (hne inc f hBf)
      have hff : f' = f := (hj Φ hΦ).2 f' hf' (ext_ctr R₁ _ _ _ fun v => hi (by rw [← hBf, ← hBf', hΦ']))
      refine LinearMap.ext fun P => LinearMap.ext fun v => ?_
      rw [hBf, hBf', hff]
  · obtain ⟨f₀, hf₀, hf0, hall⟩ := hT.line
    obtain ⟨B₀, hB₀, hBf⟩ := exists_pairing R₁ a₁ f₀ hf₀.1
    refine ⟨B₀, fun h0 => hf0 ?_, ⟨hB₀, fun Z hZ P v => ?_⟩, fun B hB => ?_⟩
    · refine LinearMap.ext fun P => eq_zero_of_ctr R₁ _ _ fun v => ?_
      rw [← hBf, h0]; rfl
    · have := LinearMap.congr_fun (hf₀.2 Z) P
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at this
      rw [hBf, hBf, this, ctr_map]
    · obtain ⟨f, hf, hBf'⟩ := exists_tintw R₁ h₁ hA R₂.HK B hB
      obtain ⟨c, rfl⟩ := hall f hf
      refine ⟨c, LinearMap.ext fun P => LinearMap.ext fun v => ?_⟩
      rw [hBf', LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, hBf, map_smul]

end GlobalTheory.ArchRec.PairOfTens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFormEigenMemSinglePart
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar.OnePart

open GlobalTheory.Hk3 GlobalTheory.Hk3.LabDet

theorem adjoin_scalar {M : Type} [AddCommGroup M] [Module ℂ M] (s : Set (Module.End ℂ M)) (S : M → Prop)
    (h : ∀ x ∈ s, ∃ l : ℂ, ∀ u, S u → x u = l • u) :
    ∀ a ∈ Algebra.adjoin ℂ s, ∃ l : ℂ, ∀ u, S u → a u = l • u := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap r =>
    refine ⟨r, fun u _ => ?_⟩
    simp [Module.algebraMap_end_apply]
  | add x y _ _ hx hy =>
    obtain ⟨l, hl⟩ := hx
    obtain ⟨m, hm⟩ := hy
    exact ⟨l + m, fun u hu => by rw [LinearMap.add_apply, hl u hu, hm u hu, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, hl⟩ := hx
    obtain ⟨m, hm⟩ := hy
    exact ⟨m * l, fun u hu => by rw [Module.End.mul_apply, hm u hu, map_smul, hl u hu, smul_smul]⟩

variable {D : D7}

theorem scalar_of_split {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (hP : Formalism.DivisionValues.conjPl P ≠ P) (S : M → Prop) (fu : ∀ u, S u → ∀ k ∈ GlobalTheory.Hk3.hyp V P, π k u = u) (a b : List ℤ → ℂ)
    (ha : ∀ u, S u → ∀ k, k ≤ V.rank →
      opOf π P (Finsupp.single (splitLab V.rank k) 1) u = a (splitLab V.rank k) • u)
    (hb : ∀ u, S u → ∀ k, k ≤ V.rank →
      opOf π (Formalism.DivisionValues.conjPl P) (Finsupp.single (splitLab V.rank k) 1) u = b (splitLab V.rank k) • u) (d : List ℤ) :
    ∃ l : ℂ, ∀ u, S u → opOf π P (Finsupp.single d 1) u = l • u := by
  obtain ⟨z, hz, hzu⟩ := _root_.GlobalTheory.SplitGen.gen_split V P hP M π d
  have gen : ∀ x ∈ {x : Module.End ℂ M | ∃ k, k ≤ V.rank ∧ (x = opOf π P (Finsupp.single (splitLab V.rank k) 1) ∨
      x = opOf π P (Finsupp.single (dualLab (splitLab V.rank k)) 1))}, ∃ l : ℂ, ∀ u, S u → x u = l • u := by
    rintro x ⟨k, hk, rfl | rfl⟩
    · exact ⟨a (splitLab V.rank k), fun u hu => ha u hu k hk⟩
    · refine ⟨b (splitLab V.rank k), fun u hu => ?_⟩
      have hc := (_root_.GlobalTheory.SphConj.sph_conj V P).2.2 (Finsupp.single (splitLab V.rank k) 1) M π u (fu u hu)
      rw [GlobalTheory.Hk3.dualC, Finsupp.mapDomain_single] at hc
      rw [← hc]
      exact hb u hu k hk
  obtain ⟨l, hl⟩ := adjoin_scalar _ S gen z hz
  exact ⟨l, fun u hu => by rw [← hzu u (fu u hu), hl u hu]⟩

theorem postOn_hk_single {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (P : Pl D.host.E) (d : List ℤ) (U : MMap M) :
    postOn M (hk V P (Finsupp.single d 1)) U = opOf (rRep M) P (Finsupp.single d 1) U := by
  unfold rRep
  simp only [hk, opOf, Finsupp.sum_single_index, one_smul, zero_smul]
  ext v g
  simp [postOn, heckeLin, rLin, LinearMap.compMultilinearMap_apply, Finset.sum_apply]

private theorem star_algebraMap_eq (c : D.host.F) : star (algebraMap D.host.F D.host.E c) = algebraMap D.host.F D.host.E c := by
  have hm : (algebraMap D.host.F D.host.E c) ∈ NumberField.maximalRealSubfield D.host.E :=
    NumberField.IsTotallyReal.le_maximalRealSubfield D.host.F c.2
  exact (NumberField.IsCMField.complexConj_eq_self_iff _ _).mpr hm

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem good_conj (R : RealDat D A Ks) (t : T0) (P : Pl D.host.E) (hP : Good R t P) : Good R t (Formalism.DivisionValues.conjPl P) := by
  intro PP hPP
  obtain ⟨h1, h2⟩ := hP PP hPP
  rw [GlobalTheory.GoodPrimes.isConjPl_iff] at h2 ⊢
  refine ⟨fun e => h2 ?_, fun e => h1 ?_⟩
  · rw [e, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
  · have e' := congrArg Formalism.DivisionValues.conjPl e
    rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl] at e'
    exact e'.symm

theorem good_of_offS (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (P : Pl D.host.E)
    (h : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P) : Good R A.μ0 P := by
  classical
  intro PP hPP
  have hPg : PP ∈ R.Pg := by
    rcases hPP with h1 | h1
    · exact h1
    · rw [GlobalTheory.LiftLower.Q_base hL] at h1
      simp at h1
  obtain ⟨x, hx, hy⟩ := h ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (Finset.mem_image_of_mem _ hPg)
  have hx' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ PP.asIdeal := hx
  have hcoe : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (x : D.host.F) := by
    first
    | rfl
    | (rw [← IsScalarTower.algebraMap_apply (𝓞 D.host.F) (𝓞 D.host.E) D.host.E,
          IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E]; rfl)
  have hnot := hy _ hcoe
  refine ⟨fun e => hnot (by rw [← e]; exact hx'), fun hc => ?_⟩
  obtain ⟨c', hc'P, hc'eq⟩ := hc _ hx'
  exact hy c' (by rw [hc'eq, hcoe, star_algebraMap_eq]) hc'P

private theorem primeIdem_and_sphOp_of_isHeckeOpFull {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ}
    {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {P : Pl D.host.E} {d : List ℤ} {Rp : Finset (GA D V)}
    (h : Hecke₂ V J χ Sb P d Rp) :
    (∃ e f, IsPrimeIdem P e f ∧ OffS D Sb P ∧ (∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) ∧
      (∀ g ∈ J, SuppF V f g → χ g = 1)) ∧ SphOp V P d Rp := by
  unfold Hecke₂ at h
  obtain ⟨e, f, ϖ, α, hS, hPf, h1, h2, h3, hJ, hχ, hα, hd, hR, hc⟩ := h
  refine ⟨⟨e, f, hPf, hS, hJ, hχ⟩, ?_⟩
  have hset : {k | k ∈ J ∧ SuppF V f k} = {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := by
    ext k
    exact ⟨fun hk => ⟨(hJ k hk.2).1 hk.1, hk.2⟩, fun hk => ⟨(hJ k hk.2).2 hk.1, hk.2⟩⟩
  unfold SphOp Hecke₂
  refine ⟨e, f, ϖ, α, GlobalTheory.LevOp.offS_empty, hPf, h1, h2, h3, fun _ _ => Iff.rfl, fun _ _ _ => rfl, hα, hd, hR, ?_⟩
  rw [← hset]
  exact hc

private theorem mult_map_mul_right_eq_of_chi_eq_one {θ} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {U : MMap M} (hU : U ∈ Mult θ M J χ) (k : GA D V) (hk : k ∈ J) (hχ : χ k = 1) :
    ∀ v g, U v (g * k) = U v g := by
  induction hU using Submodule.span_induction with
  | mem T hT =>
    intro v g
    rw [hT.lev v k hk g, hχ, one_mul]
  | zero => intro v g; rfl
  | add T T' _ _ h1 h2 =>
    intro v g
    simp only [MultilinearMap.add_apply, Pi.add_apply, h1 v g, h2 v g]
  | smul c T _ h1 =>
    intro v g
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, h1 v g]

theorem mem_one_part : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_HW → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (b : Pl D.host.E → List ℤ → ℂ), ∃ ev, ∀ w : (R.HW i σ).H, (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.ConjScalar.RelLab (Wc D i) P d → postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e w) = b P d • (R.HW i σ).e w) → w ∈ GlobalTheory.LiftLower.partH R i σ ev := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hM i σ b
  classical
  obtain ⟨Sw, hSw⟩ : ∃ Sw : MMap (R.MW i σ) → Prop, ∀ u, Sw u ↔ ∃ w : (R.HW i σ).H,
      (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.ConjScalar.RelLab (Wc D i) P d →
        postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e w) = b P d • (R.HW i σ).e w) ∧
      u = (R.HW i σ).e w := ⟨_, fun _ => Iff.rfl⟩
  refine ⟨fun P d => if h : ∃ l : ℂ, ∀ u, Sw u → opOf (rRep (R.MW i σ)) P (Finsupp.single d 1) u = l • u
    then h.choose else 0, ?_⟩
  intro w hw
  have hW : ∀ w' : (R.HW i σ).H, (R.HW i σ).e w' ∈ R.Wall i σ := by
    intro w'
    rw [← (hM i σ).2.1]
    exact LinearMap.mem_range_self _ w'
  simp only [GlobalTheory.LiftLower.partH, Submodule.mem_comap, partFull, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  refine ⟨hW w, ?_⟩
  intro P d Rp hfull
  obtain ⟨⟨e, f, hPf, hS, hJ, hχ⟩, hsph⟩ := primeIdem_and_sphOp_of_isHeckeOpFull hfull
  have hG : GlobalTheory.Hk3.Good R A.μ0 P := good_of_offS R hL P hS
  have hfix : ∀ w' : (R.HW i σ).H, ∀ k ∈ GlobalTheory.Hk3.hyp (Wc D i) P,
      rRep (R.MW i σ) k ((R.HW i σ).e w') = (R.HW i σ).e w' := by
    intro w' k hk
    obtain ⟨hk1, hk2⟩ := (GlobalTheory.LevOp.mem_hyp hPf).1 hk
    have hkJ := (hJ k hk2).2 hk1
    have hinv := mult_map_mul_right_eq_of_chi_eq_one (hW w') k hkJ (hχ k hkJ hk2)
    unfold rRep
    ext v g
    simp [postOn, rLin, LinearMap.compMultilinearMap_apply, hinv]
  have hSfix : ∀ u, Sw u → ∀ k ∈ GlobalTheory.Hk3.hyp (Wc D i) P, rRep (R.MW i σ) k u = u := by
    intro u hu k hk
    obtain ⟨w', -, rfl⟩ := (hSw u).1 hu
    exact hfix w' k hk
  have hex : ∃ l : ℂ, ∀ u, Sw u → opOf (rRep (R.MW i σ)) P (Finsupp.single d 1) u = l • u := by
    by_cases hc : Formalism.DivisionValues.conjPl P = P
    · refine ⟨b P d, fun u hu => ?_⟩
      obtain ⟨w', hw', rfl⟩ := (hSw u).1 hu
      rw [← postOn_hk_single]
      exact hw' P d hG (Or.inr ⟨hc, Rp, hsph⟩)
    · refine scalar_of_split (rRep (R.MW i σ)) P hc Sw hSfix (b P) (b (Formalism.DivisionValues.conjPl P)) ?_ ?_ d
      · intro u hu k hk
        obtain ⟨w', hw', rfl⟩ := (hSw u).1 hu
        rw [← postOn_hk_single]
        exact hw' P _ hG (Or.inl ⟨hc, k, hk, rfl⟩)
      · intro u hu k hk
        obtain ⟨w', hw', rfl⟩ := (hSw u).1 hu
        rw [← postOn_hk_single]
        refine hw' (Formalism.DivisionValues.conjPl P) _ (good_conj R A.μ0 P hG) (Or.inl ⟨?_, k, hk, rfl⟩)
        rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
        exact fun h => hc h.symm
  have hsum : heckeOn (R.MW i σ) Rp ((R.HW i σ).e w) = ∑ γ ∈ Rp, rRep (R.MW i σ) γ ((R.HW i σ).e w) := by
    unfold rRep
    ext v g
    simp [heckeOn, postOn, heckeLin, rLin, LinearMap.compMultilinearMap_apply]
  rw [hsum, ((_root_.GlobalTheory.SphLabelOps.label_operators (Wc D i) P).1 d Rp hsph).2 _ (rRep (R.MW i σ)) _ (hfix w), dite_eq_left hex]
  exact hex.choose_spec _ ((hSw _).2 ⟨w, hw, rfl⟩)

end GlobalTheory.ConjScalar.OnePart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionIsotropicPartHomOfFrameMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoFrameAct

open scoped GlobalTheory.MixModel

theorem actO_isoPart_of_mul : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (a : GL (Fin r) (AE D)) (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → ∀ (h : GA D W) (z : Mx D W.rank r), actO V W m h (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C z) = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h) z) (GlobalTheory.MixModel.adj a.val)) := by
  intro D V W r C a m hm h z
  have e : (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram).map (incA D) =
      GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V := by
    change GlobalTheory.MixModel.rat (Cᴴ * V.gram) = _
    exact Matrix.map_mul
  have hg : GlobalTheory.MixModel.gA V * GlobalTheory.MixModel.giA V = 1 := by
    change (V.gram.map (incA D)) * (V.gram⁻¹.map (incA D)) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
    exact Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))
  have hg' : GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.gA V = 1 := by
    change (V.gram⁻¹.map (incA D)) * (V.gram.map (incA D)) = 1
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
    exact Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))
  have adjmul {l n k : ℕ} (x : Mx D l n) (y : Mx D n k) :
      GlobalTheory.MixModel.adj (x * y) = GlobalTheory.MixModel.adj y * GlobalTheory.MixModel.adj x :=
    Formalism.UG.cT_mul (cA D) x y
  have hinv : Formalism.L2.Theta.mt V m⁻¹ = GlobalTheory.MixModel.giA V *
      (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V) := by
    have hh : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V) * Formalism.L2.Theta.mt V m = 1 := by
      have hr : GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V * Formalism.L2.Theta.mt V m = GlobalTheory.MixModel.gA V := mt_rel V m
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (GlobalTheory.MixModel.adj _), hr, hg']
    rw [← Matrix.one_mul (Formalism.L2.Theta.mt V m⁻¹), ← hh, Matrix.mul_assoc]
    have hm_inv : Formalism.L2.Theta.mt V m * Formalism.L2.Theta.mt V m⁻¹ = 1 := by
      change (m.val * m⁻¹.val).val = 1
      exact congrArg Units.val (mul_inv_cancel m.val)
    rw [hm_inv, Matrix.mul_one]
  have key : GlobalTheory.MixModel.adj (C.map (incA D)) * (GlobalTheory.MixModel.gA V * (GlobalTheory.MixModel.giA V *
      (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V))) =
      GlobalTheory.MixModel.adj a.val * (GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V) := by
    rw [← Matrix.mul_assoc (GlobalTheory.MixModel.gA V), hg, Matrix.one_mul, ← Matrix.mul_assoc, ← adjmul, hm, adjmul,
      Matrix.mul_assoc]
  change Formalism.L2.Theta.mt W h * (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C z) * Formalism.L2.Theta.mt V m⁻¹ = _
  rw [hinv]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart]
  rw [e]
  simp only [Matrix.mul_assoc]
  rw [key]

end GlobalTheory.IsoFrameAct

end
end

