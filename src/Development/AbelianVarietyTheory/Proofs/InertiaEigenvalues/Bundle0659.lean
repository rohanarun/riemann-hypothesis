module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0648
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0641

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationDetCharacter
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
  GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

namespace GlobalTheory.LocGL.DetQuot

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nonempty_equiv_multiProd {t : ℕ} {n : Type} [Fintype n] [DecidableEq n] (e : (Σ _ : Fin t, Fin 1) ≃ n)
    {θ : Fin t → kˣ →* ℂˣ} {Θ : Levi k (fun _ : Fin t => Fin 1) →* ℂˣ}
    (hΘ : ∀ g, Θ g = ∏ a, θ a (GeneralLinearGroup.det (g a))) :
    Nonempty ((parInd e (ofChar Θ)).Equiv (multiProd e fun a => detRep (Fin 1) (θ a))) := by
  refine ⟨parIndEquiv e (Representation.Equiv.mk
    (PiTensorProduct.constantBaseRingEquiv (Fin t) ℂ).toLinearEquiv.symm fun g => ?_)⟩
  refine LinearMap.ext_ring ?_
  apply (PiTensorProduct.constantBaseRingEquiv (Fin t) ℂ).injective
  simp [ofChar_apply, hΘ, PiTensorProduct.one_def, piTensor_tprod, detRep, detChar_apply, Units.coe_prod]

theorem exists_embedding {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {η : kˣ →* ℂˣ} (hη : IsSmoothChar η) :
    ∃ f : (detRep n η).IntertwiningMap (parInd e (ofChar (detLevi e η))), Function.Injective f := by
  have hsm : IsSmooth (detRep n η) := (isSmooth_ofChar_iff _).2 hη.detChar
  let ψ : (GlobalTheory.SmGL.jac e (detRep n η)).IntertwiningMap (ofChar (detLevi e η)) :=
    { toLinearMap := (twKer (detRep n η) (unipRad k e) 1).liftQ LinearMap.id
        (by rw [twKer_detRep]; exact bot_le)
      isIntertwining' := fun g => LinearMap.ext fun x => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, GlobalTheory.SmGL.Model.jac_detRep, map_smul, ofChar_apply,
          smul_eq_mul] }
  obtain ⟨f, hf⟩ := (GlobalTheory.SmGL.Model.evalOne_bijective e hsm (ofChar (detLevi e η))).2 ψ
  refine ⟨f, (injective_iff_map_eq_zero f).2 fun c hc => ?_⟩
  by_contra hc0
  have h1 : f 1 = 0 := by
    have h1' : (1 : ℂ) = c⁻¹ • c := by simp [hc0]
    rw [h1', map_smul, hc, smul_zero]
  have h2 : ψ (Submodule.Quotient.mk (p := twKer (detRep n η) (unipRad k e) 1) (1 : ℂ)) = 1 := rfl
  have h3 : ψ (Submodule.Quotient.mk (p := twKer (detRep n η) (unipRad k e) 1) (1 : ℂ)) = (f 1).1.1 1 := by
    rw [← hf]; rfl
  rw [h1] at h3
  exact one_ne_zero (h2.symm.trans h3)

theorem exists_surjective_of_contra {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] {π : Representation ℂ G V} {χ : G →* ℂˣ} (f : (ofChar χ⁻¹).IntertwiningMap (contra π))
    (hf : Function.Injective f) : ∃ l : π.IntertwiningMap (ofChar χ), Function.Surjective l := by
  set lam : Module.Dual ℂ V := ((f 1 : smoothPart π.dual) : Module.Dual ℂ V) with hlam
  have key : ∀ g v, lam (π g v) = (χ g : ℂ) * lam v := by
    intro g v
    have h1 : f (ofChar (χ⁻¹) (g⁻¹) (1 : ℂ)) = contra π (g⁻¹) (f 1) :=
      LinearMap.congr_fun (f.isIntertwining' (g⁻¹)) (1 : ℂ)
    have h2 : ofChar (χ⁻¹) (g⁻¹) (1 : ℂ) = (χ g : ℂ) • (1 : ℂ) := by
      rw [ofChar_apply]
      simp
    rw [h2, map_smul] at h1
    have h3 := congrArg (fun x : smoothPart π.dual => (x : Module.Dual ℂ V) v) h1
    simp only [contra_apply, inv_inv] at h3
    rw [← h3]
    simp [lam]
  have hne : lam ≠ 0 := by
    intro h0
    have h1 : f 1 = 0 := Subtype.ext (by simpa [lam] using h0)
    exact one_ne_zero (hf (h1.trans (map_zero f).symm))
  obtain ⟨v, hv⟩ : ∃ v, lam v ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (LinearMap.ext h)
  refine ⟨⟨lam, fun g => LinearMap.ext fun w => ?_⟩, fun c => ⟨(c / lam v) • v, ?_⟩⟩
  · simp [key, ofChar_apply]
  · simp [hv]

theorem exists_surjective {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {η : kˣ →* ℂˣ} (hη : IsSmoothChar η) :
    ∃ l : (parInd e (ofChar (detLevi e η⁻¹)⁻¹)).IntertwiningMap (detRep n η), Function.Surjective l := by
  have hc : IsSmoothChar (detLevi e η⁻¹) := by
    unfold detLevi
    exact (hη.inv.detChar.comp (leviEmb k e) (continuous_leviEmb (R := k) e)).mul
      (isSmoothChar_deltaHalf k).inv
  have hc' : IsSmoothChar (detLevi e η⁻¹)⁻¹ := hc.inv
  have hτ : IsSmooth (ofChar (detLevi e η⁻¹)⁻¹) := (isSmooth_ofChar_iff _).2 hc'
  obtain ⟨Φ1⟩ := GlobalTheory.LocGL.ProjLine.nonempty_equiv_contra_ofChar hc'
  rw [inv_inv] at Φ1
  obtain ⟨Φ2⟩ := (GlobalTheory.SmGL.IndDual.inductionContragredient k).nonempty_equiv e hτ
  obtain ⟨f, hf⟩ := exists_embedding e hη.inv
  let F := (Φ2.toIntertwiningMap.comp (parIndEquiv e Φ1).toIntertwiningMap).comp f
  have hF : Function.Injective F := fun a b h =>
    hf ((EquivLike.injective (parIndEquiv e Φ1)) ((EquivLike.injective Φ2) h))
  have hdet : detChar n η⁻¹ = (detChar n η)⁻¹ := by
    ext g
    simp [detChar_apply]
  have key : ∀ (χ' : GL n k →* ℂˣ), χ' = (detChar n η)⁻¹ →
      ∀ f' : (ofChar χ').IntertwiningMap (contra (parInd e (ofChar (detLevi e η⁻¹)⁻¹))), Function.Injective f' →
      ∃ l : (parInd e (ofChar (detLevi e η⁻¹)⁻¹)).IntertwiningMap (ofChar (detChar n η)), Function.Surjective l := by
    rintro χ' rfl f' hf'
    exact exists_surjective_of_contra f' hf'
  exact key (detChar n η⁻¹) hdet F hF

theorem surj_of_equiv {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] {π : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G X}
    (Φ : π.Equiv σ) (l : π.IntertwiningMap τ) (hl : Function.Surjective l) :
    ∃ l' : σ.IntertwiningMap τ, Function.Surjective l' := by
  refine ⟨l.comp Φ.symm.toIntertwiningMap, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hl y
  refine ⟨Φ x, ?_⟩
  show l (Φ.symm (Φ x)) = l x
  rw [Representation.Equiv.symm_apply_apply]

theorem detLevi_inv_apply {t : ℕ} {n : Type} [Fintype n] [DecidableEq n] (e : (Σ _ : Fin t, Fin 1) ≃ n)
    (χ : kˣ →* ℂˣ) (g : Levi k fun _ : Fin t => Fin 1) :
    (detLevi e χ⁻¹)⁻¹ g =
      ∏ a : Fin t, (χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) (GeneralLinearGroup.det (g a)) := by
  rw [MonoidHom.inv_apply, detLevi_apply, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  have hs : (((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) =
      -(-((modExp (fun _ : Fin t => Fin 1) a : ℤ) : ℂ) / 2) := by
    rw [modExp_fin (fun _ : Fin t => Fin 1) (fun _ => Fintype.card_fin 1) a]
    push_cast
    ring
  rw [hs, absPow_neg]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv]

theorem exists_surjective_multiProd {t : ℕ} {n : Type} [Fintype n] [DecidableEq n] (e : (Σ _ : Fin t, Fin 1) ≃ n)
    {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    ∃ l : (multiProd e fun a : Fin t => detRep (Fin 1)
      (χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ))).IntertwiningMap (detRep n χ), Function.Surjective l := by
  obtain ⟨Φ⟩ := nonempty_equiv_multiProd e (Θ := (detLevi e χ⁻¹)⁻¹)
    (θ := fun a : Fin t => χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) (detLevi_inv_apply e χ)
  obtain ⟨l, hl⟩ := exists_surjective e hχ
  exact surj_of_equiv Φ l hl

theorem exists_equiv_prodIrr {t : ℕ} {θ : Fin t → kˣ →* ℂˣ} (hθ : ∀ a, IsSmoothChar (θ a)) {x : Fin t → IrrGL (k := k)}
    (hx : ∀ a, x a = IrrGL.ofChar (θ a) (hθ a)) :
    ∃ (e : (Σ _ : Fin t, Fin 1) ≃ Fin t) (hd' : ∑ a, (x a).1 = t), Nonempty ((multiProd e fun a => detRep (Fin 1) (θ a)).Equiv (prodIrr x hd')) := by
  obtain rfl : x = fun a => IrrGL.ofChar (θ a) (hθ a) := funext hx
  have hd : ∑ a : Fin t, (IrrGL.ofChar (θ a) (hθ a)).1 = t := by simp [IrrGL.ofChar]
  exact ⟨stdBlocks _ hd, hd, ⟨multiProdEquiv _ fun a => equivRep (IrrRep.det (Fin 1) (θ a) (hθ a))⟩⟩

set_option maxHeartbeats 1600000 in
private theorem exists_surjective_prodIrr_to_detRep (t : ℕ) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) {x : Fin t → IrrGL (k := k)}
    (hx : ∀ j, x j = (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - (j : ℕ) : ℝ) : ℂ)) :
    ∃ (hd : ∑ a, (x a).1 = t) (l : (prodIrr x hd).IntertwiningMap (detRep (Fin t) χ)), Function.Surjective l := by
  have hθ : ∀ a : Fin t, IsSmoothChar (χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) :=
    fun a => hχ.mul (isSmoothChar_absPow _)
  have hx' : ∀ a, x a = IrrGL.ofChar (χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) (hθ a) :=
    fun a => (hx a).trans (IrrGL.tw_ofChar χ _ hχ (isSmoothChar_absPow _))
  obtain ⟨e, hd, hΦ⟩ := exists_equiv_prodIrr hθ hx'
  obtain ⟨Φ⟩ := hΦ
  obtain ⟨l, hl⟩ := exists_surjective_multiProd (t := t) (n := Fin t) e (χ := χ) hχ
  refine ⟨hd, ?_⟩
  exact surj_of_equiv Φ l hl

theorem exists_surjective_prodIrr (t : ℕ) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) {x : Fin t → IrrGL (k := k)}
    (hx : ∀ j, x j = (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - (j : ℕ) : ℝ) : ℂ)) :
    ∃ (hd : ∑ a, (x a).1 = t) (l : (prodIrr x hd).IntertwiningMap (detRep (Fin t) χ)), Function.Surjective l :=
  exists_surjective_prodIrr_to_detRep t hχ hx

end GlobalTheory.LocGL.DetQuot

namespace GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem isL_det : StandardCosocleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (t : ℕ) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
    IsL (((List.range t).map fun j : ℕ => Segment.single ((IrrGL.ofChar χ hχ).nu
      ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ)) ((IrrGL.isCusp_ofChar χ hχ).nu _) : List (Segment k)) : Multiset (Segment k))
      (IrrRep.det (Fin t) χ hχ).ρ := by
  intro H k _ _ _ _ _ t χ hχ
  let x : Fin t → IrrGL (k := k) := fun j => (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - (j : ℕ) : ℝ) : ℂ)
  obtain ⟨hd, l, hl⟩ := DetQuot.exists_surjective_prodIrr t hχ (x := x) (fun j => rfl)
  have hcusp : ∀ j, (x j).IsCusp := fun j => (IrrGL.isCusp_ofChar χ hχ).nu _
  let Δ : Fin t → Segment k := fun j => Segment.single (x j) (hcusp j)
  have hfirst : ∀ j, (Δ j).first = x j := fun j => Segment.first_ofFirst _ _ _ _
  have hord : IsOrderedForm Δ (((List.range t).map fun j : ℕ => Segment.single ((IrrGL.ofChar χ hχ).nu
      ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ)) ((IrrGL.isCusp_ofChar χ hχ).nu _) : List (Segment k)) : Multiset (Segment k)) := by
    refine ⟨?_, ?_⟩
    · rw [Fin.univ_val_map]
      congr 1
      apply List.ext_get (by simp)
      intro i h1 h2
      simp [Δ, x]
    · rintro i j hij ⟨-, m, hm, heq⟩
      rw [hfirst, hfirst] at heq
      have key : (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - ((j : ℕ) : ℝ) : ℝ) : ℂ) =
          (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - ((i : ℕ) : ℝ) + (m : ℝ) : ℝ) : ℂ) := by
        calc (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - ((j : ℕ) : ℝ) : ℝ) : ℂ) = x j := rfl
          _ = (x i).nu (m : ℂ) := heq
          _ = ((IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - ((i : ℕ) : ℝ) : ℝ) : ℂ)).nu (m : ℂ) := rfl
          _ = _ := by
            rw [IrrGL.nu_nu]
            congr 1
            push_cast
            ring
      rw [IrrGL.nu_ofChar_inj] at key
      have hij' : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      linarith
  have hL : LFactors (((List.range t).map fun j : ℕ => Segment.single ((IrrGL.ofChar χ hχ).nu
      ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ)) ((IrrGL.isCusp_ofChar χ hχ).nu _) : List (Segment k)) : Multiset (Segment k)) x :=
    ⟨Δ, hord, fun j => (single_spec (hcusp j)).2.1⟩
  obtain ⟨π0, hπ0⟩ := H k _ t t x hd hL
  obtain ⟨Ψ⟩ := hπ0.equiv_of_surjective (IrrRep.det (Fin t) χ hχ).irr l hl
  exact ⟨t, x, hd, hL, hπ0.of_equiv Ψ.symm (Representation.Equiv.refl _)⟩

end GlobalTheory.LocGL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSqIntCoeffOfIsSquareIntegrable
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL MeasureTheory

namespace GlobalTheory.LocGL.SqIntBridge

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} {π : Representation ℂ (GL (Fin N) k) V}

theorem exists_central_scalar (hs : IsSmooth π) (hi : π.IsIrreducible) (hu : IsUnitarisable π) {z : GL (Fin N) k}
    (hz : z ∈ Subgroup.center (GL (Fin N) k)) : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, π z v = c • v := by
  obtain ⟨c, hc⟩ := schur_GL hs hi ⟨π z, fun g => by
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g]⟩
  have hc' : ∀ v, π z v = c • v := hc
  refine ⟨c, ?_, hc'⟩
  obtain ⟨B, -, hp, hB⟩ := hu
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h0 : B v v ≠ 0 := fun e => by simpa [e] using hp v hv
  have h1 := congrArg norm (hB z v v)
  rw [hc'] at h1
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, norm_mul, RingHom.id_apply, RCLike.norm_conj] at h1
  have h2 : 0 < ‖B v v‖ := norm_pos_iff.2 h0
  have h3 : ‖c‖ * ‖c‖ = 1 := mul_right_cancel₀ h2.ne' (by rw [mul_assoc, h1, one_mul])
  nlinarith [norm_nonneg c]

theorem norm_coeff_out (hs : IsSmooth π) (hi : π.IsIrreducible) (hu : IsUnitarisable π) (v : V) (l : Module.Dual ℂ V)
    (g : GL (Fin N) k) : ‖l (π (QuotientGroup.mk g : AdGL k N).out v)‖ = ‖l (π g v)‖ := by
  obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin N) k)) g
  obtain ⟨c, h1, hc⟩ := exists_central_scalar hs hi hu z.2
  rw [hz, map_mul, Module.End.mul_apply, hc, map_smul, map_smul, norm_smul, h1, one_mul]


omit [ValuativeRel k] in
theorem isLocallyConstant_orbit [IsTopologicalRing k] (hs : IsSmooth π) (v : V) :
    IsLocallyConstant fun g : GL (Fin N) k => π g v := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
  refine Filter.mem_of_superset (((hs v).preimage (continuous_const_mul g⁻¹)).mem_nhds (by simp)) fun x hx => ?_
  have hx' : π (g⁻¹ * x) v = v := hx
  show π x v = π g v
  conv_rhs => rw [← hx', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem isSqIntCoeff_of_isSquareIntegrable {δ : IrrGL (k := k)} (h : UnitaryDual.IsSquareIntegrable δ) :
    IsSqIntCoeff δ.rep := by
  obtain ⟨-, hu, ν, hν, H⟩ := h
  intro m hm μ hμ v l hl
  obtain rfl : m = _root_.borel _ := hm.measurable_eq
  letI : MeasurableSpace (AdGL k δ.1) := _root_.borel _
  have := secondCountableTopology_GL k (Fin δ.1)
  have hs := δ.2.rep.smooth
  have hF := norm_coeff_out hs δ.2.rep.irr hu v l
  have hl' : l ∈ smoothPart δ.rep.dual := hl.preimage continuous_inv
  have hf : AEStronglyMeasurable (fun q : AdGL k δ.1 => ‖l (δ.rep q.out v)‖) μ := by
    refine Continuous.aestronglyMeasurable ((QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_)
    rw [show (fun q : AdGL k δ.1 => ‖l (δ.rep q.out v)‖) ∘ QuotientGroup.mk = fun g => ‖l (δ.rep g v)‖ from funext hF]
    exact ((isLocallyConstant_orbit hs v).comp fun w => ‖l w‖).continuous
  refine ⟨fun q => ‖l (δ.rep q.out v)‖, hF, ?_⟩
  rw [memLp_iff, show ENNReal.ofReal 2 = 2 by simp, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hf,
    Measure.isMulLeftInvariant_eq_smul μ ν, lintegral_smul_measure]
  have h1 := H v l hl'
  simp only [enorm_norm, ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top h1

end GlobalTheory.LocGL.SqIntBridge

namespace GlobalTheory.Published

theorem squareIntegrableSegment_of_ess (h : EssSquareIntegrableSegments) : SquareIntegrableSegment := by
  intro k _ _ _ _ _ δ hδ
  refine (h k δ hδ.1).1 ⟨1, isSmoothChar_one, ?_⟩
  rw [IrrGL.tw_one]
  exact SqIntBridge.isSqIntCoeff_of_isSquareIntegrable hδ

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTameWeilDeligneIffWildCharpoly
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LlcTame

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

end GlobalTheory.LlcTame

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial in
attribute [local instance] _root_.GlobalTheory.LocalData.complRel _root_.GlobalTheory.LocalData.isLocalField in
private theorem eq_one_of_isSemisimple_of_charpoly_eq {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) (hs : f.IsSemisimple)
    (hc : f.charpoly = (X - 1) ^ Module.finrank ℂ V) : f = 1 := by
  have hn : IsNilpotent (f - 1) := by
    refine ⟨Module.finrank ℂ V, ?_⟩
    have := LinearMap.aeval_self_charpoly f
    rw [hc] at this
    simpa using this
  have hs' : (f - 1).IsSemisimple :=
    hs.sub_of_commute (Commute.one_right f) Module.End.isSemisimple_id
  exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hn hs')

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial in
attribute [local instance] _root_.GlobalTheory.LocalData.complRel _root_.GlobalTheory.LocalData.isLocalField in
theorem _root_.GlobalTheory.LlcTame.isTameWD_iff_charPol : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (y : _root_.GlobalTheory.WeilDeligne.WD h), _root_.GlobalTheory.LocLanglands.IsTameWD y ↔
    ∀ σ : _root_.GlobalTheory.WeilDeligne.Weil h, _root_.Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) →
      y.charPol σ = (X - 1) ^ y.lpDim := by
  intro E Ω _ _ _ _ _ A w h y
  unfold _root_.GlobalTheory.LocLanglands.IsTameWD
  constructor
  · rintro ⟨n, a, rfl, ha⟩ σ hσ
    have hd : (_root_.GlobalTheory.WeilDeligne.WD.mk a).lpDim =
        Module.finrank ℂ (Fin n → ℂ) := _root_.GlobalTheory.WeilDeligne.WD.lpDim_mk a
    refine (_root_.GlobalTheory.WeilDeligne.WD.charPol_mk a σ).trans ?_
    rw [hd, ha σ hσ, LinearMap.charpoly_one]
  · intro H
    obtain ⟨n, a, rfl⟩ := y.exists_rep
    refine ⟨n, a, rfl, fun σ hσ => ?_⟩
    have hc := H σ hσ
    have hd : (_root_.GlobalTheory.WeilDeligne.WD.mk a).lpDim =
        Module.finrank ℂ (Fin n → ℂ) := _root_.GlobalTheory.WeilDeligne.WD.lpDim_mk a
    rw [hd] at hc
    have hc' := (_root_.GlobalTheory.WeilDeligne.WD.charPol_mk a σ).symm.trans hc
    exact eq_one_of_isSemisimple_of_charpoly_eq _ (a.semisimple σ) hc'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsClassificationSupercuspidalSupportMultiStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlandsClassification_supercuspidalSupport_multisegment : ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL (k := k)), IsL 𝔪 x.rep → HasSupport x.rep (msupp 𝔪) := by
  first | exact @GlobalTheory.LocGL.hasSupport_msupp_of_isL | exact GlobalTheory.LocGL.hasSupport_msupp_of_isL | (intros; apply GlobalTheory.LocGL.hasSupport_msupp_of_isL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterTeichmullerLabelOfGoodTypesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacter_teichmullerLabel_of_goodTypes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R → ∀ (k : Fin 2) (v : D.nd.PlG k) (i : Fin D.R.m) (PP : Pl D.host.E),
    R.C.P.Div k PP → ∀ (iso : ZMod (D.host.g k) ≃+* kP PP) (ε : ℤ), (ε = 1 ∨ ε = -1) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ L : GlobalTheory.GLq.LabelDatum (D.host.g k), (∀ f, D.ntypes.eSer k f = GlobalTheory.GLq.eSerC L D.R.r f) ∧
      ∃ c : ZMod (D.host.g k),
        GlobalTheory.GLp.IsCharLab L ((zpowGroupHom ε).comp ((R.chi ((i : ℕ) + 1) PP).comp
          (Units.map (iso : ZMod (D.host.g k) →* kP PP)))) c ∧
        (c = ((D.nd.chiT k v i : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)) ∨
          c = (((D.nd.chiT k v i)⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) := by
  first | exact @GlobalTheory.CharLabTransport.charLab_of_goodTypes | exact GlobalTheory.CharLabTransport.charLab_of_goodTypes | (intros; apply GlobalTheory.CharLabTransport.charLab_of_goodTypes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinInertiaIsUnitAt
section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

noncomputable section

namespace GlobalTheory.ArtinInertia

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem isUnitAt_artin_ine : ∀ {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A w')
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha : IsLocalArtin h' a') (t : Ine (F := E') A),
    IsUnitAt w' (a' (ineIncl h' t)) := by
  intro E' Ω _ _ _ _ _ A w' h' a' ha t
  have h1 := ha.ord_eq (ineIncl h' t)
  rw [deg_ineIncl, neg_zero, SphCompletion.ord_completion, neg_eq_zero] at h1
  have h0 : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') ≠ 0 := by simp
  show Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') = 1
  rw [← WithZero.exp_log h0, h1, WithZero.exp_zero]

end GlobalTheory.ArtinInertia
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalOperatorScalarOnSphericalEigenspaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localOperator_scalar_on_sphericalEigenspace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i t, BadSupp R i t → LevFix R i t → LocSmall R i t → LevProd R i → TransLaws R i → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g) → ∀ c, ∀ y ∈ part R i ∅ c, ∀ v, ∃ z : ℂ, Eu.Zop R i t μ 𝓕 v y = z • y := by
  first | exact @GlobalTheory.RawLift.Eig.zop_eigen | exact GlobalTheory.RawLift.Eig.zop_eigen | (intros; apply GlobalTheory.RawLift.Eig.zop_eigen <;> assumption)
end

