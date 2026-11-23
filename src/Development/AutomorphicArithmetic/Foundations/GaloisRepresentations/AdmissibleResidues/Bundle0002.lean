module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.WeightsConj
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0158
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopStd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0299
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharParallelWeight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0692
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.LocDefs
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open _root_.GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

structure AwV (x y : WD h) : Prop where
  pol : ∀ g : ↥(Weil h), x.charPol g = y.charPol g
  n0 : y.mono0 → x = y

variable {l : ℕ} [Fact l.Prime] {n : ℕ}

def WDN (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (y : WD h) : Prop := ∃ x : WD h, IsWDOf ι r x ∧ AwV x y

variable {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin n) (Qbar l)} {y : WD h}

theorem WDN.of_aw (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (hc : Continuous r) (k : AwV (wdOf h hl ι r) y) : WDN ι r y :=
  ⟨_, isWDOf_wdOf (h := h) hl ι (Units.continuous_val.comp hc), k⟩
end Local

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

end UpperTheory.GalN.V
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RatioWOfHasSat
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.HeckeGal GlobalTheory.GalOfCusp GlobalTheory.LocLanglands GlobalTheory.LocGL UpperTheory.V UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

private theorem norm_inf {F : Type} [Field F] [NumberField F] (χ : HChar F) (k : Fˣ)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), ‖((χ.val v : ℂˣ) : ℂ)‖ = 1 ∨ ordF v k = 0) : ‖((χ.inf k : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨N, hN, hu⟩ := GlobalTheory.Corev.UnrPow.exists_pow_unrAt F χ
  have e := (χ ^ N).val_principal ∅ (fun v _ => hu v) k
  have h1 : ‖((∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : v ∉ (∅ : Finset _)), (χ ^ N).val v ^ ordF v k : ℂˣ) : ℂ)‖ = 1 := by
    refine finprod_induction (fun z : ℂˣ => ‖(z : ℂ)‖ = 1) (by simp) (fun x y hx hy => by simp [hx, hy]) fun v => ?_
    have e2 : (χ ^ N).val v = χ.val v ^ N := rfl
    rcases h v with h | h
    · simp [e2, h]
    · simp [h]
  have e2 : (χ ^ N).inf k = χ.inf k ^ N := rfl
  rw [e, Finset.prod_empty, mul_one, e2] at h1
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, norm_inv, norm_pow, inv_eq_one] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h1

theorem type_zero_window {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (χ : HChar F) (a : (F →+* ℂ) → ℤ)
    (ha : IsAlgPos χ a) (v : HeightOneSpectrum (𝓞 F)) (h1 : ‖((χ.val v : ℂˣ) : ℂ)‖ < (normV v : ℝ))
    (h2 : 1 < (normV v : ℝ) * ‖((χ.val v : ℂˣ) : ℂ)‖) : a = 0 := by
  obtain ⟨s, hs⟩ := GlobalTheory.HeckeNormPow.norm_val_eq_rpow F χ
  obtain ⟨φ₀⟩ : Nonempty (F →+* ℂ) := inferInstance
  have hpar : ∀ φ, a φ = a φ₀ := fun φ => UpperTheory.heckeChar_parallel_weight _ _ _ ha φ φ₀
  obtain ⟨-, n2, n3⟩ := Model.absPow_isAbsPow F s
  have hq : ∀ u : HeightOneSpectrum (𝓞 F), (1 : ℝ) < (Ideal.absNorm u.asIdeal : ℝ) := fun u => by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm u
  have k := norm_inf (χ * Model.absPow F s) (Units.mk0 (2 : F) two_ne_zero) fun u => Or.inl (by
    rw [HChar.val_mul, Units.val_mul, norm_mul, hs, n2, Complex.norm_natCast_cpow_of_pos (by exact_mod_cast (zero_lt_one.trans (hq u))),
      ← Real.rpow_add (zero_lt_one.trans (hq u))]
    simp)
  have e0 : (χ * Model.absPow F s).inf (Units.mk0 (2 : F) two_ne_zero) =
    χ.inf (Units.mk0 (2 : F) two_ne_zero) * (Model.absPow F s).inf (Units.mk0 (2 : F) two_ne_zero) := rfl
  rw [e0, Units.val_mul, ha _ (fun φ => by simp [map_ofNat]), n3, ← Finset.prod_mul_distrib, norm_prod] at k
  have e1 : ∀ φ : F →+* ℂ, ‖φ ((Units.mk0 (2 : F) two_ne_zero : Fˣ) : F) ^ a φ *
      ((‖φ ((Units.mk0 (2 : F) two_ne_zero : Fˣ) : F)‖ : ℝ) : ℂ) ^ (s : ℂ)‖ = (2 : ℝ) ^ ((a φ₀ : ℝ) + s) := fun φ => by
    rw [Units.val_mk0, map_ofNat, norm_mul, norm_zpow, hpar φ, Complex.norm_cpow_eq_rpow_re_of_pos (by simp),
      Real.rpow_add two_pos, Real.rpow_intCast]
    simp
  rw [Finset.prod_congr rfl fun φ _ => e1 φ, Finset.prod_const,
    pow_eq_one_iff_of_nonneg (by positivity) (Finset.card_pos.2 ⟨φ₀, Finset.mem_univ _⟩).ne'] at k
  have e2 : (a φ₀ : ℝ) + s = 0 := by
    have := congrArg Real.log k
    rw [Real.log_rpow two_pos, Real.log_one] at this
    exact (mul_eq_zero.1 this).resolve_right (Real.log_pos one_lt_two).ne'
  have hv : (normV v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hs, hv] at h1 h2
  have a1 : s < 1 := (Real.rpow_lt_rpow_left_iff (hq v)).1 (by rwa [Real.rpow_one])
  have a2 : 0 < 1 + s := (Real.rpow_lt_rpow_left_iff (hq v)).1 (by
    rwa [Real.rpow_zero, Real.rpow_add (zero_lt_one.trans (hq v)), Real.rpow_one])
  have b1 : (-1 : ℤ) < a φ₀ := by exact_mod_cast (show (-1 : ℝ) < a φ₀ by linarith)
  have b2 : a φ₀ < (1 : ℤ) := by exact_mod_cast (show (a φ₀ : ℝ) < 1 by linarith)
  funext φ
  rw [hpar φ, Pi.zero_apply]
  omega

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

private theorem inv_mem_eig {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w} (x : WD h) (φ : Weil h) {b : ℂ}
    (hb : (x.charPol φ⁻¹).IsRoot b) : b ≠ 0 ∧ b⁻¹ ∈ x.eig φ := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  rw [WD.charPol_mk, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hb
  obtain ⟨v, hv⟩ := hb.exists_hasEigenvector
  have h1 : v = b • a.ρ φ v := by
    rw [← map_smul, ← hv.apply_eq_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hv.2 (by simpa using h1)
  refine ⟨hb0, ?_⟩
  rw [WD.eig_mk, mem_roots (LinearMap.charpoly_monic _).ne_zero, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨Module.End.mem_eigenspace_iff.2 ?_, hv.2⟩
  conv_rhs => rw [h1]
  rw [smul_smul, inv_mul_cancel₀ hb0, one_smul]

theorem ratio_roots {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)} (hr : Continuous r)
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w} (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    (H : RatioW (wdOf h hl ι r)) {b c : ℂ}
    (hb : ((r ((frob h : Weil h) : G F Ω)⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom).IsRoot b)
    (hc : ((r ((frob h : Weil h) : G F Ω)⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom).IsRoot c) :
    ‖b‖ < (normV w : ℝ) * ‖c‖ := by
  obtain ⟨t, ht', φ, hφ, N, a, hN, -, -⟩ := isWDOf_wdOf (h := h) hl ι (Units.continuous_val.comp hr)
  have e := hN.charPol_wdOf (h := h) hl ht' ι (frob h)⁻¹
  obtain ⟨b0, mb⟩ := inv_mem_eig (wdOf h hl ι r) (frob h) (b := b) (by rw [e]; exact hb)
  obtain ⟨c0, mc⟩ := inv_mem_eig (wdOf h hl ι r) (frob h) (b := c) (by rw [e]; exact hc)
  have k := H (frob h) (deg_frob) _ mc _ mb
  rw [norm_inv, norm_inv] at k
  have pb := norm_pos_iff.2 b0
  have pc := norm_pos_iff.2 c0
  rw [← div_eq_mul_inv, inv_eq_one_div, div_lt_div_iff₀ pc pb, one_mul] at k
  exact k

theorem ratioW_of_hasSat [IsTotallyReal F] (P : Hypotheses₂) {n : ℕ} {π : TR.CuspSub F n} {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    {wt : ℤ} {HT : (F →+* Qbar l) → Multiset ℤ} (H : IsGalRU π ι r wt HT) {w : HeightOneSpectrum (𝓞 F)}
    (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {A : ValuationSubring Ω} (h : IsPlaceOver A w) {B : Multiset ℂˣ} (hB : π.HasSat w B) :
    RatioW (wdOf h hl ι r) := by
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P F n π w
  obtain ⟨rc, hrc⟩ := P.exists_rec h
  exact H.ratio w hl A h rc hrc σ hσ
    (WD.unr_mono0 _ (unr_algNorm hrc σ B (((satLoc P F n w σ).2 _ π.finPart (hiso σ hσ) B).1 hB)))

theorem isWDOf_satR [IsTotallyReal F] {n : ℕ} {π : TR.CuspSub F n} {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    {wt : ℤ} {HT : (F →+* Qbar l) → Multiset ℤ} (H : IsGalRU π ι r wt HT) {w : HeightOneSpectrum (𝓞 F)}
    (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {rc : IrrGL (k := w.adicCompletion F) → WD h} (hrc : IsRec h rc) {σ : SmIrr (GL (Fin n) (w.adicCompletion F))}
    (hσ : π.IsLocComp w σ) {S : Multiset ℂˣ} (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) : IsWDOf ι r (rc (algNorm σ)) := by
  rw [← (H.away w hl A h rc hrc σ hσ).eq_unr (unr_algNorm hrc σ S hS)]
  exact isWDOf_wdOf (h := h) hl ι (Units.continuous_val.comp H.cont)

end UpperTheory.GalN.V
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealOld
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open _root_.GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem eig_lpTw (x : WD h) (s : ℝ) {φ : ↥(Weil h)} (hφ : deg φ = 1) {α : ℂ} (hα : α ∈ x.eig φ) :
    α * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ) ∈ (x.lpTw s).eig φ := by
  rw [GlobalTheory.RowTie.EigTwist.eig_lpTw x hφ s]
  exact Multiset.mem_map_of_mem _ hα

theorem RatioW.of_tempered {x : WD h} {s : ℝ} (hm : x.mono0) (ht : (x.lpTw s).tempered) : RatioW x := by
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast GlobalTheory.WeilDeligne.one_lt_normV w
  have key : ∀ y : WD h, y.mono0 → y.tempered → ∀ φ : ↥(Weil h), deg φ = 1 → ∀ α ∈ y.eig φ, ‖α‖ = 1 := by
    intro y hm ht φ hφ α hα
    induction y using WD.ind with
    | hP n b =>
      rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at hm
      rw [WD.tempered_mk] at ht
      rw [WD.eig_mk, mem_roots (LinearMap.charpoly_monic _).ne_zero, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hα
      have top := ht.norm_eq_one hm hφ
      by_contra hne
      have d := Module.End.eigenspaces_iSupIndep (b.ρ φ) α
      have le : (⊤ : Submodule ℂ (Fin n → ℂ)) ≤ ⨆ (β) (_ : β ≠ α), Module.End.eigenspace (b.ρ φ) β := by
        rw [← top]
        exact iSup₂_le fun β hβ => le_iSup₂_of_le β (fun e => hne (e ▸ hβ)) le_rfl
      exact hα (disjoint_top.1 (d.mono_right le))
  intro φ hφ α hα β hβ
  have hm' := (WD.monomial_twist_iff x s).2 hm
  have e1 := key _ hm' ht φ hφ _ (eig_lpTw x s hφ hα)
  have e2 := key _ hm' ht φ hφ _ (eig_lpTw x s hφ hβ)
  rw [norm_mul] at e1 e2
  have hc : ‖((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)‖ ≠ 0 := fun e => by rw [e, mul_zero] at e1; exact zero_ne_one e1
  have e3 : ‖α‖ = ‖β‖ := mul_right_cancel₀ hc (e1.trans e2.symm)
  have hb : 0 < ‖β‖ := lt_of_le_of_ne (norm_nonneg _) fun e => by rw [← e, zero_mul] at e2; exact zero_ne_one e2
  rw [e3]
  exact lt_mul_of_one_lt_left hb hq

variable {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'} {j : E →+* E'} {i : w.adicCompletion E ≃+* w'.adicCompletion E'}

theorem pol_of_rel {y : WD h} {y' : WD h'} (hy : WDRel φ y y') {σ : ↥(Weil h)} {σ' : ↥(Weil h')} (hs : WeilRel φ σ σ') :
    y.charPol σ = y'.charPol σ' := by
  obtain ⟨n, b, b', rfl, rfl, -, hb⟩ := hy
  rw [WD.charPol_mk, WD.charPol_mk, hb σ σ' hs]

theorem RatioW.descend (P : PlaceIso A w A' w' φ j i) {x : WD h} {x' : WD h'} (hx : WDRel φ x x') (k : RatioW x') :
    RatioW x := by
  obtain ⟨c, hc, hdeg, hq, -⟩ := _root_.GlobalTheory.WeilTransport.weil_equiv E Ω A w h E' Ω' A' w' h' φ j i P
  intro g hg α hα β hβ
  rw [WD.eig, pol_of_rel hx ((hc g (c g)).2 rfl)] at hα hβ
  rw [← hq]
  exact k (c g) (by rw [hdeg, hg]) α hα β hβ

end Local

section Real
variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ} {π : TR.CuspSub F a} {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
  {HT : (F →+* Qbar l) → Multiset ℤ}

theorem IsGalRU.of_old (H : IsGalRepOfR π ι r wt HT) : IsGalRU π ι r wt HT := by
  refine {
    cont := H.cont
    ss := H.ss
    away := ?_
    ratio := ?_
    weights := H.weights
    weights_sym := H.weights_sym
    above := ?_ }
  · intro w hl A h rc hrc σ hσ
    exact .of_eq ((H.away w hl A h rc hrc σ hσ).wdOf_eq hl)
  · intro w hl A h rc hrc σ hσ hm
    obtain ⟨x, hx, ht⟩ := H.pure w hl A h
    rw [← hx.wdOf_eq hl] at ht
    exact .of_tempered (by rwa [(H.away w hl A h rc hrc σ hσ).wdOf_eq hl]) ht
  · intro P AI T w A h O _ _ _ Bw hj
    have k := H.above P AI T w A h O Bw hj
    exact ⟨k.1, k.2.1, fun σ hσ hi _ rc hrc => by rw [(k.2.2.1 σ hσ hi).2 rc hrc]; exact ⟨fun _ => rfl, id⟩, k.2.2.2⟩

end Real

theorem exRN (h : ExR) : ExRN := fun F Ω _ _ _ _ _ _ l _ ι n _ hn π χ h1 h2 =>
  let ⟨r, wt, HT, H, a, b⟩ := h F Ω l ι n hn π χ h1 h2
  ⟨r, wt, HT, .of_old H, a, fun r' x y => .of_old (b r' x y)⟩

end UpperTheory.GalN.V
end
end

