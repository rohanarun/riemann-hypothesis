module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0510
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0503
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0443
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnKeySectionComplexValue
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)}
  {M : ModelsOf F r}

theorem exists_isThetaPt_of_adapted {k : Fin F.n} (T : ThetaData e F M k) (x : Fin T.m → ℂ)
    (hx : x ∈ T.co ⁻¹' (M.X k).dom) (y : FrPt Xo c (CAt σ)) (h₁ : y.x = F.u k (T.Pf (T.co x)))
    (h₂ : ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k (T.Pf (T.co x)) z).left)
      (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i)) :
    ∃ a : ℂ, a ≠ 0 ∧ IsThetaPt T x a y := by
  obtain ⟨hu, hsym, hpos, -⟩ := T.norm x hx
  obtain ⟨-, w, hw⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).1 _ hsym hpos
  obtain ⟨t, ht⟩ := T.fr_sec x hx
  obtain ⟨a, ha, hv⟩ := GlobalTheory.GenFactor.exists_factor GlobalTheory.abelianSchemeLaws_all.2.secTwist y.x _ h₁ y.s y.gen
    (F.ex k (T.Pf (T.co x))) (fun z => thetaChar (T.ta x) T.c₁ T.c₂ (T.h x *ᵥ z)) (fun j z => T.fr j (x, z))
    ⟨(T.h x)⁻¹ *ᵥ w, by
      show thetaChar _ _ _ (T.h x *ᵥ ((T.h x)⁻¹ *ᵥ w)) ≠ 0
      rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]⟩
    (fun j z hz => T.fr_ne j x z hx hz) t ht
  exact ⟨a, ha, h₁, h₂, hv⟩

theorem rootVal_of_isThetaPt {k : Fin F.n} (T : ThetaData e F M k) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ))
    (hun : IsNormUn T (un k)) (x : Fin T.m → ℂ) (hx : x ∈ T.co ⁻¹' (M.X k).dom) (a : ℂ) (ha : a ≠ 0)
    (y : FrPt Xo c (CAt σ)) (hy : IsThetaPt T x a y) :
    RootVal (unfOf e F M un) y
      ((normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) * (T.h x).det / a ^ 2) := by
  obtain ⟨κ, hκ, hθ⟩ := hun ⟨T.co x, hx⟩
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hκ hθ
  have hC : (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : Formalism.L2.PjFree.relab c σ (e j).1 (M.X k).ξ0 ≠ 0 := (map_ne_zero _).2 (M.X k).ξ0_ne
    positivity
  have k1 : κ ≠ 0 := fun h0 => mul_ne_zero hC (T.norm _ hx).1.ne_zero (by rw [← hκ, h0]; simp)
  let t₀ : ℂˣ := Units.mk0 (a / κ) (div_ne_zero ha k1)
  have hb := GlobalTheory.frBor_of_isThetaPt GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c σ g e F r M k T x hx κ
    (show (CAt σ)ˣ from t₀) (un k ⟨T.co x, hx⟩) y hθ (by
      have : a / κ * κ = a := div_mul_cancel₀ a k1
      show IsThetaPt T x (a / κ * κ) y
      rwa [this])
  refine ⟨k, ⟨T.co x, hx⟩, _, hb, ?_⟩
  have hk : kch (Dw := Dw) (S := ℂ) (fun i => Option.elim i t₀ (fun _ => 1)) = (t₀ ^ 2)⁻¹ := by
    rw [kch_eq]
    simp
  refine Eq.trans ?_ (congrArg Units.val hk).symm
  rw [← hκ, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_mk0]
  field_simp

end

theorem continuousOn_rootVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (T : ∀ k, ThetaData e F M k) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)), Formalism.L2.PjFree.GoodEmb c σ → ModelBase M → NegXi M → (∀ k, IsNormUn (T k) (un k)) → FramesOK e F M un → ∀ (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (ρ : (Fin m → ℂ) → ℂ), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → (∀ b ∈ B, RootVal (unfOf e F M un) (y b) (ρ b)) → ContinuousOn ρ B := by
  intro E _ _ _ H Dw l Xo c σ g e F r M T un hσ hM hξ hun hok A _ _ yA m B φ y ρ hB hφ hy hρ b₀ hb₀
  obtain ⟨B', k, P, hB', hb', hsub, hP, hd⟩ :=
    GlobalTheory.AdaptedPeriods.exists_holPeriods_adapted E H Dw l Xo c σ g e F A yA m B φ y hB hφ hy b₀ hb₀
  obtain ⟨x, hx, hxc⟩ :=
    GlobalTheory.FrameLiftAt.exists_frame_lift E H Dw l Xo c σ g e F r M k (T k) hσ hM hξ m B' P hB' hP b₀ hb'
  have h₁ : ∀ b ∈ B', ∃ a : ℂ, a ≠ 0 ∧ IsThetaPt (T k) (x b) a (y b) := fun b hb =>
    exists_isThetaPt_of_adapted (T k) (x b) (hx b hb).1 (y b) (by rw [(hx b hb).2]; exact (hd b hb).1)
      (by rw [(hx b hb).2]; exact (hd b hb).2)
  choose! a ha hθ using h₁
  have hac : ContinuousAt a b₀ :=
    GlobalTheory.ThetaScalar.continuousAt_scalar E H Dw l Xo c σ g e F r M k (T k) A yA m B' φ y P x a hB'
      (fun t => (hφ t).mono hsub) (fun b hb => hy b (hsub hb)) hP
      (fun b hb => ⟨(hx b hb).1, (hx b hb).2, hθ b hb⟩) b₀ hb' hxc
  have hO : IsOpen ((T k).co ⁻¹' (M.X k).dom) := (FourierCoefficientDomain.isOpen_dom _).preimage (T k).co.continuous
  have hh : ContinuousAt (T k).h (x b₀) := continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
    ((T k).hol i j).1.continuousOn.continuousAt (hO.mem_nhds (hx b₀ hb').1)
  have hdet : ContinuousAt (fun b => ((T k).h (x b)).det) b₀ :=
    (continuous_id.matrix_det.continuousAt).comp (ContinuousAt.comp hh hxc)
  have hq : ContinuousAt (fun b => (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) *
      ((T k).h (x b)).det / a b ^ 2) b₀ :=
    (continuousAt_const.mul hdet).div (hac.pow 2) (pow_ne_zero 2 (ha b₀ hb'))
  refine (hq.congr ?_).continuousWithinAt
  filter_upwards [hB'.mem_nhds hb'] with b hb
  exact rootVal_unique E H Dw l Xo c σ g e F r M un hσ hM hξ hok (y b) _ _
    (rootVal_of_isThetaPt (T k) un (hun k) (x b) (hx b hb).1 (a b) (ha b hb) (y b) (hθ b hb)) (hρ b (hsub hb))

end GlobalTheory.KeyFourth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOnRdUFlat
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TrueCx.FlatConst

section Hol

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT
open GlobalTheory.Reg GlobalTheory.KeyFourth GlobalTheory.AllWt GlobalTheory.FlatLine

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_generic_units (hpq : 1 ≤ Dw.p + Dw.q) (h : GenFrEx Xo c) :
    ∃ v : ∀ Z : Comp Xo c, (Om Z)ˣ, ∀ C : FChart h,
      ∃ u : (C.R)ˣ, ((u : C.R) : Om C.Z) = ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) := by
  obtain ⟨κ, h₁, h₂, -, -, -, h₃, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm
  have hc : ∀ Z : Comp Xo c, CharZero (Om Z) := fun Z =>
    charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
  choose Ψ hΨ using fun Z : Comp Xo c => exists_tied E H Dw l Xo c _ e (Om Z) (genFr h Z) hpq
  refine ⟨fun Z => κ (Om Z) (Ψ Z).key, fun C => ?_⟩
  letI : Algebra c.F C.R := Subalgebra.algebra C.R
  haveI := C.sm
  haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
  haveI : IsNoetherianRing C.R := Algebra.FiniteType.isNoetherianRing c.F C.R
  haveI : CharZero C.R := charZero_of_injective_algebraMap (algebraMap c.F C.R).injective
  obtain ⟨Φ, hΦ⟩ := exists_tied E H Dw l Xo c _ e C.R C.y hpq
  obtain ⟨Φ', hΦ'⟩ := exists_tied E H Dw l Xo c _ e (Om C.Z) C.yg hpq
  obtain ⟨u, hu⟩ := h₃ C.R Φ.key
  refine ⟨u, ?_⟩
  rw [← rule_frBor κ h₁ h₂ E H Dw l Xo c _ e (Om C.Z) C.t _ _ (Ψ C.Z) Φ' C.bor (hΨ _) hΦ']
  exact (hu (Om C.Z) _ _ (tied_keyPB E H Dw l Xo c _ e _ _ C.R.val C.y C.yg Φ Φ' C.gen hΦ hΦ')).symm

theorem exists_key_four (hpq : 1 ≤ Dw.p + Dw.q) (σ : c.F →+* ℂ) :
    ∃ ρ ∈ secZ Xo c (fun i => keyEx Dw i * 4), ∀ y : FrPt Xo c (CAt σ), toC (evR Xo c ρ y) ≠ 0 := by
  obtain ⟨-, -, h, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨v, hv⟩ := exists_generic_units hpq h
  have hk : ∀ C : FChart h, (∏ i, C.t i ^ (keyEx Dw i * 4) : (Om C.Z)ˣ) = kch C.t ^ 4 := fun C => by
    rw [kch, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [zpow_mul]; rfl
  obtain ⟨ρ, hρ, hρv⟩ := GlobalTheory.SecGlueInt.exists_secZ_of_regular E H Dw l Xo c h (fun i => keyEx Dw i * 4)
    (fun Z => v Z) fun C => by
      obtain ⟨u, hu⟩ := hv C
      rw [hk, ← Units.val_mul, ← hu]
      exact u.1.2
  refine ⟨ρ, hρ, fun y => ?_⟩
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨C, ψ, z, t, hz, hb⟩ := hA h (CAt σ) y
  obtain ⟨u, hu⟩ := hv C
  obtain ⟨b, hb₁, hb₂⟩ := GlobalTheory.DegCmp.fChart_exists_val C hρ
  have hbu : b = u := Subtype.ext (by
    rw [hb₁, hu, hk, GlobalTheory.CompHt.genVal_apply h, hρv, Units.val_mul])
  show evR Xo c ρ y ≠ 0
  rw [GlobalTheory.FlagTan.evR_frBor hρ hb, hb₂ _ ψ z hz, hbu]
  exact mul_ne_zero (Units.ne_zero _) (u.isUnit.map ψ).ne_zero

theorem exists_sec_four (hpq : 1 ≤ Dw.p + Dw.q) {σ : c.F →+* ℂ} (y : FrPt Xo c (CAt σ)) :
    ∃ n, Even n ∧ ∃ g ∈ sec Xo c (fun _ => 4) n, toC (evR Xo c g y) ≠ 0 := by
  obtain ⟨ρ, hρ, h0⟩ := exists_key_four (Xo := Xo) hpq σ
  obtain ⟨n, hn, ⟨m, rfl⟩, η, hη, hη0⟩ := exists_even_sec_evR_ne_zero E H Dw l Xo c σ y
  rw [← secZ_nat] at hη
  have h2 := mul_mem_secZ hη hη
  have h3 := mul_mem_secZ (mul_mem_secZ h2 h2) hρ
  refine ⟨2 * (4 * m - 4), even_two_mul _, η * η * (η * η) * ρ, ?_, ?_⟩
  · rw [← secZ_nat]
    convert h3 using 2
    funext i
    cases i with
    | none => simp only [ex, keyEx, Pi.add_apply]; omega
    | some i => simp [ex, keyEx]
  · have h1 : toC (evR Xo c η y) ≠ 0 := hη0
    simp only [CompSplitPfB.cspB_evR_mul]
    exact mul_ne_zero (M₀ := ℂ) (mul_ne_zero (M₀ := ℂ) (mul_ne_zero (M₀ := ℂ) h1 h1) (mul_ne_zero (M₀ := ℂ) h1 h1)) (h0 y)


variable {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r}

end Hol

section Main

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

end Main

end GlobalTheory.TrueCx.FlatConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbRtSq
section
open NumberField

namespace GlobalTheory.ConjugateMultiplicity

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by

  have hsq := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have h0 : H.rt0.re = 0 := by
    by_contra hne
    have hprod : H.rt0.re * H.rt0.im = 0 := by linarith [mul_comm H.rt0.re H.rt0.im]
    have him0 : H.rt0.im = 0 := (mul_eq_zero.1 hprod).resolve_left hne
    rw [him0] at hre
    nlinarith [sq_nonneg H.rt0.re]
  apply Complex.ext <;> simp [h0]

theorem emb_rt_sq (H : Host E) (τ : E →+* ℂ) : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
  have h : (H.rt : E) ^ 2 = -(H.d : E) := by
    have h' := congrArg ((↑) : 𝓞 E → E) H.rt_sq
    push_cast at h'
    exact h'
  rw [← map_pow, h, map_neg, map_natCast, H.sqrt_neg_disc_sq]

private theorem mult_conjEmb_eq_ite {H : Host E} (D : Datum H) (τ : E →+* ℂ) :
    Datum.mult D (conjEmb τ) = if τ (H.rt : E) = H.rt0 then Datum.q D else Datum.p D := by

  have hne : H.rt0 ≠ -H.rt0 := by
    intro h
    have h0 : H.rt0 = 0 := by linear_combination h / 2
    have hsq := H.sqrt_neg_disc_sq
    rw [h0] at hsq
    have hd : (H.d : ℂ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
    exact hd (by linear_combination hsq)
  have hc : conjEmb τ (H.rt : E) = starRingEnd ℂ (τ (H.rt : E)) := rfl
  unfold Datum.mult

  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (emb_rt_sq H τ) with h | h
  · have h2 : ¬ conjEmb τ (H.rt : E) = H.rt0 := by
      rw [hc, h, rt0_conj_neg_ne_zero]
      exact fun e => hne e.symm
    rw [if_pos h, if_neg h2]
  · have h2 : conjEmb τ (H.rt : E) = H.rt0 := by
      rw [hc, h, map_neg, rt0_conj_neg_ne_zero, neg_neg]
    have h3 : ¬ τ (H.rt : E) = H.rt0 := by
      rw [h]
      exact fun e => hne e.symm
    rw [if_pos h2, if_neg h3]

end GlobalTheory.ConjugateMultiplicity

theorem GlobalTheory.ConjugateMultiplicity.target : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (D : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (τ : E →+* ℂ), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult D (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ) + ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult D τ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.p D + ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.q D := by
  intro E _ _ _ H D τ
  rw [GlobalTheory.ConjugateMultiplicity.mult_conjEmb_eq_ite]
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult
  split_ifs <;> omega
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlag
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.Spread

open GlobalTheory.LieLocFrame (res res_sum res_res)
open GlobalTheory.LieMet (tan_ext)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)
open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_affine_germs {X : Scheme.{0}} (y : X) {W : X.Opens} (hW : y ∈ W) {κ : Type} [Finite κ]
    (a : κ → X.presheaf.stalk y) : ∃ (U : X.Opens) (_ : IsAffineOpen U) (hy : y ∈ U) (s : κ → Γ(X, U)), U ≤ W ∧
      ∀ i, X.presheaf.germ U y hy (s i) = a i := by
  choose V hV s hs using fun i => X.presheaf.exists_germ_eq (a i)
  have ho : IsOpen ((W : Set X) ∩ ⋂ i, (V i : Set X)) :=
    W.isOpen.inter (isOpen_iInter_of_finite fun i => (V i).isOpen)
  obtain ⟨U, hU, hy, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⟨_, ho⟩) (x := y)
    ⟨hW, Set.mem_iInter.2 hV⟩
  have hl : ∀ i, U ≤ V i := fun i z hz => Set.mem_iInter.1 (hle hz).2 i
  exact ⟨U, hU, hy, fun i => X.presheaf.map (homOfLE (hl i)).op (s i), fun z hz => (hle hz).1,
    fun i => (X.presheaf.germ_res_apply (homOfLE (hl i)) y hy (s i)).trans (hs i)⟩

theorem spMap_germ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {y : X} (hy : y ∈ U) :
    spMap (X.presheaf.germ U y hy).hom ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec) =
      (show Sp (X.presheaf.stalk y) ⟶ X from X.fromSpecStalk y) :=
  hU.fromSpecStalk_eq_fromSpecStalk hy

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

theorem exists_bc {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* S) {φ' : c.F →+* S}
    {x' : Sp S ⟶ Z.X} (hφ : ψ.comp φ = φ') (hx : spMap ψ ≫ x = x') :
    ∃ g : EigFrame Z φ' x', ∀ τ i, g.vec τ i = res ψ hx (f.vec τ i) := by
  subst hφ hx
  have h : ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x),
      ∀ τ i, g.v τ i = spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ i :=
    GlobalTheory.ShFam.EigFrame.exists_baseChange E H Dw l Xo c O β Z R S φ x f ψ
  obtain ⟨g, hg⟩ := h
  exact ⟨g, fun τ i => tan_ext (hg τ i)⟩

theorem exists_coord {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f g : EigFrame Z φ x) (τ : E →+* ℂ) :
    ∃ A B : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R, B * A = 1 ∧ ∀ i, g.vec τ i = ∑ k, A i k • f.vec τ k := by
  choose A hA _ using fun i => f.existsUnique_sum τ (g.vec τ i) (g.act_vec τ i)
  choose B hB _ using fun i => g.existsUnique_sum τ (f.vec τ i) (f.act_vec τ i)
  refine ⟨Matrix.of A, Matrix.of B, Matrix.ext fun i => congrFun ?_, hA⟩
  refine (f.existsUnique_sum τ (f.vec τ i) (f.act_vec τ i)).unique ?_ ?_
  · refine (hB i).trans ?_
    simp only [show ∀ i, g.vec τ i = ∑ k, A i k • f.vec τ k from hA, Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul]
    exact Finset.sum_comm
  · simp only [Matrix.one_apply, ite_smul, one_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      zero_smul R]

theorem exists_change {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x)
    (A B : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) (h : ∀ τ, B τ * A τ = 1) :
    ∃ g : EigFrame Z φ x, ∀ τ i, g.vec τ i = ∑ k, A τ i k • f.vec τ k := by
  have hs : ∀ τ (a : Fin (Dw.mult τ) → R), ∑ i, a i • ∑ k, A τ i k • f.vec τ k =
      ∑ k, (Matrix.vecMul a (A τ)) k • f.vec τ k := fun τ a => by
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  refine ⟨EigFrame.ofVec (fun τ i => ∑ k, A τ i k • f.vec τ k) (fun τ i a => ?_) fun τ w hw => ?_,
    fun τ i => tan_ext rfl⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, f.act_vec, Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  · obtain ⟨a, ha, hu⟩ := f.existsUnique_sum τ w hw
    refine ⟨Matrix.vecMul a (B τ), ?_, fun b hb => ?_⟩
    · show w = _
      rw [hs, Matrix.vecMul_vecMul, h, Matrix.vecMul_one]
      exact ha
    · rw [← hu _ (hb.trans (hs τ b)), Matrix.vecMul_vecMul, mul_eq_one_comm.1 (h τ), Matrix.vecMul_one]

end GlobalTheory.ShFam.Spread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj
set_option maxSynthPendingDepth 32
attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet in
private theorem eigFrame_isComb_iff {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {X : Scheme.{0}} {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X}
    {m : ℕ} (u : Fin m → TanM x t.G) (a : Fin m → S) (w : TanM x t.G) :
    IsCombAtG t x (fun i => (tv (u i)).left) a (tv w).left ↔ w = ∑ i, a i • u i := by
  have e : tv (∑ i, a i • u i) = combT x (fun i => tv (u i)) a := by
    classical
    unfold combT
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => rfl
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, tv_add, ih]; rfl
  refine (isCombAtG_iff t x (fun i => tv (u i)) a _).trans ?_
  rw [← e]
  exact ⟨fun h => (tan_ext h).symm, fun h => h ▸ rfl⟩

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigFrame_baseChange' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (A B : Type) [CommRing A] [CommRing B] (φ : c.F →+* A) (x : Sp A ⟶ Z.X) (fr : EigFrame Z φ x) (ψ : A →+* B), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ fr.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z A B _ _ φ x fr ψ
  open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.LocM GlobalTheory.LocM.FrameBC in
  have h : GlobalTheory.LocM.IsFrame Z.t (ψ.comp φ) (spMap ψ ≫ x) ((fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i)) := by
    letI : Algebra c.F A := φ.toAlgebra
    letI : Algebra c.F B := (ψ.comp φ).toAlgebra
    let v : ∀ τ, Fin (Dw.mult τ) → TanM x Z.t.G := fun τ i => tanOf (fr.tan τ i)
    have eps_dual (a : A) : spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (Formalism.L2.Pj.dualMap ψ) := by
      rw [spMap_comp_spMap, spMap_comp_spMap]
      congr 1
      refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [Formalism.L2.Pj.dualMap, epsMul, mul_comm]
    have he : ∀ τ i (a : 𝓞 E), (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) τ i ≫ (Z.t.act.act a).left =
        spMap (epsMul ((ψ.comp φ) (embK c τ a))) ≫ (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) τ i := fun τ i a => by
      show (spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) ≫ _ = _ ≫ spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i
      rw [Category.assoc, fr.eig τ i a, ← Category.assoc, eps_dual, Category.assoc, RingHom.comp_apply]
    have h1 := full_of_eig c v (fun τ i => (eig_iff c τ (v τ i)).1 (fr.eig τ i)) fun τ n hn => by
      exact (existsUnique_congr fun a => eigFrame_isComb_iff (v τ) a n).1 (fr.basis τ _ (isTan_tv n) ((eig_iff c τ n).2 hn))
    have h2 : Full fun k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => resM ψ (v k.1 k.2) := by
      have h := full_equiv (eB Dw).symm (full_bc ψ (full_equiv (eB Dw) h1))
      exact (funext fun k => congrArg (fun j : IxB Dw => resM ψ (v j.1 j.2)) ((eB Dw).apply_symm_apply k)) ▸ h
    refine ⟨fun τ i => ⟨isTan_map ψ rfl (fr.tan τ i), he τ i⟩, fun τ w hw hwe => ?_⟩
    have h3 := eig_of_full c (fun τ i => resM ψ (v τ i)) (fun τ i => (eig_iff c τ _).1 (he τ i)) h2 τ (tanOf hw)
      ((eig_iff c τ _).1 hwe)
    exact (existsUnique_congr fun a => eigFrame_isComb_iff (fun i => resM ψ (v τ i)) a (tanOf hw)).2 h3
  exact ⟨⟨_, fun τ i => (h.1 τ i).1, fun τ i => (h.1 τ i).2, h.2⟩, fun _ _ => rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedPointOverOfLieEigenspaceFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framed_point_over_of_lie_eigenspace_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (L : Type) [Field L] (φ : c.F →+* L) (z : Sp L ⟶ Xo.XF c) (x : Sp L ⟶ Z.X) (g : EigFrame Z φ x), z ≫ pullback.snd _ _ = spMap φ → z ≫ Z.jQ ≫ genι Z = x → letI := φ.toAlgebra; ∃ y : FrPt Xo c L, GlobalTheory.AllWt.ptF y = z ∧ ∀ τ i, ∃ w : Sp (DualNumber L) ⟶ Z.oF.t.G.left, w ≫ Z.oF.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ z ∧ w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = g.v τ i := by
  first | exact @GlobalTheory.ShFam.exists_frPt_ptF_over_of_eigFrame | exact GlobalTheory.ShFam.exists_frPt_ptF_over_of_eigFrame | (intros; apply GlobalTheory.ShFam.exists_frPt_ptF_over_of_eigFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernDvdOfDifferencesDvdStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagRelativeTangentTopChern_dvd_of_differences_dvd : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (P : MvPolynomial (Root m) ℝ), (∀ (τ : ι) (i j : Fin (m τ)), i < j → (X ⟨τ, j⟩ - X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ) ∣ P) → rootDiscr m ∣ P := by
  first | exact @GlobalTheory.GoodMetric.DiscrDvd.rootDiscr_dvd | exact GlobalTheory.GoodMetric.DiscrDvd.rootDiscr_dvd | (intros; apply GlobalTheory.GoodMetric.DiscrDvd.rootDiscr_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherPlacePenultimateChartCharacterInverseValuStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.furtherPlace_penultimateChart_character_inverseValue : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Q → ∀ β (x : (K β).lev.Uloc v), (((K β).lev.chi (GlobalTheory.Mem.Col2.ChartLevel.embU (K β).lev v x) : ℂˣ) : ℂ) * GlobalTheory.Mem.Col2.QChi.valV I l Z a v x.1 = 1 := by
  first | exact @GlobalTheory.Mem.Col2.QChi.chi_embU_mul_valV | exact GlobalTheory.Mem.Col2.QChi.chi_embU_mul_valV | (intros; apply GlobalTheory.Mem.Col2.QChi.chi_embU_mul_valV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameComposeRingHomBaseChange
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

theorem GlobalTheory.ShFam.Pad.isFrame_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (f : c.F →+* R) (φ : R →+* S) (x : Sp R ⟶ X) (u : Vecs Dw t R), GlobalTheory.LocM.IsFrame t f x u → GlobalTheory.LocM.IsFrame t (φ.comp f) (spMap φ ≫ x) (u.bc φ) :=
  GlobalTheory.LocM.isFrame_bc
end

