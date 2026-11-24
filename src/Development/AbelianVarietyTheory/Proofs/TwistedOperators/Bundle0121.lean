module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtEqInfMat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilDeriv

theorem compAt_mt_eq_infMat {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) :
    compAt θ τ (mt V g) = infMat D.sp.cm.sig V.gram (θ τ) g := by
  ext i j
  simp only [compAt, Formalism.L2.Theta.mt, infMat, matHom, Matrix.map_apply]
  rfl

theorem om_dRho_infMat : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (g : GA D S) (h : GA D T) τ z f, IsThetaFunO ψ S T f → om (g, h) (Datum.dRho (heisO ψ S T) θ τ z f) = Datum.dRho (heisO ψ S T) θ τ (infMat D.sp.cm.sig T.gram (θ τ) h * z * infMat D.sp.cm.sig S.gram (θ τ) g⁻¹) (om (g, h) f) := by
  intro D ψ S T χS χT om hW θ hθ g h τ z f hf
  rw [← compAt_mt_eq_infMat θ τ T h, ← compAt_mt_eq_infMat θ τ S g⁻¹]
  exact GlobalTheory.WeilVacMove.om_dRho hW hθ g h τ z hf

end GlobalTheory.WeilDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongrOfSignatureOfAdelicNorm
section
open Formalism.BasicNotions IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.HermAdelicNorm

theorem congr_of_hasSignature {c p q : ℕ} {J J' : Matrix (Fin c) (Fin c) ℂ}
    (h : Formalism.UG.HasSignature J p q) (h' : Formalism.UG.HasSignature J' p q) :
    ∃ Q : Matrix (Fin c) (Fin c) ℂ, Q.det ≠ 0 ∧ J' = Qᵀ * J * Q.map conj := by
  obtain ⟨e, P, hP⟩ := h
  obtain ⟨e', P', hP'⟩ := h'
  set R : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P * P'⁻¹).val with hR
  have hRP : R * P'.val = P.val := by
    rw [hR, ← Units.val_mul, inv_mul_cancel_right]
  have h1 : Formalism.UG.cT (starRingEnd ℂ) R * J.reindex e e * R = J'.reindex e' e' := by
    have hu : IsUnit (Formalism.UG.cT (starRingEnd ℂ) (P' : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) := by
      rw [Matrix.isUnit_iff_isUnit_det, Formalism.UG.cT, Matrix.det_transpose,
        show ((P' : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map (starRingEnd ℂ)).det = _ from
          (RingHom.map_det (starRingEnd ℂ) _).symm]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 P'.isUnit).map _
    refine hu.mul_left_cancel (P'.isUnit.mul_right_cancel ?_)
    rw [hP', ← hP, ← hRP, Formalism.UG.cT_mul]
    simp only [Matrix.mul_assoc]
  let S : Matrix (Fin c) (Fin c) ℂ := R.submatrix e e'
  have hS : S.det ≠ 0 := by
    have : S * (P * P'⁻¹)⁻¹.val.submatrix e' e = 1 := by
      rw [Matrix.submatrix_mul_equiv, hR, Units.mul_inv, Matrix.submatrix_one_equiv]
    exact (Matrix.isUnit_det_of_right_inverse this).ne_zero
  refine ⟨S.map conj, ?_, ?_⟩
  · rw [show (S.map conj).det = _ from (RingHom.map_det (starRingEnd ℂ) _).symm]
    exact (map_ne_zero _).2 hS
  · have h2 : (S.map conj).map conj = S := by
      ext a b
      simp
    have h3 : J' = (J'.reindex e' e').submatrix e' e' := by simp
    have h4 : J = (J.reindex e e).submatrix e e := by simp
    rw [h2, h3, ← h1]
    conv_rhs => rw [h4]
    rw [← Matrix.submatrix_mul_equiv _ _ _ e, ← Matrix.submatrix_mul_equiv _ _ _ e]
    rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem exists_coord (cm : CMData F E) {θ : E} (h0 : θ ≠ 0) (hθ : star θ = -θ) (x : E) :
    ∃ a b : F, x = algebraMap F E a + algebraMap F E b * θ := by
  have h2 : star (2 : E) = 2 := star_ofNat 2
  obtain ⟨a, ha⟩ := (cm.fixed ((x + star x) / 2)).1 (by
    rw [star_div₀, star_add, star_star, h2, add_comm])
  obtain ⟨b, hb⟩ := (cm.fixed ((x - star x) / (2 * θ))).1 (by
    rw [star_div₀, star_sub, star_star, star_mul', h2, hθ]
    field_simp
    ring)
  refine ⟨a, b, ?_⟩
  rw [ha, hb]
  field_simp
  ring

theorem exists_sq_sub (cm : CMData F E) {θ : E} (h0 : θ ≠ 0) (hθ : star θ = -θ) {d a : F}
    (hd : algebraMap F E d = θ * θ) (R : Type) [CommRing R] [Algebra F R] (y : E ⊗[F] R)
    (hy : Formalism.UG.sigR cm.sig R y * y = Formalism.UG.inclE R (algebraMap F E a)) :
    ∃ u w : R, algebraMap F R a = u ^ 2 - algebraMap F R d * w ^ 2 := by
  obtain ⟨u, w, rfl⟩ : ∃ u w : R, y = (1 : E) ⊗ₜ[F] u + θ ⊗ₜ[F] w := by
    clear hy
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul x r =>
      obtain ⟨s, t, rfl⟩ := exists_coord cm h0 hθ x
      refine ⟨s • r, t • r, ?_⟩
      rw [TensorProduct.add_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
        Algebra.smul_def, Algebra.smul_def, mul_one]
    | add x y hx hy =>
      obtain ⟨u, w, rfl⟩ := hx
      obtain ⟨u', w', rfl⟩ := hy
      exact ⟨u + u', w + w', by simp only [TensorProduct.tmul_add]; ring⟩
  refine ⟨u, w, Algebra.TensorProduct.includeRight_injective (R := F) (A := E) (B := R)
    (algebraMap F E).injective ?_⟩
  have h1 : Formalism.UG.sigR cm.sig R ((1 : E) ⊗ₜ[F] u + θ ⊗ₜ[F] w) =
      (1 : E) ⊗ₜ[F] u - θ ⊗ₜ[F] w := by
    rw [map_add (f := _)]
    change (star (1 : E)) ⊗ₜ[F] u + (star θ) ⊗ₜ[F] w = _
    rw [star_one, hθ, TensorProduct.neg_tmul, sub_eq_add_neg]
  have h2 : ∀ s : F, ∀ r : R, (algebraMap F E s) ⊗ₜ[F] r = (1 : E) ⊗ₜ[F] (algebraMap F R s * r) := by
    intro s r
    rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  have h3 : Formalism.UG.inclE (F := F) R (algebraMap F E a) = (1 : E) ⊗ₜ[F] (algebraMap F R a) := by
    rw [← mul_one (algebraMap F R a), ← h2]
    rfl
  rw [h1, h3] at hy
  simp only [Algebra.TensorProduct.includeRight_apply]
  rw [← hy, TensorProduct.tmul_sub, ← h2, hd, pow_two, pow_two,
    ← Algebra.TensorProduct.tmul_mul_tmul]
  rw [show ((1 : E) ⊗ₜ[F] (u * u) : E ⊗[F] R) = (1 : E) ⊗ₜ[F] u * (1 : E) ⊗ₜ[F] u by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
  ring

theorem congr_of_signature_of_adelic_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (c : ℕ) (G G' : Matrix (Fin c) (Fin c) E), Gᴴ = G → G'ᴴ = G' → G.det ≠ 0 → G'.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ p q, Formalism.UG.HasSignature (G.map τ) p q ∧ Formalism.UG.HasSignature (G'.map τ) p q) → (∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = Formalism.UG.inclE (FiniteAdeleRing (𝓞 F) F) (G.det / G'.det)) → ∃ P : Matrix (Fin c) (Fin c) E, P.det ≠ 0 ∧ Pᴴ * G * P = G' := by
  intro F E _ _ _ _ _ _ cm c G G' hG hG' hd hd' hs ⟨y, hy⟩
  haveI := cm.totReal
  haveI := cm.cmUnram.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨cm.deg2⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  have hcc : ∀ x : E, ReciprocityTheory.ChartRestriction.G.FD.cc x = star x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective ((GlobalTheory.Published.embedding_cc τ x).trans (cm.cmUnram.2.1 τ x).symm)
  have hH : ∀ {M : Matrix (Fin c) (Fin c) E}, Mᴴ = M →
      ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (M a b) = M b a := fun h a b => by
    rw [hcc]
    exact congrFun (congrFun h b) a
  have hs' : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin c) (Fin c) ℂ, Q.det ≠ 0 ∧
      G'.map τ = Qᵀ * G.map τ * Q.map conj := fun τ => by
    obtain ⟨p, q, h, h'⟩ := hs τ
    exact congr_of_hasSignature h h'
  obtain ⟨a, ha⟩ := (cm.fixed (G.det / G'.det)).1 (by
    rw [star_div₀, ← Matrix.det_conjTranspose, ← Matrix.det_conjTranspose, hG, hG'])
  obtain ⟨θ, h0, hθ⟩ := GlobalTheory.Published.exists_cc_eq_neg (E := E)
  rw [hcc] at hθ
  obtain ⟨d, hdθ⟩ := (cm.fixed (θ * θ)).1 (by rw [star_mul', hθ]; ring)
  have hd0 : d ≠ 0 := fun h => mul_ne_zero h0 h0 (by rw [← hdθ, h, map_zero])
  have ha0 : a ≠ 0 := fun h => div_ne_zero hd hd' (by rw [← ha, h, map_zero])
  obtain ⟨u, w, huw⟩ := exists_sq_sub cm h0 hθ hdθ _ y (hy.trans (by rw [ha]))
  obtain ⟨s, t, hst⟩ := GlobalTheory.QNorm.hasseNormSt F d a hd0 ha0
    (fun ρ => by
      let τ := ComplexEmbedding.lift E (Complex.ofRealHom.comp ρ)
      have h1 : τ (algebraMap F E a) = (Complex.ofRealHom.comp ρ) a :=
        ComplexEmbedding.lift_algebraMap_apply E _ a
      have h2 : 0 < (τ (G.det / G'.det)).re := GlobalTheory.Published.Landherr.re_det_div_pos hd τ (hs' τ)
      rw [← ha, h1] at h2
      exact ⟨√(ρ a), 0, by rw [Real.sq_sqrt (le_of_lt (by simpa using h2))]; ring⟩)
    (fun v => by
      let ev : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
        RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) v
      have h1 := congrArg ev huw
      rw [map_sub, map_mul, map_pow, map_pow] at h1
      exact ⟨ev u, ev w, h1⟩)
  obtain ⟨P, hP, hPG⟩ := GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt E c G G'
    (hH hG) (hH hG') hd hd' hs' ⟨algebraMap F E s + algebraMap F E t * θ, by
      have hf : ∀ z : F, star (algebraMap F E z) = algebraMap F E z :=
        fun z => (cm.fixed _).2 ⟨z, rfl⟩
      rw [hcc, star_add, star_mul', hf, hf, hθ, ← ha, hst, map_sub, map_mul, map_pow, map_pow, hdθ]
      ring⟩
  refine ⟨P.map ReciprocityTheory.ChartRestriction.G.FD.cc, ?_, ?_⟩
  · rw [GlobalTheory.Published.det_map_cc]
    exact GlobalTheory.Published.cc_ne_zero hP
  · rw [hPG]
    congr 2
    ext a b
    simp [hcc]

end GlobalTheory.HermAdelicNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjStableInverseDifferentAndNormIdeal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) ((D.host.ddE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ * D.host.AA * D.host.AAbar) := by
  intro D
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hs : ∀ x : D.host.E, star x = ReciprocityTheory.ChartRestriction.G.FD.cc x := fun _ => rfl
  have hcc : ∀ a : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc a = D.host.conj a := fun a => bridge_star_holds D.R D.host a
  have key : ∀ nn : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E, nn ≠ 0 → GlobalTheory.conjFrac nn = nn →
      GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) nn := fun nn h0 h =>
    ⟨h0, fun x => by rw [hs, ← GlobalTheory.mem_conjFrac, h]⟩
  have hb : D.host.AAbar = GlobalTheory.conjFrac D.host.AA := by
    ext a
    rw [GlobalTheory.mem_conjFrac, hcc]
    exact ⟨Formalism.L2.Pj.conj_mem_AA D, fun ha => by
      simpa only [Formalism.L2.Pj.conj_conj] using Formalism.L2.Pj.conj_mem_AAbar D ha⟩
  have hA : D.host.AA ≠ 0 := Formalism.L2.Pj.AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hg : (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero))
  refine ⟨key _ (inv_ne_zero GlobalTheory.coe_different_ne_zero) ?_, key _ ?_ ?_⟩
  · rw [GlobalTheory.conjFrac_inv]
    exact congrArg _ GlobalTheory.conjFrac_different
  · rw [hb]
    exact mul_ne_zero (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hg) hA) (GlobalTheory.conjFrac_ne_zero hA)
  · have hc : ReciprocityTheory.ChartRestriction.G.FD.cc (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ =
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ := by
      rw [hcc, map_inv₀, map_natCast]
    rw [hb, map_mul, map_mul, GlobalTheory.conjFrac_spanSingleton, GlobalTheory.conjFrac_conjFrac, hc, mul_right_comm]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
section
noncomputable section

namespace GlobalTheory.Grow

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open GlobalTheory.AdelicU (EmbOver htInf htFin compInf compFin infProj opNorm)
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (infHt infNorm)
open GlobalTheory.SmoothForms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem infEmb_tmul_one_eq_extensionEmbedding {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {w : InfinitePlace F} {τ : E →+* ℂ} (hτ : τ.comp (algebraMap F E) = w.embedding)
    {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) (b : Ainf F) :
    θ (b ⊗ₜ[F] (1 : E)) = InfinitePlace.Completion.extensionEmbedding w (b w) := by
  have hc : Continuous fun b : Ainf F => InfinitePlace.Completion.extensionEmbedding w (b w) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
  have key := (InfiniteAdeleRing.denseRange_algebraMap F).equalizer hθ.2 hc ?_
  · exact congrFun key b
  funext x
  simp only [Function.comp_apply]
  rw [← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply', hθ.1,
    ← RingHom.comp_apply, hτ]
  simp

theorem htInf_eq_infMat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {w : InfinitePlace F} (t : EmbOver E w)
    [StarRing E] {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb t.1 θ) (g : HA (AF F) σ J) :
    htInf F w (bc (compInf F E w) (GlobalTheory.AdelicU.matHom _ σ J g)) =
      max 1 (max (opNorm (infMat σ J θ g)) (opNorm (infMat σ J θ g⁻¹))) := by
  have hre := infEmb_tmul_one_eq_extensionEmbedding t.2 hθ
  have hz : ∀ z : AF F ⊗[F] E, GlobalTheory.AdelicU.infEmb t (compInf F E w z) =
      θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have e : (fstA F a) ⊗ₜ[F] x = ((fstA F a) ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] x) := by simp
      simp only [GlobalTheory.AdelicU.compInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, GlobalTheory.AdelicU.infEmb_tmul]
      rw [e, map_mul, hre, hθ.1]
      rfl
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have hm : ∀ k : HA (AF F) σ J, ((bc (compInf F E w) (GlobalTheory.AdelicU.matHom _ σ J k) : GL (Fin n) _) :
      Matrix (Fin n) (Fin n) _).map (GlobalTheory.AdelicU.infEmb t) = infMat σ J θ k := by
    intro k
    ext i j
    exact hz _
  show max 1 (max (GlobalTheory.AdelicU.normInf F w _) (GlobalTheory.AdelicU.normInf F w _)) = _
  rw [GlobalTheory.AdelicU.normInf_eq_opNorm h t, GlobalTheory.AdelicU.normInf_eq_opNorm h t, ← map_inv (bc (compInf F E w)),
    ← map_inv (GlobalTheory.AdelicU.matHom _ σ J), hm, hm]

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (V : HSp D)

theorem htInf_eq_infHt (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g : GA D V) :
    htInf D.host.F (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
      (bc (compInf D.host.F D.host.E _) (Formalism.L2.Theta.matHom V g)) = infHt θ V τ g := by
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have ht : (tauE D τ).comp (algebraMap D.host.F D.host.E) =
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))).embedding :=
    (InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.mp (hcm.1.isReal _))).symm
  exact (htInf_eq_infMat hcm V.gram ⟨_, ht⟩ (hθ τ) g).trans rfl

private theorem htFin_eq_one_of_mem_GinfC {g : GA D V} (hg : g ∈ GinfC V) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    htFin D.host.F v (bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom V g)) = 1 := by
  have hk : Formalism.L2.Theta.finHom V g = 1 := hg
  have hz : ∀ z : AF D.host.F ⊗[D.host.F] D.host.E, compFin D.host.F D.host.E v z =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add y z hy hz => rw [map_add (f := _), map_add (f := _), map_add (f := _), hy, hz]
  have h1 : bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom V g) = 1 := by
    apply Units.ext
    ext i j
    have hij : Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
        (((Formalism.L2.Theta.matHom V g : GL _ _) : Matrix _ _ _) i j) =
        ((1 : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) : Matrix _ _ _) i j := by
      rw [← hk]; rfl
    show compFin D.host.F D.host.E v (((Formalism.L2.Theta.matHom V g : GL _ _) : Matrix _ _ _) i j) = _
    rw [hz, hij, Units.val_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [h1]
  refine (GlobalTheory.AdelicU.htOf_eq_one).2 ⟨?_, ?_⟩ <;> simpa using GlobalTheory.AdelicU.normFin_one_le D.host.F v

theorem height_eq_prod_infHt (hθ : IsInfFam θ) {g : GA D V} (hg : g ∈ GinfC V) :
    height V g = ∏ τ, (infHt θ V τ g : ℝ) := by
  have hinf : ∏ w, htInf D.host.F w (bc (compInf D.host.F D.host.E w) (Formalism.L2.Theta.matHom V g)) =
      ∏ τ, infHt θ V τ g :=
    (Fintype.prod_bijective _ (GlobalTheory.CMTypePlaces.places_bijective D) _ _
      fun τ => (htInf_eq_infHt V hθ τ g).symm).symm
  show ((GlobalTheory.AdelicU.heightGL D.host.F (Formalism.L2.Theta.matHom V g) : NNReal) : ℝ) = _
  rw [GlobalTheory.AdelicU.heightGL, hinf]
  simp only [htFin_eq_one_of_mem_GinfC V hg, finprod_one, mul_one, NNReal.coe_prod]

theorem normInf_le_height (hθ : IsInfFam θ) : ∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * height V g := by
  refine ⟨2 * (Fintype.card D.what₂.Tau * V.rank * V.rank : ℝ), fun g => ?_⟩
  have hb : ∀ τ, (infHt θ V τ g : ℝ) ≤ height V g := fun τ => by
    have := htInf_le_height V g (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
    rwa [htInf_eq_infHt V hθ τ g] at this
  have he : ∀ τ i j, ‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖ ≤
      2 * height V g := by
    intro τ i j
    have h1 := GlobalTheory.SmoothForms.NormInf.norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g) i j
    have h2 := GlobalTheory.SmoothForms.NormInf.norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g⁻¹) i j
    have h3 : infNorm θ V τ g ≤ infHt θ V τ g := le_max_of_le_right (le_max_left _ _)
    have h4 : infNorm θ V τ g⁻¹ ≤ infHt θ V τ g := le_max_of_le_right (le_max_right _ _)
    have h3' : (infNorm θ V τ g : ℝ) ≤ height V g := (NNReal.coe_le_coe.2 h3).trans (hb τ)
    have h4' : (infNorm θ V τ g⁻¹ : ℝ) ≤ height V g := (NNReal.coe_le_coe.2 h4).trans (hb τ)
    have e3 : (infNorm θ V τ g : ℝ) =
        ‖Matrix.toEuclideanCLM (n := Fin V.rank) (𝕜 := ℂ) (infMat D.sp.cm.sig V.gram (θ τ) g)‖ := rfl
    have e4 : (infNorm θ V τ g⁻¹ : ℝ) =
        ‖Matrix.toEuclideanCLM (n := Fin V.rank) (𝕜 := ℂ) (infMat D.sp.cm.sig V.gram (θ τ) g⁻¹)‖ := rfl
    linarith
  calc normInf θ V g = ∑ τ, ∑ i, ∑ j,
        (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := rfl
    _ ≤ ∑ _τ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, 2 * height V g := by
        gcongr with τ _ i _ j _
        exact he τ i j
    _ = 2 * (Fintype.card D.what₂.Tau * V.rank * V.rank : ℝ) * height V g := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem height_le_normInf_pow (hθ : IsInfFam θ) : ∃ d : ℕ, ∀ g ∈ GinfC V, height V g ≤ normInf θ V g ^ d := by
  rcases Nat.eq_zero_or_pos V.rank with h0 | hpos
  · refine ⟨0, fun g hg => ?_⟩
    rw [height_eq_prod_infHt V hθ hg, pow_zero]
    simp [GlobalTheory.SmoothForms.HeightCoset.infHt_rank_zero θ V h0]
  · refine ⟨Fintype.card D.what₂.Tau, fun g hg => ?_⟩
    rw [height_eq_prod_infHt V hθ hg, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun τ _ => NNReal.coe_nonneg _)
      (fun τ _ => GlobalTheory.SmoothForms.HeightCoset.infHt_le_normInf θ V hpos τ g)

theorem normInf_height_comparison (D : D7) (V : HSp D)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) :
    (∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * height V g) ∧
      ∃ (C : ℝ) (d : ℕ), ∀ g ∈ GinfC V, height V g ≤ C * (1 + normInf θ V g) ^ d := by
  obtain ⟨C, hC⟩ := normInf_le_height V hθ
  obtain ⟨d, hd⟩ := height_le_normInf_pow V hθ
  refine ⟨⟨C, hC⟩, 1, d, fun g hg => ?_⟩
  have h0 : 0 ≤ normInf θ V g := by
    unfold Formalism.L2.Theta.normInf
    positivity
  calc height V g ≤ normInf θ V g ^ d := hd g hg
    _ ≤ (1 + normInf θ V g) ^ d := pow_le_pow_left₀ h0 (by linarith) d
    _ = 1 * (1 + normInf θ V g) ^ d := (one_mul _).symm

private theorem exists_coset_bound_of_modGrowthExp (V : HSp D) {d : ℕ} (hd : ∀ g ∈ GinfC V, height V g ≤ normInf θ V g ^ d) {A : ℕ}
    {f : GA D V → ℂ} (hf : ModGrowthExp V A f) (x : GA D V) :
    ∃ C : ℝ, ∀ g ∈ GinfC V, ‖f (x * g)‖ ≤ C * normInf θ V g ^ (d * A) := by
  obtain ⟨C, hC⟩ := hf
  have hC0 : 0 ≤ C := nonneg_of_growth hC
  refine ⟨C * height V x ^ A, fun g hg => ?_⟩
  have h1 : height V (x * g) ≤ height V x * normInf θ V g ^ d :=
    (height_mul_le V x g).trans (mul_le_mul_of_nonneg_left (hd g hg) (height_pos V x).le)
  calc ‖f (x * g)‖ ≤ C * height V (x * g) ^ A := hC _
    _ ≤ C * (height V x * normInf θ V g ^ d) ^ A :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos V _).le h1 A) hC0
    _ = C * height V x ^ A * normInf θ V g ^ (d * A) := by rw [mul_pow, ← pow_mul]; ring

variable {V}

theorem exists_modGrowthExp_le_normInf_pow (hθ : IsInfFam θ) (A : ℕ) :
    ∃ N : ℕ, ∀ f : GA D V → ℂ, ModGrowthExp V A f →
      ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V, ‖f (x * g)‖ ≤ C * normInf θ V g ^ N := by
  obtain ⟨d, hd⟩ := height_le_normInf_pow V hθ
  exact ⟨d * A, fun f hf x => exists_coset_bound_of_modGrowthExp V hd hf x⟩

theorem UnifModGrowth.growth (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : UnifModGrowth V θ φ) :
    ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
        ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨N, hN⟩ := exists_modGrowthExp_le_normInf_pow (V := V) hθ A
  exact ⟨N, fun l hl x => hN _ (hA l hl) x⟩

theorem UnifModGrowth.isAutFunSm (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : UnifModGrowth V θ φ) (ha : IsAutFun V φ)
    (hs : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod))
    (hz : ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W) :
    IsAutFunSm θ V φ :=
  { toIsAutFun := ha, smooth := hs, zfin := hz, growth := h.growth hθ }

end GlobalTheory.Grow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnFundamentalDomain
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CocompactIntegrable

theorem integrableOn_of_cocompact {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (𝓕 C : Set G)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : G, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (F : G → ℂ) (hF : Continuous F)
    (hinv : ∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) : IntegrableOn F 𝓕 μ := by
  have hle : μ 𝓕 ≤ μ C := by
    rw [h𝓕.measure_eq_tsum C]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    intro h hh
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨c, hc, rfl⟩, hh⟩
  have hfin : μ 𝓕 ≠ ⊤ := (hle.trans_lt hC.measure_lt_top).ne
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
  refine Measure.integrableOn_of_bounded (M := M) hfin hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun h => ?_)
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
  rw [hinv γ hγ]
  exact hM c hc

theorem integrableOn_fundamentalDomain : ∀ {D : D7} (V : HSp D) (μ : Measure (GA D V)) (𝓕 C : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → IsCompact C → (∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c) → ∀ F : GA D V → ℂ, Continuous F → (∀ γ ∈ GQ V, ∀ h, F (γ * h) = F h) → IntegrableOn F 𝓕 μ := by
  intro D V μ 𝓕 C hμ h𝓕 hC hcov F hF hinv
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  exact integrableOn_of_cocompact (GQ V) μ 𝓕 C h𝓕 hC hcov F hF hinv

end GlobalTheory.CocompactIntegrable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelativeHeightEntryLeAdelicHeightGLStatement
section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativeHeight_entry_le_adelicHeightGL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (γ : GL (Fin N) E) (i j : Fin N), GlobalTheory.RatCount.htE F ((γ : Matrix (Fin N) (Fin N) E) i j) ≤ GlobalTheory.AdelicU.heightGL F (Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ) := by
  first | exact @GlobalTheory.RatCount.htE_entry_le_heightGL | exact GlobalTheory.RatCount.htE_entry_le_heightGL | (intros; apply GlobalTheory.RatCount.htE_entry_le_heightGL <;> assumption)
end

