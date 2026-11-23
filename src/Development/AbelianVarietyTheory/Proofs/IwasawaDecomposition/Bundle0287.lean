module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDictionaryCoreLawsBaseFrameChange
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
public import ReciprocityTheory.GaloisValuations.GlobalB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0271

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CevInjective
section
noncomputable section

namespace GlobalTheory.Mem.Col2.PerConj

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Matrix
open scoped ComplexOrder

section Val

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ} (lam : ι → DomWeight n)

def cev : Pol ℂ ι n →ₛₗ[starRingEnd ℂ] (Fr emb σ n → ℂ) := evFr (Gr emb σ n) (shiftOf lam) (starRingEnd ℂ)

theorem cev_injective : Function.Injective (cev emb σ lam) := evFr_injective _ _ _ (fr0 emb σ n)

theorem cev_mem {P : Pol ℂ ι n} (hP : P ∈ VV ℂ lam) : cev emb σ lam P ∈ ValC (Gr emb σ n) lam :=
  ⟨_, map_mem_CSpan (starRingEnd ℂ) lam P hP, rfl⟩

theorem exists_cev {z : Fr emb σ n → ℂ} (hz : z ∈ ValC (Gr emb σ n) lam) : ∃ P ∈ VV ℂ lam, cev emb σ lam P = z := by
  obtain ⟨p, hp, rfl⟩ := hz
  have h := CSpan_le_span (starRingEnd ℂ) lam hp
  clear hp
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨P, hP, rfl⟩ := hx
    exact ⟨P, hP, rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by rw [map_zero, map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨P, hP, e⟩ := hx
    obtain ⟨Q, hQ, e'⟩ := hy
    exact ⟨P + Q, Submodule.add_mem _ hP hQ, by rw [map_add (f := _), map_add (f := _), e, e']⟩
  | smul r x _ hx =>
    obtain ⟨P, hP, e⟩ := hx
    exact ⟨starRingEnd ℂ r • P, Submodule.smul_mem _ _ hP, by rw [map_smulₛₗ, map_smul, e, Complex.conj_conj]⟩

theorem polOf_cev (P : Pol ℂ ι n) :
    polOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n) (cev emb σ lam P) = MvPolynomial.map (starRingEnd ℂ) P := by
  have h := polOf_fnOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n) (MvPolynomial.map (starRingEnd ℂ) P)
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = (1 : ι → Matrix (Fin n) (Fin n) ℂ) := by
    funext τ
    exact inv_one
  rw [e] at h
  exact h

theorem nfAll_conj (p P : Pol ℂ ι n) : nfAll lam p (MvPolynomial.map (starRingEnd ℂ) P) = pairB lam p P := by
  have h1 := map_extNorm (RingHom.id ℂ) lam
  rw [RingHom.id_apply, pb_extNorm_eq] at h1
  rw [nfAll, ← h1, pairB_apply, div_eq_inv_mul]
  congr 1
  rw [fockF_eq_sum _ _ _ subset_rfl, fockB]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map, starRingEnd_apply, star_star, mfact]

theorem ipVal_cev (P : Pol ℂ ι n) (w : Fr emb σ n → ℂ) :
    ipVal emb σ lam (cev emb σ lam P) w = pairB lam (polOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n) w) P := by
  rw [ipVal, ipFr_apply, polOf_cev, nfAll_conj]

theorem ipVal_pos {z : Fr emb σ n → ℂ} (hz : z ∈ ValC (Gr emb σ n) lam) (h0 : z ≠ 0) : 0 < ipVal emb σ lam z z := by
  obtain ⟨P, -, rfl⟩ := exists_cev emb σ lam hz
  rw [ipVal, ipFr_apply, polOf_cev, nfAll]
  have hP : MvPolynomial.map (starRingEnd ℂ) P ≠ 0 := by
    intro h
    apply h0
    have : P = 0 := MvPolynomial.map_injective _ (starRingEnd ℂ).injective (by rw [h, map_zero])
    rw [this, map_zero]
  exact div_pos (ps_fockF_pos _ hP)
    (Finset.prod_pos fun τ _ => ps_fockF_pos _ (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _))

theorem cev_act [StarRing E] (hE : ∀ τ x, embAt σ emb τ (star x) = starRingEnd ℂ (embAt σ emb τ x)) (γ : GL (Fin n) E)
    (hγ : (γ : Matrix (Fin n) (Fin n) E)ᴴ * (γ : Matrix (Fin n) (Fin n) E) = 1) (c : Kˣ) (hc : ∃ m : ℕ, 0 < m ∧ c ^ m = 1)
    (P : Pol ℂ ι n) :
    cev emb σ lam ((σ (c : K))⁻¹ • rhoP lam (embGL (embAt σ emb) γ) P) = trFr emb σ γ c (cev emb σ lam P) := by
  have h1 : starRingEnd ℂ (σ (c : K))⁻¹ = σ c := by
    obtain ⟨m, hm, hc⟩ := hc
    have h2 : σ (c : K) ^ m = 1 := by rw [← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]
    have h3 : ‖σ (c : K)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h2 hm.ne'
    rw [Complex.inv_eq_conj h3, Complex.conj_conj]
  have h4 : ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = (γ : Matrix (Fin n) (Fin n) E)ᴴ := by
    rw [Matrix.coe_units_inv]
    exact Matrix.inv_eq_left_inv hγ
  funext y
  rw [map_smulₛₗ, h1, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine (congrFun (evFr_actP (Gr emb σ n) (starRingEnd ℂ) lam (embGL (embAt σ emb) γ) P) y).trans ?_
  refine Eq.trans ?_ (fnOf_tr (G := Gr emb σ n) (G' := Gr emb σ n) (shiftOf lam) 1
    (fun τ => ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ))
    (MvPolynomial.map (starRingEnd ℂ) P) (frMul emb σ γ⁻¹ y) y fun _ => rfl).symm
  refine congrArg (fun M => fnOf (Gr emb σ n) (shiftOf lam) M (MvPolynomial.map (starRingEnd ℂ) P) y) ?_
  funext τ
  rw [h4, Pi.one_apply, Matrix.one_mul]
  ext a b
  exact (hE τ _).symm

end Val

section Per

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  {I : ChainIn E K ι R} (Q : PerIn I) (emb : ι → E →+* K) (σ : K →+* ℂ)

def law (b : Q.S'.β) : Q.S'.G b →* Module.End ℂ (Pol ℂ ι (R.N R.m - 1)) where
  toFun g := (σ (Q.S'.chr b g : K))⁻¹ • rhoP Q.sgT (embGL (embAt σ emb) (Q.S'.gam b g))
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, Units.val_mul]
    rw [smul_mul_smul_comm, mul_inv]

def jM : Q.Mt emb σ →ₛₗ[starRingEnd ℂ] (Q.S'.Cl → Fr emb σ (R.N R.m - 1) → ℂ) where
  toFun F c := cev emb σ Q.sgT (F.1 c.1 (Q.S'.rep c))
  map_add' F G := by
    funext c
    exact map_add (cev emb σ Q.sgT) _ _
  map_smul' r F := by
    funext c
    exact map_smulₛₗ (cev emb σ Q.sgT) r _

variable {Q}

theorem mt_law (hH : ∀ b, Q.H b = ⊤) (F : Q.Mt emb σ) (b : Q.S'.β) (g : Q.S'.G b) (d : Q.S'.D b) :
    F.1 b (g • d) = law Q emb σ b g (F.1 b d) :=
  (F.2 b d).2 g (by rw [hH]; trivial)

theorem jM_injective (hH : ∀ b, Q.H b = ⊤) : Function.Injective (jM Q emb σ) := by
  intro F G h
  apply Subtype.ext
  funext b d
  have h1 := cev_injective emb σ Q.sgT (congrFun h (Q.S'.cl b d))
  have h2 := mt_law emb σ hH F b (Q.S'.mv b d) (Q.S'.rep (Q.S'.cl b d))
  have h3 := mt_law emb σ hH G b (Q.S'.mv b d) (Q.S'.rep (Q.S'.cl b d))
  rw [Q.S'.mv_smul] at h2 h3
  rw [h2, h3]
  exact congrArg _ h1

variable (hE : ∀ τ x, embAt σ emb τ (star x) = starRingEnd ℂ (embAt σ emb τ x))
include hE

theorem cev_law (h : Q.Ok) (b : Q.S'.β) (g : Q.S'.G b) (P : Pol ℂ ι (R.N R.m - 1)) :
    cev emb σ Q.sgT (law Q emb σ b g P) = Q.S'.tr emb σ b g (cev emb σ Q.sgT P) :=
  cev_act emb σ Q.sgT hE _ (h.step.unit b g) _ (h.step.root b g) P

theorem jM_mem (h : Q.Ok) (hH : ∀ b, Q.H b = ⊤) (F : Q.Mt emb σ) : jM Q emb σ F ∈ Q.S'.Fi emb σ Q.sgT := by
  intro c
  refine ⟨cev_mem emb σ Q.sgT (F.2 c.1 (Q.S'.rep c)).1, fun g => ?_⟩
  have h2 := mt_law emb σ hH F c.1 g.1 (Q.S'.rep c)
  rw [g.2] at h2
  exact (cev_law emb σ hE h c.1 g.1 _).symm.trans (congrArg _ h2.symm)

theorem jM_onto (h : Q.Ok) (z : Q.S'.Cl → Fr emb σ (R.N R.m - 1) → ℂ) (hz : z ∈ Q.S'.Fi emb σ Q.sgT) :
    ∃ F, jM Q emb σ F = z := by
  choose P hP hPz using fun c => exists_cev emb σ Q.sgT (hz c).1
  have hfix : ∀ b q (g : Q.S'.G b), g • Q.S'.rp b q = Q.S'.rp b q → law Q emb σ b g (P ⟨b, q⟩) = P ⟨b, q⟩ := by
    intro b q g hg
    apply cev_injective emb σ Q.sgT
    rw [cev_law emb σ hE h, hPz]
    exact (hz ⟨b, q⟩).2 ⟨g, hg⟩
  have key : ∀ b q (g : Q.S'.G b) (d : Q.S'.D b), g • Q.S'.rp b q = d →
      law Q emb σ b (Q.S'.mv b d) (P (Q.S'.cl b d)) = law Q emb σ b g (P ⟨b, q⟩) := by
    intro b q g d hd
    have hq : q = Quotient.mk (MulAction.orbitRel (Q.S'.G b) (Q.S'.D b)) d := by
      rw [← Q.S'.rp_spec b q]
      exact (Quotient.sound (⟨g, hd⟩ : (MulAction.orbitRel (Q.S'.G b) (Q.S'.D b)).r d (Q.S'.rp b q))).symm
    subst hq
    have h1 : Q.S'.mv b d • Q.S'.rp b (Quotient.mk _ d) = d := Q.S'.mv_smul b d
    have h2 := hfix b (Quotient.mk _ d) (g⁻¹ * Q.S'.mv b d) (by rw [mul_smul, h1, inv_smul_eq_iff, hd])
    refine Eq.trans ?_ (congrArg (law Q emb σ b g) h2)
    rw [← Module.End.mul_apply ((law Q emb σ b) g), ← map_mul, mul_inv_cancel_left]
  refine ⟨⟨fun b d => law Q emb σ b (Q.S'.mv b d) (P (Q.S'.cl b d)), fun b d => ⟨?_, fun g _ => ?_⟩⟩, ?_⟩
  · exact Submodule.smul_mem _ _ (polyAction_mem_VV _ _ (hP _))
  · have h1 : Q.S'.mv b d • Q.S'.rp b (Quotient.mk _ d) = d := Q.S'.mv_smul b d
    refine (key b (Quotient.mk _ d) (g * Q.S'.mv b d) (g • d) (by rw [mul_smul, h1])).trans ?_
    rw [map_mul]
    rfl
  · funext c
    have h1 := key c.1 c.2 1 (Q.S'.rep c) (one_smul _ _)
    rw [map_one] at h1
    exact (congrArg (cev emb σ Q.sgT) h1).trans (hPz c)

omit hE in
theorem petersson_apply (h : Q.Ok) (z w : Q.S'.Cl → Fr emb σ (R.N R.m - 1) → ℂ) :
    Q.ipP emb σ h z w = letI := Q.clFin h; ∑ c, Q.wt c * ipVal emb σ Q.sgT (z c) (w c) := by
  simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

omit hE in
theorem period_eq (hI : I.Ok) (h : Q.Ok) (hc : ι → HCParam R) (w : Q.S'.Cl → Fr emb σ (R.N R.m - 1) → ℂ) (F : Q.Mt emb σ) :
    (Q.per emb σ hI h hc).period w F = Q.ipP emb σ h (jM Q emb σ F) w := by
  rw [petersson_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  exact (ipVal_cev emb σ Q.sgT _ _).symm

omit hE in
theorem re_petersson_self_pos (h : Q.Ok) (z : Q.S'.Cl → Fr emb σ (R.N R.m - 1) → ℂ) (hz : z ∈ Q.S'.Fi emb σ Q.sgT) (h0 : z ≠ 0) :
    0 < (Q.ipP emb σ h z z).re := by
  letI := Q.clFin h
  refine (Complex.lt_def.mp ?_ : (0 : ℂ).re < _ ∧ _).1
  rw [petersson_apply]
  have hw : ∀ c, 0 < Q.wt c := fun c => by
    haveI := h.step.fin_stab c.1 (Q.S'.rep c)
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  obtain ⟨c, hc⟩ := Function.ne_iff.1 h0
  refine Finset.sum_pos' (fun c _ => ?_) ⟨c, Finset.mem_univ _, mul_pos (hw c) (ipVal_pos emb σ _ (hz c).1 hc)⟩
  by_cases h1 : z c = 0
  · simp [h1]
  · exact (mul_pos (hw c) (ipVal_pos emb σ _ (hz c).1 h1)).le

end Per

open Formalism.MainNotions Formalism.L2.Ker Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem period_conj : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι), ∃ jM : (I.per l u a).Mt →ₛₗ[starRingEnd ℂ] (I.per l u a).Wrow, Function.Injective jM ∧ (∀ z ∈ (I.fm l u a).ptC, ∃ F, jM F = z) ∧ (∀ F, jM F ∈ (I.fm l u a).ptC) ∧ (∀ w F, (I.per l u a).period w F = (I.fm l u a).ipP (jM F) w) ∧ ∀ z ∈ (I.fm l u a).ptC, z ≠ 0 → 0 < ((I.fm l u a).ipP z z).re := by
  intro B X I _ _ l _ u a
  have hE : ∀ τ x, embAt B.embLL B.fields.emb τ (letI := B.fields.starE; star x) =
      starRingEnd ℂ (embAt B.embLL B.fields.emb τ x) := fun τ x => (GlobalTheory.Mem.FieldsLaws.fields_ok B).conjE _ x
  have hH : ∀ b, (I.perIn u a).H b = ⊤ := fun _ => rfl
  exact ⟨jM (I.perIn u a) B.fields.emb B.embLL, jM_injective _ _ hH, jM_onto _ _ hE (l.per u a),
    jM_mem _ _ hE (l.per u a) hH, period_eq _ _ (l.ch u a) (l.per u a) (B.hcW u), re_petersson_self_pos _ _ (l.per u a)⟩

end GlobalTheory.Mem.Col2.PerConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyRevNegFinSumBlockDiagonalMatrix
section
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem det_blockSum {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) : (blockSum a b).det = a.det * b.det := by
  rw [blockSum, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

theorem neg_blockSum {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) : -(blockSum a b) = blockSum (-a) (-b) := by
  ext i j
  simp only [blockSum, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.neg_apply]
  rcases finSumFinEquiv.symm i with x | x <;> rcases finSumFinEquiv.symm j with y | y <;> simp

theorem one_sub_smul_blockSum {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) :
    (1 - (Polynomial.X : Polynomial R) • (blockSum a b).map Polynomial.C) =
      blockSum (1 - (Polynomial.X : Polynomial R) • a.map Polynomial.C)
        (1 - (Polynomial.X : Polynomial R) • b.map Polynomial.C) := by
  rw [blockSum_map]
  ext i j
  simp only [blockSum, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply]
  rw [show (1 : Matrix (Fin (M + N)) (Fin (M + N)) (Polynomial R)) i j =
      (1 : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) (Polynomial R)) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) by
    simp [Matrix.one_apply]]
  rcases finSumFinEquiv.symm i with x | x <;> rcases finSumFinEquiv.symm j with y | y <;>
    simp [Matrix.one_apply]

theorem charpolyRev_neg_blockSum : ∀ {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R) (b : Matrix (Fin N) (Fin N) R), Matrix.charpolyRev (-(blockSum a b)) = Matrix.charpolyRev (-a) * Matrix.charpolyRev (-b) := by
  intro R _ M N a b
  rw [neg_blockSum, Matrix.charpolyRev, Matrix.charpolyRev, Matrix.charpolyRev, one_sub_smul_blockSum, det_blockSum]

end GlobalTheory.GoodMetric.ChernSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffCharpolyRevMemTracePowerProductRealSpan
section
set_option autoImplicit false

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem trace_pow_mul_mem_trSpan {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (τ : ι)
    (j w : ℕ) (hj : 1 ≤ j) (f : Mat m S → S) (hf : f ∈ TrSpan m w S) :
    (fun A : Mat m S => ((A τ) ^ j).trace * f A) ∈ TrSpan m (j + w) S := by
  unfold TrSpan at hf
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨l, hl, hw, rfl⟩ := h
    refine Submodule.subset_span ⟨(τ, j) :: l, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hj
      · exact hl x hx
    · simp [hw]
    · funext A
      simp [trProd]
  | zero =>
    have : (fun A : Mat m S => ((A τ) ^ j).trace * (0 : Mat m S → S) A) = 0 := by
      funext A; simp
    rw [this]; exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    have : (fun A : Mat m S => ((A τ) ^ j).trace * (f + g) A) =
        (fun A : Mat m S => ((A τ) ^ j).trace * f A) + (fun A : Mat m S => ((A τ) ^ j).trace * g A) := by
      funext A; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf =>
    have : (fun A : Mat m S => ((A τ) ^ j).trace * (c • f) A) =
        c • (fun A : Mat m S => ((A τ) ^ j).trace * f A) := by
      funext A; simp
    rw [this]; exact Submodule.smul_mem _ c hf

theorem coeff_charpolyRev_mem_trSpan {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S]
    (τ : ι) (k : ℕ) :
    (fun A : Mat m S => (Matrix.charpolyRev (-(A τ))).coeff k) ∈ TrSpan m k S := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine Submodule.subset_span ⟨[], by simp, by simp, ?_⟩
      funext A
      simp [trProd, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    · have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
      have key : (fun A : Mat m S => (Matrix.charpolyRev (-(A τ))).coeff k) =
          (-(k : ℝ)⁻¹) • ∑ i ∈ Finset.range k, ((-1 : ℝ) ^ (i + 1)) •
            (fun A : Mat m S => ((A τ) ^ (i + 1)).trace *
              (Matrix.charpolyRev (-(A τ))).coeff (k - 1 - i)) := by
        funext A
        have h := GlobalTheory.natCast_mul_coeff_charpolyRev (-(A τ)) k
        have e : ∀ i : ℕ, ((-(A τ)) ^ (i + 1)).trace = ((-1 : ℝ) ^ (i + 1)) • ((A τ) ^ (i + 1)).trace := by
          intro i
          rw [← neg_one_smul ℝ (A τ), smul_pow, Matrix.trace_smul]
        simp only [e, smul_mul_assoc] at h
        simp only [Pi.smul_apply, Finset.sum_apply]
        rw [neg_smul, ← smul_neg, ← h, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
          inv_mul_cancel₀ hk', one_smul]
      rw [key]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_)
      have hi' := Finset.mem_range.1 hi
      have h := trace_pow_mul_mem_trSpan m S τ (i + 1) (k - 1 - i) (by omega) _ (ih (k - 1 - i) (by omega))
      rwa [show i + 1 + (k - 1 - i) = k by omega] at h

end GlobalTheory.GoodMetric.ChernSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CosetInMvUp
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2

theorem cosetIn_mv_up : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (j : ℕ), X.Ok → Pr.Ok → (∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) → ∀ (q : PtAt R sel mu cst u j) (P : Pr.vT u) (x : Sp X.E (R.N j)), x ∈ q.1.1.deco.1.N → q.1.1.deco.1.f P x = 1 → cosetIn (PtY.mv q (q.1.1.deco.up P (Pr.T u : 𝓞 X.E) x) : PtAt R sel mu cst u j) = cosetIn q := by
  intro X Pr R sel S mu cst u j hX hPr hQ q P x hx hf
  have hP := moveHyp_of_ok hPr u P
  have h := mv_up (Pr.T u) q P hP (T_unif hX hPr u P) (fun w => ne_of_T_notMem hPr u P (hQ w.1 w.2))
    (ysAt_off sel mu cst hPr u hQ j P) hx hf
  have hs := (upN_spec q.1.1.deco.2.lat q.1.1.deco.2.uni P.1 hP.ne hx).2.2.1
  have key : ∀ w : Pr.vGs, (q.1.1.deco.1.up P (Pr.T u : 𝓞 X.E) x).at w.1 = q.1.1.deco.1.at w.1 := fun w =>
    (hs w.1 (hP.sg w).1 (hP.sg w).2).localization_eq
  have hfr : frsF sel mu (PtY.mv q (q.1.1.deco.up P (Pr.T u : 𝓞 X.E) x)).1.1 = frsF sel mu q.1.1 := by
    funext P'
    unfold frsF
    split_ifs with hw
    · show (PtY.mv q (q.1.1.deco.up P (Pr.T u : 𝓞 X.E) x)).1.1.deco.1.liftFr ⟨P'.1, hw⟩ = q.1.1.deco.1.liftFr ⟨P'.1, hw⟩
      rw [h.1]
      unfold Deco.liftFr
      rw [key ⟨P'.1, hw⟩]
      rfl
    · show (PtY.mv q (q.1.1.deco.up P (Pr.T u : 𝓞 X.E) x)).1.1.1.2 _ = q.1.1.1.2 _
      rw [h.2.1]
  funext P'
  unfold cosetIn
  rw [hfr, h.2.2]

end GlobalTheory.Mem.Col2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigensystemCarriedByFiniteTypeOfMeetsLevelRowsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigensystem_carried_by_finiteType_of_meets_level_rows : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (c : Pl D.host.E → List ℤ → ℂ) (b : Bool) (x : R.HE.H), x ≠ 0 → x ∈ R.EEc c → R.HE.e x ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 b) → ∃ p, R.Carries p c := by
  first | exact @GlobalTheory.Mem.R3.LabCarry.carried | exact GlobalTheory.Mem.R3.LabCarry.carried | (intros; apply GlobalTheory.Mem.R3.LabCarry.carried <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDictionaryCoreLawsBaseFrameChangeStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dictionary_core_laws_baseFrame_change : ∀ (D : D7) (T : CoreJ D) (x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), VolTieG D → LawsJ T → LawsCore T.toCore → (∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (x₀ j σ)) → ∃ dict, LawsJ (reCore T dict T.mu T.chiW x₀ T.cE) ∧ LawsCore (reCore T dict T.mu T.chiW x₀ T.cE).toCore := by
  first | exact @GlobalTheory.BaseFrameChange.exists_dict_of_x0Orth | exact GlobalTheory.BaseFrameChange.exists_dict_of_x0Orth | (intros; apply GlobalTheory.BaseFrameChange.exists_dict_of_x0Orth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRatSecOfPull
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar
open scoped Pointwise

namespace GlobalTheory.TrueGeo.SmallSec

variable {F : Type} [Field F] [NumberField F]

section Local

variable {Z : Scheme.{0}} [IsIntegral Z] {D : CartierDiv Z} {x : Z} {u g : Z.functionFieldˣ}
  {f : Z.functionField} {k τ : ℕ}

end Local

variable {C : CxSt F} {Y : Var F} (A : Adl C Y) {k τ : ℕ} {f : Y.Fn}

theorem isRatSec_pow {Z : Scheme.{0}} [IsIntegral Z] {L : LB Z} {r : L.ι → Z.functionFieldˣ}
    (hr : IsRatSec L r) (τ : ℕ) : IsRatSec (lbPow L τ) fun c => r (c PUnit.unit) ^ τ :=
  fun c c' h => by
  have l : (lbPow L τ).U c ⊓ (lbPow L τ).U c' ≤ L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit) :=
    fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have e : (lbPow L τ).g c c' = res l (L.g (c PUnit.unit) (c' PUnit.unit)) ^ τ := by
    change ∏ _k : PUnit, _ = _
    refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
    rfl
  rw [e, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow,
    ← mul_pow, hr _ _ (l h)]
  exact congrArg (fun a => (a * _) ^ τ) (fnOf_resG l h _).symm


end GlobalTheory.TrueGeo.SmallSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeOverSplitNotMemConjStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_over_split_not_mem_conj : ∀ (R : Ranks) (H : Host R) (p : ℕ), p.Prime → Th.SplitK H p → ∃ (𝔭 : HeightOneSpectrum (𝓞 H.K)) (α β : 𝓞 H.K), (p : 𝓞 H.K) ∈ 𝔭.asIdeal ∧ α ∈ 𝔭.asIdeal ∧ β ∉ 𝔭.asIdeal ∧ (β : H.K) = HostK.conjK H α := by
  first | exact @GlobalTheory.Mem.Col2.SplitPrime.exists_prime_not_conj | exact GlobalTheory.Mem.Col2.SplitPrime.exists_prime_not_conj | (intros; apply GlobalTheory.Mem.Col2.SplitPrime.exists_prime_not_conj <;> assumption)
end

