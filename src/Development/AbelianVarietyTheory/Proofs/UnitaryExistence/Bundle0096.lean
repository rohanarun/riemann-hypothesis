module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0087

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointArithmeticGroupInvariantSig
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem wchar_ex_sign {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) {S : Type} [CommRing S] (t : Ix Dw → Sˣ) (h0 : (t none : S) ^ 2 = 1)
    (h1 : ∀ p, t (some p) = 1) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hn : Even n) : wchar (ex Dw a n) t = 1 := by
  obtain ⟨m, rfl⟩ := hn
  unfold wchar
  rw [Fintype.prod_option]
  simp only [h1, Units.val_one, one_pow, Finset.prod_const_one, mul_one]
  show (t none : S) ^ (m + m) = 1
  rw [← two_mul, pow_mul, h0, one_pow]

theorem normUn_gamma : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (k : Fin F.n) (T : ThetaData e F M k), GoodEmb c σ → ModelBase M → NegXi M → IsNormUn T (un k) → ∀ γ ∈ (M.X k).Γ, ∀ (x : (M.X k).dom) (h : lact γ x.1 ∈ (M.X k).dom), ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧ ∀ a n, Dom a n → toC (wchar (ex Dw a n) t) = 1 := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M un k T hσ hM hN hun γ hγ x h
  obtain ⟨gam, hgam, hP⟩ := GlobalTheory.per_gam E H Dw l Xo c σ g e F r M hσ hM hN k T.Pf T.per γ hγ
  obtain ⟨κ, hκ, hy⟩ := hun x
  obtain ⟨κ', hκ', hy'⟩ := hun ⟨_, h⟩
  have hb : T.co.symm x.1 ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm x.1) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact x.2
  have hb' : T.co.symm (lact γ x.1) ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm (lact γ x.1)) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact h
  obtain ⟨hx, hd, t₀, hsec, ht⟩ := _root_.GlobalTheory.ThetaPtChg.thetaPt_change hS E H Dw l Xo c σ g e F r M k T _ hb _ hb' κ κ' (un k x)
    (un k ⟨_, h⟩) gam 1 hy hy' hgam (fun a => by
      rw [T.co.apply_symm_apply, T.co.apply_symm_apply, Matrix.one_mulVec]; exact hP x.1 x.2 a)
  have hu : ∀ τ i, (un k ⟨_, h⟩).u τ i = (un k x).u τ i := fun τ i => by
    have h1 := hd τ i
    rw [inv_one, Matrix.one_mulVec] at h1
    exact ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k _ (T.isPer _ hb)).2.1 _).unique h1 (hy.2.1 τ i)
  have hC : (normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : relab c σ (e j).1 (M.X k).ξ0 ≠ 0 := (map_ne_zero _).2 (M.X k).ξ0_ne
    positivity
  have ht2 : toC (t₀ : CAt σ) ^ 2 = 1 := by
    have d1 := (T.norm _ hb).1.ne_zero
    have d2 := (T.norm _ hb').1.ne_zero
    rw [hκ, hκ', Matrix.det_one, mul_one] at ht
    refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hC d1) d2) ?_
    rw [ht]; ring
  refine ⟨fun i => i.elim t₀ fun _ => 1, ?_, fun a n hn => ?_⟩
  · refine (frBor_iff_frChg _ _ _).2 ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne,
      fun τ i => Matrix.one_apply_eq i, hx, fun τ i => ?_, hsec⟩
    rw [hu]
    exact (_root_.GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c (CAt σ) (un k x) (un k x) (un k x)).1.2.1 τ i
  · exact wchar_ex_sign Dw _ ht2 (fun _ => rfl) a n hn.2

end GlobalTheory.FrameUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointTriangularFrameWeightRule
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.NormUnBor

theorem diag_ne_zero {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (A : Matrix (Fin g) (Fin g) ℂ) (hA : A.det ≠ 0)
    (htri : ∀ j j', A j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) (j : Fin g) : A j j ≠ 0 := by
  have hdet : A.det = ∏ i, A i i := by
    rw [Matrix.det_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin g))]
    · simp
    · intro s _ hs
      by_contra hne
      have hp : ∏ i, A (s i) i ≠ 0 := fun h0 => hne (by rw [h0, smul_zero])
      have hall : ∀ i, A (s i) i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hp i (Finset.mem_univ i)
      have hsum : ∑ i, ((e (s i)).2 : ℕ) = ∑ i, ((e i).2 : ℕ) :=
        Equiv.sum_comp s (fun i => ((e i).2 : ℕ))
      have heq := (Finset.sum_eq_sum_iff_of_le (fun i _ => (htri _ _ (hall i)).2)).1 hsum
      apply hs
      ext i
      have h1 := (htri _ _ (hall i)).1
      have h2 := heq i (Finset.mem_univ i)
      have : e (s i) = e i := Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
      simp [e.injective this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hdet] at hA
  exact Finset.prod_ne_zero_iff.1 hA j (Finset.mem_univ j)

theorem col_eq_sum {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (A : Matrix (Fin g) (Fin g) ℂ)
    (htri : ∀ j j', A j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) (τ : T) (i : Fin (m τ)) :
    ∑ i' : Fin (m τ), A (e.symm ⟨τ, i'⟩) (e.symm ⟨τ, i⟩) • (Pi.single (e.symm ⟨τ, i'⟩) (1 : ℂ) : Fin g → ℂ) =
      A *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1 := by
  funext p
  obtain ⟨⟨τ', i'⟩, rfl⟩ := e.symm.surjective p
  rw [Matrix.mulVec_single_one, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
  by_cases hτ : τ' = τ
  · subst hτ
    rw [Finset.sum_eq_single i']
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne, mul_zero]
      intro h
      exact hj (sigma_mk_injective (β := fun τ => Fin (m τ)) (e.symm.injective h)).symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · have h0 : A (e.symm ⟨τ', i'⟩) (e.symm ⟨τ, i⟩) = 0 := by
      by_contra hne
      have := (htri _ _ hne).1
      rw [e.apply_symm_apply, e.apply_symm_apply] at this
      exact hτ this
    rw [h0]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Pi.single_eq_of_ne, mul_zero]
    intro h
    exact hτ (congrArg Sigma.fst (e.symm.injective h))

theorem normConst_ne_zero {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) {ξ₀ : E} (h : ξ₀ ≠ 0) :
    (normConst ty ξ₀ : ℂ) ≠ 0 := by
  refine Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (div_pos (by positivity) ?_)).ne'
  exact Finset.prod_pos fun j _ => mul_pos two_pos (norm_pos_iff.2 ((map_ne_zero _).2 h))

theorem normUn_bor : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (k : Fin F.n) (T : ThetaData e F M k), GoodEmb c σ → ModelBase M → NegXi M → IsNormUn T (un k) → ∀ (x : (M.X k).dom) b (_hb : b ∈ Bor (M.X k).Ψ r) (h : rmul x.1 b ∈ (M.X k).dom), ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧ ∀ a n, Dom a n → toC (wchar (ex Dw a n) t) = bchar (laU (unfOf e F M un) a n k) b := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M un k T hG hB hN hU x b hb h
  obtain ⟨h₀, hdet, hP, htri, -, -, hw⟩ :=
    _root_.GlobalTheory.per_bor E H Dw l Xo c σ g e F r M hG hB hN k T.Pf T.per x.1 x.2 b hb
  obtain ⟨κ, hκ, hy⟩ := hU x
  obtain ⟨κ', hκ', hy'⟩ := hU ⟨_, h⟩
  have hx : T.co.symm x.1 ∈ T.co ⁻¹' (M.X k).dom := by
    simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using x.2
  have hx' : T.co.symm (rmul x.1 b) ∈ T.co ⁻¹' (M.X k).dom := by
    simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using h
  obtain ⟨hxx, hder, t₀, hsec, ht₀⟩ := _root_.GlobalTheory.ThetaPtChg.thetaPt_change hS E H Dw l Xo c σ g e F r M k T _ hx _ hx' κ κ' _ _
    (LinearEquiv.refl _ _) h₀ hy hy'
    ⟨fun _ _ => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩⟩
    (fun a => by
      simp only [ContinuousLinearEquiv.apply_symm_apply, LinearEquiv.refl_apply]
      exact hP a)
  have hsq : toC (t₀ : CAt σ) ^ 2 * h₀.det = 1 := by
    have hc := normConst_ne_zero (fun j => relab c σ (e j).1) (M.X k).ξ0_ne
    have h1 := (T.norm _ hx).1.ne_zero
    have h2 := (T.norm _ hx').1.ne_zero
    rw [hκ, hκ'] at ht₀
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hc h1) h2)
    linear_combination ht₀
  have hinv : (h₀⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det h₀ hdet).ne_zero
  have hdiag := diag_ne_zero e h₀⁻¹ hinv htri
  let d : Fin g → (CAt σ)ˣ := fun j => (Units.mk0 (h₀⁻¹ j j) (hdiag j) : ℂˣ)
  let t : Ix Dw → (CAt σ)ˣ := fun o => Option.elim o t₀ (fun p => d (e.symm p))
  refine ⟨t, ⟨hxx, fun τ i => ⟨fun i' => (h₀⁻¹ (e.symm ⟨τ, i'⟩) (e.symm ⟨τ, i⟩) : ℂ), rfl, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro j hj
    by_contra hne
    have := (htri _ _ hne).2
    rw [e.apply_symm_apply, e.apply_symm_apply] at this
    exact absurd hj (not_lt.2 this)
  · rw [hy.1]
    refine (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k _ (T.isPer _ hx) _ _ _ (hy.2.1 τ) _ _).2 ?_
    rw [col_eq_sum e h₀⁻¹ htri]
    exact hder τ i
  · obtain ⟨pm, h1, h2, h3⟩ := hsec
    refine ⟨pm, h1, ?_, h3⟩
    rw [h2]
    simp [spMap]
  · intro a n hD
    rw [← hw un a n (toC (t₀ : CAt σ)) hD.2 hsq]
    show (∏ o : Ix Dw, toC ((t o : (CAt σ)ˣ) : CAt σ) ^ ex Dw a n o) = _
    rw [Fintype.prod_option, mul_comm]
    congr 1
    rw [← Equiv.prod_comp e]
    refine Finset.prod_congr rfl fun j _ => ?_
    show h₀⁻¹ (e.symm (e j)) (e.symm (e j)) ^ a ((e j).1, (e j).2) = _
    rw [e.symm_apply_apply]

end GlobalTheory.NormUnBor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.OneMemSecAndSecInfEqBot
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.SecSeparation

theorem exists_frBor {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (t : Ix Dw → Sˣ) : ∃ y' : FrPt Xo c S, FrBor t y y' := by
  classical
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S y
    (fun τ => Matrix.diagonal fun i => (t (some ⟨τ, i⟩) : S)) (t none) (fun τ => by
      rw [Matrix.det_diagonal]
      exact IsUnit.prod_univ_iff.2 fun i => Units.isUnit _)
  refine ⟨y', ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S y y' y').1 t).2 ⟨_, ?_, ?_, hy'⟩⟩
  · intro τ i j hij
    exact Matrix.diagonal_apply_ne _ hij.ne
  · intro τ i
    exact Matrix.diagonal_apply_eq _ _

end GlobalTheory.SecSeparation

namespace GlobalTheory

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PointsDetectFrobeniusSections
section
noncomputable section

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GeometricValues

theorem eq_zero_of_forall_algClosed {K R : Type} [Field K] [CommRing R] [Algebra K R] [IsReduced R] (x : R)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (φ : R →ₐ[K] Ω), φ x = 0) : x = 0 := by
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  let φ : R →ₐ[K] AlgebraicClosure (FractionRing (R ⧸ J)) :=
    (IsScalarTower.toAlgHom K (FractionRing (R ⧸ J)) (AlgebraicClosure (FractionRing (R ⧸ J)))).comp
      ((IsScalarTower.toAlgHom K (R ⧸ J) (FractionRing (R ⧸ J))).comp (Ideal.Quotient.mkₐ K J))
  have h0 := h _ φ
  have h1 : algebraMap (R ⧸ J) (FractionRing (R ⧸ J)) (Ideal.Quotient.mk J x) = 0 := by
    apply (algebraMap (FractionRing (R ⧸ J)) (AlgebraicClosure (FractionRing (R ⧸ J)))).injective
    rw [map_zero]
    exact h0
  have h2 : Ideal.Quotient.mk J x = 0 := by
    apply IsFractionRing.injective (R ⧸ J) (FractionRing (R ⧸ J))
    rw [map_zero]
    exact h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

theorem ptsDetect_of {K : Type} [Field K] {ι : Type} [Fintype ι]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
    (hW : EvalWD pts mapR)
    (hB : ∀ (S : Type) [CommRing S] [Algebra K S] (T : Type) [CommRing T] [Algebra K T] (φ : S →ₐ[K] T)
      (y : pts S), ∃ z : pts T, mapR φ y z)
    (e : ι → ℕ) : PtsDetect pts mapR borR e := by
  intro g hg h
  funext p y
  have : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).mp p.rad
  refine eq_zero_of_forall_algClosed (K := K) (g p y) ?_
  intro Ω _ _ _ φ
  obtain ⟨z, hz⟩ := hB p.R Ω φ y
  have hT : FromTest pts mapR z := ⟨p, φ, y, hz⟩
  have h0 := h Ω z
  unfold evalAt at h0
  rw [dite_eq_left hT] at h0
  rw [← h0]
  exact hW g hg.1 Ω p _ φ _ y _ z hz hT.choose_spec.choose_spec.choose_spec

end GeometricValues

theorem ptsDetect_framed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), PtsDetect (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y') (ex Dw a n) := by
  intro E _ _ _ H Dw l Xo c a n
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  exact GeometricValues.ptsDetect_of (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
    (fun t y y' => FrBor t y y') (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.2.1
    (fun S _ _ T _ _ φ y => GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c S T φ y) (ex Dw a n)

end GlobalTheory.Frames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SupNormDefiniteOnCuspFormsGoodEmbedding
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

theorem SupNormCusp.eq_zero_of_pnorm_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    (hx : x ∈ X.dom) (h : X.pnorm la P x = 0) : P x = 0 := by
  have hx' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  have hd : ∀ τ i, dmin X.Gm x τ i ≠ 0 := by
    intro τ i h0
    have := (hx' τ).2 i
    rw [h0] at this
    simp at this
  unfold Data.pnorm at h
  rcases mul_eq_zero.1 h with h1 | h1
  · exact norm_eq_zero.1 h1
  · exfalso
    refine (ne_of_gt ?_) h1
    refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
    exact norm_pos_iff.2 (div_ne_zero (hd τ _) (hd τ _))

theorem supNorm_definite_on_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → Formalism.L2.PjFree.SupDef Xo c U := by
  intro E _ _ _ H Dw l Xo c r U hU a n hd σ hσ f hf h0
  refine (_root_.GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c σ r (U σ) (hU σ hσ) a n).2 f
    (Formalism.L2.PjFree.cusp_le_sec Xo c U a n hf) fun k x hx => ?_
  have hfin := Formalism.L2.PjFree.supE_cusp_ne_top hσ hf
  have hE : Formalism.L2.PjFree.supE (U σ).X (Formalism.L2.PjFree.laU (U σ) a n) (Formalism.L2.PjFree.rdU (U σ) f) = 0 := by
    unfold Formalism.L2.PjFree.supN at h0
    rcases ENNReal.toReal_eq_zero_iff _ |>.1 h0 with h1 | h1
    · exact h1
    · exact absurd h1 hfin
  have hle : ENNReal.ofReal (((U σ).X k).pnorm (Formalism.L2.PjFree.laU (U σ) a n k)
      (Formalism.L2.PjFree.rdU (U σ) f k) x) ≤ 0 := by
    rw [← hE]
    exact le_iSup (fun p : Formalism.L2.PjFree.FPt (U σ).X => ENNReal.ofReal (((U σ).X p.1).pnorm
      (Formalism.L2.PjFree.laU (U σ) a n p.1) (Formalism.L2.PjFree.rdU (U σ) f p.1) p.2)) ⟨k, ⟨x, hx⟩⟩
  have hp : ((U σ).X k).pnorm (Formalism.L2.PjFree.laU (U σ) a n k) (Formalism.L2.PjFree.rdU (U σ) f k) x = 0 := by
    refine le_antisymm (ENNReal.ofReal_eq_zero.1 (le_antisymm hle zero_le)) ?_
    unfold Data.pnorm
    exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _)
  exact SupNormCusp.eq_zero_of_pnorm_eq_zero _ _ _ x hx hp

end GlobalTheory
end

