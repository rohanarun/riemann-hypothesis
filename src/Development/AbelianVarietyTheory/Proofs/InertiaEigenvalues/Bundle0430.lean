module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0393
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceCoefficientRing
section
noncomputable section

namespace GlobalTheory.ComplementCompare

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N ReciprocityTheory.Gal
open GlobalTheory.IndefiniteRowSideFullHecke

section General

variable {k Γ : Type} [Field k] [Group Γ]

theorem semisimple_congr {V W : Type} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k Γ V} {σ : Representation k Γ W} (e : V ≃ₗ[k] W)
    (he : ∀ g v, e (ρ g v) = σ g (e v)) :
    ρ.IsSemisimpleRepresentation ↔ σ.IsSemisimpleRepresentation := by
  have he' : ∀ g w, e.symm (σ g w) = ρ g (e.symm w) := fun g w => by
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
  let o : Subrepresentation ρ ≃o Subrepresentation σ :=
    { toFun := fun P => ⟨P.toSubmodule.comap e.symm.toLinearMap, fun g w hw => by
        change e.symm (σ g w) ∈ P.toSubmodule
        rw [he']
        exact P.apply_mem_toSubmodule g hw⟩
      invFun := fun Q => ⟨Q.toSubmodule.comap e.toLinearMap, fun g v hv => by
        change e (ρ g v) ∈ Q.toSubmodule
        rw [he]
        exact Q.apply_mem_toSubmodule g hv⟩
      left_inv := fun P => by ext v; simp
      right_inv := fun Q => by ext w; simp
      map_rel_iff' := by
        intro P Q
        constructor
        · intro h v hv
          have := @h (e v) (by
            change e.symm (e v) ∈ P.toSubmodule
            rw [e.symm_apply_apply]
            exact hv)
          change e.symm (e v) ∈ Q.toSubmodule at this
          rw [e.symm_apply_apply] at this
          exact this
        · intro h w hw
          exact @h (e.symm w) hw }
  exact OrderIso.complementedLattice_iff o

theorem isCompl_sub_iff {V : Type} [AddCommGroup V] [Module k V] {ρ : Representation k Γ V}
    (P Q : Subrepresentation ρ) : IsCompl P Q ↔ IsCompl P.toSubmodule Q.toSubmodule := by
  rw [isCompl_iff, isCompl_iff, disjoint_iff, disjoint_iff, codisjoint_iff, codisjoint_iff,
    ← Subrepresentation.toSubmodule_injective.eq_iff, ← Subrepresentation.toSubmodule_injective.eq_iff]
  rfl

theorem isSSRep_iff {a : ℕ} (ρ : Γ →* GL (Fin a) k) :
    IsSSRep ρ ↔ (glRep ρ).IsSemisimpleRepresentation := by
  constructor
  · intro h
    refine ⟨fun P => ?_⟩
    obtain ⟨W', h1, h2⟩ := h P.toSubmodule fun g v hv => P.apply_mem_toSubmodule g hv
    exact ⟨⟨W', fun g v hv => h1 g v hv⟩, (isCompl_sub_iff _ _).2 h2⟩
  · intro h W hW
    obtain ⟨Q, hQ⟩ := h.exists_isCompl ⟨W, fun g v hv => hW g v hv⟩
    exact ⟨Q.toSubmodule, fun g v hv => Q.apply_mem_toSubmodule g hv, (isCompl_sub_iff _ _).1 hQ⟩

variable {O : Type} [CommRing O] [IsDomain O]

theorem fracRep_eq {a : ℕ} (r : Γ →* GL (Fin a) O) :
    BlockRepresentationsSemisimple.fracRep r = RepresentationOverSumChar.repOver (FractionRing O) ((Units.coeHom _).comp r) := rfl

theorem sum_equivariant {a : ℕ} (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) (g : Γ)
    (v : Fin a ⊕ Fin t → FractionRing O) :
    LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin t) (FractionRing O) (FractionRing O)
        (RepresentationOverSumChar.repOver (FractionRing O) (RepresentationOverSumChar.blockSum t ρ χ) g v) =
      BlockRepresentationsSemisimple.blockRep ρ χ t g
        (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin t) (FractionRing O) (FractionRing O) v) := by
  rw [BlockRepresentationsSemisimple.blockRep_apply]
  have key : ∀ s : Fin a ⊕ Fin t, RepresentationOverSumChar.repOver (FractionRing O) (RepresentationOverSumChar.blockSum t ρ χ) g v s =
      ∑ s' : Fin a ⊕ Fin t, algebraMap O (FractionRing O)
        (Matrix.fromBlocks ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O) 0 0
          (Matrix.diagonal fun c : Fin t => ((χ (c.1 + 1) g : Oˣ) : O)) s s') * v s' := fun s => rfl
  refine Prod.ext (funext fun j => ?_) (funext fun c => ?_)
  · refine (key (Sum.inl j)).trans ?_
    simp [Fintype.sum_sum_type, Matrix.mulVec, dotProduct]
  · refine (key (Sum.inr c)).trans ?_
    simp [Fintype.sum_sum_type, Matrix.diagonal_apply, apply_ite]

theorem trace_repOver {n : Type} [Fintype n] [DecidableEq n] (M : Γ →* Matrix n n O) (g : Γ) :
    LinearMap.trace _ _ (RepresentationOverSumChar.repOver (FractionRing O) M g) =
      algebraMap O (FractionRing O) (M g).trace := by
  change LinearMap.trace _ _ (Matrix.toLin' ((M g).map (algebraMap O (FractionRing O)))) = _
  rw [Matrix.trace_toLin'_eq, AddMonoidHom.map_trace]

omit [IsDomain O] in
theorem trace_eq_of_charpoly_eq [Nontrivial O] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (A : Matrix m m O) (B : Matrix n n O) (h : A.charpoly = B.charpoly) :
    A.trace = B.trace := by
  rw [Matrix.trace_eq_neg_charpoly_nextCoeff, Matrix.trace_eq_neg_charpoly_nextCoeff, h]

end General

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

theorem ss_iff (i : N.Loc) (ρ : GE N →* GL (Fin R.r) (N.O i)) :
    BlockRepresentationsSemisimple.BlockSemisimple ρ (N.chi i) R.t ↔ RepresentationOverSumChar.IsSSSum N i ρ :=
  (semisimple_congr _ (sum_equivariant ρ (N.chi i) R.t)).symm

theorem isoBlock_iff (i : N.Loc) (r₀ : GE N →* GL (Fin R.nV) (N.O i)) (ρ : GE N →* GL (Fin R.r) (N.O i)) :
    BlockRepresentationsSemisimple.IsoBlock r₀ ρ (N.chi i) R.t ↔ RepresentationOverSumChar.SplitsAs N i r₀ ρ := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e.trans (LinearEquiv.sumArrowLequivProdArrow _ _ _ _).symm, fun g u => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
    refine (he g u).trans ?_
    refine Eq.trans ?_ (sum_equivariant ρ (N.chi i) R.t g _).symm
    rw [LinearEquiv.apply_symm_apply]
  · rintro ⟨e, he⟩
    refine ⟨e.trans (LinearEquiv.sumArrowLequivProdArrow _ _ _ _), fun g u => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, fracRep_eq, he g u]
    exact sum_equivariant ρ (N.chi i) R.t g _

theorem isHeckeGalois_iff (i : N.Loc) (x : N.X i) (r : GE N →* GL (Fin R.nV) (N.O i)) :
    IsHeckeGalois N i x r ↔ RepresentationOverSumChar.IsRx N i x ((Units.coeHom _).comp r) :=
  and_congr Iff.rfl (and_congr (isSSRep_iff _) Iff.rfl)

theorem second_of_first (i : N.Loc) (π : N.X i) (r₀ : GE N →* GL (Fin R.nV) (N.O i))
    (ρ : GE N →* GL (Fin R.r) (N.O i)) (hr : IsHeckeGalois N i π r₀)
    (h : BlockRepresentationsSemisimple.IsComplement N i r₀ ρ) : RepresentationOverSumChar.IsComplement N i π ρ :=
  ⟨RepresentationOverSumChar.isRhoAt_of_splitsAs N i π r₀ ρ hr.2.2 ((isoBlock_iff N i r₀ ρ).1 h.rho),
    (ss_iff N i ρ).1 h.ss, h.cont⟩

theorem exists_conj_ne (H : Host R) : ∃ x y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) ∧ y - x ≠ 0 := by
  by_contra hc
  push Not at hc
  have h1 : ∀ x : 𝓞 H.E, H.conj (x : H.E) = x := fun x => by
    have := hc x ⟨H.conj x, (RingOfIntegers.isIntegral_coe x).map (H.conj.toAlgHom.restrictScalars ℤ)⟩ rfl
    exact congrArg (fun z : 𝓞 H.E => (z : H.E)) (sub_eq_zero.1 this)
  have h2 : ∀ z : H.E, H.conj z = z := fun z => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 H.E) z
    rw [map_div₀]
    exact congrArg₂ (· / ·) (h1 a) (h1 b)
  have := H.isCMField_hostE
  refine IsTotallyComplex.complexEmbedding_not_isReal H.φ₀ (ComplexEmbedding.isReal_iff.2 ?_)
  ext z
  exact (H.conjE_apply H.φ₀ z).symm.trans (congrArg H.φ₀ (h2 z))

theorem exists_int_sub_mem {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))
    (hv : v.asIdeal.inertiaDeg ℤ = 1) (x : 𝓞 E) : ∃ n : ℤ, x - n ∈ v.asIdeal := by
  have := v.isPrime
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  have hp := Nat.absNorm_under_prime v.asIdeal
  have h := Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under ℤ) v.asIdeal
  rw [hv, pow_one] at h
  rw [h] at hp
  have : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨hp⟩
  have hc : Nat.card (𝓞 E ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal :=
    (Ideal.absNorm_eq_natCard v.asIdeal).symm
  have : Nontrivial (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.2 v.isPrime.ne_top
  have hm := mem_zmultiples_of_prime_card hc (g := (1 : 𝓞 E ⧸ v.asIdeal)) (g' := Ideal.Quotient.mk _ x)
    one_ne_zero
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hm
  refine ⟨n, Ideal.Quotient.eq.1 ?_⟩
  rw [← hn]
  simp

theorem eq_univ_of_frob (hC : GlobalTheory.TwSys.Cheb) (i : N.Loc) (s : Set (GE N)) (hs : IsClosed s)
    (h : ∀ w : PlE H, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : GE N),
      IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ → σ ∈ s) (g : GE N) : g ∈ s := by
  classical
  by_contra hg
  have : IsGalois H.E N.Om := {}
  have hn : (fun u : GE N => u * g) ⁻¹' sᶜ ∈ nhds (1 : GE N) :=
    (hs.isOpen_compl.preimage (continuous_mul_const g)).mem_nhds (by simpa using hg)
  obtain ⟨L, hfd, hN, hL⟩ := (krullTopology_mem_nhds_one_iff_of_normal H.E N.Om _).1 hn
  have hgal : IsGalois H.E L := {}
  obtain ⟨x, y, hxy, hne⟩ := exists_conj_ne H
  have f1 : {v : PlE H | v.asIdeal ∣ Ideal.span {y - x}}.Finite :=
    Ideal.finite_factors (by simpa using hne)
  have f2 : {v : PlE H | v.asIdeal ∣ Ideal.span {((N.l i : ℕ) : 𝓞 H.E)}}.Finite :=
    Ideal.finite_factors (by simpa using (N.lPrime i).out.ne_zero)
  obtain ⟨v, hv, hf, -, B, hB, -, σ, hσ, hU⟩ := hC H.E N.Om L.fixingSubgroup L.fixingSubgroup_isOpen
    ((InfiniteGalois.normal_iff_isGalois L).2 hgal) g (f1.toFinset ∪ f2.toFinset ∪ N.S i ∪ N.Q i)
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton,
    not_or] at hv
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hv
  obtain ⟨n, hx⟩ := exists_int_sub_mem v hf x
  have hsplit : IsSplitPl H v := by
    refine ⟨x - n, hx, fun z hz hzv => h1 ?_⟩
    have hz' : z = y - n := by
      apply RingOfIntegers.ext
      rw [hz]
      simp [hxy]
    have := v.asIdeal.sub_mem hzv hx
    rwa [hz', sub_sub_sub_cancel_right] at this
  have := hL hU
  simp only [Set.mem_preimage, inv_mul_cancel_right, Set.mem_compl_iff] at this
  exact this (h v ⟨hsplit, h2, h3, h4⟩ B σ hB hσ)

theorem t2Space_coefficientRing (i : N.Loc) : T2Space (N.O i) :=
  have := N.O_complete i
  (N.O_adic i).isHausdorff_iff.1 inferInstance

theorem isRx_unique (hC : GlobalTheory.TwSys.Cheb) (i : N.Loc) (x : N.X i) {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (M : GE N →* Matrix m m (N.O i)) (M' : GE N →* Matrix n n (N.O i))
    (h : RepresentationOverSumChar.IsRx N i x M) (h' : RepresentationOverSumChar.IsRx N i x M') :
    ∃ e : (m → KK N i) ≃ₗ[KK N i] (n → KK N i), ∀ g u,
      e (RepresentationOverSumChar.repOver (KK N i) M g u) = RepresentationOverSumChar.repOver (KK N i) M' g (e u) := by
  have := t2Space_coefficientRing N i
  have : CharZero what₂.LL := what₂.embLL.charZero
  have : CharZero (FractionRing (N.O i)) :=
    (N.embK i).charZero_iff (N.embK i).injective |>.1 inferInstance
  refine GlobalTheory.TraceIso.exists_equiv_of_trace_eq _ _ h.2.1 h'.2.1 fun g => ?_
  rw [trace_repOver, trace_repOver]
  congr 1
  refine eq_univ_of_frob N hC i {g | (M g).trace = (M' g).trace}
    (isClosed_eq h.1.matrix_trace h'.1.matrix_trace) (fun w hw B σ hB hσ => ?_) g
  exact trace_eq_of_charpoly_eq _ _ ((h.2.2 w hw B σ hB hσ).trans (h'.2.2 w hw B σ hB hσ).symm)

end GlobalTheory.ComplementCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorDeRhamCoordMulGaloisAction
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

noncomputable section
namespace GlobalTheory.HodgeAt

theorem PhiS_act : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L : FinExt l) (σ : GQ l) (a : ℕ) (r : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), (∀ g v, R g v = (r g).val *ᵥ v) → ∀ g : ↥(GK K), (∀ y : ↥L.1, (g : GQ l) (σ (y : Om l)) = σ (y : Om l)) → ∀ x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR, PhiS P σ L a (actVdR (P.PD K) R g x) = ((r g).val.map fun y => algebraMap (Om l) P.R.BdR (σ (y : Om l))) *ᵥ fun i => P.actQdR (g : GQ l) (PhiS P σ L a x i) := by
  intro l _ P K L σ a r R hR g hg x
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, PhiS_zero, Pi.zero_apply]
    exact (Matrix.mulVec_zero _).symm
  | add x y hx hy =>
    rw [map_add (f := _), PhiS_add, hx, hy, PhiS_add]
    rw [← Matrix.mulVec_add]
    congr 1
    ext i
    simp only [Pi.add_apply, map_add]
  | tmul v b =>
    rw [GlobalTheory.DRFil.actVdR_tmul, P.PD_actdR, hR, PhiS_tmul, PhiS_tmul]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [IntermediateField.coe_sum, IntermediateField.coe_mul, map_sum, map_mul, Finset.sum_mul,
      P.actQdR_Om, hg, mul_assoc]

end GlobalTheory.HodgeAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TieConclusion
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
open scoped ENNReal

namespace GlobalTheory.Proof.QuotientLengthInfimum

open GlobalTheory.IndefiniteRowSideFullHecke

theorem length_quot_eq_iInf {O : Type} [CommRing O] [IsPrincipalIdealRing O] (I : Ideal O) :
    Module.length O (O ⧸ I) = ⨅ x ∈ I, Module.length O (O ⧸ Ideal.span {x}) := by
  apply le_antisymm
  · refine le_iInf₂ fun x hx => ?_
    have hle : Ideal.span {x} ≤ I := (Ideal.span_singleton_le_iff_mem _).2 hx
    exact Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
  · have hg : Ideal.span {Submodule.IsPrincipal.generator I} = I :=
      Ideal.span_singleton_generator I
    refine iInf₂_le_of_le (Submodule.IsPrincipal.generator I)
      (Submodule.IsPrincipal.generator_mem I) ?_
    rw [hg]

theorem mem_ccAt {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (Z : Finset X) (π : X) (y : O) :
    y ∈ ccAt T Z π ↔ ∃ f ∈ ccIdeal T Z, ((f : T) : X → O) π = y := by
  have hs : Function.Surjective ((Pi.evalRingHom (fun _ : X => O) π).comp T.val.toRingHom) :=
    fun a => ⟨algebraMap O T a, by simp⟩
  unfold ccAt
  rw [Ideal.mem_map_iff_of_surjective _ hs]
  rfl

theorem div_le_iff_lengths (e c s h v q : ℕ∞) (he0 : e ≠ 0) (he : e ≠ ⊤) :
    ((c : ℝ≥0∞) / (e : ℝ≥0∞) ≤ (s : ℝ≥0∞) / (e : ℝ≥0∞) + (h : ℝ≥0∞) + (v : ℝ≥0∞) + (q : ℝ≥0∞) / (e : ℝ≥0∞)) ↔
      c ≤ s + e * h + e * v + q := by
  have he0' : (e : ℝ≥0∞) ≠ 0 := by simpa using he0
  have he' : (e : ℝ≥0∞) ≠ ⊤ := by simpa using he
  rw [← ENat.toENNReal_le, ← ENNReal.mul_le_mul_iff_right he0' he']
  simp only [mul_add, ENNReal.mul_div_cancel he0' he', ENat.toENNReal_add, ENat.toENNReal_mul]

theorem toENNReal_sum {ι : Type} (s : Finset ι) (f : ι → ℕ∞) :
    ((∑ a ∈ s, f a : ℕ∞) : ℝ≥0∞) = ∑ a ∈ s, (f a : ℝ≥0∞) :=
  map_sum ENat.toENNRealRingHom f s

section Hyp

end Hyp

section Terms

variable (D : D7) (i : D.nd.Loc)

theorem ramLen_ne : SelmerSumLargePrime.ramLen D i ≠ 0 ∧ SelmerSumLargePrime.ramLen D i ≠ ⊤ := by
  have h := BaseSizes.vO_l D i
  unfold BaseSizes.vO BaseSizes.nlen at h
  change ((SelmerSumLargePrime.ramLen D i : ℕ∞) : ℝ≥0∞) / ((SelmerSumLargePrime.ramLen D i : ℕ∞) : ℝ≥0∞) = 1 at h
  constructor
  · intro h0; rw [h0] at h; simp at h
  · intro h0; rw [h0] at h; simp at h

theorem vCC_eq (π : D.nd.X i) :
    BaseSizes.vCC D i π = (SelmerSumLargePrime.ccLen D i π : ℝ≥0∞) / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) := by
  unfold BaseSizes.vCC BaseSizes.vO BaseSizes.nlen SelmerSumLargePrime.ccLen
  change ⨅ f ∈ D.nd.cc i, _ / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) = _
  apply le_antisymm
  · set I := ccAt (D.nd.T i) (D.nd.Z i) π with hI
    have hg : Ideal.span {Submodule.IsPrincipal.generator I} = I := Ideal.span_singleton_generator I
    obtain ⟨f, hf, hfx⟩ := (mem_ccAt _ _ π _).1 (Submodule.IsPrincipal.generator_mem I)
    refine iInf₂_le_of_le f hf ?_
    rw [hfx, hg]
  · refine le_iInf₂ fun f hf => ?_
    refine ENNReal.div_le_div_right ?_ _
    rw [ENat.toENNReal_le, length_quot_eq_iInf]
    exact iInf₂_le _ ((mem_ccAt _ _ π _).2 ⟨f, hf, rfl⟩)

theorem sPi_eq (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) :
    BaseSizes.sPi D i π ρ = (SelmerSumLargePrime.selLen D i ρ π : ℝ≥0∞) / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) := rfl

theorem shaSum_eq : BaseSizes.shaSum D i = (SelmerSumLargePrime.shaSum D i : ℝ≥0∞) := by
  unfold BaseSizes.shaSum SelmerSumLargePrime.shaSum
  rw [toENNReal_sum]

theorem vClass_eq :
    BaseSizes.vClass D i = (((padicValNat (D.nd.l i) (hE D.host) : ℕ) : ℕ∞) : ℝ≥0∞) := by
  unfold BaseSizes.vClass hE
  simp

theorem zetaP_eq (P : HeightOneSpectrum (𝓞 D.host.E)) : BaseSizes.zetaP D i P = SelmerSumLargePrime.zetaP D i P := rfl

theorem epsQ_eq : BaseSizes.epsQ D i = (SelmerSumLargePrime.twistLen D i : ℝ≥0∞) / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) := by
  unfold BaseSizes.epsQ SelmerSumLargePrime.twistLen BaseSizes.vO BaseSizes.nlen
  rw [ENat.toENNReal_mul, toENNReal_sum, mul_div_assoc, div_eq_mul_inv (∑ _ ∈ _, _), Finset.sum_mul]
  rfl

theorem conclusion_iff (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) :
    (BaseSizes.vCC D i π ≤ BaseSizes.sPi D i π ρ + BaseSizes.shaSum D i + BaseSizes.vClass D i + BaseSizes.epsQ D i) ↔
      SelmerSumLargePrime.ccLen D i π ≤ SelmerSumLargePrime.selLen D i ρ π + SelmerSumLargePrime.ramLen D i * SelmerSumLargePrime.shaSum D i +
        SelmerSumLargePrime.ramLen D i * (padicValNat (D.nd.l i) (hE D.host) : ℕ∞) + SelmerSumLargePrime.twistLen D i := by
  rw [vCC_eq, sPi_eq, shaSum_eq, vClass_eq, epsQ_eq]
  exact div_le_iff_lengths _ _ _ _ _ _ (ramLen_ne D i).1 (ramLen_ne D i).2

end Terms

end GlobalTheory.Proof.QuotientLengthInfimum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricCharacterIsCMHostValueDatum
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem toricCharacter_isCMHostValueDatum : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (s : ℕ), 1 ≤ s → (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 → IsHostDatum D.host (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 l j a) := by
  intro D Z hZ l j a s hs hN
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨hcm, hind⟩ := _root_.GlobalTheory.LamTie.CMType.phi_cmType D.R D.host
  obtain ⟨hκ, hinf⟩ := GlobalTheory.T.one_le_kap_and_lam0_hasInf D Z hZ l j a s hN
  obtain ⟨hu, ht⟩ := _root_.GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield D Z hZ l j a
  have hb : IsBaseCond (cond0 D.host Z.w0) :=
    _root_.GlobalTheory.LamTie.isBaseCond_cond0 D.R D.host Z.q0 Z.w0 (fun p hp P hP => by
      obtain ⟨h1, -, h3, h4⟩ := hZ.places.splits p hp
      exact _root_.GlobalTheory.LamTie.SplitBelow.splits_below_of_absNorm D.host.E p h1 h3 h4 P hP) hZ.places
  refine ⟨hcm, hind, hs, hκ, hb, hu, ht, hinf, fun v P hP => ⟨fun h => absurd h (Finset.notMem_empty v), fun _ => ?_⟩⟩
  have hv : v = below P := HeightOneSpectrum.ext (hP.symm.trans (over_below P))
  subst hv
  exact _root_.GlobalTheory.LamTie.lam0_expAt D Z hZ l j a P

end GlobalTheory.LamTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceEstimateScaledProductSpanLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_estimate_scaledProductSpanLattice : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (c N n : ℕ) (cs : Fin m → Om l), n ≤ N → (∀ g, ‖trc r g - ∑ k, cs k * trc (ρs k) g‖ ≤ ((l : ℝ)⁻¹) ^ (N + c)) → ∃ M₁ : ℕ, ∀ M, M₁ ≤ M → ∀ (F : Γ →₀ ℤ_[l]) (y : Fin m → Matrix (Fin a) (Fin a) (Om l)), y ∈ GlobalTheory.TraceConjugationCover.latL t M → ‖(F.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace - ∑ k, cs k * (((F.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) + y) k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
  first | (exact @GlobalTheory.trace_estimate_latL) | (exact GlobalTheory.trace_estimate_latL) | (intros; apply GlobalTheory.trace_estimate_latL  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeCompletionDegreeOneCountProof
section
noncomputable section

namespace GlobalTheory.Pass

open _root_.Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module

theorem stepDeg_main : StepDeg := fun D _ => GlobalTheory.TypeDegOne.degree_one D

end GlobalTheory.Pass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalSelmerCocycleMapAlgHom
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime

theorem univ_map : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (A : Type) [CommRing A] [Algebra (X.O0 i) A] (π : B →ₐ[X.O0 i] A) (κ : GE N →* Bˣ) (κ' : GE N →* Aˣ), (∀ g, ((κ' g : Aˣ) : A) = π (κ g : Bˣ)) → ∀ (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) B) Z, Univ bkP i s κ Q Φ Z → Univ bkP i s κ' Q (Φ.map π) (fun g => (Z g).map π) := by
  intro D N X bkP i s B _ _ A _ _ π κ κ' hκ Q a Φ Z hU Y _ _ _ _
  letI : Module B Y := Module.compHom Y π.toRingHom
  have hsm : ∀ (b : B) (y : Y), b • y = π b • y := fun _ _ => rfl
  obtain ⟨hrep, hsel⟩ := _root_.GlobalTheory.NewPrime.ScalarChange.selC_transfer D N X bkP i s B A π κ κ' hκ Y hsm
  obtain ⟨h1, h2, h3⟩ := hU Y
  have hm : ∀ x : Fin a → Y, matAct (Φ.map π) x = matAct Φ x := fun _ => rfl
  have hr : ∀ g (x : Fin a → Y), rect ((Z g).map π) x = rect (Z g) x := fun _ _ => rfl
  have hc : ∀ f, Cob (repOn (Tgl i s) κ Y) f ↔ Cob (repOn (Tgl i s) κ' Y) f := fun f => by
    simp only [Cob, hrep]
  simp only [hm, hr]
  refine ⟨fun x hx => (hsel _ _).1 (h1 x hx), fun x hx hb => h2 x hx ((hc _).2 hb), fun f hf => ?_⟩
  obtain ⟨x, hx, hb⟩ := h3 f ((hsel _ _).2 hf)
  exact ⟨x, hx, (hc _).1 hb⟩

end GlobalTheory.NewPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibilityStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachExpansion_basis_divisibility : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → Full (Di (HW l) h T i) (Lat C h T i ζ) → (∀ (a : AA K LL) (x : ↥(W.N T)), ex C h T i ζ (a • x) = conv (W.lev i ζ a) (ex C h T i ζ x)) ∧ ∀ (r : ℕ) (nb : Module.Basis (Fin r) (AA K LL) ↥(W.N T)), (∀ e : Fin r → PowerSeries ↥LL.1, ∑ j, conv (e j) (ex C h T i ζ (nb j)) = 0 → e = 0) ∧ (∀ f ∈ Lat C h T i ζ, ∃ e : Fin r → PowerSeries ↥LL.1, f = ∑ j, conv (e j) (ex C h T i ζ (nb j))) ∧ ∀ (y : ↥(W.N T)) (k : ℕ), (∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ y j = f (j - k)) ↔ ∀ j, nb.repr y j ∈ van W i ζ k := by
  first | exact @GlobalTheory.NL.LevInj.expansion_basis | exact GlobalTheory.NL.LevInj.expansion_basis | (intros; apply GlobalTheory.NL.LevInj.expansion_basis <;> assumption)
end

