module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0011
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
section
noncomputable section

namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds
open scoped ComplexOrder

section Ops

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def OpLe (S S' : GSD K) (v : InfinitePlace K) (T : S.V →ₗ[K] S'.V) (t : ℝ) : Prop :=
  ∀ x : S.V, (S'.pairAt v (T x) (T x)).re ≤ t * (S.pairAt v x x).re

def PosAt (S : GSD K) (v : InfinitePlace K) : Prop := (S.gramV.map v.embedding).PosSemidef

end Ops

section Coef

variable {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι]

def sqAt (σ : K →+* ℂ) {n : ℕ} (lam : ι → DomWeight n) (x : Formalism.L2.DIV.VV K lam) : ℝ :=
  (∑ i, ∑ j, starRingEnd ℂ (σ ((bVV K lam).repr x i)) *
    σ (pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) K)) (bVV K lam i) (bVV K lam j)) * σ ((bVV K lam).repr x j)).re

def CoefOpLe (σ : K →+* ℂ) {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (T : Formalism.L2.DIV.VV K lam →ₗ[K] Formalism.L2.DIV.VV K lam') (t : ℝ) : Prop :=
  ∀ x, sqAt σ lam' (T x) ≤ t * sqAt σ lam x


open Classical in
def degAt {a b : ℕ} (e : DVar ι a b →₀ ℕ) (τ : ι) : ℕ := ∑ k ∈ e.support.filter (fun k => k.1 = τ), e k

end Coef

section Data

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}

def LocSmall (q : ℕ) (M : Submodule (𝓞 E) (Sp E a)) (M' : Submodule (𝓞 E) (Sp E b)) (Φ : HomE E a b → K) (β : ℝ) : Prop :=
  (∀ x, Φ x ≠ 0 → ∀ y ∈ M, x y ∈ M') ∧ (∀ x z : HomE E a b, (∀ y ∈ M, z y ∈ M') → Φ (x + (q : E) • z) = Φ x) ∧
    ∀ (σ : K →+* ℂ) (x : HomE E a b), ‖σ (Φ x)‖ ≤ β

def SmallDatum (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (c : ℕ)
    (Ξ : HomE E a b → K) (β : ℝ) : Prop :=
  (∀ x, Ξ x ≠ 0 → x ∈ homAt S N N') ∧ (∀ x, ∀ y ∈ mulLat c (homAt S N N'), Ξ (x + y) = Ξ x) ∧
    ∀ (σ : K →+* ℂ) (x : HomE E a b), ‖σ (Ξ x)‖ ≤ β

end Data

def Pres (D : D7) (T : TaylorLogMetric.Tor D) {a b : ℕ} (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (G F : TaylorLogMetric.VC D a b → ℂ) (n : ℝ) : Prop :=
  ∃ (k : ℕ) (r : Fin k → ℂ) (y : Fin k → TaylorLogMetric.VC D a b), (∀ i, r i ∈ TaylorLogMetric.Qbar) ∧ (∀ i, StandardLatticesGL3.LaQ D T L L' (y i)) ∧
    (∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, ∑ i, ‖StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (r i)‖ ≤ n) ∧ F = StandardLatticesGL3.comb D T r y G

def toHost {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (F : VCx X.Tau a b → ℂ) : TaylorLogMetric.VC D a b → ℂ :=
  fun w => F fun τ => w (s.iT τ)

def supConst (D : D7) (a b : ℕ) : ℝ :=
  3 * (2 * ((TaylorLogMetric.fF D * a * b : ℕ) : ℝ) * D.host.rdE + 1) ^ (TaylorLogMetric.fF D * a * b)

def errUnit (N : NumDatum) (T : ℕ) : ℝ :=
  N.R.f * (N.R.m : ℝ) ^ 2 * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1 * T)

def FamilyTie : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D →
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → B.kc.YFinite → StandardLatticesGL3.natTie D cc δ (B.eNat χ)

def FamilyVectors : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D →
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → B.kc.YFinite → B.VecP χ

def FamilyNorms : Prop :=
  ∃ C : ℝ, ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D →
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → B.kc.YFinite → B.ThP C χ

def PeriodLattices : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (cD : D.what₂.Tau → ℂ), X.Ok → s.Ok → TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    TaylorLogMetric.IsChi D χ → IsDgen D cD → B.kc.YFinite → ∀ (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))), Even a → Even b →
    (∀ P ∈ S, conjPrime₂ P ∉ S) → (ambOf s B χ cD).AAUnit S → (ambOf s B χ cD).LaHyp a b S

def CosetRefinement : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (Md : ℕ), X.Ok →
    (∀ P ∈ S, (2 : 𝓞 X.E) ∉ P.asIdeal) → Odd Md → A.LaHyp a b S → A.IndAdd a b S Md

end GlobalTheory.ColNorms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivWeierstrassPAddHalfPeriod
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory

theorem derivWeierstrassP_add_half_period :
    ∀ (L : PeriodPair) (a t : ℂ), a ∉ L.lattice → 2 * a ∈ L.lattice → t ∉ L.lattice → t + a ∉ L.lattice → L.derivWeierstrassP (t + a) * (L.weierstrassP t - L.weierstrassP a) ^ 2 = -(3 * L.weierstrassP a ^ 2 - L.g₂ / 4) * L.derivWeierstrassP t := by
  intro L a t ha h2 ht hta
  have hd : L.derivWeierstrassP a = 0 :=
    (GlobalTheory.derivWeierstrassP_eq_zero_iff L ha).2 (by rw [← two_mul]; exact h2)
  have hne : L.weierstrassP t ≠ L.weierstrassP a := by
    intro h
    rcases (GlobalTheory.weierstrassP_eq_iff L ht ha).1 h with h' | h'
    · apply hta
      have := L.lattice.add_mem h' h2
      rwa [show t - a + 2 * a = t + a by ring] at this
    · exact hta h'
  obtain ⟨h1, h3⟩ := GlobalTheory.weierstrassP_add L ht ha hne
  have e1 := L.derivWeierstrassP_sq t ht
  have e2 := L.derivWeierstrassP_sq a ha
  rw [h3, h1]
  rw [hd] at e2 ⊢
  have hd0 : L.weierstrassP t - L.weierstrassP a ≠ 0 := sub_ne_zero.2 hne
  generalize L.weierstrassP t = x at *
  generalize L.weierstrassP a = e at *
  generalize L.derivWeierstrassP t = y at *
  generalize L.g₂ = g at *
  generalize L.g₃ = k at *
  have hq : ((y - 0) / (x - e)) ^ 2 = (4 * (x ^ 2 + x * e + e ^ 2) - g) / (x - e) := by
    rw [div_pow, div_eq_div_iff (pow_ne_zero 2 hd0) hd0]
    linear_combination (x - e) * (e1 - e2)
  rw [hq]
  field_simp
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDIsTestAndIntegralParts
section
open NumberField IsDedekindDomain MeasureTheory Matrix Polynomial GroundTheory.Automorphic UpperTheory.V
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin)
open UpperTheory.V.TR (Rinf Lie chart infGL pInf toL rmul invSet CuspSub)
open scoped ContDiff
open GlobalTheory.HenQ

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HenQ.DetDParts

section General

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def wD (w : List E) (g : E → ℂ) : E → ℂ :=
  List.foldr (fun (u : E) (f : E → ℂ) (x : E) => fderiv ℝ f x u) g w

theorem top_add_one_le : (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := le_of_eq rfl

theorem fderiv_fderiv_comm {U : Set E} (hU : IsOpen U) {g : E → ℂ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    {x : E} (hx : x ∈ U) (u v : E) :
    fderiv ℝ (fun y => fderiv ℝ g y u) x v = fderiv ℝ (fun y => fderiv ℝ g y v) x u := by
  have hgx : ContDiffAt ℝ (⊤ : ℕ∞) g x := hg.contDiffAt (hU.mem_nhds hx)
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hgx.fderiv_right (m := 1) (by norm_cast)).differentiableAt one_ne_zero
  have key : ∀ a b : E, fderiv ℝ (fun y => fderiv ℝ g y a) x b = fderiv ℝ (fderiv ℝ g) x b a := by
    intro a b
    rw [fderiv_clm_apply hd (differentiableAt_const a)]
    simp
  rw [key, key]
  exact (hgx.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)).eq v u

variable {μ : Measure E} [μ.IsAddHaarMeasure]

theorem continuous_mul_of_tsupport {U : Set E} (hU : IsOpen U) {u χ : E → ℂ}
    (hu : ContinuousOn u U) (hχ : Continuous χ) (hs : tsupport χ ⊆ U) :
    Continuous fun x => χ x * u x :=
  (hχ.continuousOn.mul hu).continuous_of_tsupport_subset hU (tsupport_mul_subset_left.trans hs)

theorem integrable_mul_of_tsupport {U : Set E} (hU : IsOpen U) {u χ : E → ℂ}
    (hu : ContinuousOn u U) (hχ : Continuous χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ U) :
    Integrable (fun x => χ x * u x) μ :=
  (continuous_mul_of_tsupport hU hu hχ hs).integrable_of_hasCompactSupport hc.mul_right

theorem integral_partial_mul {U : Set E} (hU : IsOpen U) {Ψ g : E → ℂ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hc : HasCompactSupport Ψ) (hs : tsupport Ψ ⊆ U)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (u : E) :
    ∫ x, fderiv ℝ Ψ x u * g x ∂μ = -∫ x, Ψ x * fderiv ℝ g x u ∂μ := by
  have h1 : ContDiff ℝ 1 Ψ := hΨ.of_le (by exact_mod_cast le_top)
  have hg1 : ContDiffOn ℝ 1 g U := hg.of_le (by exact_mod_cast le_top)
  have hg' : ContDiffOn ℝ 0 (fun x => fderiv ℝ g x u) U :=
    (hg1.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  rw [eq_neg_iff_add_eq_zero, add_comm, ← eq_neg_iff_add_eq_zero]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_of_tsupport hU hg1.continuousOn
      ((h1.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hc.fderiv_apply ℝ _)
      ((tsupport_fderiv_apply_subset ℝ _).trans hs))
    (integrable_mul_of_tsupport hU hg'.continuousOn h1.continuous hc hs)
    (integrable_mul_of_tsupport hU hg1.continuousOn h1.continuous hc hs)
    (fun x _ => h1.differentiable one_ne_zero x)
    (fun x hx => (hg1.contDiffAt (hU.mem_nhds (hs hx))).differentiableAt one_ne_zero)

end General

section Specific

variable {K : Type} [Field K] [NumberField K] {n : ℕ}


open Classical in
def wordOf (v : InfinitePlace K) (p : Equiv.Perm (Fin n)) (l : List (Fin n)) : List (Lie K n) :=
  l.map fun j => toL (Matrix.single (p j) j (Pi.single v 1))

theorem foldr_pdL_eq (v : InfinitePlace K) (p : Equiv.Perm (Fin n)) (F : Lie K n → ℂ) (l : List (Fin n)) :
    l.foldr (fun j G => pdL v (p j) j G) F = wD (wordOf v p l) F := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldr_cons, wordOf, List.map_cons]
    rw [ih]
    rfl

theorem detD_eq (v : InfinitePlace K) (G : Lie K n → ℂ) :
    detD v G = fun x => ∑ p : Equiv.Perm (Fin n),
      (((Equiv.Perm.sign p : ℤˣ) : ℤ) : ℂ) * wD (wordOf v p (List.finRange n)) G x := by
  funext x
  simp only [detD, foldr_pdL_eq]

end Specific

end GlobalTheory.HenQ.DetDParts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfUnitCoord
section
open Finset
open scoped ComplexConjugate Real

noncomputable section

namespace GlobalTheory.JetFrameCompare

open GlobalTheory.IndefiniteRowSideFullHecke Formalism.DimensionVariation

section Calculus

variable {E κ W : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem wordDeriv_eq_lineDerivList (v : κ → E) {F : E → ℂ} (hF : Differentiable ℂ F) (w : List κ) :
    TensorCoordinateForms.wordDeriv v w F = lineDerivList ℂ (w.map v) F := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    funext z
    have h := (analyticAt_lineDerivList
      (SCV.analyticOnNhd_of_differentiable hF Set.univ z (Set.mem_univ z)) (w.map v)).differentiableAt
    rw [List.map_cons, lineDerivList_cons]
    change TensorCoordinateForms.dirDeriv (v x) (TensorCoordinateForms.wordDeriv v w F) z = _
    rw [ih]
    exact h.lineDeriv_eq_fderiv.symm

theorem wordDeriv_perm (v : κ → E) {F : E → ℂ} (hF : Differentiable ℂ F) {w w' : List κ}
    (h : w.Perm w') : TensorCoordinateForms.wordDeriv v w F = TensorCoordinateForms.wordDeriv v w' F := by
  funext z
  rw [wordDeriv_eq_lineDerivList v hF, wordDeriv_eq_lineDerivList v hF]
  exact lineDerivList_perm (SCV.analyticOnNhd_of_differentiable hF Set.univ z (Set.mem_univ z)) (h.map v)

def stdWord [Fintype κ] (e : κ → ℕ) : List κ :=
  (univ : Finset κ).toList.flatMap fun x => List.replicate (e x) x


omit [FiniteDimensional ℂ E] in
theorem monoDeriv_eq_wordDeriv [Fintype κ] (v : κ → E) (e : κ → ℕ) (F : E → ℂ) :
    TaylorCoefficientForms.monoDeriv v e F = TensorCoordinateForms.wordDeriv v (stdWord e) F := by
  unfold TaylorCoefficientForms.monoDeriv TensorCoordinateForms.wordDeriv stdWord
  induction (univ : Finset κ).toList with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldr_cons, List.flatMap_cons, List.foldr_append, ← ih]
    generalize List.foldr (fun x G => (TaylorCoefficientForms.dirDeriv (v x))^[e x] G) F l = G
    induction e x with
    | zero => rfl
    | succ n ihn => rw [Function.iterate_succ_apply', List.replicate_succ, List.foldr_cons, ← ihn]; rfl

theorem isSpelling_stdWord [Fintype κ] [DecidableEq κ] : TensorCoordinateForms.IsSpelling (stdWord (κ := κ)) := by
  intro e x
  rw [stdWord, List.count_flatMap, Finset.sum_map_toList]
  simp [List.count_replicate]

theorem wordDeriv_eq_monoDeriv [Fintype κ] [DecidableEq κ] {w : (κ → ℕ) → List κ}
    (hw : TensorCoordinateForms.IsSpelling w) (v : κ → E) {F : E → ℂ} (hF : Differentiable ℂ F) (e : κ → ℕ) :
    TensorCoordinateForms.wordDeriv v (w e) F = TaylorCoefficientForms.monoDeriv v e F := by
  rw [monoDeriv_eq_wordDeriv]
  exact wordDeriv_perm v hF (List.perm_iff_count.2 fun x => (hw e x).trans (isSpelling_stdWord e x).symm)

theorem coordVec_eq [DecidableEq κ] : (TensorCoordinateForms.coordVec : κ → κ → ℂ) = TaylorCoefficientForms.coordVec := by
  funext p
  unfold TensorCoordinateForms.coordVec TaylorCoefficientForms.coordVec
  congr
  exact Subsingleton.elim _ _

theorem hasSum_taylorCoeff [Fintype κ] {F : (κ → ℂ) → ℂ} (hF : Differentiable ℂ F) (u : κ → ℂ) :
    HasSum (fun e => TaylorCoefficientForms.taylorCoeff F e * mono u e) (F u) := by
  classical
  have han := SCV.analyticOnNhd_of_differentiable hF Set.univ 0 (Set.mem_univ _)
  have hw : TensorCoordinateForms.IsSpelling fun e : κ → ℕ =>
      (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm e)).toList := fun e x => by
    rw [← Multiset.coe_count, Multiset.coe_toList, Finsupp.count_toMultiset]
    rfl
  have key : ∀ α : κ →₀ ℕ, TaylorCoefficientForms.monoDeriv TaylorCoefficientForms.coordVec α F =
      lineDerivList ℂ ((Finsupp.toMultiset α).toList.map fun k => Pi.single k (1 : ℂ)) F := fun α => by
    rw [← wordDeriv_eq_monoDeriv hw _ hF, wordDeriv_eq_lineDerivList _ hF, ← coordVec_eq]
    simp only [Finsupp.equivFunOnFinite_symm_coe]
    rfl
  have hne : ∀ α : κ →₀ ℕ, ((∏ i, (α i).factorial : ℕ) : ℂ) ≠ 0 := cast_prod_factorial_ne_zero
  have hc : ∀ α : κ →₀ ℕ,
      (∏ j, ((α j).factorial : ℂ)) * TaylorCoefficientForms.taylorCoeff F α = pderivIter α F 0 := fun α => by
    rw [TaylorCoefficientForms.taylorCoeff, key, mfact,
      ← Nat.cast_prod, mul_div_cancel₀ _ (hne α)]
    rfl
  have hc' : ∀ α : κ →₀ ℕ,
      TaylorCoefficientForms.taylorCoeff F α = MvPowerSeries.coeff α (GlobalTheory.taylor F) := fun α => by
    rw [GlobalTheory.taylor, coeff_taylorDir_eq_lineDerivList _ han (Multiset.coe_toList _), TaylorCoefficientForms.taylorCoeff, key,
      mfact, div_eq_inv_mul]
  have h1 := EntireTaylor.summable_of_entire hF (fun α => TaylorCoefficientForms.taylorCoeff F α) hc u
  have h2 := ProdThetaConj.tsum_of_entire hF (fun α => TaylorCoefficientForms.taylorCoeff F α) hc hc' u
  rw [← h2, ← (Finsupp.equivFunOnFinite (α := κ) (M := ℕ)).hasSum_iff]
  exact h1.hasSum

end Calculus

section Objects

variable {Pl : Type} [Fintype Pl] [DecidableEq Pl] {X₀ X₁ : Pl → Type}
  [∀ τ, NormedAddCommGroup (X₀ τ)] [∀ τ, InnerProductSpace ℂ (X₀ τ)] [∀ τ, FiniteDimensional ℂ (X₀ τ)]
  [∀ τ, NormedAddCommGroup (X₁ τ)] [∀ τ, InnerProductSpace ℂ (X₁ τ)] [∀ τ, FiniteDimensional ℂ (X₁ τ)]
  {n₀ n₁ : ℕ} (ξ D : Pl → ℂ) (b₀ : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ))
  (b₁ : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ))

end Objects

section Clauses

variable {Pl : Type} [Fintype Pl] {X₀ X₁ : Pl → Type}
  [∀ τ, NormedAddCommGroup (X₀ τ)] [∀ τ, InnerProductSpace ℂ (X₀ τ)] [∀ τ, FiniteDimensional ℂ (X₀ τ)]
  [∀ τ, NormedAddCommGroup (X₁ τ)] [∀ τ, InnerProductSpace ℂ (X₁ τ)] [∀ τ, FiniteDimensional ℂ (X₁ τ)]
  {n₀ n₁ : ℕ}

end Clauses

end GlobalTheory.JetFrameCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightEntriesSignsSizes
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop.Wts

variable {ι : Type} {N : ℕ} (W : Wts ι N)

theorem div_gap_step (h : W.Hyp) (hd : W.IsDiv) (τ : ι) (a b : Fin N) (hab : (b : ℕ) = a + 1) :
    0 ≤ W.u1 τ a - W.u1 τ b ∧
      ((W.T : ℤ) + W.Dd + 1) * (W.u1 τ a - W.u1 τ b) ≤ W.u τ a - W.u τ b + 2 := by
  have hM : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1 := by positivity
  have hc := h.weightConst_nonneg
  obtain ⟨h41, -, h43⟩ := h.h4 τ a b hab
  have h2 := h.h2.1
  rw [(hd τ).2 a b hab]
  have hN : (0 : ℤ) ≤ N := by positivity
  split_ifs with hb
  · have := h43 hb
    refine ⟨Int.ediv_nonneg (by linarith) hM.le, ?_⟩
    refine (Int.mul_ediv_self_le hM.ne').trans ?_
    linarith
  · have h5 := h41 hb
    have h6 : (0 : ℤ) ≤ ((W.T : ℤ) + W.Dd + 2) * ((W.T : ℤ) + W.Dd + 2 + 2 * N) := by positivity
    exact ⟨Int.ediv_nonneg (by linarith) hM.le, Int.mul_ediv_self_le hM.ne'⟩

theorem div_gap_sum (h : W.Hyp) (hd : W.IsDiv) (τ : ι) (n : ℕ) : ∀ a b : Fin N, (b : ℕ) = a + n →
    0 ≤ W.u1 τ a - W.u1 τ b ∧
      ((W.T : ℤ) + W.Dd + 1) * (W.u1 τ a - W.u1 τ b) ≤ W.u τ a - W.u τ b + 2 * n := by
  induction n with
  | zero =>
    intro a b hab
    have : b = a := Fin.ext (by simpa using hab)
    subst this
    simp
  | succ n ih =>
    intro a b hab
    have hlt : (a : ℕ) + n < N := by have := b.2; omega
    obtain ⟨h1, h2⟩ := ih a ⟨a + n, hlt⟩ rfl
    obtain ⟨h3, h4⟩ := W.div_gap_step h hd τ ⟨a + n, hlt⟩ b (by simp; omega)
    refine ⟨by linarith, ?_⟩
    push_cast
    nlinarith

end GlobalTheory.MeanTop.Wts

namespace GlobalTheory.MeanTop

theorem divided_entries : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ i,
    ((W.T : ℤ) + W.Dd + 1) * |W.u1 τ i| ≤ |W.u τ i| + W.c0 + 4 * N ∧
      (W.kc ≤ (i : ℕ) + 1 → W.u1 τ i ≤ 0) ∧ ((i : ℕ) < W.kc → 0 ≤ W.u1 τ i) := by
  intro ι _ N W h hd τ i
  have hk := h.kc_pos
  have hk2 := h.kc_lt
  have hp := h.p_lt
  have hc := h.weightConst_nonneg
  have hi := i.2
  have hN : (0 : ℤ) ≤ N := by positivity
  let a : Fin N := ⟨W.kc - 1, by omega⟩
  have ha : (a : ℕ) + 1 = W.kc := by simp only [a]; omega
  have hu : W.u τ a = 0 := h.anchor τ a ha
  have hu1 : W.u1 τ a = 0 := (hd τ).1 a ha
  have up : (i : ℕ) < W.kc → 0 ≤ W.u1 τ i ∧
      ((W.T : ℤ) + W.Dd + 1) * W.u1 τ i ≤ W.u τ i + 2 * N := by
    intro hi'
    obtain ⟨h1, h2⟩ := W.div_gap_sum h hd τ (a - i) i a (by omega)
    have h3 : (((a : ℕ) - i : ℕ) : ℤ) ≤ N := by omega
    rw [hu1, sub_zero] at h1 h2
    rw [hu] at h2
    exact ⟨h1, by linarith⟩
  have down : W.kc ≤ (i : ℕ) + 1 → W.u1 τ i ≤ 0 ∧
      ((W.T : ℤ) + W.Dd + 1) * (-W.u1 τ i) ≤ -W.u τ i + 2 * N := by
    intro hi'
    obtain ⟨h1, h2⟩ := W.div_gap_sum h hd τ (i - a) a i (by omega)
    have h3 : (((i : ℕ) - a : ℕ) : ℤ) ≤ N := by omega
    rw [hu1, zero_sub] at h1 h2
    rw [hu] at h2
    exact ⟨by linarith, by linarith⟩
  refine ⟨?_, fun hi' => (down hi').1, fun hi' => (up hi').1⟩
  by_cases hi' : (i : ℕ) < W.kc
  · obtain ⟨h1, h2⟩ := up hi'
    rw [abs_of_nonneg h1]
    have := le_abs_self (W.u τ i)
    linarith
  · obtain ⟨h1, h2⟩ := down (by omega)
    rw [abs_of_nonpos h1]
    have := neg_le_abs (W.u τ i)
    linarith

end GlobalTheory.MeanTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbBaseChange

theorem isAbelianScheme_and_relDim_of_isGrpPullback : ∀ {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (φ : A'.left ⟶ A.left) (g : ℕ), IsGrpPullback A' A (spMap f) φ → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom := by
  intro R R' _ _ f A _ A' _ φ g h hA hg
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  exact ⟨GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h,
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h.1 hg⟩

end GlobalTheory.AbBaseChange
end

