module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NotLtLtOfMemMinimalPrimes
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0028
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointsIntegralProductFormula
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

section Words

variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem prod_X_word {R : Type} [CommRing R] {n : ℕ} (w : Fin n → σ) :
    ∏ j, (X (w j) : MvPolynomial σ R) = monomial (∑ j, Finsupp.single (w j) 1) 1 :=
  (monomial_sum_one _ _).symm

theorem exists_perm_of_word_eq {n : ℕ} (v w : Fin n → σ)
    (h : (∑ j, Finsupp.single (v j) 1 : σ →₀ ℕ) = ∑ j, Finsupp.single (w j) 1) :
    ∃ π : Equiv.Perm (Fin n), v = w ∘ π := by
  have count : ∀ (u : Fin n → σ) (s : σ),
      (∑ j, Finsupp.single (u j) 1 : σ →₀ ℕ) s = Fintype.card {j // u j = s} := by
    intro u s
    rw [Finsupp.finsetSum_apply, Fintype.card_subtype, Finset.card_filter]
    exact Finset.sum_congr rfl fun j _ => by simp [Finsupp.single_apply]
  have hc : ∀ s, Fintype.card {j // v j = s} = Fintype.card {j // w j = s} := fun s => by
    rw [← count, ← count, h]
  refine ⟨Equiv.ofFiberEquiv (f := v) (g := w) fun s => Fintype.equivOfCardEq (hc s), funext fun j => ?_⟩
  exact (Equiv.ofFiberEquiv_map _ j).symm

theorem eq_of_formPoly_eq {n : ℕ} {a b : (Fin n → σ) → ℝ}
    (ha : ∀ (π : Equiv.Perm (Fin n)) w, a (w ∘ π) = a w) (hb : ∀ (π : Equiv.Perm (Fin n)) w, b (w ∘ π) = b w)
    (h : PB.formPoly n a = PB.formPoly n b) (w₀ : Fin n → σ) : a w₀ = b w₀ := by
  set m : σ →₀ ℕ := ∑ j, Finsupp.single (w₀ j) 1 with hm
  set T := Finset.univ.filter fun w : Fin n → σ => (∑ j, Finsupp.single (w j) 1 : σ →₀ ℕ) = m with hT
  have hco : ∀ c : (Fin n → σ) → ℝ, (∀ (π : Equiv.Perm (Fin n)) w, c (w ∘ π) = c w) →
      AddMonoidAlgebra.coeff (PB.formPoly n c) m = (T.card : ℝ) * c w₀ := by
    intro c hc
    simp only [PB.formPoly, coeff_sum, coeff_C_mul, prod_X_word, coeff_monomial, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter, ← nsmul_eq_mul]
    rw [Finset.sum_congr rfl (g := fun _ => c w₀), Finset.sum_const]
    intro w hw
    obtain ⟨π, rfl⟩ := exists_perm_of_word_eq w w₀ (Finset.mem_filter.1 hw).2
    exact hc π w₀
  have hpos : (T.card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨w₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩)
  have := congrArg (AddMonoidAlgebra.coeff · m) h
  rw [hco a ha, hco b hb] at this
  exact mul_left_cancel₀ hpos this

theorem eval_formPoly {n : ℕ} (a : (Fin n → σ) → ℝ) (l : σ → ℝ) :
    eval l (PB.formPoly n a) = ∑ w, a w * ∏ j, l (w j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [PB.formPoly, map_sum, map_prod]

end Words

section Flag

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem weylAct_injective (u : Ψ → Equiv.Perm (Fin N)) : Function.Injective (weylAct Ψ N u) := by
  rintro ⟨τ, i⟩ ⟨τ', i'⟩ h
  simp only [weylAct, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  rw [(u τ).injective h]

theorem mapDomain_permExp (u : Ψ → Equiv.Perm (Fin N)) :
    Finsupp.mapDomain (weylAct Ψ N u) (Top.permExp u) = rhoMono Ψ N := by
  ext ⟨τ, i⟩
  have h : ((τ, i) : Ψ × Fin N) = weylAct Ψ N u (τ, (u τ)⁻¹ i) := by simp [weylAct]
  rw [h, Finsupp.mapDomain_apply_of_injective (weylAct_injective u)]
  simp [Top.permExp, rhoMono, weylAct]

theorem flagInt_eq_sum (P : RootPoly Ψ N) :
    flagInt Ψ N P = ∑ u, weylSign Ψ N u * AddMonoidAlgebra.coeff P (Top.permExp u) := by
  unfold flagInt GroundTheory.Heights₂.Heights.LowerBoundFree.antisym
  rw [coeff_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [coeff_smul, smul_eq_mul, ← mapDomain_permExp u, coeff_rename_mapDomain _ (weylAct_injective u)]

theorem flagInt_word_cast {n : ℕ} (w : Fin n → Ψ × Fin N) :
    ((flagInt Ψ N (∏ r, X (w r)) : ℚ) : ℝ) =
      ∑ u : Ψ → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (u τ) : ℤ) : ℝ)) *
        (∏ r, X (w r) : Top.RP Ψ N).coeff (Top.permExp u) := by
  rw [flagInt_eq_sum, Rat.cast_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [prod_X_word, prod_X_word, coeff_monomial, coeff_monomial, weylSign]
  split_ifs <;> simp

theorem flagDeg_eq_formPoly (n : ℕ) (hn : n = Top.dimFl Ψ N) (l : Ψ × Fin N → ℝ) :
    Top.flagDeg (fun τ i => l (τ, i)) =
      eval l (PB.formPoly n fun w : Fin n → Ψ × Fin N => ((flagInt Ψ N (∏ r, X (w r)) : ℚ) : ℝ)) := by
  subst hn
  have hS : (∑ x : Ψ × Fin N, C (l x) * X x : Top.RP Ψ N) ^ Top.dimFl Ψ N =
      ∑ w : Fin (Top.dimFl Ψ N) → Ψ × Fin N, C (∏ r, l (w r)) * ∏ r, X (w r) := by
    rw [Fintype.sum_pow]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.prod_mul_distrib, map_prod]
  have hneg : Top.linRoot (fun τ i => l (τ, i)) ^ Top.dimFl Ψ N =
      C ((-1) ^ Top.dimFl Ψ N) * (∑ x : Ψ × Fin N, C (l x) * X x : Top.RP Ψ N) ^ Top.dimFl Ψ N := by
    rw [Top.linRoot, neg_pow, map_pow, map_neg, map_one]
  rw [eval_formPoly, Top.flagDeg, Top.degFl, hneg, hS]
  simp only [coeff_C_mul, coeff_sum, flagInt_word_cast, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun u _ => ?_
  have h1 : ((-1 : ℝ) ^ Top.dimFl Ψ N) * (-1) ^ Top.dimFl Ψ N = 1 := by
    rw [← mul_pow]; simp
  linear_combination ((∏ τ, ((Equiv.Perm.sign (u τ) : ℤ) : ℝ)) *
    (∏ r, l (w r)) * (∏ r, X (w r) : Top.RP Ψ N).coeff (Top.permExp u)) * h1

theorem ptsIntegral_word_eq (n : ℕ) (hn : n = antisymDegree Ψ N) (hD : n = Top.dimFl Ψ N)
    (h : ∀ l : Ψ × Fin N → ℝ, eval l (PB.degFlPoly Ψ N) = Top.flagDeg (fun τ i => l (τ, i)))
    (w : Fin n → Ψ × Fin N) :
    ptsIntegral (PFl Ψ N) (pot fun r => xLine Ψ N (w r)) (fun _ => 1) =
      ((flagInt Ψ N (∏ r, X (w r)) : ℚ) : ℝ) := by
  subst hn
  refine eq_of_formPoly_eq (a := fun w => ptsIntegral (PFl Ψ N) (pot fun r => xLine Ψ N (w r)) fun _ => 1)
    (b := fun w => ((flagInt Ψ N (∏ r, X (w r)) : ℚ) : ℝ)) ?_ ?_ ?_ w
  · intro π v
    exact GroundTheory.Heights₂.Heights.Inter.ptsIntegral_comp_perm (PFl Ψ N) (pot fun r => xLine Ψ N (v r)) π _
  · intro π v
    have : ∏ r, (X ((v ∘ π) r) : RootPoly Ψ N) = ∏ r, X (v r) := Equiv.prod_comp π fun r => (X (v r) : RootPoly Ψ N)
    simp only [this]
  · refine MvPolynomial.funext fun l => ?_
    rw [← flagDeg_eq_formPoly _ hD l, ← h l]
    rfl

end Flag

theorem borel_word : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ) (w : Fin (GroundTheory.Heights₂.Heights.LowerBoundFree.dimFl Ψ N) → Ψ × Fin N), 2 ≤ N → ptsIntegral (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (pot fun r => GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N (w r)) (fun _ => 1) = ((GroundTheory.Heights₂.Heights.LowerBoundFree.flagInt Ψ N (∏ r, X (w r)) : ℚ) : ℝ) := by
  rintro hI ⟨II, hII⟩ Ψ _ _ _ N w hN
  refine ptsIntegral_word_eq _ ?_ rfl (fun l => ?_) w
  · simp [Top.dimFl, GroundTheory.Heights₂.Heights.LowerBoundFree.dimFl, GroundTheory.Heights₂.Heights.antisymDegree, Nat.choose_two_right]
  · exact _root_.GlobalTheory.CompanionTheory.Relay.flag_degree_polynomial_eval hI II hII Ψ N (fun τ i => l (τ, i)) hN

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

open NumberField Matrix _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Automorphic GroundTheory.Heights₂.Heights.FiniteCovolume

section Pure

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

abbrev Sg (j j' : ℕ) : Type := Fin j ⊕ Fin j'

def sgI (j j' : ℕ) : Matrix (Sg j j') (Sg j j') ℂ := fromBlocks 1 0 0 (-1)

def IsSgU (u : Matrix (Sg j j') (Sg j j') ℂ) : Prop := uᴴ * sgI j j' * u = sgI j j'

def moebW (u : Matrix (Sg j j') (Sg j j') ℂ) (W : Matrix (Fin j') (Fin j) ℂ) : Matrix (Fin j') (Fin j) ℂ :=
  (u.toBlocks₂₁ + u.toBlocks₂₂ * W) * (u.toBlocks₁₁ + u.toBlocks₁₂ * W)⁻¹

def ballPt (q : Ψ × Fin j × Fin j' ≃ Fin n) (W : Ψ → Matrix (Fin j') (Fin j) ℂ) : Fin n → ℂ :=
  fun k => W (q.symm k).1 (q.symm k).2.2 (q.symm k).2.1

def moebBall (q : Ψ × Fin j × Fin j' ≃ Fin n) (u : Ψ → Matrix (Sg j j') (Sg j j') ℂ) (t : Fin n → ℂ) : Fin n → ℂ :=
  ballPt q fun τ => moebW (u τ) (ballMat q t τ)ᵀ

end Pure

section Arch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ]


omit [IsCMField E] in
theorem intEmb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  have hc : (RingHom.ker s).comap (algebraMap ℤ (𝓞 E)) = ⊥ := by
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)
  exact (RingHom.injective_iff_ker_eq_bot s).2 (Ideal.eq_bot_of_comap_eq_bot hc)

def embOf (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (intEmb_injective s)

structure LatEmb (F : UnivFam E Ψ j j' n g Λ) where

  h : HermitianForm (maximalRealSubfield E) E (Fin (j + j') → E)

  e : Λ →+ (Fin (j + j') → E)
  e_inj : Function.Injective e
  e_smul : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x

  Dn : ℕ
  integral : IsDIntegral h Dn e.range
  orth : ∀ x y, h.toSesq (e x) (e y) = 0 ↔ ∀ a : 𝓞 E, F.form (a • x) y = 0

  xi : E

  c : ℝ
  c_pos : 0 < c

  eps : Ψ → ℝ
  eps_sq : ∀ τ, eps τ ^ 2 = 1
  xi_eq : ∀ τ, embOf (F.σ τ) xi = Complex.I * ((c * eps τ : ℝ) : ℂ)
  form_eq : ∀ x y, ((F.form x y : ℤ) : ℚ) = Algebra.trace ℚ E (xi * h.toSesq (e y) (e x))

  lam : Module.Basis (Fin (2 * g)) ℤ Λ

  bas : Module.Basis (Fin (2 * g)) ℝ (Ψ → Fin (j + j') → ℂ)
  bas_eq : ∀ k τ i, bas k τ i = embOf (F.σ τ) (e (lam k) i)

def plc (F : UnivFam E Ψ j j' n g Λ) (τ : Ψ) : InfinitePlace E := InfinitePlace.mk (embOf (F.σ τ))


open Classical in
def tauMat (F : UnivFam E Ψ j j' n g Λ) (a : InfinitePlace E → GL (Fin (j + j')) ℂ) (τ : Ψ) :
    Matrix (Fin (j + j')) (Fin (j + j')) ℂ :=
  if (plc F τ).embedding = embOf (F.σ τ) then (a (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ)
  else (a (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ).map (starRingEnd ℂ)

namespace LatEmb

variable {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)

def vec (x : Λ) : Ψ → Fin (j + j') → ℂ := fun τ i => embOf (F.σ τ) (C.e x i)

def gr (τ : Ψ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ :=
  (gram C.h.toSesq (Pi.basisFun E (Fin (j + j')))).map (embOf (F.σ τ))

def sgr (τ : Ψ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ := ((C.eps τ : ℝ) : ℂ) • C.gr τ

def Fm (y y' : Ψ → Fin (j + j') → ℂ) : ℝ :=
  ∑ τ, 2 * (embOf (F.σ τ) C.xi * (star (y' τ) ⬝ᵥ (C.gr τ *ᵥ y τ))).re

def cinv (A : Matrix (Fin (j + j')) (Sg j j') ℂ) (τ : Ψ) : Matrix (Sg j j') (Fin (j + j')) ℂ :=
  sgI j j' * Aᴴ * C.sgr τ

def perExt (R : RiemLat E g Λ) : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
  C.bas.constr ℝ fun k => R.P (C.lam k)


open Classical in
def pPart (R : RiemLat E g Λ) (τ : Ψ) (y : Fin (j + j') → ℂ) : Fin g → ℂ :=
  (1 / 2 : ℂ) • (C.perExt R (Pi.single τ y) - Complex.I • C.perExt R (Pi.single τ (Complex.I • y)))


open Classical in
def pBar (R : RiemLat E g Λ) (τ : Ψ) (y : Fin (j + j') → ℂ) : Fin g → ℂ :=
  (1 / 2 : ℂ) • (C.perExt R (Pi.single τ y) + Complex.I • C.perExt R (Pi.single τ (Complex.I • y)))

structure IsAdapted (R : RiemLat E g Λ) (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) : Prop where
  unit : ∀ τ, (A τ)ᴴ * C.sgr τ * A τ = sgI j j'
  ker : ∀ τ (v : Fin j → ℂ), C.pPart R τ (A τ *ᵥ Sum.elim v 0) = 0
  kerBar : ∀ τ (v : Fin j' → ℂ), C.pBar R τ (A τ *ᵥ Sum.elim 0 v) = 0

abbrev Arch : Subgroup (InfinitePlace E → GL (Fin (j + j')) ℂ) := archUnitary C.h (Pi.basisFun E (Fin (j + j')))

def tm (a : C.Arch) (τ : Ψ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ :=
  tauMat F (a : InfinitePlace E → GL (Fin (j + j')) ℂ) τ

end LatEmb

end Arch

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

