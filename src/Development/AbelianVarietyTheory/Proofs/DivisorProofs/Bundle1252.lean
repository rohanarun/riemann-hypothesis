module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1229
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeScalarOnSphericalVectors
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSmoothAdelicFunctions
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology Set
open scoped ContDiff

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem contDiff_lmul_uncurry : ContDiff ℝ ∞ fun q : Lie E a × Lie E a => lmul q.1 q.2 := by
  have e : (fun q : Lie E a × Lie E a => lmul q.1 q.2) = fun q i j => ∑ k, q.1 i k * q.2 k j := by
    funext q i j
    rfl
  rw [e]
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ContDiff.sum fun k _ => ?_
  exact ((contDiff_apply ℝ _ k).comp ((contDiff_apply ℝ _ i).comp contDiff_fst)).mul
    ((contDiff_apply ℝ _ j).comp ((contDiff_apply ℝ _ k).comp contDiff_snd))

theorem contDiffOn_smoothing_integrand {α : Lie E a → ℂ} (hα : IsTest (invSet E a) α) {ψ : GA E a → ℂ}
    (hψ : ψ ∈ Sm E a) (g : GA E a) :
    ContDiffOn ℝ ∞ (fun q : Lie E a × Lie E a => α (-q.2) * chart ψ g (lmul q.1 (-q.2))) (invSet E a ×ˢ univ) := by
  rintro ⟨p, t⟩ ⟨hp, -⟩
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases ht : -t ∈ tsupport α
  · have hpt : lmul p (-t) ∈ invSet E a := IsUnit.mul hp (hα.2.2 ht)
    have h1 : ContDiffAt ℝ ∞ (fun q : Lie E a × Lie E a => lmul q.1 (-q.2)) (p, t) :=
      (contDiff_lmul_uncurry.comp (contDiff_fst.prodMk contDiff_snd.neg)).contDiffAt
    have h3 : ContDiffAt ℝ ∞ (fun q : Lie E a × Lie E a => chart ψ g (lmul q.1 (-q.2))) (p, t) :=
      by
        have h4 := contDiffAt_chart hψ g hpt
        exact h4.comp (p, t) h1
    exact (hα.1.comp contDiff_snd.neg).contDiffAt.mul h3
  · have h0 : α =ᶠ[𝓝 (-t)] 0 := notMem_tsupport_iff_eventuallyEq.1 ht
    have h2 : (fun q : Lie E a × Lie E a => α (-q.2)) =ᶠ[𝓝 (p, t)] fun _ => 0 :=
      ((continuous_snd.neg).continuousAt.tendsto (x := (p, t))).eventually h0
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [h2] with q hq
    simp [hq]

theorem smoothing_mem_Sm (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ) (hα : IsTest (invSet E a) α)
    (ψ : GA E a → ℂ) (hψ : ψ ∈ Sm E a) : smoothing ν α ψ ∈ Sm E a := by
  intro g
  let G : Lie E a → Lie E a → ℂ := fun p t => α (-t) * chart ψ g (lmul p (-t))
  have hk : IsCompact ((fun t : Lie E a => -t) '' tsupport α) := hα.2.1.isCompact.image continuous_neg
  have hgs : ∀ p, ∀ x, p ∈ invSet E a → x ∉ (fun t : Lie E a => -t) '' tsupport α → G p x = 0 := by
    intro p x _ hx
    have : α (-x) = 0 := image_eq_zero_of_notMem_tsupport fun h => hx ⟨-x, h, neg_neg x⟩
    simp [G, this]
  have hf : LocallyIntegrable (fun _ : Lie E a => (1 : ℂ)) ν := locallyIntegrable_const 1
  have H := contDiffOn_convolution_right_with_param_comp (μ := ν) (n := ⊤) (ContinuousLinearMap.mul ℝ ℂ)
    (contDiffOn_const (c := (0 : Lie E a))) isOpen_invSet hk hgs hf (contDiffOn_smoothing_integrand hα hψ g)
  refine H.congr fun x hx => ?_
  obtain ⟨u, hu⟩ := hx
  obtain rfl : x = toL u.val := hu.symm
  rw [chart_val, smoothing, chart_mul, convolution_def]
  simp [G]

end GlobalTheory.AutGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealStableOfCharacters
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

namespace GlobalTheory.TrMult


end GlobalTheory.TrMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimConeImageOfBirationalLinearSystem
section
open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.ConeDim

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {N : ℕ}

theorem isAlgebraic_of_closure_eq_top (y : Fin N → Ω) (hy : y ≠ 0)
    (hgen : Subfield.closure (Set.range (algebraMap k Ω) ∪ {r | ∃ i j, r = y i / y j}) = ⊤)
    (A : Subalgebra k (Polynomial Ω)) (hXy : ∀ i, Polynomial.X * Polynomial.C (y i) ∈ A) :
    Algebra.IsAlgebraic A (Polynomial Ω) := by
  classical
  let ι : Polynomial Ω →+* FractionRing (Polynomial Ω) := algebraMap _ _
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  let L : Subfield (FractionRing (Polynomial Ω)) := Subfield.closure (ι '' (A : Set (Polynomial Ω)))
  have hA : ∀ a ∈ A, ι a ∈ L := fun a ha => Subfield.subset_closure ⟨a, ha, rfl⟩
  have hne : ∀ j, y j ≠ 0 → ι (Polynomial.X * Polynomial.C (y j)) ≠ 0 := fun j hj =>
    (map_ne_zero_iff ι hι).2 (mul_ne_zero Polynomial.X_ne_zero (Polynomial.C_ne_zero.2 hj))
  let M : Subfield Ω := L.comap (ι.comp Polynomial.C)
  have hM : M = ⊤ := by
    refine top_unique (hgen ▸ Subfield.closure_le.2 ?_)
    rintro _ (⟨c, rfl⟩ | ⟨i, j, rfl⟩)
    · show ι (Polynomial.C (algebraMap k Ω c)) ∈ L
      rw [← Polynomial.algebraMap_apply]
      exact hA _ (A.algebraMap_mem c)
    · show ι (Polynomial.C (y i / y j)) ∈ L
      by_cases hj : y j = 0
      · rw [hj, div_zero, Polynomial.C_0, map_zero]
        exact zero_mem L
      · have e : ι (Polynomial.C (y i / y j)) =
            ι (Polynomial.X * Polynomial.C (y i)) / ι (Polynomial.X * Polynomial.C (y j)) := by
          rw [eq_div_iff (hne j hj), ← map_mul]
          congr 1
          rw [mul_left_comm, ← Polynomial.C_mul, div_mul_cancel₀ _ hj]
        rw [e]
        exact div_mem (hA _ (hXy i)) (hA _ (hXy j))
  have hC : ∀ c, ι (Polynomial.C c) ∈ L := fun c => by
    have h : c ∈ M := hM ▸ Subfield.mem_top c
    exact h
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  have hX : ι Polynomial.X ∈ L := by
    have e : ι Polynomial.X = ι (Polynomial.X * Polynomial.C (y j)) * ι (Polynomial.C (y j)⁻¹) := by
      rw [← map_mul, mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hj, Polynomial.C_1, mul_one]
    rw [e]
    exact mul_mem (hA _ (hXy j)) (hC _)
  have hall : ∀ p, ι p ∈ L := fun p => by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      exact mul_mem (hC c) (pow_mem hX n)
  have hcl : Subring.closure (ι '' (A : Set (Polynomial Ω))) ≤ (A.toSubring.map ι) :=
    Subring.closure_le.2 (by rintro _ ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩)
  refine ⟨fun p => ?_⟩
  obtain ⟨_, ha₀, _, hb₀, hab⟩ := Subfield.mem_closure_iff.1 (hall p)
  obtain ⟨a, ha, rfl⟩ := hcl ha₀
  obtain ⟨b, hb, rfl⟩ := hcl hb₀
  by_cases hb0 : b = 0
  · rw [hb0, map_zero, div_zero, eq_comm, map_eq_zero_iff ι hι] at hab
    rw [hab]
    exact isAlgebraic_zero
  · have e : b * p = a := by
      apply hι
      rw [map_mul, ← hab, mul_div_cancel₀ _ ((map_ne_zero_iff ι hι).2 hb0)]
    refine ⟨Polynomial.C (⟨b, hb⟩ : A) * Polynomial.X - Polynomial.C (⟨a, ha⟩ : A), fun h => hb0 ?_, ?_⟩
    · have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q 1) h
      simp at this
      exact congrArg Subtype.val this
    · simp [e]

theorem ringKrullDim_imageIdeal_of_birational : ∀ (k : Type) [Field k] (S : LinSys k), S.IsVariety →
    S.BasePointFree → S.Birational →
    ringKrullDim (MvPolynomial (Fin S.N) k ⧸ S.imageIdeal) = ((S.D + 1 : ℕ) : WithBot ℕ∞) := by
  intro k _ S h hb ⟨η, hη, hr⟩
  have := HeightExists.isIntegral h
  let Ω := S.Y.residueField η
  let : Algebra k Ω := (S.baseHom (resPt η)).toAlgebra
  let x : S.Pt Ω := ⟨resPt η, S.comp_str _⟩
  set y : Fin S.N → Ω := S.coords (resPt η) with hy
  have hI : S.imageIdeal = coneIdeal k y :=
    imageIdeal_eq_coneIdeal_of_generic k Ω S x (by rw [ptOf_resPt]; exact hη) 1 y one_ne_zero
      (one_smul _ _).symm
  have hD : Algebra.trdeg k Ω = S.D :=
    (residueField_fg_trdeg_of_smoothOfRelativeDimension S.str S.D h.smooth η
      fun z hz => (hz.antisymm (hη.specializes trivial)).eq).2
  rw [hI]
  have := isPrime_coneIdeal (K := k) y
  refine ringKrullDim_eq_of_trdeg_eq k _ ?_
  let f := Ideal.kerLiftAlg (coneMap k y)
  have hf : Function.Injective f := Ideal.kerLiftAlg_injective _
  let A := f.range
  let e := AlgEquiv.ofInjective f hf
  have hQA : Algebra.trdeg k (MvPolynomial (Fin S.N) k ⧸ coneIdeal k y) = Algebra.trdeg k A :=
    le_antisymm (trdeg_le_of_injective e.toAlgHom e.injective)
      (trdeg_le_of_injective e.symm.toAlgHom e.symm.injective)
  have hXy : ∀ i, Polynomial.X * Polynomial.C (y i) ∈ A := fun i => by
    have := AlgHom.mem_range_self f (Ideal.Quotient.mk _ (X i))
    rw [Ideal.kerLiftAlg_mk] at this
    simp only [coneMap, aeval_X] at this
    exact this
  have := ConeDim.isAlgebraic_of_closure_eq_top y (hb.coords_ne_zero _) hr A hXy
  have : FaithfulSMul k A := (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have : FaithfulSMul A (Polynomial Ω) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  rw [hQA, ← GlobalTheory.trdeg_eq_of_isAlgebraic_top k A (Polynomial Ω), ← trdeg_add_eq k Ω (A := Polynomial Ω),
    Polynomial.trdeg_of_isDomain, hD]
  norm_cast

end GlobalTheory.Adelic.ConeDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimLocalizationGraphIdealMinimalPrimeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_localization_graphIdeal_minimalPrime : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    [Algebra (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (k : ℕ) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  𝔭 ∈ (graphIdeal E R π ρ).minimalPrimes →
  ringKrullDim (locAt (L := L) 𝔭) = k + 1 := by
  first | exact @GlobalTheory.GraphLocal.dim_locAt_graph | exact GlobalTheory.GraphLocal.dim_locAt_graph | (intros; apply GlobalTheory.GraphLocal.dim_locAt_graph <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypeHasSphericalHeckeEigensystem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.RowEig

open Formalism.IndefR.principalLevelFrame

variable {D : D7}

def rtV (V : HSp D) : GA D V →* Module.End ℂ (GA D V → ℂ) where
  toFun g := { toFun := fun f h => f (h * g), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  map_one' := by ext f h; simp
  map_mul' g g' := by ext f h; simp [mul_assoc]

theorem rtV_apply (V : HSp D) (g : GA D V) (f : GA D V → ℂ) (h : GA D V) : rtV V g f h = f (h * g) := rfl

variable {V : HSp D} {n : ℕ}

theorem pre_psi (Q : RowPsi V n) (z : Formalism.AUTREP.GAf D.host.E n) : pre Q (Q.ψ z) = z := by
  have h : ∃ x, Q.ψ x = Q.ψ z := ⟨z, rfl⟩
  unfold pre
  rw [dite_eq_left h]
  exact Q.inj h.choose_spec

theorem psi_pre (Q : RowPsi V n) {γ : GA D V} (hγ : γ ∈ GfC V) : Q.ψ (pre Q γ) = γ := by
  obtain ⟨h, hh⟩ := Q.onto γ hγ
  have h' : ∃ x, Q.ψ x = γ := ⟨h, hh⟩
  unfold pre
  rw [dite_eq_left h']
  exact h'.choose_spec


open Classical in
def lift (Q : RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n → ℂ) : GA D V → ℂ :=
  fun g => if g ∈ GfC V then x (pre Q g) else 0

theorem rtV_lift_psi (Q : RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n → ℂ) {γ : GA D V} (hγ : γ ∈ GfC V)
    (y : Formalism.AUTREP.GAf D.host.E n) : rtV V γ (lift Q x) (Q.ψ y) = x (y * pre Q γ) := by
  rw [rtV_apply]
  have hmem : Q.ψ y * γ ∈ GfC V := (GfC V).mul_mem (Q.into y) hγ
  have heq : Q.ψ y * γ = Q.ψ (y * pre Q γ) := by rw [map_mul, psi_pre Q hγ]
  unfold lift
  rw [if_pos hmem, heq, pre_psi]

theorem lift_fixed (Q : RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n → ℂ) (K : Set (GA D V)) (hK : K ⊆ GfC V)
    (hx : ∀ κ, Q.ψ κ ∈ K → Formalism.L2.NG.rt D.host.E n κ x = x) : ∀ k ∈ K, rtV V k (lift Q x) = lift Q x := by
  intro k hk
  have hkG : k ∈ GfC V := hK hk
  funext g
  rw [rtV_apply]
  by_cases hg : g ∈ GfC V
  · have hgk : g * k ∈ GfC V := (GfC V).mul_mem hg hkG
    have heq : g * k = Q.ψ (pre Q g * pre Q k) := by rw [map_mul, psi_pre Q hg, psi_pre Q hkG]
    have hfix := congrFun (hx (pre Q k) (by rw [psi_pre Q hkG]; exact hk)) (pre Q g)
    unfold lift
    rw [if_pos hgk, if_pos hg, heq, pre_psi]
    exact hfix
  · have hgk : g * k ∉ GfC V := fun h => hg (by simpa using (GfC V).mul_mem h ((GfC V).inv_mem hkG))
    unfold lift
    rw [if_neg hgk, if_neg hg]

theorem heckeOperator_apply' (Q : RowPsi V n) (B : Finset (GA D V)) (x : Formalism.AUTREP.GAf D.host.E n → ℂ) (y : Formalism.AUTREP.GAf D.host.E n) :
    Hecke₃ Q B x y = ∑ γ ∈ B, x (y * pre Q γ) := by
  simp [Hecke₃, heckeG, LinearMap.sum_apply, Finset.sum_apply, Formalism.L2.NG.rt]

theorem sph_mem_GfC {P : Pl D.host.E} {d : List ℤ} {B : Finset (GA D V)} (hB : SphOp V P d B) : ∀ γ ∈ B, γ ∈ GfC V := by
  obtain ⟨e, f, ϖ, α, -, -, -, -, -, -, -, -, -, -, hR⟩ := hB
  exact fun γ hγ => (hR.1 γ hγ).1

theorem hyp_sub (P : Pl D.host.E) : GlobalTheory.Hk3.hyp V P ⊆ GfC V := fun k hk => hk.1.1

theorem heckeOperator_eq_of_spherical (Q : RowPsi V n) (P : Pl D.host.E) (d : List ℤ) (B B' : Finset (GA D V)) (hB : SphOp V P d B)
    (hB' : SphOp V P d B') (x : Formalism.AUTREP.GAf D.host.E n → ℂ) (hx : ∀ κ, Q.ψ κ ∈ GlobalTheory.Hk3.hyp V P → Formalism.L2.NG.rt D.host.E n κ x = x) :
    Hecke₃ Q B x = Hecke₃ Q B' x := by
  have hu := lift_fixed Q x (GlobalTheory.Hk3.hyp V P) (hyp_sub P) hx
  have e1 := ((GlobalTheory.SphLabelOps.label_operators V P).1 d B hB).2 (GA D V → ℂ) (rtV V) (lift Q x) hu
  have e2 := ((GlobalTheory.SphLabelOps.label_operators V P).1 d B' hB').2 (GA D V → ℂ) (rtV V) (lift Q x) hu
  have e := e1.trans e2.symm
  funext y
  have ey := congrFun e (Q.ψ y)
  rw [Finset.sum_apply, Finset.sum_apply] at ey
  rw [heckeOperator_apply', heckeOperator_apply']
  rw [Finset.sum_congr rfl (fun γ hγ => rtV_lift_psi Q x (sph_mem_GfC hB γ hγ) y),
    Finset.sum_congr rfl (fun γ hγ => rtV_lift_psi Q x (sph_mem_GfC hB' γ hγ) y)] at ey
  exact ey

theorem sph_of_full {J : Set (GA D V)} {χ : GA D V → ℂ} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {P : Pl D.host.E}
    {d : List ℤ} {B : Finset (GA D V)} (h : Hecke₂ V J χ S P d B) : SphOp V P d B := by
  obtain ⟨e, f, ϖ, α, -, hPI, h1, h2, hd, hJ, -, hα, hdiv, hR, hcos⟩ := h
  have hset : {k | k ∈ J ∧ SuppF V f k} = {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := by
    ext k
    exact ⟨fun ⟨a, b⟩ => ⟨(hJ k b).1 a, b⟩, fun ⟨a, b⟩ => ⟨(hJ k b).2 a, b⟩⟩
  rw [hset] at hcos
  exact ⟨e, f, ϖ, α, fun v hv => absurd hv (Finset.notMem_empty v), hPI, h1, h2, hd, fun _ _ => Iff.rfl,
    fun _ _ _ => rfl, hα, hdiv, hR, hcos⟩

end GlobalTheory.RowEig

namespace GlobalTheory.RowEig

open Formalism.IndefR.principalLevelFrame


set_option maxHeartbeats 1000000 in
theorem row_type_eig : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ SF, IsSF R SF → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π, π ∈ principalLevelFrame.OccRows R.θ PY (R.MY 0) (fun b => (levS _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun b => (levChi _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun _ => R.e0) → ∀ i0, ∃ c, principalLevelFrame.IsEigOf (PW i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF π c := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk hCore hX SF hSF n hF PY PW hPY hPW π hπ i0
  classical
  have hsc : ∀ Pr d B, SphOp (Wc D i0) Pr d B → ∃ a : ℂ, ∀ x ∈ π.S,
      (∀ κ, (PW i0).ψ κ ∈ GlobalTheory.Hk3.hyp (Wc D i0) Pr → Formalism.L2.NG.rt D.host.E n κ x = x) → Hecke₃ (PW i0) B x = a • x :=
    fun Pr d B h => _root_.GlobalTheory.SphScalar.spherical_scalar hF (PW i0) (hPW i0) π Pr d B h

  obtain ⟨c0, hBase⟩ := hCore.lev.βW i0
  rw [one_pow] at hBase

  have hfix : ∀ Pr d B, Hecke₂ (Wc D i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A))))
      (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF Pr d B → ∀ x,
      IsTypeVec ((PW i0).ψ ⁻¹' levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A))))
        (fun κ => levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A))) ((PW i0).ψ κ)) x →
      ∀ κ, (PW i0).ψ κ ∈ GlobalTheory.Hk3.hyp (Wc D i0) Pr → Formalism.L2.NG.rt D.host.E n κ x = x := by
    intro Pr d B hB x hx κ hκ
    have hOff : OffS D SF Pr := by
      obtain ⟨e, f, ϖ, α, h, -⟩ := hB
      exact h
    have hGood : Good R A.μ0 Pr := ((GlobalTheory.GoodPrimes.good_primes R F hCore.lev).2.2.1 SF hSF Pr).mp hOff
    have hN : ((1 : ℕ) : 𝓞 D.host.E) ∉ Pr.asIdeal := by
      rw [Nat.cast_one]
      exact (Ideal.ne_top_iff_one _).mp Pr.isPrime.ne_top
    have hL := (GlobalTheory.LevOp.level_operators (Wc D i0) (R.βW i0) (R.ΛW i0) 1 (R.datWp i0 (R.levL F false (sg0 D A))) hBase Pr hN
      (fun PP hPP => by
        rcases hPP with h | h
        · exact hGood PP (Or.inl h)
        · exact absurd h (Finset.notMem_empty PP))).1 _ hκ
    have := hx κ hL.1
    rw [this]
    dsimp only
    rw [hL.2, one_smul]
  refine ⟨fun Pr d => if h : ∃ B, Hecke₂ (Wc D i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A))))
      (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF Pr d B then
      (hsc Pr d h.choose (sph_of_full h.choose_spec)).choose else 0, ?_, ?_, ?_⟩
  · exact _root_.GlobalTheory.RowTypeVec.vec_of_rows R F hOk hCore hX hF PY PW hPY hPW π hπ i0
  · intro Pr d B hB x hxS hx
    have hex : ∃ B, Hecke₂ (Wc D i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A))))
      (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF Pr d B := ⟨B, hB⟩
    have hxf := hfix Pr d B hB x hx
    dsimp only
    rw [dite_eq_left hex, heckeOperator_eq_of_spherical (PW i0) Pr d B hex.choose (sph_of_full hB) (sph_of_full hex.choose_spec) x hxf]
    exact (hsc Pr d hex.choose (sph_of_full hex.choose_spec)).choose_spec x hxS hxf
  · intro Pr d hne
    exact dif_neg hne

end GlobalTheory.RowEig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsInSpanOfRankNormalForm
section
open ValuativeRel Matrix

namespace GlobalTheory

theorem rows_mem_span_of_isUnit_mul (K : Type) [Field K] (A D : Type) [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D] (r : ℕ) (X : Matrix A D K) (H : Matrix (Fin r) A K)
    (Q : Matrix D (Fin r) K) (hX : X.rank ≤ r) (hU : IsUnit (H * X * Q)) :
    ∀ i, ∃ s : Fin r → K, X i = s ᵥ* (H * X) := by
  intro i
  have hle : Submodule.span K (Set.range (H * X)) ≤ Submodule.span K (Set.range X) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have : (H * X) j = ∑ a, H j a • X a := by
      ext d; simp [Matrix.mul_apply, Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have h1 : r ≤ (H * X).rank := by
    have := Matrix.rank_mul_le_left (H * X) Q
    rw [Matrix.rank_of_isUnit _ hU] at this
    simpa using this
  have heq : Submodule.span K (Set.range (H * X)) = Submodule.span K (Set.range X) := by
    apply Submodule.eq_of_le_of_finrank_le hle
    have e1 : X.rank = Module.finrank K (Submodule.span K (Set.range X)) :=
      Matrix.rank_eq_finrank_span_row X
    have e2 : (H * X).rank = Module.finrank K (Submodule.span K (Set.range (H * X))) :=
      Matrix.rank_eq_finrank_span_row (H * X)
    omega
  have hi : X i ∈ Submodule.span K (Set.range (H * X)) := heq ▸ Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hi
  refine ⟨c, ?_⟩
  rw [← hc]
  ext d
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDetEqUnitMulNormAtInertStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitian_det_eq_unit_mul_norm_at_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n r s : ℕ) (W : Spc F E n), W.IsSkew σ B r s → Even n →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) →
    ∃ (y : Fv F v ⊗[F] E) (u : Fv F v), Valued.v u = 1 ∧
      (1 : Fv F v) ⊗ₜ[F] W.J.det = algebraMap (Fv F v) (Fv F v ⊗[F] E) u *
        (y * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ y) := by
  first | exact @GlobalTheory.SkewDetParity.det_eq_unit_mul_norm | exact GlobalTheory.SkewDetParity.det_eq_unit_mul_norm | (intros; apply GlobalTheory.SkewDetParity.det_eq_unit_mul_norm <;> assumption)
end

