module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalRingCardinality.HostCls
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0004
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0002
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GlobalOrthonormalBasisFour
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0137
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0153

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeOfUnitarisableHasSatake
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.SatHecke

open GlobalTheory.LatHecke GlobalTheory.LFun Formalism.UG

section Lemmas

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))


variable {w} in
theorem diagJ_det_ne {n : ℕ} {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (j : ℕ) :
    (diagJ n ϖ j).det ≠ 0 := by
  have h0 : ϖ ≠ 0 := fun e => by simp [IsUnifV, e] at hϖ
  rw [diagJ, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun i _ => by split_ifs <;> simp [h0]

theorem stab_iff (n : ℕ) (g : GL (Fin n) (w.adicCompletion E)) :
    glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 =
      (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ↔ g ∈ GLint (Fin n) (Ov E w) :=
  _root_.GlobalTheory.LatHecke.glMap_std_eq_iff_mem_GLint E w n g

theorem coset_of_elem (n : ℕ) (ϖ : w.adicCompletion E) (hϖ : IsUnifV E w ϖ) (j : ℕ) (hj : j ≤ n)
    (g : GL (Fin n) (w.adicCompletion E)) :
    haveI := GlobalTheory.RowSatakeBound.finite_residue w
    glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈
      Subtype.val '' subElem j (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) →
    ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (a : Matrix (Fin n) (Fin n) _) * diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) _) :=
  GlobalTheory.T.mem_cartanDoubleCoset_of_lattice_between_uniformizer E w n ϖ hϖ j hj g

theorem diag_elem (n : ℕ) (ϖ : w.adicCompletion E) (hϖ : IsUnifV E w ϖ) (S : Finset (Fin n))
    (d : GL (Fin n) (w.adicCompletion E))
    (hd : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (fun i => if i ∈ S then ϖ else 1)) :
    haveI := GlobalTheory.RowSatakeBound.finite_residue w
    glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈
      Subtype.val '' subElem S.card (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) :=
  GlobalTheory.T.glMap_diagUniformizer_elementarySublattice E w n ϖ hϖ S d hd

theorem elem_of_coset (n : ℕ) (ϖ : w.adicCompletion E) (hϖ : IsUnifV E w ϖ) (j : ℕ) (hj : j ≤ n)
    (g : GL (Fin n) (w.adicCompletion E)) :
    haveI := GlobalTheory.RowSatakeBound.finite_residue w
    (∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (a : Matrix (Fin n) (Fin n) _) * diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) _)) →
    glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈
      Subtype.val '' subElem j (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) := by
  haveI := GlobalTheory.RowSatakeBound.finite_residue w
  rintro ⟨a, ha, b, hb, e⟩
  set S : Finset (Fin n) := Finset.univ.filter fun i => (i : ℕ) < j
  have hS : S.card = j := by
    have : S = (Finset.range j).attachFin (n := n) (fun m hm => lt_of_lt_of_le (Finset.mem_range.1 hm) hj) := by
      ext i; simp [S]
    rw [this, Finset.card_attachFin, Finset.card_range]
  set D := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagJ n ϖ j) (diagJ_det_ne hϖ j)
  have hg : g = a * D * b := Units.ext (by rw [e]; simp [D, Matrix.GeneralLinearGroup.mkOfDetNeZero])
  obtain ⟨M, hM, hM'⟩ := diag_elem w n ϖ hϖ S D (by simp [D, Matrix.GeneralLinearGroup.mkOfDetNeZero, diagJ, S])
  rw [hS] at hM
  have hstd : ∀ k ∈ GLint (Fin n) (Ov E w), k • std (w.adicCompletionIntegers E) (w.adicCompletion E) n =
      std (w.adicCompletionIntegers E) (w.adicCompletion E) n := fun k hk => Subtype.ext ((stab_iff w n k).2 hk)
  refine ⟨glLat a M, ?_, ?_⟩
  · have := (smul_mem_subElem_iff a j M (std (w.adicCompletionIntegers E) (w.adicCompletion E) n)).2 hM
    rw [hstd a ha] at this
    exact this
  · rw [hg, glMap_mul, glMap_mul, (stab_iff w n b).2 hb, ← hM']
    rfl

end Lemmas

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}

theorem Tj_eq_dosetInd {n : ℕ} {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (j : ℕ) :
    Tj ℂ n (Ov E w) ϖ j = dosetInd ℂ (GLint (Fin n) (Ov E w))
      (Matrix.GeneralLinearGroup.mkOfDetNeZero (diagJ n ϖ j) (diagJ_det_ne hϖ j)) := by
  unfold Tj dosetInd
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
  refine exists_congr fun a => and_congr_right fun _ => exists_congr fun b => and_congr_right fun _ => ?_
  rw [Units.ext_iff]
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem heckeVec_Tj_eq_sum {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) {x : V} (hx : x ∈ fixed ρ (KGL w (n := n)))
    {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {j : ℕ} (hj : j ≤ n)
    (s : Finset (GL (Fin n) (w.adicCompletion E)))
    (hs : haveI := GlobalTheory.RowSatakeBound.finite_residue w
      Set.BijOn (fun g => glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1) s
        (Subtype.val '' subElem j (std (w.adicCompletionIntegers E) (w.adicCompletion E) n))) :
    heckeVec ρ (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) x = ∑ g ∈ s, ρ g x := by
  haveI := GlobalTheory.RowSatakeBound.finite_residue w
  set D := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagJ n ϖ j) (diagJ_det_ne hϖ j)
  have hD : ∀ g : GL (Fin n) (w.adicCompletion E), g ∈ DoubleCoset.doubleCoset D (KGL w (n := n) : Set _) (KGL w (n := n)) ↔
      ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
        (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (a : Matrix (Fin n) (Fin n) _) * diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) _) := by
    intro g
    simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    refine exists_congr fun a => and_congr_right fun _ => exists_congr fun b => and_congr_right fun _ => ?_
    rw [Units.ext_iff]
    simp [D, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  rw [Tj_eq_dosetInd hϖ j]
  refine heckeVec_dosetInd hx (fun γ hγ => (hD γ).2 (coset_of_elem w n ϖ hϖ j hj γ (hs.mapsTo hγ)))
    fun g hg => ?_
  obtain ⟨γ, hγ, e⟩ := hs.surjOn (elem_of_coset w n ϖ hϖ j hj g ((hD g).1 hg))
  have hmem : ∀ γ' : GL (Fin n) (w.adicCompletion E),
      γ'⁻¹ * g ∈ KGL w (n := n) ↔ glMap γ' (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 =
        glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 := fun γ' => by
    rw [← stab_iff w n, glMap_mul]
    constructor
    · intro h
      conv_lhs => rw [← h]
      rw [← glMap_mul, mul_inv_cancel, glMap_one]
    · intro h
      rw [← h, ← glMap_mul, inv_mul_cancel, glMap_one]
  refine ⟨γ, ⟨hγ, (hmem γ).2 e⟩, fun γ' ⟨hγ', h'⟩ => hs.injOn hγ' hγ ?_⟩
  exact ((hmem γ').1 h').trans e.symm

end GlobalTheory.SatHecke

namespace GlobalTheory.SatHecke

open GlobalTheory.LatHecke GlobalTheory.LFun Formalism.UG

def formCore {X : Type} [AddCommGroup X] [Module ℂ X] (B : X →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ)
    (hB : ∀ v w, B w v = starRingEnd ℂ (B v w)) (hp : ∀ v, v ≠ 0 → 0 < (B v v).re) :
    InnerProductSpace.Core ℂ X where
  inner x y := B y x
  conj_inner_symm x y := (hB x y).symm
  re_inner_nonneg x := by
    by_cases h : x = 0
    · simp [h]
    · exact (hp x h).le
  add_left x y z := by change B z (x + y) = B z x + B z y; simp
  smul_left x y r := by change B y (r • x) = _ * B y x; simp
  definite x h := by
    by_contra h0
    have := hp x h0
    change B x x = 0 at h
    rw [h] at this
    simp at this

end GlobalTheory.SatHecke

namespace GlobalTheory.SatHecke

theorem isUnitarySatakeAt_of_hasSatake : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ), letI := GlobalTheory.LocalData.complRel w; haveI := GlobalTheory.LocalData.isLocalField w; ∀ (π : Irr (w.adicCompletion E) n) (α : Fin n → ℂˣ), HasSatake π.π α → IsUnitarisable π.π → GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w n (Finset.univ.val.map fun i => (α i : ℂ)) := by
  intro E _ _ w n
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  intro π α hS hU
  have hG : GlobalTheory.LGrp.HasSatakeGL π.π (Finset.univ.val.map α) :=
    (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ π.π _).2 ⟨α, rfl, hS⟩
  obtain ⟨x, hx⟩ := (GlobalTheory.LFun.SatCompare.hasSatGL_of_hasSatakeGL hG).exists_vec
  obtain ⟨B, hB, hpos, hi⟩ := hU
  letI cd : InnerProductSpace.Core ℂ π.V := formCore B hB hpos
  letI : NormedAddCommGroup π.V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ π.V := InnerProductSpace.ofCore cd.toCore
  haveI := GlobalTheory.RowSatakeBound.finite_residue w
  have hn : ∀ y : π.V, ‖y‖ ^ 2 = (B y y).re := fun y => by
    rw [← @inner_self_eq_norm_sq ℂ]
    rfl
  refine ⟨by simp, π.V, inferInstance, inferInstance, π.π, x, fun g y => ?_, hx.1, fun g hg => ?_, fun k hk s hs => ?_⟩
  · have h2 : ‖π.π g y‖ ^ 2 = ‖y‖ ^ 2 := by rw [hn, hn, hi]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  · exact GlobalTheory.LGrp.mem_fixed.1 hx.2.1 g ((stab_iff w n g).1 hg)
  · obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
    rw [← heckeVec_Tj_eq_sum π.π hx.2.1 hϖ hk s hs, hx.2.2.2 ϖ hϖ k hk, GlobalTheory.LFun.satEig, Multiset.map_map]
    congr 2
    rw [GlobalTheory.RowSatakeBound.qRes_eq_normV w]
    have hq : (Formalism.UG.qV E w : ℕ) = normV w := by
      unfold Formalism.UG.qV normV
      exact Ideal.absNorm_eq_natCard _
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _), hq]
    push_cast
    rfl

end GlobalTheory.SatHecke
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacobiOfClass
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HostInert


open Formalism.InvariantFactorPaths.G7 (lgF at1) in
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp) in
theorem inParamK_eq {l : ℕ} [Fact l.Prime] {ι : Type} (f : MvPowerSeries ι ℂ_[l]) :
    @Formalism.MainNotions.FormalGroupSystem.inParamK l _ ι ℂ_[l] _ (wittFractionAlgebraCp l) f = MvPowerSeries.subst (fun i => at1 i (lgF ℂ_[l] l)) f := by
  unfold Formalism.MainNotions.FormalGroupSystem.inParamK
  have hlog : PowerSeries.map (k0ToC l) (Formalism.MainNotions.FormalGroupSystem.logF l) = lgF ℂ_[l] l := by
    ext n
    rw [PowerSeries.coeff_map]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.MainNotions.FormalGroupSystem.logF, lgF, PowerSeries.coeff_mk, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_mul]
    split_ifs <;> simp
  congr 1
  funext i
  rw [show @algebraMap (Formalism.MainNotions.FormalGroupSystem.K0 l) ℂ_[l] _ _ (wittFractionAlgebraCp l) = k0ToC l from rfl, hlog]
  rfl

theorem jacobi_of_class (D : D7) (p : ℕ) [Fact p.Prime] (h : IsResidueClassZero D p ∨ IsSg D p) :
    jacobiSym (-(D.host.d : ℤ)) p = -1 := by
  have hp : p.Prime := Fact.out
  have hd : D.host.d.Prime := D.host.hyp.2.1
  have key : p ≠ D.host.d ∧ jacobiSym (-(D.host.d : ℤ)) p ≠ 1 := by
    have h' : D.host.cls p = PrimeClass.inertClass ∨
        D.host.cls p = PrimeClass.signal := h
    rcases h' with h' | h'
    · obtain ⟨-, -, h3, h4, -⟩ := (primeClass_eq_inert_iff _).1 h'
      exact ⟨h3, h4⟩
    · obtain ⟨-, -, h3, h4, -⟩ := (primeClass_eq_signal_iff _).1 h'
      exact ⟨h3, h4⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rcases jacobiSym.trichotomy (-(D.host.d : ℤ)) p with h0 | h1 | h1
  · exfalso
    rw [jacobiSym.eq_zero_iff_not_coprime] at h0
    apply h0
    have : Nat.Coprime D.host.d p := (Nat.coprime_primes hd hp).2 key.1.symm
    simpa [Int.gcd_neg, Int.gcd_natCast_natCast] using this
  · exact absurd h1 key.2
  · exact h1

theorem hostAt_inert : Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam := by
  intro h1 h2 h3 D cc δ B χ hc hδ hχ p _ lam h5 hcl
  have hin := jacobi_of_class D p hcl
  obtain ⟨cc', δ', g, -, -, hL, hlam, hAt, hM, hLT⟩ := h1 D cc δ hc hδ p h5 hin lam
  obtain ⟨g2, g3, ε, s2, -, -, -, -, hn, ⟨a1, a2, a3, a4, a5, -, F, hF, -⟩, hD⟩ := h2 D cc' δ' p g hLT hAt h5 hin hM
  obtain ⟨σ, hσ, -⟩ := Formalism.L2.Th1.D.fieldDataCM p h5
  refine ⟨_, g2, g3, s2, ε, σ, F, hn, ⟨h5, a1, a2, a3, a4, hσ, hF, a5 σ hσ⟩, ?_⟩
  intro N N' L L' hA
  obtain ⟨r, b, hb, ho⟩ := Formalism.L2.KerInert.orthBasisExists_of Formalism.L2.KerInert.global_orthonormal_basis_four
    Formalism.L2.KerInert.weakApprox_of_approx_and_separation D p h5 hin N N' L L' hA
  refine ⟨r, b, hb, ho, fun G hG => ?_⟩
  obtain ⟨C, wq, hC, hw, hd⟩ := hD D
  have hΛ : g.abelian₂ = B.tor.abelian₂ := hAt.2.2.2.1.trans hL
  subst hlam
  rw [hΛ] at hC hw hd
  have := hd N N' r b G (h3 D cc δ B hc hδ χ hχ p h5 hin g.lam N N' L L' hA G hG C wq r b hC hw hb ho)
  rw [HostLog.iff_phSum]
  rw [inParamK_eq] at this
  exact this

end GlobalTheory.KerStd.HostInert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NabLeDelOfLocal
section
noncomputable section

namespace GlobalTheory.ColPeriod.WeylLoc

open NumberField IsDedekindDomain MvPolynomial Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
theorem localized_le_of_le_localized {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    {N N' : Submodule (𝓞 K) V} (h : N ≤ localization₂ w.asIdeal N') : localization₂ w.asIdeal N ≤ localization₂ w.asIdeal N' := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, h'⟩ := h hx
  exact ⟨t * s, mul_mem ht hs, by rw [mul_smul]; exact h'⟩

omit [NumberField K] in
theorem intCast_notMem {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) {c : ℤ}
    (hc : ¬ (p : ℤ) ∣ c) : (c : 𝓞 K) ∉ w.asIdeal := by
  intro ha
  have hco : IsCoprime (p : ℤ) c := (Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 hc
  obtain ⟨x, y, e⟩ := hco.map (Int.castRingHom (𝓞 K))
  simp only [eq_intCast, Int.cast_natCast] at e
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw) (w.asIdeal.mul_mem_left _ ha)))

theorem nablaSq_le_locP (h : NablaMemDeltaLocallyAtLargePrime) {n : ℕ} (lam : DomWeight n) {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) (hs : lam.spread < p) :
    (nablaSq (𝓞 K) n lam).map (toK K _) ≤ localization₂ w.asIdeal ((delSq (𝓞 K) n lam).map (toK K _)) := by
  unfold nablaSq
  rw [GlobalTheory.StdDual.dualWeyl_eq, Submodule.map_span, Submodule.span_le,
    ← GlobalTheory.StdDual.image_bidSet (Int.castRingHom (𝓞 K))]
  rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  have hf' : f ∈ nablaSq ℤ n lam := by
    unfold nablaSq
    rw [GlobalTheory.StdDual.dualWeyl_eq]
    exact Submodule.subset_span hf
  obtain ⟨c, hc, hcf⟩ := h n lam p hp hs f hf'
  refine ⟨(c : 𝓞 K), intCast_notMem hp w hw hc, map (Int.castRingHom (𝓞 K)) (c • f),
    GlobalTheory.TestLat.WeylLocal.map_mem_weyl _ _ hcf, ?_⟩
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul (𝓞 K), map_smul]
  rfl

theorem nabStd_le_locP (h : NablaMemDeltaLocallyAtLargePrime) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) (hs : ∀ τ, (lam τ).spread < p) :
    nabStd K lam ≤ localization₂ w.asIdeal (delStd K lam) := by
  unfold nabStd Formalism.GradedWeylDivisibility.tensorLat
  rw [Submodule.span_le]
  rintro _ ⟨f, hf, rfl⟩
  exact GlobalTheory.TestLat.WeylLocal.ten_mem_locP w _ f fun τ => nablaSq_le_locP h (lam τ) hp w hw (hs τ) (hf τ)

theorem nabLeDel_of_local (h : NablaMemDeltaLocallyAtLargePrime)
    (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsFullLattice K (M τ))
    (p : ℕ) (w : HeightOneSpectrum (𝓞 K)) (hp : p.Prime) (hw : (p : 𝓞 K) ∈ w.asIdeal)
    (hs : ∀ τ, (lam τ).spread < p) :
    localization₂ w.asIdeal (nabK lam M) ≤ localization₂ w.asIdeal (delK lam M) := by
  intro x hx
  choose B hB using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (hM τ) w
  have h1 := GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι n lam M hM w B hB
  have hx' : x.1 ∈ localization₂ w.asIdeal (nabP lam M) := hx
  change x.1 ∈ localization₂ w.asIdeal (delP lam M)
  rw [h1.1] at hx'
  rw [h1.2]
  exact Submodule.map_mono (localized_le_of_le_localized w (nabStd_le_locP h lam hp w hw hs)) hx'

end GlobalTheory.ColPeriod.WeylLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NuRowSuccEqWt
section
noncomputable section

namespace GlobalTheory.ColPeriod

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recWts)

theorem nuRow_succ_eq_wt (D : D7) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (τ : D.what₂.Tau) (n : ℕ) (hn : n < D.R.N j) :
    DV.nuRow D u (j + 1) τ n =
      ((Examples₂.wtN (D.hcW u τ) n + wG D.R ((D.hcW u τ).e ⟨j, hj⟩) (j + 1) : ℚ) : ℝ) := by
  have hw : DV.wSz D (j + 1) τ = (((D.hcW u τ).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold DV.wSz
    rw [dite_eq_left ⟨by omega, by omega⟩, D.hcW_e]
    rfl
  unfold DV.nuRow
  rw [hw]
  unfold DV.srcPar Examples₂.wtN Examples₂.blkN
  by_cases hk : n < D.R.k
  · rw [dite_eq_left hk, dite_eq_left hk]
    unfold hcToWeightQ rhoVec wG Ranks.N
    push_cast
    ring
  · have hb : (n - D.R.k) / (D.R.t + 1) < D.R.m := by
      have hN : n < D.R.k + j * (D.R.t + 1) := hn
      have h2 : n - D.R.k < j * (D.R.t + 1) := Nat.sub_lt_left_of_lt_add (by omega) hN
      have h3 : (n - D.R.k) / (D.R.t + 1) < j := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h2)
      omega
    rw [dite_eq_right hk, dite_eq_right hk, dite_eq_left hb, dite_eq_left hb]
    have hnat : n = D.R.k + (n - D.R.k) / (D.R.t + 1) * (D.R.t + 1) + (n - D.R.k) % (D.R.t + 1) := by
      have := Nat.div_add_mod (n - D.R.k) (D.R.t + 1)
      rw [mul_comm] at this
      omega
    have key : (n : ℝ) = (D.R.k : ℝ) + (((n - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) * ((D.R.t : ℝ) + 1)
        + (((n - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
      conv_lhs => rw [hnat]
      push_cast
      ring
    unfold wG Ranks.N
    push_cast
    linear_combination key

theorem partitionSize : PartitionSize := by
  intro D EX u j hj τ
  unfold nuAbs
  show ∑ i ∈ Finset.range (D.R.N j), DV.nuRow D u (j + 1) τ i = _
  rw [Finset.sum_range, Int.cast_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [nuRow_succ_eq_wt D u j hj τ a a.2]
  have h1 := Wts.nuW_eq (recWts EX) u hj τ a
  have h2 := lamOf_wtN ((recWts EX).hc u τ) hj.le a
  have h3 : (((recWts EX).nuW u (j + 1) τ).w a : ℝ) = ((((recWts EX).nuW u (j + 1) τ).w a : ℚ) : ℝ) := by
    simp
  rw [h3, h1]
  unfold Wts.lamN
  rw [h2]
  rfl

end GlobalTheory.ColPeriod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperatorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_family_normal_operators : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ t, ∃ h, IsOpsX R t h ∧ NormalFam (Good R t) h) ∧ ∀ i t, ∃ h, IsOpsV R i t h ∧ NormalFam (Good R t) h := by
  first | exact @GlobalTheory.DefiniteOps.definite_ops | exact GlobalTheory.DefiniteOps.definite_ops | (intros; apply GlobalTheory.DefiniteOps.definite_ops <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SqrtNegPrimeMemKur
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory.SqrtUnram

theorem sqrt_neg_prime_mem_Kur : ∀ (l : ℕ) [Fact l.Prime] (q : ℕ), q.Prime → q % 4 = 3 → l ≠ q →
    ∀ x : PadicAlgCl l, x ^ 2 = -(q : PadicAlgCl l) → x ∈ Loc.MaximalUnramifiedExtension l := by
  intro l _ q hq h4 hne x hx
  exact GlobalTheory.MemN.SelfGood.sqrt_mem q hq h4 _
    (fun z hz => GlobalTheory.MemN.SelfGood.root_mem_Kur hq.pos
      (fun hd => hne ((Nat.prime_dvd_prime_iff_eq Fact.out hq).1 hd)) hz) x hx

end GlobalTheory.SqrtUnram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarySegmentOfCentralUnit
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

noncomputable section

namespace GlobalTheory.UnitLSeg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.UnitLSeg

end
end

