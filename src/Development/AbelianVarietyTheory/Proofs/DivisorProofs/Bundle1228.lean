module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0824
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0164
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.CCRFock

variable {V : Type} [AddCommGroup V] [Module ℂ V]

open scoped IsMulCommutative in
def polEval {ι : Type} (m : ι → Module.End ℂ V) (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V) :
    MvPolynomial ι ℂ →ₗ[ℂ] V :=
  letI : IsMulCommutative (Algebra.adjoin ℂ (Set.range m)) :=
    Algebra.isMulCommutative_adjoin ℂ (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact hm i j)
  (LinearMap.applyₗ f₀ ∘ₗ (Algebra.adjoin ℂ (Set.range m)).val.toLinearMap) ∘ₗ
    (MvPolynomial.aeval (fun i => (⟨m i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : Algebra.adjoin ℂ (Set.range m)))).toLinearMap

def polMap (W Λ : Type) [Fintype W] [DecidableEq W] :
    (⨂[ℂ] _ : W, MvPolynomial Λ ℂ) →ₗ[ℂ] MvPolynomial (W × Λ) ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ W (MvPolynomial (W × Λ) ℂ)).compLinearMap
    fun w => (MvPolynomial.rename (Prod.mk w)).toLinearMap)

def unitAt {W : Type} [DecidableEq W] {P Q R S : ℕ} (j : W × (Ix P Q × Ix R S)) (z : ℂ) :
    W → Matrix (Ix P Q) (Ix R S) ℂ :=
  Pi.single j.1 (Matrix.single j.2.1 j.2.2 z)

def fockM {W : Type} [DecidableEq W] {P Q R S : ℕ} (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V)
    (j : W × (Ix P Q × Ix R S)) : Module.End ℂ V :=
  (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAt j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAt j Complex.I))

def fockD {W : Type} [DecidableEq W] {P Q R S : ℕ} (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V)
    (j : W × (Ix P Q × Ix R S)) : Module.End ℂ V :=
  -((2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAt j 1) + (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAt j Complex.I)))

def coefM (z ε : ℂ) : ℂ := (z.re : ℂ) + ε * Complex.I * (z.im : ℂ)

def coefD (z ε : ℂ) : ℂ := -(z.re : ℂ) + ε * Complex.I * (z.im : ℂ)

end GlobalTheory.CCRFock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointCompositeLiftLeSpanBlockEigenspaces
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.AdjSpan


open _root_.Formalism.L2 in
theorem eigSum_le_span {K V H I : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] {σ : K →+* ℂ} {j : V →ₛₗ[σ] H}
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) {op : I → Module.End K V} {U : I → Module.End ℂ H}
    (hU : ∀ i v, U i (j v) = j (op i v)) (hc : Col.PairComm op) (hs : Col.SplitOver op)
    {C : (I → K) → Prop} {CC : (I → ℂ) → Prop} (hC : ∀ x, CC (fun i => σ (x i)) → C x) :
    Col.eigSum U CC ≤ Submodule.span ℂ (j '' (Col.eigSum op C : Set V)) := by
  have hcU : Col.PairComm U := fun i i' => GlobalTheory.AdjBlock.ext_of_span hsp fun v => by
    simp only [Module.End.mul_apply, hU]
    exact congrArg j (LinearMap.congr_fun (hc i i').eq v)
  have h1 : ∀ x, Col.eigAt op x ≤ (Col.eigAt U fun i => σ (x i)).comap j := by
    intro x v hv
    rw [Submodule.mem_comap, Col.eigAt, Submodule.mem_iInf]
    intro i
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 (Col.eigAt_le op x i hv)
    refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
    have : ∀ (k : ℕ) w, ((U i - σ (x i) • (1 : Module.End ℂ H)) ^ k) (j w) =
        j (((op i - x i • (1 : Module.End K V)) ^ k) w) := by
      intro k
      induction k with
      | zero => intro w; simp
      | succ k ih =>
        intro w
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← ih]
        simp [hU, map_smulₛₗ]
    rw [this, hk, map_zero]
  have h2 : ∀ Q : (I → K) → Prop, Submodule.span ℂ (j '' (Col.eigSum op Q : Set V)) ≤
      Col.eigSum U fun y => ∃ x, Q x ∧ y = fun i => σ (x i) := fun Q => by
    have : Col.eigSum op Q ≤ (Col.eigSum U fun y => ∃ x, Q x ∧ y = fun i => σ (x i)).comap j :=
      iSup₂_le fun x hx => (h1 x).trans (Submodule.comap_mono (Col.eigAt_le_eigSum ⟨x, hx, rfl⟩))
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    exact this hv
  have h3 : Submodule.span ℂ (j '' (Col.eigSum op C : Set V)) ⊔
      Submodule.span ℂ (j '' (Col.eigSum op (fun x => ¬ C x) : Set V)) = ⊤ := by
    rw [eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    obtain ⟨a, ha, c, hc', rfl⟩ := Submodule.mem_sup.1
      ((Col.isCompl_eigSum hc hs C).sup_eq_top ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule K V)))
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨a, ha, rfl⟩) (Submodule.subset_span ⟨c, hc', rfl⟩)
  have h4 : Disjoint (Col.eigSum U fun y => CC y ∨ ∃ x, C x ∧ y = fun i => σ (x i))
      (Col.eigSum U fun y => ∃ x, ¬ C x ∧ y = fun i => σ (x i)) := by
    refine Col.disjoint_eigSum hcU ?_
    rintro y hy ⟨x, hx, rfl⟩
    rcases hy with hy | ⟨x', hx', he⟩
    · exact hx (hC x hy)
    · have : x = x' := funext fun i => σ.injective (congrFun he i)
      exact hx (this ▸ hx')
  rw [Col.eigSum_or] at h4
  intro w hw
  obtain ⟨a, ha, c, hc', rfl⟩ := Submodule.mem_sup.1 (h3 ▸ (Submodule.mem_top : w ∈ (⊤ : Submodule ℂ H)))
  have h5 : c = 0 := by
    refine (Submodule.disjoint_def.1 h4) _ ?_ (h2 _ hc')
    have : c = (a + c) - a := by abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hw) (Submodule.mem_sup_right (h2 _ ha))
  rw [h5, add_zero]
  exact ha

theorem heckePolyOf_congr {L : Type} [Field L] (n q : ℕ) {a b : ℕ → L} (h : ∀ k, k ≤ n → a k = b k) :
    Formalism.L2.Col.heckePolyOf n q a = Formalism.L2.Col.heckePolyOf n q b := by
  unfold Formalism.L2.Col.heckePolyOf
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]

open Classical in
theorem evC_splitC {D : D7} (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) (z : ℕ → ℂ) :
    GlobalTheory.Hk3.evC V P a (GlobalTheory.Hk3.splitC V.rank z) = ∑ j ∈ Finset.range (V.rank + 1),
      z j * (if IsLab V P (splitLab V.rank j) then a (splitLab V.rank j) else 0) := by
  unfold GlobalTheory.Hk3.evC GlobalTheory.Hk3.splitC
  rw [← Finsupp.sum_finsetSum_index (by simp) (by intro d x y; split_ifs <;> simp [add_mul])]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.sum_single_index (by simp)]
  split_ifs <;> simp


open _root_.Formalism.L2 in
theorem range_le_span_blockSum {K V H E Pl ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {σ : K →+* ℂ} {j : V →ₛₗ[σ] H}
    (hV : FiniteDimensional K V)
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) {op : Pl × ℕ → Module.End K V} (hc : Col.PairComm op)
    (hs : Col.SplitOver op) {n m t : ℕ} (hm : m = n) {q : Pl → ℕ} {bl : List (Pl → K)}
    (hz : ∀ P k, m < k → op (P, k) = 0) (Θ : H →ₗ[ℂ] E) (W : ι → Submodule ℂ E) (hW : ⨆ c, W c = ⊤)
    (T : Pl → ℕ → Module.End ℂ H) (hT : ∀ P k, k ≤ m → ∀ v, j (op (P, k) v) = T P k (j v))
    (ev : ι → Pl → ℕ → ℂ) (g : ι → Pl → ℂ[X])
    (hg : ∀ c P, Col.heckePolyOf m (q P) (ev c P) = g c P * ((bl.map fun ν => Col.blockPoly (ν P) (q P) t).prod).map σ)
    (hev : ∀ c, ∀ w ∈ W c, ∀ P k, k ≤ m → T P k (LinearMap.adjoint Θ w) = ev c P k • LinearMap.adjoint Θ w) :
    LinearMap.range (LinearMap.adjoint Θ) ≤ Submodule.span ℂ (j '' (Col.blockSum n q t bl op : Set V)) := by
  subst hm
  let U : Pl × ℕ → Module.End ℂ H := fun i => if i.2 ≤ m then T i.1 i.2 else 0
  have hU : ∀ i v, U i (j v) = j (op i v) := by
    rintro ⟨P, k⟩ v
    by_cases hk : k ≤ m
    · simp only [U, if_pos hk]
      exact (hT P k hk v).symm
    · simp only [U, if_neg hk]
      rw [hz P k (not_le.1 hk)]
      simp
  refine le_trans ?_ (eigSum_le_span (U := U) hsp hU hc hs fun x hx => (Col.hasBlocks_map σ m q t bl x).1 hx)
  rw [LinearMap.range_eq_map, ← hW, Submodule.map_iSup]
  refine iSup_le fun c => ?_
  rintro _ ⟨w, hw, rfl⟩
  let x : Pl × ℕ → ℂ := fun i => if i.2 ≤ m then ev c i.1 i.2 else 0
  refine Col.eigAt_le_eigSum (x := x) (fun P => ?_) (Col.mem_eigAt_of_forall_apply ?_)
  · have h1 : Col.heckePolyOf m (q P) (fun k => x (P, k)) = _ :=
      (heckePolyOf_congr _ _ fun k hk => if_pos hk).trans (hg c P)
    refine Dvd.intro_left (g c P) (Eq.trans ?_ h1.symm)
    simp only [Polynomial.map_list_prod, List.map_map, Function.comp_def, Col.map_blockPoly]
  · rintro ⟨P, k⟩
    by_cases hk : k ≤ m
    · simp only [U, x, if_pos hk]
      exact hev c w hw P k hk
    · simp only [U, x, if_neg hk]
      simp

theorem range_adjoint_le_span : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A.fam.Ok s → Core R F → SchurAll R → ∀ t, LinearMap.range (LinearMap.adjoint (R.Th t)) ≤ Submodule.span ℂ (R.jX t '' ((A.fam.R t).ZH : Set (A.fam.R t).S.Forms)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hI hOk hC hS t
  classical
  have hSF : IsSF R (R.Pg.image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
    intro v
    simp only [Finset.mem_image, HeightOneSpectrum.ext_iff]
    rfl
  have htop : ⨆ c, EEc R _ c = ⊤ := (_root_.GlobalTheory.Hk3.OpsRows.exists_opsE R F hC hS _ hSF).elim fun _ h => h.2.2.1
  choose hX hXo _ using (GlobalTheory.T.realization_family_normal_operators R F hC.lev hC.fam hC.models).1 t
  have hsplit := (GlobalTheory.SplitHeckeLabel.split_ops R F hC.lev hC.fam hC.models).1 t hX hXo
  have hf := GlobalTheory.AdjBlock.model_form (W := R.cX.W) (ι := Bridge.ratF D.sp.X') (ρ := R.cX.coef.ρ)
    (J := (levEnv _ R.βX (R.datXt t)).J) (χ := (levEnv _ R.βX (R.datXt t)).χ) (R.B.R t).pres (R.HX t) (hC.models.HX t)
    (hC.models.jX t)
  choose z hm hp using fun P : A.ok t => _root_.GlobalTheory.Hk3.SplitChain.exists_transfer R F hI hC hS t P
  let a : (Pl D.host.E → List ℤ → ℂ) → A.ok t → ℕ → ℂ := fun c P j =>
    if IsLab (Yc D 0) (R.pl P) (splitLab (Yc D 0).rank j) then c (R.pl P) (dualLab (splitLab (Yc D 0).rank j)) else 0
  exact range_le_span_blockSum (Pl := A.ok t) (q := fun P => A.q P) (Module.Finite.of_basis (A.MtildeCSD t).basis) hf.2.1 (hOk.what₂ t).comm (hOk.what₂ t).split R.B.rankR
    (fun P => (hC.fam.degR t P).2) (R.Th t) _ htop
    (fun P k => hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1)) hsplit
    (fun c P k => ∑ j ∈ Finset.range ((Yc D 0).rank + 1), z P k j * a c P j) _ (fun c P => hp P (a c P))
    fun c w hw P k hk => ((_root_.GlobalTheory.Hk3.SysE.matched_commute R F hC hS _ hSF t (R.pl P)
      ((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.2.2 hC.fam t P.1 P.2).1 _ _ (hm P k hk) hX hXo).2 c w hw).trans
        (congrArg (· • LinearMap.adjoint (R.Th t) w) (evC_splitC _ _ _ _))

end GlobalTheory.AdjSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalBoundedInfiniteCompactFinitePolyCount
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory

theorem place_le_norm_pInf {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (ξ : E)
    (w : InfinitePlace E) : w ξ ≤ ‖pInf E (algebraMap E (Ad E) ξ)‖ := by
  have h := norm_le_pi_norm (pInf E (algebraMap E (Ad E) ξ)) w
  rw [pInf_algebraMap, InfinitePlace.norm_embedding_eq] at h
  exact h

theorem rat_bounded_compact_polynomial : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], ∃ m : ℕ,
    ∀ Kf : Set (Af E), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.Finite ∧
      ({ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.ncard : ℝ)
        ≤ C * T ^ m := by
  intro E _ _ _
  obtain ⟨m, C₀, hC₀, hcount⟩ := _root_.GlobalTheory.IntCount.card_bounded_integers_le E
  refine ⟨m, fun Kf hKf => ?_⟩
  obtain ⟨n, hn, hint⟩ := _root_.GlobalTheory.AdeleDenom.exists_common_denom E Kf hKf
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨C₀ * (n : ℝ) ^ m, by positivity, fun T hT => ?_⟩
  have hnT : (1 : ℝ) ≤ n * T := by nlinarith
  obtain ⟨hAfin, hAcard⟩ := hcount (n * T) hnT
  set A := {x : 𝓞 E | ∀ w : InfinitePlace E, w (x : E) ≤ n * T}
  set S := {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}
  have hnE : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  have hsub : S ⊆ (fun x : 𝓞 E => (x : E) / n) '' A := by
    intro ξ hξ
    have hi : IsIntegral ℤ ((n : E) * ξ) := hint ξ hξ.2
    refine ⟨⟨(n : E) * ξ, hi⟩, fun w => ?_, ?_⟩
    · show w ((n : E) * ξ) ≤ n * T
      rw [← InfinitePlace.norm_embedding_eq, map_mul, map_natCast, norm_mul, Complex.norm_natCast,
        InfinitePlace.norm_embedding_eq]
      exact mul_le_mul_of_nonneg_left ((place_le_norm_pInf ξ w).trans hξ.1) (Nat.cast_nonneg n)
    · show (n : E) * ξ / n = ξ
      field_simp
  have hSfin : S.Finite := (hAfin.image _).subset hsub
  refine ⟨hSfin, ?_⟩
  have h1 : S.ncard ≤ A.ncard :=
    (Set.ncard_le_ncard hsub (hAfin.image _)).trans (Set.ncard_image_le hAfin)
  calc (S.ncard : ℝ) ≤ A.ncard := by exact_mod_cast h1
    _ ≤ C₀ * (n * T) ^ m := hAcard
    _ = C₀ * (n : ℝ) ^ m * T ^ m := by rw [mul_pow]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlace
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section
namespace GlobalTheory.RealScalar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ext_realAd (r : ℝ) (w : InfinitePlace F) :
    InfinitePlace.Completion.extensionEmbedding w (evInf F w (realAd F r)) = (r : ℂ) := by
  set y : mixedEmbedding.mixedSpace F := algebraMap ℝ _ r with hy
  set a := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y with ha
  have hev : evInf F w (realAd F r) = a w := rfl
  have hay : InfiniteAdeleRing.ringEquiv_mixedSpace F a = y := by rw [ha]; exact RingEquiv.apply_symm_apply _ _
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at hay
  rw [hev]
  rcases w.isReal_or_isComplex with hw | hw
  · have h1 := congrFun (congrArg Prod.fst hay) ⟨w, hw⟩
    simp only [hy] at h1
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
    rw [show (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (a w)) = r from by simpa using h1]
  · have h1 := congrFun (congrArg Prod.snd hay) ⟨w, hw⟩
    simpa [hy] using h1

theorem piInf_algebraMap {w : InfinitePlace F} (τ : EmbOver E w) (x : AF F) :
    piInf τ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) x) = InfinitePlace.Completion.extensionEmbedding w (evInf F w x) := by
  change infEmb τ (compInf F E w (x ⊗ₜ[F] (1 : E))) = _
  rw [compInf]
  change infEmb τ ((evInf F w x) ⊗ₜ[F] ((AlgHom.id F E) 1)) = _
  rw [infEmb_tmul]
  simp

theorem piInf_realAd_smul {w : InfinitePlace F} (τ : EmbOver E w) (r : ℝ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piInf τ (realAd F r • z) = (r : ℂ) * piInf τ z := by
  rw [Algebra.smul_def, map_mul, piInf_algebraMap, ext_realAd]

theorem realAd_smul_map : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    (τ : ∀ w : InfinitePlace F, EmbOver E w), IsCMExt F E σ →
    ∀ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (r : ℝ) (w : InfinitePlace F),
      (realAd F r • u).map (piInf (τ w)) = (r : ℂ) • u.map (piInf (τ w)) := by
  intro F E _ _ _ _ _ σ α β τ _ u r w
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  exact piInf_realAd_smul (τ w) r (u i j)

end GlobalTheory.RealScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightLieDerivativeRealEntryPolynomialFunctionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightLieDerivative_realEntryPolynomialFunction : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), RealPoints θ V → ∀ (τ : D.what₂.Tau) (X : LieAt V τ) (P : PolyE V), lieDer V (expInf θ V) (atPlace V τ X) (polyFun θ V P) = polyFun θ V (matDer τ X.1 P) := by
  first | exact @GlobalTheory.PolyRightDeriv.lieDer_polyFun | exact GlobalTheory.PolyRightDeriv.lieDer_polyFun | (intros; apply GlobalTheory.PolyRightDeriv.lieDer_polyFun <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypeExistsBaseLevelVector
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

namespace GlobalTheory.RowTypeVec

theorem vec_of_rows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π, π ∈ principalLevelFrame.OccRows R.θ PY (R.MY 0) (fun b => (levS _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun b => (levChi _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun _ => R.e0) → ∀ i, ∃ x ∈ π.S, x ≠ 0 ∧ principalLevelFrame.IsTypeVec ((PW i).ψ ⁻¹' (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A))))) (fun κ => (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) ((PW i).ψ κ)) x := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk hC hgen n hF PY PW hPY hPW π hπ i
  obtain ⟨v, hvS, hv0, hvT, hvG⟩ := GlobalTheory.T.exists_good_fixed_vector_of_type_occurring_in_rows R F hOk hC PY π hπ
  obtain ⟨x, hxS, hx0, hxT⟩ := GlobalTheory.T.exists_baseLevel_vector_of_principalLevel_fixed R F hOk hC hgen PY (principalLevelFrame.FinTyp.conjT π) v hvS hv0 hvT hvG
  set y : Formalism.AUTREP.GAf D.host.E n → ℂ := fun g => star (x g) with hy
  have hyS : y ∈ π.S := hxS
  have hy0 : y ≠ 0 := by
    intro h
    apply hx0
    funext g
    have := congrFun h g
    simpa [hy] using this
  have hyT : principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 (R.levL F false (sg0 D A))))
      (fun κ => levChi _ (R.βY 0) (R.dat0 (R.levL F false (sg0 D A))) (PY.ψ κ)) y := by
    intro κ hκ
    have e := hxT κ hκ
    funext g
    have eg := congrFun e g
    simp only [principalLevelFrame.rt_apply, Pi.smul_apply, smul_eq_mul] at eg
    simp only [hy, principalLevelFrame.rt_apply, Pi.smul_apply, smul_eq_mul, eg, star_mul', GlobalTheory.T.star_rows_level_character_eq_lifts_level_character R F false]
  obtain ⟨h, hh⟩ := GlobalTheory.T.levels_standardFrames_conjugate_standardGroup R F hC i hF PY (PW i) hPY (hPW i) (R.levL F false (sg0 D A))
  refine ⟨Formalism.L2.NG.rt D.host.E n h y, π.stable h y hyS, ?_, ?_⟩
  · intro h0
    apply hy0
    have := congrArg (Formalism.L2.NG.rt D.host.E n h⁻¹) h0
    rwa [principalLevelFrame.rt_rt, inv_mul_cancel, principalLevelFrame.rt_one, map_zero] at this
  · intro κ hκ
    obtain ⟨h1, h2⟩ := hh κ hκ
    have e : κ * h = h * (h⁻¹ * κ * h) := by group
    show Formalism.L2.NG.rt D.host.E n κ (Formalism.L2.NG.rt D.host.E n h y) = _
    rw [principalLevelFrame.rt_rt, e, ← principalLevelFrame.rt_rt, hyT _ h1, map_smul]
    exact congrArg (· • Formalism.L2.NG.rt D.host.E n h y) h2.symm

end GlobalTheory.RowTypeVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsDimLeAddMulSectionsDimCutStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionsDim_le_add_mul_sectionsDim_cut : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (F : X.Modules) [IsFiniteQC F], ∀ (B M : LB X) (hB : B.IsLB) (hM : M.IsLB) (s t : B.Sec), Mono (cutHom F hB s) → Mono (cutHom (cut F hB s) hB t) → ∀ (j : ℕ) (M' : LB X) (hM' : M'.IsLB), cls M hM = cls M' hM' + j • cls B hB → hdim k (twist F M) 0 ≤ hdim k (twist F M') 0 + j * hdim k (twist (cut F hB s) M) 0 := by
  first | exact @GlobalTheory.SiuChain.hdim_le_add_mul_hdim_cut | exact GlobalTheory.SiuChain.hdim_le_add_mul_hdim_cut | (intros; apply GlobalTheory.SiuChain.hdim_le_add_mul_hdim_cut <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def spanK (φ : Sm E a) : Submodule ℂ (Sm E a) := Submodule.span ℂ (Set.range fun k => cptRep E a k φ)

theorem spanK_stable (φ : Sm E a) : ∀ k, ∀ w ∈ spanK E a φ, cptRep E a k w ∈ spanK E a φ := by
  intro k w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k', rfl⟩ := hx
    exact Submodule.subset_span ⟨k * k', by simp only [map_mul, mul_apply_eq_comp]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem self_mem_spanK (φ : Sm E a) : φ ∈ spanK E a φ :=
  Submodule.subset_span ⟨1, by simp only [map_one, one_apply_eq_self]⟩

def mapsJ (φ : Sm E a) (L : Subgroup (GL (Fin a) (Af E))) : Submodule ℂ (spanK E a φ →ₗ[ℂ] Sm E a) where
  carrier := {T | T ∈ maps L (spanK E a φ) (spanK_stable φ) ∧ ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T w) = 0}
  zero_mem' := ⟨zero_mem _, fun z _ _ w => by simp⟩
  add_mem' {T T'} h h' := ⟨add_mem h.1 h'.1, fun z hz h0 w => by
    simp [h.2 z hz h0 w, h'.2 z hz h0 w]⟩
  smul_mem' c T h := ⟨Submodule.smul_mem _ c h.1, fun z hz h0 w => by simp [h.2 z hz h0 w]⟩

end GlobalTheory.AutGrowth
end
end

