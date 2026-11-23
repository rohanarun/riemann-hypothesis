module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProducts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1295
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.IsClosedImmersionLift
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0151
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreEnvelopingAlgebraCommuteRealLieSmoothing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0535
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbscissaConvergenceIdentity
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.GramAct

theorem ip_mt {D : D7} {a b : ℕ} (V : HSp D) (g : GA D V) (x : Mx D V.rank a) (y : Mx D V.rank b) :
    ip V (mm (mt V g) x) (mm (mt V g) y) = ip V x y := by
  have hu : adj (mt V g) * (gA V * mt V g) = gA V := mt_unitary V g
  unfold ip mm
  rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA V), ← Matrix.mul_assoc (adj (mt V g)), hu]

theorem acEq : AcEq := by
  intro D r t V b₀ g z
  have h12 : ip V (ac V g z).1 (ac V g z).2 = ip V z.1 z.2 := ip_mt V g z.1 z.2
  have h22 : ip V (ac V g z).2 (ac V g z).2 = ip V z.2 z.2 := ip_mt V g z.2 z.2
  have hy : yv V b₀ (ac V g z) = yv V b₀ z := by
    unfold yv
    rw [h12]
  refine ⟨ip_mt V g z.1 z.1, hy, ?_⟩
  unfold qv
  rw [h22, hy]

end GlobalTheory.CompanionTheory.ColumnSplitting.GramAct

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjacentQuotientOfTwoSegment
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.ProdReorder
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.AdjQuot

section Linear

theorem nontrivial_piTensorProduct {ι : Type} [Fintype ι] {X : ι → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] [∀ a, Nontrivial (X a)] : Nontrivial (PiTensorProduct ℂ X) := by
  classical
  choose v hv using fun a => exists_ne (0 : X a)
  have hex : ∀ a, ∃ φ : Module.Dual ℂ (X a), φ (v a) ≠ 0 := fun a => by
    by_contra hc
    push_neg at hc
    exact hv a ((Module.forall_dual_apply_eq_zero_iff ℂ (v a)).1 hc)
  choose φ hφ using hex
  let L := PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap φ)
  have h : L (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    simp only [L, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hφ a
  exact ⟨PiTensorProduct.tprod ℂ v, 0, fun h0 => h (by rw [h0, map_zero])⟩

end Linear

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Induction

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {W W' : Type} [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

theorem nontrivial_indSp (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W} (hρ : IsSmooth ρ)
    [Nontrivial W] : Nontrivial (IndSp e ρ) := by
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨f, hf, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one e ρ hρ u
  exact ⟨f, 0, fun h => hu (by rw [← hf, h]; rfl)⟩

end Induction

theorem nontrivial_prodIrr {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) :
    Nontrivial (IndSp (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep)) := by
  haveI : ∀ a, Nontrivial (x a).2.rep.V := fun a => GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible (x a).2.rep.irr
  haveI := nontrivial_piTensorProduct (X := fun a => (x a).2.rep.V)
  exact nontrivial_indSp _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)

section Two

variable {V U W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
  {r t N : ℕ}

end Two

section Concat



end Concat

end GlobalTheory.CompanionTheory.AdjQuot
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMatrixPreservesForm
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin

theorem archMat_projArch_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : GAd σ J) (w : InfinitePlace F) (τ : EmbOver E w), cT (starRingEnd ℂ) (archMat σ J τ (projArch σ J w g)) * J.map τ.1 * archMat σ J τ (projArch σ J w g) = J.map τ.1 := by
  intro F E _ _ _ _ _ σ hcm n J g w τ
  have h := GlobalTheory.HeisCoords.archMat_unitary hcm τ (projArch σ J w g)
  have e : cT (starRingEnd ℂ) (archMat σ J τ (projArch σ J w g)) = (archMat σ J τ (projArch σ J w g))ᴴ := by
    ext i j
    simp [cT, Matrix.conjTranspose_apply]
  rw [e]
  exact h

end GlobalTheory.CompanionTheory.CFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyPointDimension
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.DimVar

open _root_.Topology

theorem finiteType_of_chart {Y : Scheme.{0}} (f : Y ⟶ Spec (.of ℤ)) [LocallyOfFiniteType f] {C : Type} [CommRing C]
    [Algebra ℤ C] (j : Spec (.of C) ⟶ Y) [IsOpenImmersion j] (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℤ C))) :
    Algebra.FiniteType ℤ C :=
  RingHom.finiteType_algebraMap.mp <|
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap ℤ C))).mp (hj ▸ inferInstance)

theorem topologicalKrullDim_closure_eq (Y : Scheme.{0}) (f : Y ⟶ Spec (.of ℤ)) [LocallyOfFiniteType f] (y : Y)
    [CharZero (Y.residueField y)] :
    topologicalKrullDim (closure ({y} : Set Y)) =
      (((Algebra.trdeg ℤ (Y.residueField y)).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨B, _, _, j, _, q, hq, hj⟩ := exists_affine_chart_over f y
  subst hq
  have := finiteType_of_chart f j hj
  rw [← GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ Y B j q inferInstance, ← topologicalKrullDim_range_inter_closure_eq j q]
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun z ↦ ?_)
    (IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  obtain ⟨C, _, _, j', _, y', hy, hj'⟩ := exists_affine_chart_over f z.1
  have := finiteType_of_chart f j' hj'
  obtain ⟨q', hq'⟩ := (specializes_iff_mem_closure.mpr z.2).mem_open
    j'.isOpenEmbedding.isOpen_range ⟨y', hy⟩
  refine ⟨Subtype.val ⁻¹' Set.range j',
    j'.isOpenEmbedding.isOpen_range.preimage continuous_subtype_val, ⟨y', hy⟩, ?_⟩
  rw [← topologicalKrullDim_eq_of_isEmbedding (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
    (Z := Set.range j' ∩ closure {j q})
    (by rw [Set.range_comp, Subtype.range_coe, Subtype.image_preimage_coe, Set.inter_comm])]
  rw [topologicalKrullDim_range_inter_closure_eq j q, GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ Y B j q inferInstance]
  conv_lhs => rw [← hq', topologicalKrullDim_range_inter_closure_eq j' q']
  have h0 : CharZero (Y.residueField (j' q')) := hq' ▸ inferInstance
  rw [GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ Y C j' q' h0, hq']

theorem ptCoord_chart_ne_zero {m : ℕ} {n : Fin (m + 1) → ℕ} (x : MP ℤ m n) (k : Fin (m + 1)) :
    ptCoord x ⟨k, ptChart x k⟩ ≠ 0 := by
  simp [ptCoord, pullRatio_self]

theorem isArithVar_ptIdeal : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (d : ℕ), CharZero ((MP ℤ m n).residueField x) → topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (d : ℕ) → Geo.IsArithVar (ptIdeal x) d := by
  intro m n x d hch hd
  have hdim := topologicalKrullDim_closure_eq (MP ℤ m n) (mpStr ℤ m n) x
  rw [hd] at hdim
  have h1 : ((d : ℕ∞)) = (Algebra.trdeg ℤ ((MP ℤ m n).residueField x)).toENat + 1 := WithBot.coe_injective hdim
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (Algebra.trdeg ℤ ((MP ℤ m n).residueField x)).toENat = t := by
    refine ⟨(Algebra.trdeg ℤ ((MP ℤ m n).residueField x)).toENat.toNat, (ENat.natCast_toNat ?_).symm⟩
    intro h
    rw [h] at h1
    simp at h1
  have hdt : d = t + 1 := by
    rw [ht] at h1
    exact_mod_cast h1
  subst hdt
  have htr : Algebra.trdeg ℤ (blockFnField (ptCoord x)) = t := by
    rw [_root_.GlobalTheory.CompanionTheory.MPDict.GenTop.blockFnField_ptCoord_eq_top m n x, GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.trdeg_top]
    exact Cardinal.toENat_eq_natCast.mp ht
  exact GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.isArithVar_of_trdeg (ptCoord x) (ptChart x) (ptCoord_chart_ne_zero x) t htr

end GlobalTheory.CompanionTheory.MPDict.DimVar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CTAevalMulEq
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct

namespace GlobalTheory.CompanionTheory.AdjointPoly

theorem cT_aeval_mul_eq :
    ∀ (K : Type) [Field K] (s : K →+* K) (n : ℕ) (A H₀ : Matrix (Fin n) (Fin n) K) (a : K[X]),
      cT s A * H₀ * A = H₀ → aeval A a * A = 1 →
      ∀ f : K[X], cT s (aeval A f) * H₀ = H₀ * aeval A ((f.map s).comp a) := by
  intro K _ s n A H₀ a hA ha f
  have hcomm : A * aeval A a = aeval A a * A := by
    have h : aeval A (X * a) = aeval A (a * X) := by rw [mul_comm]
    simpa only [map_mul, aeval_X] using h
  have hAB : A * aeval A a = 1 := hcomm.trans ha
  have hstep : cT s A * H₀ = H₀ * aeval A a := by
    calc cT s A * H₀ = cT s A * H₀ * (A * aeval A a) := by rw [hAB, mul_one]
      _ = (cT s A * H₀ * A) * aeval A a := by simp only [mul_assoc]
      _ = H₀ * aeval A a := by rw [hA]
  have cT_mul : ∀ P Q : Matrix (Fin n) (Fin n) K, cT s (P * Q) = cT s Q * cT s P := by
    intro P Q
    simp only [cT, Matrix.map_mul, Matrix.transpose_mul]
  have cT_add : ∀ P Q : Matrix (Fin n) (Fin n) K, cT s (P + Q) = cT s P + cT s Q := by
    intro P Q
    ext i j
    simp [cT]
  have cT_C : ∀ c : K, cT s (algebraMap K (Matrix (Fin n) (Fin n) K) c)
      = algebraMap K (Matrix (Fin n) (Fin n) K) (s c) := by
    intro c
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
    by_cases h : i = j
    · subst h; simp
    · have h' : ¬ j = i := fun e => h e.symm
      simp [h, h']
  induction f using Polynomial.induction_on with
  | C c =>
    simp only [aeval_C, Polynomial.map_C, Polynomial.C_comp]
    rw [cT_C, Algebra.commutes]
  | add p q hp hq =>
    simp only [map_add (f := _), Polynomial.map_add (f := _), Polynomial.add_comp, cT_add, add_mul, mul_add, hp, hq]
  | monomial k c ih =>
    have e1 : aeval A (C c * X ^ (k + 1)) = A * aeval A (C c * X ^ k) := by
      have h : aeval A (C c * X ^ (k + 1)) = aeval A (X * (C c * X ^ k)) := by
        congr 1; ring
      rw [h, map_mul, aeval_X]
    have e2 : ((C c * X ^ (k + 1) : K[X]).map s).comp a
        = ((C c * X ^ k : K[X]).map s).comp a * a := by
      simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp, pow_succ]
      ring
    rw [e1, e2, cT_mul, mul_assoc, hstep, ← mul_assoc, ih, mul_assoc,
      map_mul (aeval A) (((C c * X ^ k : K[X]).map s).comp a) a]

end GlobalTheory.CompanionTheory.AdjointPoly
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapacityEquivalence
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem adjoin_lie_equiv {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    {U : Submodule ℂ (Sm E N)} (T : Sm E N →ₗ[ℂ] Sm E N) (hU : _root_.GlobalTheory.CuspRep.IsStable U)
    (hT : ∀ o, ∀ χ ∈ U, T (act o χ) = act o (T χ)) {z : Module.End ℂ (Sm E N)}
    (hz : z ∈ Algebra.adjoin ℂ (Set.range (lie E N))) :
    ∀ χ ∈ U, z χ ∈ U ∧ T (z χ) = z (T χ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨X, rfl⟩ := hx
    exact fun χ hχ => ⟨hU (.lie X) χ hχ, hT (.lie X) χ hχ⟩
  | algebraMap c =>
    intro χ hχ
    simpa [Module.algebraMap_end_apply] using U.smul_mem c hχ
  | add x y _ _ hx hy =>
    intro χ hχ
    obtain ⟨x₁, x₂⟩ := hx χ hχ
    obtain ⟨y₁, y₂⟩ := hy χ hχ
    exact ⟨by simpa using U.add_mem x₁ y₁, by simp [x₂, y₂]⟩
  | mul x y _ _ hx hy =>
    intro χ hχ
    obtain ⟨y₁, y₂⟩ := hy χ hχ
    obtain ⟨x₁, x₂⟩ := hx _ y₁
    exact ⟨by simpa [Module.End.mul_apply] using x₁, by simp [Module.End.mul_apply, x₂, y₂]⟩

theorem capEquiv : CapEquiv := by
  intro E _ _ _ N U T ψ m hU hT hψ hc τ u
  rw [← (adjoin_lie_equiv T hU hT (GlobalTheory.CentreSmooth.cap_mem τ u) ψ hψ).2, hc τ u, map_smul]

end GlobalTheory.CompanionTheory.EGlue

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartGramFirstEntry
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.ChartGram

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory _root_.Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem sigR_halfR (σ : E →ₐ[F] E) : sigR R σ (halfR (F := F) (E := E) R) = halfR (F := F) (E := E) R := by
  unfold halfR
  rw [sigR_inclR, AlgHom.commutes]

theorem halfR_add_halfR (h2 : (2 : F) ≠ 0) :
    halfR (F := F) (E := E) R + halfR (F := F) (E := E) R = 1 := by
  have h : (1 / 2 : F) + 1 / 2 = 1 := by field_simp; norm_num
  unfold halfR
  rw [← map_add (f := _), ← map_add (f := _), h, map_one, map_one]

theorem vH_zero {K : Type} {M : ℕ} (a s : K) (Y : Fin M → K) : vH a s Y 0 = a := rfl
theorem vH_one {K : Type} {M : ℕ} (a s : K) (Y : Fin M → K) : vH a s Y 1 = s := rfl
theorem tailH_vH {K : Type} {M : ℕ} (a s : K) (Y : Fin M → K) : tailH (vH a s Y) = Y := rfl

theorem hR_hypOne (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin (M + 2) → R ⊗[F] E) :
    hR R σ (hypOne J) x y =
      sigR R σ (x 0) * y 1 + sigR R σ (x 1) * y 0 + hR R σ J (tailH x) (tailH y) := by
  unfold hR hform JR tailH
  simp only [Fin.sum_univ_succ, Matrix.map_apply, Fin.succ_zero_eq_one, hypOne_zero_zero, hypOne_zero_one,
    hypOne_one_zero, hypOne_one_one, hypOne_zero_rest, hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one,
    hypOne_rest_rest, map_zero, map_one, mul_zero, zero_mul, mul_one, Finset.sum_const_zero, add_zero, zero_add]
  ring

theorem sigR_hR (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J x y) = hR R σ J y x := by
  unfold hR hform JR
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, sigR_sigR R σ hσ, Matrix.map_apply, sigR_inclR]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ i j]
  ring

theorem hR_comb_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : R ⊗[F] E)
    (x u w : Fin M → R ⊗[F] E) :
    hR R σ J x (fun i => c * u i + w i) = c * hR R σ J x u + hR R σ J x w := by
  unfold hR hform
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_comb_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : R ⊗[F] E)
    (u w y : Fin M → R ⊗[F] E) :
    hR R σ J (fun i => c * u i + w i) y = sigR R σ c * hR R σ J u y + hR R σ J w y := by
  unfold hR hform
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, map_add (f := _), map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sigR_tHalf (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin (M + 2) → R ⊗[F] E) :
    sigR R σ (tHalf R σ J x) = tHalf R σ J x := by
  unfold tHalf
  rw [map_mul, sigR_halfR, hR_hypOne, map_add (f := _), map_add (f := _), map_mul, map_mul, sigR_sigR R σ hσ, sigR_sigR R σ hσ,
    sigR_hR R σ hσ J hJ]
  ring

theorem hR_cvec_right (h2 : (2 : F) ≠ 0) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x v : Fin (M + 2) → R ⊗[F] E) (hu : IsUnit (x 0)) :
    hR R σ (hypOne J) x (cvec R σ J x v) = v 1 + tHalf R σ J x * v 0 := by
  have e1 : Ring.inverse (sigR R σ (x 0)) * sigR R σ (x 0) = 1 :=
    Ring.inverse_mul_cancel _ (hu.map (sigR R σ))
  have e3 : tHalf R σ J x + tHalf R σ J x = hR R σ (hypOne J) x x := by
    unfold tHalf
    rw [← add_mul, halfR_add_halfR R h2, one_mul]
  have e4 := hR_hypOne R σ J x x
  have ht : tailH (cvec R σ J x v) = fun i => v 0 * tailH x i + tailH v i := rfl
  rw [hR_hypOne, ht, hR_comb_right]
  simp only [cvec, vH_zero, vH_one]
  linear_combination (v 1 - tHalf R σ J x * v 0 - hR R σ J (tailH x) (tailH v)) * e1 - v 0 * e3 - v 0 * e4

theorem hR_cvec_cvec (h2 : (2 : F) ≠ 0) (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (x v w : Fin (M + 2) → R ⊗[F] E) (hu : IsUnit (x 0)) :
    hR R σ (hypOne J) (cvec R σ J x v) (cvec R σ J x w) = hR R σ (hypOne J) v w := by
  have e1 : Ring.inverse (sigR R σ (x 0)) * sigR R σ (x 0) = 1 :=
    Ring.inverse_mul_cancel _ (hu.map (sigR R σ))
  have e2 : sigR R σ (Ring.inverse (sigR R σ (x 0))) * x 0 = 1 := by
    have := congrArg (sigR R σ) e1
    rwa [map_mul, sigR_sigR R σ hσ, map_one] at this
  have e3 : tHalf R σ J x + tHalf R σ J x = hR R σ (hypOne J) x x := by
    unfold tHalf
    rw [← add_mul, halfR_add_halfR R h2, one_mul]
  have e4 := hR_hypOne R σ J x x
  have htv : tailH (cvec R σ J x v) = fun i => v 0 * tailH x i + tailH v i := rfl
  have htw : tailH (cvec R σ J x w) = fun i => w 0 * tailH x i + tailH w i := rfl
  rw [hR_hypOne, hR_hypOne R σ J v w, htv, htw, hR_comb_left, hR_comb_right, hR_comb_right]
  simp only [cvec, vH_zero, vH_one, map_add (f := _), map_sub, map_mul, sigR_tHalf R σ hσ J hJ,
    sigR_hR R σ hσ J hJ]
  linear_combination
    (sigR R σ (v 0) * (w 1 - tHalf R σ J x * w 0 - hR R σ J (tailH x) (tailH w))) * e1 +
    (w 0 * (sigR R σ (v 1) - tHalf R σ J x * sigR R σ (v 0) - hR R σ J (tailH v) (tailH x))) * e2 -
    sigR R σ (v 0) * w 0 * e3 - sigR R σ (v 0) * w 0 * e4

end Alg

theorem gramR_chartS : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (n : ℕ) (x : Fin 1 → Fin (M + 2) → R ⊗[F] E) (a s : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E), IsUnit (x 0 0) → gramR R σ (hypOne J) (chartS R σ J x a s Y) 0 0 = hR R σ (hypOne J) (x 0) (x 0) ∧ (∀ j : Fin n, gramR R σ (hypOne J) (chartS R σ J x a s Y) 0 j.succ = s 0 j) ∧ ∀ i j : Fin n, gramR R σ (hypOne J) (chartS R σ J x a s Y) i.succ j.succ = gramR R σ J Y i j + (sigR R σ (a 0 i) * s 0 j + sigR R σ (s 0 i) * a 0 j - hR R σ (hypOne J) (x 0) (x 0) * (sigR R σ (a 0 i) * a 0 j)) := by
  intro F E _ _ _ _ _ σ hc M J hJ R _ _ n x a s Y hu
  have hσ := sig_invol σ hc
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have e3 : tHalf R σ J (x 0) + tHalf R σ J (x 0) = hR R σ (hypOne J) (x 0) (x 0) := by
    unfold tHalf
    rw [← add_mul, halfR_add_halfR R h2, one_mul]
  refine ⟨rfl, fun j => ?_, fun i j => ?_⟩
  · change hR R σ (hypOne J) (x 0) (cvec R σ J (x 0) (vH (a 0 j) (s 0 j - tHalf R σ J (x 0) * a 0 j) (Y j))) = s 0 j
    rw [hR_cvec_right R h2 σ J _ _ hu, vH_zero, vH_one]
    ring
  · change hR R σ (hypOne J) (cvec R σ J (x 0) (vH (a 0 i) (s 0 i - tHalf R σ J (x 0) * a 0 i) (Y i)))
      (cvec R σ J (x 0) (vH (a 0 j) (s 0 j - tHalf R σ J (x 0) * a 0 j) (Y j))) = hR R σ J (Y i) (Y j) + _
    rw [hR_cvec_cvec R h2 σ hσ J hJ.1 _ _ _ hu, hR_hypOne]
    simp only [vH_zero, vH_one, tailH_vH, map_sub, map_mul, sigR_tHalf R σ hσ J hJ.1]
    linear_combination (-(sigR R σ (a 0 i) * a 0 j)) * e3

end GlobalTheory.CompanionTheory.WeilSiegel.ChartGram
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredient_product_irreducible : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), ∃ hd' : ∑ a, (dualCl (x a)).1 = N, Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr (fun a => dualCl (x a)) hd')) := by
  first | exact @GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr | exact GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr | (intros; apply GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsFurther
section

end

