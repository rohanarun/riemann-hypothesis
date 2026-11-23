module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0884
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1161
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.HeightExists

open CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Twist GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.QCoh

attribute [local instance] MvPolynomial.gradedAlgebra

section Algebra

variable {k K σ : Type} [Field k] [Field K] [Algebra k K]

def coeffMap (l : K →ₗ[k] k) (g : MvPolynomial σ K) : MvPolynomial σ k :=
  ∑ a ∈ g.support, monomial a (l (AddMonoidAlgebra.coeff g a))

theorem coeff_coeffMap (l : K →ₗ[k] k) (g : MvPolynomial σ K) (a : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (coeffMap l g) a = l (AddMonoidAlgebra.coeff g a) := by
  classical
  simp only [coeffMap, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero]

theorem isHomogeneous_coeffMap (l : K →ₗ[k] k) {g : MvPolynomial σ K} {d : ℕ} (hg : g.IsHomogeneous d) :
    (coeffMap l g).IsHomogeneous d := fun a ha =>
  hg fun h => ha (by rw [coeff_coeffMap, h, map_zero])

theorem mem_map_of_coeffMap {I : Ideal (MvPolynomial σ k)} {g : MvPolynomial σ K}
    (h : ∀ l : K →ₗ[k] k, coeffMap l g ∈ I) :
    g ∈ I.map (MvPolynomial.map (algebraMap k K) : MvPolynomial σ k →+* MvPolynomial σ K) := by
  classical
  let b := Module.Basis.ofVectorSpace k K
  let s := g.support.biUnion fun a => (b.repr (AddMonoidAlgebra.coeff g a)).support
  have e : g = ∑ i ∈ s, C (b i) * map (algebraMap k K) (coeffMap (b.coord i) g) := by
    ext a
    simp only [coeff_sum, coeff_C_mul, coeff_map, coeff_coeffMap]
    have hs : (b.repr (AddMonoidAlgebra.coeff g a)).support ⊆ s := by
      by_cases ha : a ∈ g.support
      · exact Finset.subset_biUnion_of_mem (fun a => (b.repr (AddMonoidAlgebra.coeff g a)).support) ha
      · simp [notMem_support_iff.1 ha]
    conv_lhs => rw [← b.linearCombination_repr (AddMonoidAlgebra.coeff g a),
      Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hs _ (by simp)]
    exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]; rfl
  rw [e]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h _))

theorem le_of_ringKrullDim_coneIdeal {N D e : ℕ} (y : Fin N → K) (hD : Algebra.trdeg k K = D)
    (he : ringKrullDim (MvPolynomial (Fin N) k ⧸ coneIdeal k y) = (e + 1 : ℕ)) : e ≤ D := by
  have := isPrime_coneIdeal (K := k) y
  obtain ⟨d, h1, h2⟩ := exists_ringKrullDim_eq_and_trdeg_eq k (MvPolynomial (Fin N) k ⧸ coneIdeal k y)
  obtain rfl : d = e + 1 := by exact_mod_cast h1.symm.trans he
  have h3 := trdeg_le_of_injective (Ideal.kerLiftAlg (coneMap k y)) (Ideal.kerLiftAlg_injective _)
  rw [← trdeg_add_eq k K (A := Polynomial K), Polynomial.trdeg_of_isDomain, hD] at h3
  have h4 : ((e + 1 : ℕ) : Cardinal.{0}) ≤ ((D + 1 : ℕ) : Cardinal.{0}) := by
    rw [← h2, Nat.cast_add, Nat.cast_one]; exact h3
  have : e + 1 ≤ D + 1 := by exact_mod_cast h4
  omega

end Algebra

variable {k : Type} [Field k] (S : LinSys k)

theorem chartEval_eq_zero {g : MvPolynomial (Fin S.N) k} {d : ℕ} (hg : g.IsHomogeneous d) (h : g ∈ S.imageIdeal)
    (i : S.L.ι) {W : S.Y.Opens} (hle : W ≤ S.L.U i) : chartEval k S.b i hle g = 0 := by
  have e : resG _ hle (zfun (S.form hg) i) = 0 := by
    rw [(S.mem_imageIdeal_iff hg).1 h]
    exact (congrArg _ (zfun_zero i)).trans (map_zero _)
  rwa [LinSys.form, zfun_formSec, resG_chartEval] at e

theorem coeffMap_mem_imageIdeal (E : Type) [Field E] [Algebra k E] {g : MvPolynomial (Fin S.N) E} {d : ℕ}
    (hg : g.IsHomogeneous d) (h : g ∈ (S.baseChange E).imageIdeal) (l : E →ₗ[k] k) :
    coeffMap l g ∈ S.imageIdeal := by
  refine (S.mem_imageIdeal_iff (isHomogeneous_coeffMap l hg)).2 (zglobal_ext fun i => ?_)
  rw [zfun_zero, LinSys.form, zfun_formSec]
  refine S.Y.sheaf.eq_of_locally_eq' (fun W : {W : S.Y.affineOpens // W.1 ≤ S.L.U i} => W.1.1) _
    (fun W => homOfLE W.2) (fun y hy => ?_) _ _ fun W => ?_
  · obtain ⟨V, hV, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := S.L.U i) (x := y) hy
    exact Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hle⟩, hx⟩
  obtain ⟨⟨W, hW⟩, hle⟩ := W
  have H := S.isPullback_baseChange E
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := W) le_top le_top
    (UY := S.bcFst E ⁻¹ᵁ W) (by simp)).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hW)
  have po' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ S.str.appLE ⊤ W le_top)
      (CommRingCat.ofHom (algebraMap k E)) ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl)
      ((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
        (S.baseChange E).str.appLE ⊤ (S.bcFst E ⁻¹ᵁ W) le_top) := by
    refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
      (by simp) ?_ (by simp) (by simp)
    rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  obtain ⟨Λ, hΛ⟩ := IndepBaseChange.exists_contract po' l
  have hle' : S.bcFst E ⁻¹ᵁ W ≤ (S.baseChange E).L.U fun _ => i :=
    fun y hy => Set.mem_iInter.2 fun _ => hle hy
  have e := (eval₂_eq _ _ _).symm.trans (chartEval_eq_zero (S.baseChange E) hg h (fun _ => i) hle')
  have e' : ∀ j, resG (S.baseChange E).Y hle' (((S.baseChange E).b j).f fun _ => i) =
      ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl).hom (resG S.Y hle ((S.b j).f i)) := fun j => by
    have a := (S.bcFst E).appLE_map (U := S.L.U i) (V := (S.baseChange E).L.U fun _ => i)
      (fun y hy => Set.mem_iInter.1 hy PUnit.unit) (homOfLE hle').op
    have b := (S.bcFst E).map_appLE (U := W) (V := S.bcFst E ⁻¹ᵁ W) le_rfl (homOfLE hle).op
    exact congrArg (fun g => g.hom ((S.b j).f i)) (a.trans b.symm)
  have e₂ := congrArg Λ e
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, map_sum] at e₂
  refine (resG_chartEval k S.b i le_rfl hle _).trans (Eq.trans ?_ (e₂.trans (map_zero _).symm))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeffMap, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [chartEval, eval₂Hom_monomial]
  refine Eq.trans (hΛ (AddMonoidAlgebra.coeff g a) (a.prod fun j n => resG S.Y hle ((S.b j).f i) ^ n)).symm (congrArg Λ ?_)
  refine congrArg₂ (· * ·) rfl ?_
  refine (map_prod ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl).hom _ _).trans
    (Finset.prod_congr rfl fun j _ => ?_)
  exact (map_pow _ _ _).trans (congrArg (· ^ _) (e' j).symm)

theorem del_eq_zero (hp : IsProjOver S.str) (s : Fin S.D → S.L.Sec) (hs : ∀ y, ∃ i, y ∈ nonzeroLocus (s i)) :
    S.del = 0 := by
  have := isNoetherian_of_isProjOver hp
  have key := CutDegree.interNum_eq_sum_length S.str hp S.isLB S.chartAt S.mem_chartAt ∅ (by simp) (List.ofFn s)
    (structureModule S.Y) (fun x _ hx => by
      obtain ⟨i, hi⟩ := hs x
      exact (hx _ (List.mem_ofFn.2 ⟨i, rfl⟩) hi).elim) (by simp)
  have e : topSelfIntersection k S.L S.D = topSelfIntersection k S.L (List.ofFn s).length := by rw [List.length_ofFn]
  rw [LinSys.del, e, topSelf_def]
  exact key

variable {S}

theorem isIntegral (h : S.IsVariety) : IsIntegral S.Y := by
  have := h.smooth
  have := h.conn
  have : Smooth S.str := SmoothOfRelativeDimension.smooth S.D S.str
  have := geometricallyIntegral_of_smooth S.str
  exact GeometricallyIntegral.isIntegral_of_subsingleton S.str

theorem exists_generic (h : S.IsVariety) : ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra k Ω) (x : S.Pt Ω),
    IsGenericPoint (ptOf x.1) Set.univ ∧ Algebra.trdeg k Ω = S.D := by
  have := isIntegral h
  have hg := genericPoint_spec S.Y
  refine ⟨S.Y.residueField (genericPoint S.Y), inferInstance, (S.baseHom (resPt _)).toAlgebra,
    ⟨resPt _, S.comp_str _⟩, by rw [ptOf_resPt]; exact hg, ?_⟩
  exact (residueField_fg_trdeg_of_smoothOfRelativeDimension S.str S.D h.smooth _
    fun y hy => (hy.antisymm (hg.specializes trivial)).eq).2

theorem map_imageIdeal (h : S.IsVariety) (E : Type) [Field E] [Algebra k E] :
    S.imageIdeal.map (MvPolynomial.map (algebraMap k E) : MvPolynomial (Fin S.N) k →+* MvPolynomial (Fin S.N) E) =
      (S.baseChange E).imageIdeal := by
  refine le_antisymm ?_ (Ideal.span_le.2 ?_)
  · have := isIntegral (h.baseChange E)
    obtain ⟨Ω, _, _, x, hx, -⟩ := exists_generic (h.baseChange E)
    let : Algebra k Ω := ((algebraMap E Ω).comp (algebraMap k E)).toAlgebra
    have : IsScalarTower k E Ω := .of_algebraMap_eq' rfl
    obtain ⟨c, hc, e⟩ := S.exists_coords_baseChange E x.1
    rw [imageIdeal_eq_coneIdeal_of_generic E Ω _ x hx c _ hc e]
    refine Ideal.map_le_iff_le_comap.2 (Ideal.span_le.2 ?_)
    rintro g ⟨d, hg, h0⟩
    refine (mem_coneIdeal_of_isHomogeneous _ (hg.map (algebraMap k E))).2 ?_
    have h1 := S.eval₂_coords_eq_zero (LinSys.toBase x).1 ((S.mem_imageIdeal_iff hg).2 h0)
    rw [LinSys.baseHom_ptOver] at h1
    exact (aeval_map_algebraMap E _ g).trans h1
  · rintro g ⟨d, hg, h0⟩
    exact mem_map_of_coeffMap
      (coeffMap_mem_imageIdeal S E hg (((S.baseChange E).mem_imageIdeal_iff hg).2 h0))

theorem isPrime_imageIdeal (h : S.IsVariety) : S.imageIdeal.IsPrime := by
  have := isIntegral h
  obtain ⟨Ω, _, _, x, hx, -⟩ := exists_generic h
  rw [imageIdeal_eq_coneIdeal_of_generic k Ω S x hx 1 _ one_ne_zero (one_smul _ _).symm]
  exact isPrime_coneIdeal _

theorem del_eq_zero_of_lt [Infinite k] (hp : IsProjOver S.str) (hb : S.BasePointFree) {e δ : ℕ}
    {f : MvPolynomial (Fin (e + 1) × Fin S.N) k} (hf : IsChowFormInt S.imageIdeal e δ f) (he : e < S.D) :
    S.del = 0 := by
  obtain ⟨u, hu⟩ : ∃ u, eval u f ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf.ne_zero (MvPolynomial.funext fun u => by rw [hc, map_zero])
  refine del_eq_zero S hp (fun i => if hi : (i : ℕ) < e + 1 then S.comb fun j => u (⟨i, hi⟩, j) else 0) fun y => ?_
  by_contra hc
  push Not at hc
  let Ω := AlgebraicClosure (S.Y.residueField y)
  let x : Sp Ω ⟶ S.Y := spMap (algebraMap (S.Y.residueField y) Ω) ≫ resPt y
  have hx : ptOf x = y := (ptOf_spMap_comp _ _).trans (ptOf_resPt y)
  let : Algebra k Ω := (S.baseHom x).toAlgebra
  have h1 := (hf.zero_iff_of_isAlgClosed S.isHomogeneous_imageIdeal fun p => algebraMap k Ω (u p)).2
    ⟨S.coords x, hb.coords_ne_zero x, fun g hg => S.eval₂_coords_eq_zero x hg, fun i => by
      have h2 := hc ⟨i, by omega⟩
      rw [dite_eq_left i.2, ← hx, ← S.val_ne_zero_iff, not_not, S.val_comb] at h2
      exact h2⟩
  exact hu ((map_eq_zero (algebraMap k Ω)).1 ((aeval_algebraMap_apply Ω u f).symm.trans h1))

theorem ringKrullDim_imageIdeal [CharZero k] (h : S.IsVariety) (hb : S.BasePointFree) (hd : S.del ≠ 0) :
    ringKrullDim (MvPolynomial (Fin S.N) k ⧸ S.imageIdeal) = (S.D + 1 : ℕ) := by
  have := isIntegral h
  have hp := isPrime_imageIdeal h
  obtain ⟨Ω, _, _, x, hx, hD⟩ := exists_generic h
  have hI := imageIdeal_eq_coneIdeal_of_generic k Ω S x hx 1 _ one_ne_zero (one_smul _ _).symm
  obtain ⟨j, hj⟩ := Function.ne_iff.1 (hb.coords_ne_zero x.1)
  obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_succ S.isHomogeneous_imageIdeal (i := j)
    fun hX => hj (by simpa using S.eval₂_coords_eq_zero x.1 hX)
  obtain ⟨f, hf⟩ := ChowExists.exists_isChowFormInt hp S.isHomogeneous_imageIdeal he
  obtain rfl : e = S.D := le_antisymm (le_of_ringKrullDim_coneIdeal _ hD (hI ▸ he))
    (not_lt.1 fun hlt => hd (del_eq_zero_of_lt h.proj hb hf hlt))
  exact he

theorem exists_isChowForm [CharZero k] (h : S.IsVariety) (hb : S.BasePointFree) (hd : S.del ≠ 0) :
    ∃ f, IsChowForm S.imageIdeal S.D (hilbertDegree S.imageIdeal) f :=
  ChowExists.exists_isChowForm S.isHomogeneous_imageIdeal
    (by rw [map_imageIdeal h]; exact isPrime_imageIdeal (h.baseChange _)) (ringKrullDim_imageIdeal h hb hd)

theorem exists_isHeight : ∀ (F : Type) [Field F] [NumberField F] (T : HermSys F),
    T.IsAlgebraicData → 0 < T.del → ∃ h, T.IsHeight h := fun _ _ _ T h hd =>
  have ⟨_, hf⟩ := exists_isChowForm h.variety h.bpf hd.ne'
  ⟨_, T.isHeight_of_isChowForm hf⟩

end GlobalTheory.Adelic.HeightExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelsStandardFramesConjugateStandardGroup
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

namespace GlobalTheory.FrameMove

variable {D : D7}

theorem levChi_datY (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (Pg : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (κ : GA D V) :
    levChi V β (datY V.rank r t 0 hr Pg ∅ P χ ξ Frm.B) κ =
      ((ext1 P.H P.chi (rTup β (datY V.rank r t 0 hr Pg ∅ P χ ξ Frm.B) (finE V κ)) : ℂˣ) : ℂ) := by
  unfold levChi levFn
  simp [datY]
  rfl


set_option maxHeartbeats 1600000 in
theorem frame_move : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → ∀ (i : Fin D.R.m) {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → StdPsi hF PW → ∀ P : LevelP R.Pg D.R.r ℂ, ∃ h : Formalism.AUTREP.GAf D.host.E n, ∀ κ, PW.ψ κ ∈ levS _ (R.βW i) (R.datWp i P) → PY.ψ (h⁻¹ * κ * h) ∈ levS _ (R.βY 0) (R.dat0 P) ∧ levChi _ (R.βW i) (R.datWp i P) (PW.ψ κ) = levChi _ (R.βY 0) (R.dat0 P) (PY.ψ (h⁻¹ * κ * h)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC i n hF PY PW hY hW P
  obtain ⟨c, hc⟩ := hC.lev.βY 0 (Fin.pos i)
  obtain ⟨c', hc'⟩ := hC.lev.βW i
  have hrk : (Yc D 0).rank = (Wc D i).rank := GlobalTheory.PartDims.rank_zeroth_component_eq.trans (GlobalTheory.PartDims.rank_weight_component_eq i).symm
  obtain ⟨j, Φ, hΦ⟩ := GlobalTheory.FinIsoExists.exists_isFinIso (Yc D 0) (Wc D i) (R.βY 0) (R.ΛY 0) _ (R.βW i) (R.ΛW i) _ R.Pg
    hrk hc hc' (GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hC.lev.Pg)
  obtain ⟨h, hh⟩ := GlobalTheory.KapIsot.frames_inner (Yc D 0) (Wc D i) hF PY PW hY hW
    (by rw [GlobalTheory.PartDims.rank_zeroth_component_eq]; exact GlobalTheory.KapIsot.odd_r D.R) _ _ _ j Φ hΦ
  refine ⟨h, fun κ hκ => ?_⟩
  have hx := hh (h⁻¹ * κ * h)
  rw [show h * (h⁻¹ * κ * h) * h⁻¹ = κ by group] at hx
  obtain ⟨l1, l2⟩ := GlobalTheory.LevTrans.levtrans (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) D.R.r D.R.t (r_le_Y 0) (r_le_rank_Wc i) R.Pg R.chi
    (fun _ _ => 1) j Φ hΦ ⟨PY.ψ (h⁻¹ * κ * h), PY.into _⟩
  rw [hx] at l1 l2
  obtain ⟨hp, hH⟩ := mem_lev.1 hκ.2
  have hpY := l1.2 hp
  have hrt : rTup (R.βW i) (R.datWp i P) (finE (Wc D i) (PW.ψ κ)) =
      rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) (PY.ψ (h⁻¹ * κ * h))) := l2 hpY
  refine ⟨?_, ?_⟩
  · show PY.ψ (h⁻¹ * κ * h) ∈
      (GfC (Yc D 0) ⊓ (lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P)).comap (finE (Yc D 0)) : Subgroup _)
    refine Subgroup.mem_inf.2 ⟨PY.into _, ?_⟩
    show finE (Yc D 0) (PY.ψ (h⁻¹ * κ * h)) ∈ lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P)
    refine mem_lev.2 ⟨hpY, ?_⟩
    rw [← hrt]
    exact hH
  · have e1 : levChi (Wc D i) (R.βW i) (R.datWp i P) (PW.ψ κ) =
        ((ext1 P.H P.chi (rTup (R.βW i) (R.datWp i P) (finE (Wc D i) (PW.ψ κ))) : ℂˣ) : ℂ) :=
      levChi_datY (Wc D i) (R.βW i) D.R.r D.R.t (r_le_rank_Wc i) R.Pg P (fun _ _ => 1) (fun _ => 1) (PW.ψ κ)
    have e2 : levChi (Yc D 0) (R.βY 0) (R.dat0 P) (PY.ψ (h⁻¹ * κ * h)) =
        ((ext1 P.H P.chi (rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) (PY.ψ (h⁻¹ * κ * h)))) : ℂˣ) : ℂ) :=
      levChi_datY (Yc D 0) (R.βY 0) D.R.r D.R.t (r_le_Y 0) R.Pg P R.chi (fun _ => 1) (PY.ψ (h⁻¹ * κ * h))
    rw [e1, e2, hrt]

end GlobalTheory.FrameMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberAmpleConsNefNonnegStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIntersectionNumber_ample_cons_nef_nonneg : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k E P) → ∀ A : LB X, IsAmpleLB A → (∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k (GlobalTheory.structureModule X) (Fin.cons A P : Fin (d + 1) → LB X)) := by
  first | exact @GlobalTheory.interNum_cons_ample_nef_nonneg | exact GlobalTheory.interNum_cons_ample_nef_nonneg | (intros; apply GlobalTheory.interNum_cons_ample_nef_nonneg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberNonnegOfAmpleStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIntersectionNumber_nonneg_of_ample : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, IsAmpleLB (P i)) → 0 ≤ interNum k F P := by
  first | exact @GlobalTheory.interNum_nonneg_of_isAmpleLB_of_isProjOver | exact GlobalTheory.interNum_nonneg_of_isAmpleLB_of_isProjOver | (intros; apply GlobalTheory.interNum_nonneg_of_isAmpleLB_of_isProjOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqOfWeylAntisymmetrizationEq
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem linForm_eq_of_antisymm_eq : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ), (∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q, L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q) → ∀ Q Q' : MvPolynomial (Root m) ℝ, antisymm Q = antisymm Q' → L Q = L Q' := by
  intro ι _ m L hL Q Q' h
  have sq : ∀ u : ℤˣ, ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
    intro u
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have key : ∀ P : MvPolynomial (Root m) ℝ,
      L (antisymm P) = (Fintype.card (∀ τ, Equiv.Perm (Fin (m τ))) : ℝ) * L P := by
    intro P
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.GoodMetric.antisymm, map_sum, map_zsmul]
    rw [Finset.sum_congr rfl (fun w _ => by
      rw [GlobalTheory.T.linearForm_alternating_of_adjacent_swap_blocks ι m L hL w P, zsmul_eq_mul, ← mul_assoc, sq, one_mul])]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (∀ τ, Equiv.Perm (Fin (m τ))) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ∀ τ, Equiv.Perm (Fin (m τ)))).ne'
  have e := congrArg L h
  rw [key, key] at e
  exact mul_left_cancel₀ hc e

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFubiniStudyDensityEqOne
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

theorem lintegral_fubiniStudy_density_eq_one : ∀ n : ℕ, ∫⁻ v : ReciprocityTheory.L2DbarEstimates.V n,
    ENNReal.ofReal (n.factorial / Real.pi ^ n * ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) = 1 := by
  intro n
  have hc : (0 : ℝ) ≤ n.factorial / Real.pi ^ n := by positivity
  have hmeas : Measurable fun v : ReciprocityTheory.L2DbarEstimates.V n =>
      ENNReal.ofReal (((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) := by fun_prop
  have hsplit : ∀ v : ReciprocityTheory.L2DbarEstimates.V n,
      ENNReal.ofReal (n.factorial / Real.pi ^ n * ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) =
        ENNReal.ofReal (n.factorial / Real.pi ^ n) *
          ENNReal.ofReal (((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) := fun v => ENNReal.ofReal_mul hc
  simp_rw [hsplit]
  rw [lintegral_const_mul _ hmeas]
  have hV : ∫⁻ v : ReciprocityTheory.L2DbarEstimates.V n, ENNReal.ofReal (((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) =
      ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (((1 + ∑ i, ‖z i‖ ^ 2) ^ (n + 0 + 1))⁻¹) := by
    rw [← (FinChart.measurePreserving_toV (D := n)).lintegral_comp hmeas]
    congr 1
    funext z
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  rw [hV, _root_.GlobalTheory.ComplexSpaceIntegral.lintegral_inv_pow_add_sum_norm_sq n 0 1 one_pos, ← ENNReal.ofReal_mul hc]
  have hpi : Real.pi ^ n ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [show (n.factorial : ℝ) / Real.pi ^ n * (Real.pi ^ n * (Nat.factorial 0 : ℝ) /
      (((n + 0).factorial : ℝ) * 1 ^ (0 + 1))) = 1 by
    simp only [Nat.factorial_zero, Nat.cast_one, add_zero, one_pow, mul_one]
    field_simp]
  exact ENNReal.ofReal_one

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceGraphIdealTensorNeTopStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeGraphIdealTensor_ne_top : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K)),
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  graphIdeal (κ' := κ') E R π ρ ≠ ⊤ := by
  first | exact @GlobalTheory.GraphLocal.graphIdeal_ne_top | exact GlobalTheory.GraphLocal.graphIdeal_ne_top | (intros; apply GlobalTheory.GraphLocal.graphIdeal_ne_top <;> assumption)
end

