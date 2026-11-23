module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Formalism.DegreeFormula.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0233
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionEmbeddingCompatibleClosures
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem normGroup_adjoin_eq_norm_range_completion : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)) (j : K → Kbar w) (f : w.adicCompletion E →+* W.adicCompletion K) (b : Kbar w ≃+* Kbar W), Continuous f → (∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) → (∀ x : K, b (j x) = algebraMap (W.adicCompletion K) _ (algebraMap K (W.adicCompletion K) x)) → (∀ x : E, f (algebraMap E _ x) = algebraMap K _ (algebraMap E K x)) → letI := f.toAlgebra; Neutral.B1.normGroup (w.adicCompletion E) (IntermediateField.adjoin (w.adicCompletion E) (Set.range j)) = (Units.map (Algebra.norm (w.adicCompletion E) : W.adicCompletion K →* w.adicCompletion E)).range := by
  intro E K _ _ _ _ _ w W j f b hfc hb hj hf
  letI := f.toAlgebra

  let c : W.adicCompletion K →ₐ[w.adicCompletion E] Kbar w :=
    { toRingHom := b.symm.toRingHom.comp (algebraMap (W.adicCompletion K) (Kbar W))
      commutes' := fun x => by
        change b.symm (algebraMap _ _ (f x)) = _
        rw [← hb x]; exact b.symm_apply_apply _ }
  have hcj : ∀ x : K, c (algebraMap K (W.adicCompletion K) x) = j x := by
    intro x
    change b.symm (algebraMap _ _ _) = _
    rw [← hj x]; exact b.symm_apply_apply _
  have hrange : c.fieldRange = IntermediateField.adjoin (w.adicCompletion E) (Set.range j) := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      have hspan := span_basis_image_adicCompletion_eq_top E K w W f hfc hf _ (Module.finBasis E K)
      have hy : y ∈ Submodule.span (w.adicCompletion E)
          (Set.range fun i => algebraMap K (W.adicCompletion K) (Module.finBasis E K i)) := by
        rw [hspan]; trivial
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        change c _ ∈ _
        rw [hcj]
        exact IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩
      | zero => simp
      | add x y _ _ hx hy =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add (f := _)] at hx hy ⊢
        exact add_mem hx hy
      | smul a x _ hx =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_smul] at hx ⊢
        exact IntermediateField.smul_mem _ hx
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      exact ⟨algebraMap K _ x, hcj x⟩
  let e : W.adicCompletion K ≃ₐ[w.adicCompletion E]
      IntermediateField.adjoin (w.adicCompletion E) (Set.range j) :=
    (AlgEquiv.ofInjectiveField c).trans (IntermediateField.equivOfEq hrange)
  ext u
  simp only [Neutral.B1.normGroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨Units.map e.symm.toRingEquiv.toMonoidHom v, ?_⟩
    ext
    simp [Algebra.norm_eq_of_algEquiv]
  · rintro ⟨v, rfl⟩
    refine ⟨Units.map e.toRingEquiv.toMonoidHom v, ?_⟩
    ext
    simp [Algebra.norm_eq_of_algEquiv]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CurvatureFormMatrixBoundedDomainModelMetricAtZer
section
set_option autoImplicit false

noncomputable section

open Matrix MvPolynomial Filter Topology ComplexConjugate
open GlobalTheory.HermFrame

namespace GlobalTheory.DomainDens

variable {ι : Type} [Fintype ι] {p q n : ℕ} (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι)

def flatCoordinateMatrixBlock (u : ReciprocityTheory.L2DbarEstimates.V n) : Matrix (Fin p) (Fin q) ℂ :=
  Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h u) τ

theorem block_reshape_apply (u : ReciprocityTheory.L2DbarEstimates.V n) (i : Fin p) (b : Fin q) :
    flatCoordinateMatrixBlock h τ u i b = u (Fintype.equivFinOfCardEq h (τ, i, b)) := rfl

theorem flatCoordinateMatrixBlock_entry_eq_proj (i : Fin p) (b : Fin q) :
    (fun u => flatCoordinateMatrixBlock h τ u i b) = fun u => EuclideanSpace.proj (𝕜 := ℂ) (Fintype.equivFinOfCardEq h (τ, i, b)) u :=
  rfl

theorem flatCoordinateMatrixBlock_at_zero : flatCoordinateMatrixBlock h τ 0 = 0 := by
  ext i b; simp [block_reshape_apply]

theorem matrixHolomorphicPartialDeriv_flatCoordinateMatrixBlock (x ξ : ReciprocityTheory.L2DbarEstimates.V n) : mdel (flatCoordinateMatrixBlock h τ) x ξ = flatCoordinateMatrixBlock h τ ξ := by
  ext i b
  rw [mdel_apply, flatCoordinateMatrixBlock_entry_eq_proj, del_eq_fderiv (ContinuousLinearMap.differentiableAt _),
    ContinuousLinearMap.fderiv]
  rfl

theorem matrixAntiholomorphicPartialDeriv_flatCoordinateMatrixBlock (x η : ReciprocityTheory.L2DbarEstimates.V n) : mdbar (flatCoordinateMatrixBlock h τ) x η = 0 := by
  ext i b
  rw [mdbar_apply, flatCoordinateMatrixBlock_entry_eq_proj, dbar_eq_zero (ContinuousLinearMap.differentiableAt _)]
  rfl

theorem matrixEntriesContDiffAt_flatCoordinateMatrixBlock {k : WithTop ℕ∞} (x : ReciprocityTheory.L2DbarEstimates.V n) : MContDiffAt k (flatCoordinateMatrixBlock h τ) x :=
  fun i b => by
    rw [flatCoordinateMatrixBlock_entry_eq_proj]
    exact (ContinuousLinearMap.contDiff (𝕜 := ℂ) (n := k)
      (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) (Fintype.equivFinOfCardEq h (τ, i, b)) : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ)).restrict_scalars ℝ |>.contDiffAt

theorem mContDiffAt_hP {k : WithTop ℕ∞} (x : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt k (fun u => Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u)) x := by
  unfold Formalism.DegreeFormula.hP
  exact (mContDiffAt_const 1).sub ((matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ x).mul (matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ x).conjTranspose)

theorem mdel_hP (x ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u => Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u)) x ξ = -(flatCoordinateMatrixBlock h τ ξ * (flatCoordinateMatrixBlock h τ x)ᴴ) := by
  have hz : MContDiffAt 1 (flatCoordinateMatrixBlock h τ) x := matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ x
  have e : (fun u => Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u)) =
      fun u => (fun _ => (1 : Matrix (Fin p) (Fin p) ℂ)) u + -(flatCoordinateMatrixBlock h τ u * (flatCoordinateMatrixBlock h τ u)ᴴ) := by
    funext u; simp [Formalism.DegreeFormula.hP, sub_eq_add_neg]
  rw [e, mdel_add (mContDiffAt_const _) (hz.mul hz.conjTranspose).neg, mdel_const, mdel_neg,
    mdel_mul hz hz.conjTranspose, mdel_conjTranspose, matrixAntiholomorphicPartialDeriv_flatCoordinateMatrixBlock, matrixHolomorphicPartialDeriv_flatCoordinateMatrixBlock]
  simp

theorem hP_zero : Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ 0) = 1 := by simp [Formalism.DegreeFormula.hP, flatCoordinateMatrixBlock_at_zero]

theorem conn_model (x ξ : ReciprocityTheory.L2DbarEstimates.V n) (hu : IsUnit (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ x)).det) :
    conn (fun u => ((Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹)ᵀ) x ξ =
      flatCoordinateMatrixBlock h τ ξ * (flatCoordinateMatrixBlock h τ x)ᴴ * (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ x))⁻¹ := by
  rw [conn, transpose_transpose, mdel_transpose (fun u => (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹), transpose_transpose,
    mdel_inv (mContDiffAt_hP h τ x) hu, nonsing_inv_nonsing_inv _ hu, mdel_hP]
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]

theorem curv_model (ξ η : ReciprocityTheory.L2DbarEstimates.V n) :
    curv (fun u => ((Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹)ᵀ) 0 ξ η = -(flatCoordinateMatrixBlock h τ ξ * (flatCoordinateMatrixBlock h τ η)ᴴ) := by
  have hu0 : IsUnit (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ 0)).det := by simp [hP_zero]
  have hev := (mContDiffAt_hP (k := 1) h τ 0).eventually_isUnit hu0
  have hz : MContDiffAt 1 (flatCoordinateMatrixBlock h τ) 0 := matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ 0
  rw [curv, mdbar_congr (hev.mono fun x hx => conn_model h τ x ξ hx),
    mdbar_mul ((mContDiffAt_const _).mul hz.conjTranspose) ((mContDiffAt_hP h τ 0).inv hu0),
    mdbar_mul (mContDiffAt_const _) hz.conjTranspose, mdbar_conjTranspose, matrixHolomorphicPartialDeriv_flatCoordinateMatrixBlock, mdbar_const, hP_zero,
    flatCoordinateMatrixBlock_at_zero]
  simp

theorem curvPoly_model_zero : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι),
    GlobalTheory.GoodMetric.curvPoly
      (fun u => Matrix.transpose (Formalism.DegreeFormula.hP (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 =
      -GlobalTheory.DomainDens.blockSym h τ := by
  intro ι _ p q n h τ
  have e2 : ∀ (a c : Fin n) (i j : Fin p),
      curv (fun u => Matrix.transpose (Formalism.DegreeFormula.hP (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹)
        0 (GlobalTheory.GoodMetric.coordVec a) (GlobalTheory.GoodMetric.coordVec c) i j =
      -∑ b : Fin q, (if Fintype.equivFinOfCardEq h (τ, i, b) = a then 1 else 0) *
        (if Fintype.equivFinOfCardEq h (τ, j, b) = c then 1 else 0) := by
    intro a c i j
    change curv (fun u => ((Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹)ᵀ) 0 _ _ i j = _
    rw [curv_model h τ, Matrix.neg_apply, Matrix.mul_apply]
    simp [block_reshape_apply, PiLp.single_apply]
  refine Matrix.ext fun i j => ?_
  simp only [GlobalTheory.GoodMetric.curvPoly, of_apply, e2, Matrix.neg_apply, blockSym_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_neg, neg_mul, Finset.sum_neg_distrib, neg_inj, map_sum, Finset.sum_mul, mul_ite, ite_mul, one_mul,
    zero_mul, mul_zero, apply_ite (C : ℂ → MvPolynomial (Fin n × Fin n) ℂ), map_one, map_zero]
  rw [Finset.sum_congr rfl fun _ _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [Finset.sum_ite_eq]

end GlobalTheory.DomainDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DictionaryRationalElementAnalyticPoint
section
namespace GlobalTheory.OneMapRef.DictPt

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem isDerivAt0_comp {X : Scheme.{0}} {g g' : ℕ} {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (hol : IsHolTo Set.univ e)
    (ρ : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) {w : Fin g' → ℂ} {u : Sp (DualNumber ℂ) ⟶ X} (h : IsDerivAt0 e (ρ w) u) :
    IsDerivAt0 (fun z => e (ρ z)) w u := by
  rw [HolHom.isDerivAt0_iff] at h ⊢
  refine ⟨h.1.trans (congrArg e (map_zero ρ).symm), fun U hU f => ?_⟩
  have hU' : ⊤ ≤ e 0 ⁻¹ᵁ U := by simpa only [map_zero] using hU
  have h1 : HasFDerivAt (fun t => valAt' (e t) U f) (fderiv ℂ (fun t => valAt' (e t) U f) 0) (ρ 0) := by
    rw [map_zero]; exact ((HolHom.holAt_of_isHolTo hol (Set.mem_univ 0) U hU').2 f).hasFDerivAt
  exact (h.2 U hU' f).trans (congrArg (· w) (h1.comp 0 ρ.hasFDerivAt).fderiv).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g g' : ℕ} {ty : Fin g' → (E →+* ℂ)}

theorem isHolTo_ex (F : FamilyUnif Xo σ ty) (i : Fin F.n) {P : (F.Di i).La →+ (Fin g' → ℂ)}
    (hP : IsPeriod (F.Di i) ty P) : IsHolTo Set.univ (fun z => (F.ex i P z).left) := by
  have h := (F.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  exact HolHom.isHolTo_of_holAt isOpen_univ fun z _ =>
    (HolHom.holAt_of_isHolTo h (z := (0, z)) ⟨trivial, trivial⟩).precomp (k := fun z => (0, z)) (by fun_prop)

theorem levPt_eq (F : FamilyUnif Xo σ ty) (i : Fin F.n) {Pm : (F.Di i).La →+ (Fin g' → ℂ)}
    (hper : IsPeriod (F.Di i) ty Pm) (π : Fin g ≃ Fin g') {y : Sp ℂ ⟶ Xo.X} (h : y = F.u i Pm)
    (ex : (Fin g → ℂ) → (ptO Xo y ⟶ Xo.univ.t.G)) (u : Fin g' → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left))
    (b1 : ∀ z w, ex (z + w) = ex z * ex w) (b2 : IsHolTo Set.univ (fun z => (ex z).left))
    (b3 : ∀ m, IsDerivAt0 (fun z => (ex z).left) (Pi.single (π.symm m) 1) (u m))
    (b4 : ∀ m, IsDerivAt0 (fun z => (F.ex i Pm z).left) (Pi.single m 1) (u m))
    (a : Dw.La) (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La)) :
    levPt Xo y a = ex (fun j => (l.M : ℂ)⁻¹ * Pm (F.t i a) (π j)) := by
  subst h
  let ρ : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ) := ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (π j)
  have hρ : ∀ m, ρ (Pi.single m 1) = Pi.single (π.symm m) 1 := fun m => by
    funext j
    change (Pi.single m 1 : Fin g' → ℂ) (π j) = _
    simp only [Pi.single_apply, Equiv.eq_symm_apply]
  have E : (fun z => ex (ρ z)) = F.ex i Pm :=
    GlobalTheory.AnUniq.exp_eq (fun z w => by rw [map_add (f := _), b1]) (F.ex_add _ _ hper)
      (HolHom.isHolTo_of_holAt isOpen_univ fun z _ =>
        (HolHom.holAt_of_isHolTo b2 (Set.mem_univ (ρ z))).precomp ρ.differentiableAt) (isHolTo_ex F _ hper)
      u (fun m => isDerivAt0_comp b2 ρ (by rw [hρ]; exact b3 m)) b4
  exact (F.ex_eta i Pm hper a ha).trans (congrFun E _).symm

theorem ex_add_ker {y : Sp ℂ ⟶ Xo.X} (ex : (Fin g → ℂ) → (ptO Xo y ⟶ Xo.univ.t.G))
    (b1 : ∀ z w, ex (z + w) = ex z * ex w) (z k z' : Fin g → ℂ) (hk : ex k = 1) (h : z' = z + k) : ex z = ex z' := by
  rw [h, b1, hk, _root_.mul_one]

theorem sub_eq_nsmul {A : Type} [AddCommGroup A] (M : ℕ) (p q z w w' : A) (e : p - z = M • w)
    (e' : q - z = M • w') : p - q = M • (w - w') := by
  rw [smul_sub, ← e, ← e', sub_sub_sub_cancel_right]

end GlobalTheory.OneMapRef.DictPt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

theorem GlobalTheory.OneMapRef.DictPt.exists_sub_eq {D : D7} (V : HSp D) (g : GA D V) (M : ℕ) (hM : M ≠ 0)
    (p q : Fin V.rank → D.host.E) (z w w' : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hw : w ∈ latGHat V g) (hw' : w' ∈ latGHat V g) (e : finVec V p - z = M • w) (e' : finVec V q - z = M • w') :
    (M : D.host.E)⁻¹ • (p - q) ∈ latG V g := by
  rw [(GlobalTheory.MarkCoset.latG_spec D V g).1]
  have hM' : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have h1 : M • finVec V ((M : D.host.E)⁻¹ • (p - q)) = M • (w - w') := by
    refine Eq.trans ?_ (GlobalTheory.OneMapRef.DictPt.sub_eq_nsmul M _ _ z w w' e e')
    funext i
    change M • ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((M : D.host.E)⁻¹ * (p i - q i))) = 1 ⊗ₜ p i - 1 ⊗ₜ q i
    rw [← TensorProduct.tmul_smul, nsmul_eq_mul, mul_inv_cancel_left₀ hM', TensorProduct.tmul_sub]
  have h2 : finVec V ((M : D.host.E)⁻¹ • (p - q)) = w - w' :=
    GlobalTheory.MarkCoset.nsmul_cancel D.host.F M (Nat.cast_ne_zero.2 hM) h1
  rw [h2]
  exact sub_mem hw hw'


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.OneMapRef.DictPt.dict_point : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (W : HSp D) (r : ℕ) (hr : W.rank = r) (U : Unf Xo c σ r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (g₀ : ℕ) (e₀ : Fin g₀ ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e₀ j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (θ : InfFam D) (Z₀ : Fam W), GoodEmb c σ → IsUnf U → 1 ≤ r → IsInfFam θ → (∀ k τ, IsInfEmb τ.1 (th k τ)) → DictLat U W hr dict ι e₀ F ik φ th x₀ → (∀ ρ, x₀ (tauE D ρ) = Matrix.reindex (finCongr hr) (finCongr hr) (Z₀ ρ)) → ∀ h : GA D W, ∃ γ ∈ GQ W, MarkBy U W hr dict ι F ik φ h γ ∧ latW hr (U.X (dict h).1).Λ = latG W (γ * h) ∧ (∀ eT : D.what₂.Tau ≃ (U.X (dict h).1).Ψ, (∀ ρ, (eT ρ).1 = tauE D ρ) → (dict h).2 = frOf hr eT (mvZ θ (γ * h) Z₀)) ∧ ∀ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X (dict h).1).Λ) (idx : Fin g ≃ (U.X (dict h).1).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl (U.X (dict h).1) bas → Matched c σ (U.X (dict h).1) idx e → letI : Algebra c.F ℂ := σ.toAlgebra; ∀ (A : AnFib (U.X (dict h).1) bas idx e (dict h).2 (U.X (dict h).1).Λ (ptC U (dict h).1 ⟨(dict h).2, hx⟩)) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), (∀ a, mk a ∈ (U.X (dict h).1).Λ) → MarkAd hr l ι (γ * h) mk → A.Marked mk := by
  intro D H Dw l Xo c σ W r hr U dict ι g₀ e₀ F ik φ th x₀ θ Z₀ hσ hU h1 hθ hth hD hx₀ h
  subst hr
  obtain ⟨γ, hγ, hl, hm, hf⟩ := hD.2 h
  have hΛ : (U.X (dict h).1).Λ = latG W (γ * h) := SetLike.ext' (hl.trans (Set.image_id _))
  refine ⟨γ, hγ, ⟨hγ, hl, hm⟩, hΛ, fun eT heT => ?_, ?_⟩
  · funext τ
    obtain ⟨ρ, rfl⟩ := eT.surjective τ
    have e1 : th _ (eT ρ) = θ ρ :=
      GlobalTheory.SmoothForms.RealPts.infEmb_unique _ _ _ (hth _ (eT ρ)) (by rw [heT]; exact hθ ρ)
    have := hf (eT ρ)
    rw [e1, heT, hx₀] at this
    funext a b
    simp only [frOf, Equiv.symm_apply_apply]
    exact congrFun (congrFun this a) b
  · intro hx g bas idx e hs hM
    letI : Algebra c.F ℂ := σ.toAlgebra
    intro A mk hmk hA a ha
    obtain ⟨Pm, hPm, hP, hu, hder⟩ := hD.1.2 (dict h).1 ⟨(dict h).2, hx⟩
    have hM0 : l.M ≠ 0 := by have := l.three_le; omega
    have key := GlobalTheory.OneMapRef.DictPt.levPt_eq F _ hP (e.trans e₀.symm) hu A.ex (fun m => (U.un _ ⟨(dict h).2, hx⟩).u (e₀ m).1 (e₀ m).2)
      A.ex_add A.hol (fun m => A.der (e₀ m)) (fun m => by simpa only [Sigma.eta, Equiv.symm_apply_apply] using hder (e₀ m).1 (e₀ m).2) a ha
    obtain ⟨w, hw, ew⟩ := hA a ha
    obtain ⟨w', hw', ew'⟩ := hm a ha
    have hmem := GlobalTheory.OneMapRef.DictPt.exists_sub_eq W (γ * h) l.M hM0 _ _ _ w w' hw hw' ew ew'
    rw [← hΛ] at hmem
    have hk := (A.ex_ker _).2 ⟨_, hmem, rfl⟩
    refine key.trans (GlobalTheory.OneMapRef.DictPt.ex_add_ker A.ex A.ex_add _ _ _ hk ?_)
    funext j
    have e3 : ∀ v (ℓ ℓ' : Lt1 Dw), ℓ = ℓ' → perFr (U.X (dict h).1) (dict h).2 v (relab c σ ℓ.1) ℓ.2 =
        perFr (U.X (dict h).1) (dict h).2 v (relab c σ ℓ'.1) ℓ'.2 := fun v ℓ ℓ' hℓ => by rw [hℓ]
    rw [Pi.add_apply, hPm, Equiv.trans_apply, e3 _ _ _ (e₀.apply_symm_apply (e j)), ← hM.1]
    have e2 : ∀ p q : Fin W.rank → D.host.E, (l.M : D.host.E)⁻¹ • p =
        (l.M : D.host.E)⁻¹ • q + (l.M : D.host.E)⁻¹ • (p - q) := fun p q => by rw [← smul_add, add_sub_cancel]
    rw [e2 (mk a) (φ _ (F.t _ a))]
    simp only [pv, Function.comp_apply, per_add, Pi.add_apply]
    congr 1
    rw [per_smul, map_inv₀, map_natCast]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DrowsPos
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

theorem drows_pos : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → Lam3 Z → 0 < D.what₂.Drows := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z _ hH _
  have e1 : Module.finrank D.what₂.LL D.div.RR.V = Fintype.card D.div.RR.ι :=
    Module.finrank_eq_card_basis D.div.RR.b
  have e2 : Module.finrank ℂ D.what₂.EE = Fintype.card D.div.RR.ι :=
    Module.finrank_eq_card_basis (Module.Basis.mk D.jEE_basis.1 (le_of_eq D.jEE_basis.2.symm))
  have e3 : Module.finrank ℂ D.what₂.EE = D.what₂.Drows := by
    simpa using Module.finrank_eq_card_basis D.what₂.onb.toBasis
  have h2 : Module.finrank D.what₂.LL D.div.RR.V = ((R.toCx3 F).data F.cr true).D := by
    rw [← Z.eRR.finrank_eq, Module.finrank_fin_fun]
  have h3 : 0 < ((R.toCx3 F).data F.cr true).D := hH.prim.pos true
  omega

end GlobalTheory.Mem.R3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgHomFunctionFieldOfSpecializesGenericPoi
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

theorem exists_algHom_of_specializes_genericPoint :
    ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] [Algebra F K] (q : Sp K ⟶ Y.X),
      q (IsLocalRing.closedPoint K) ⤳ genericPoint Y.X → q ≫ Y.str = spMap (algebraMap F K) →
        ∃ ψ : Y.Fn →ₐ[F] K, q = spMap ψ.toRingHom ≫ (ratOf Y).pt := by
  intro F _ Y K _ _ q h hq
  let ψ₀ : Y.Fn →+* K := (Y.X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := .of K) q).hom
  have e : spMap ψ₀ ≫ (ratOf Y).pt = q := by
    change Spec.map (CommRingCat.ofHom ψ₀) ≫ Y.X.fromSpecStalk (genericPoint Y.X) = q
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact spMap_stalkClosedPointTo q
  have hc : ψ₀.comp (algebraMap F Y.Fn) = algebraMap F K := by
    have h1 : spMap (ψ₀.comp (algebraMap F Y.Fn)) = spMap (algebraMap F K) := by
      have hs := (ratOf Y).pt_s
      calc spMap (ψ₀.comp (algebraMap F Y.Fn)) = spMap ψ₀ ≫ spMap (algebraMap F Y.Fn) := by
            change Spec.map (CommRingCat.ofHom (ψ₀.comp (algebraMap F Y.Fn))) = _
            rw [CommRingCat.ofHom_comp, Spec.map_comp]
        _ = spMap ψ₀ ≫ ((ratOf Y).pt ≫ (ratOf Y).s) := by rw [hs]
        _ = (spMap ψ₀ ≫ (ratOf Y).pt) ≫ (ratOf Y).s := (Category.assoc _ _ _).symm
        _ = q ≫ Y.str := by
            change (spMap ψ₀ ≫ (ratOf Y).pt) ≫ Y.str = q ≫ Y.str
            rw [e]
            rfl
        _ = spMap (algebraMap F K) := hq
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  refine ⟨{ ψ₀ with commutes' := fun a => congrArg (fun g : F →+* K => g a) hc }, ?_⟩
  exact e.symm

end GlobalTheory.FlagBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAveragedOperatorMappingToKFinite
section
noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem exists_isAvg_apply_eq : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ a : H, a ≠ 0 → ∀ v, IsKFin ε σ v → ∃ T : H → H, IsAvg ε σ T ∧ T a = v := by
  intro n ε H _ _ _ σ h a ha v hv
  obtain ⟨a1, a2, a3, a4, a5⟩ := isAvg_closure n ε H σ h.1
  obtain ⟨c1, c2, c3, c4⟩ := kCoef_kAvg n ε H σ h.1
  let A : Submodule ℂ H :=
    { carrier := {x | ∃ T : H → H, IsAvg ε σ T ∧ T a = x}
      add_mem' := by
        rintro _ _ ⟨T, hT, rfl⟩ ⟨T', hT', rfl⟩
        exact ⟨_, (a2 T T' hT hT').1, rfl⟩
      zero_mem' := ⟨_, a5, rfl⟩
      smul_mem' := by
        rintro c _ ⟨T, hT, rfl⟩
        exact ⟨_, a3 c T hT, rfl⟩ }
  have hA : ∀ T : H → H, IsAvg ε σ T → ∀ x ∈ A, T x ∈ A := by
    rintro T hT _ ⟨T', hT', rfl⟩
    exact ⟨_, (a2 T T' hT hT').2, rfl⟩
  have haA : a ∈ A := ⟨_, a1 1 (one_mem_UJ ε), sigma_one h.1 a⟩
  have hdense : Dense (A : Set H) :=
    dense_of_irred h.2.1 (fun g hg x hx => hA _ (a1 g hg) x hx) ((Submodule.ne_bot_iff _).2 ⟨a, haA, ha⟩)
  have hrange : ∀ e : KG ε → ℂ, KFinFun ε e → Continuous e → ∀ w, kAvg ε σ e w ∈ A := by
    intro e he hc w
    obtain ⟨m, b, c, -, -, -, hbc⟩ := _root_.GlobalTheory.TypeSum.kAvg_finite_rank n ε H σ h e he
    obtain ⟨Q, hQ⟩ := c3 e hc
    let F : Submodule ℂ H := Submodule.span ℂ (Set.range b)
    haveI : FiniteDimensional ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
    haveI : FiniteDimensional ℂ (A ⊓ F : Submodule ℂ H) := Submodule.finiteDimensional_inf_right A F
    have hcl : IsClosed (Q ⁻¹' ((A ⊓ F : Submodule ℂ H) : Set H)) :=
      (Submodule.closed_of_finiteDimensional _).preimage Q.continuous
    have hsub : (A : Set H) ⊆ Q ⁻¹' ((A ⊓ F : Submodule ℂ H) : Set H) := by
      intro x hx
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [hQ]; exact hA _ (a4 e hc) x hx
      · rw [hQ, hbc]
        exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have := closure_minimal hsub hcl (hdense w)
    rw [← hQ]
    exact (Submodule.mem_inf.1 this).1
  obtain ⟨S, hS, hvS, hK⟩ := hv
  haveI : FiniteDimensional ℂ (S ⊓ A : Submodule ℂ H) := Submodule.finiteDimensional_inf_left S A
  obtain ⟨w, hw, y, hy, hvwy⟩ := (S ⊓ A).exists_add_mem_mem_orthogonal v
  have hyS : y ∈ S := by
    have := S.sub_mem hvS (Submodule.mem_inf.1 hw).1
    rwa [hvwy, add_sub_cancel_left] at this
  have hy0 : y = 0 := by
    by_contra hy0
    have hk := c1 y ⟨S, hS, hyS, hK⟩
    have hc : Continuous fun k : KG ε => star ⟪y, σ (toMK k) y⟫_ℂ := by
      obtain ⟨F, -, h1, h2, -⟩ := hk
      exact h2 _ h1
    exact c2 y hy0 (Submodule.inner_left_of_mem_orthogonal
      (Submodule.mem_inf.2 ⟨c4 _ hc S hS hK y hyS, hrange _ hk hc y⟩) hy)
  rw [hvwy, hy0, add_zero]
  exact (Submodule.mem_inf.1 hw).2

end GlobalTheory.TypeSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmConjugationOmega
section
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemN

theorem exists_isCMConjOm_nData : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (nd : NData R H what₂), ∃ c : nd.Om ≃+* nd.Om, IsCMConjOm H.E nd.Om c :=
  fun _ H _ nd => GlobalTheory.Mem.GaloisStage.exists_isCMConjOm H nd.Om

end GlobalTheory.MemN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtensionPowStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_pow_alt : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (e : ℕ), 0 < e → (∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e) → ∃ f : v.adicCompletion K →+* v'.adicCompletion L, Continuous f ∧ (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧ ∀ y, Valued.v (f y) = Valued.v y ^ e := by
  first | exact @GlobalTheory.DenseCompl.exists_extension_pow | exact GlobalTheory.DenseCompl.exists_extension_pow | (intros; apply GlobalTheory.DenseCompl.exists_extension_pow <;> assumption)
end

