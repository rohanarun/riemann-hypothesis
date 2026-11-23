module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantsActKernelFamilyShifted
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift.OneSide

section Abstract

variable {n : ℕ} {Y S M : Type} [AddCommGroup S] [Module ℂ S] [AddCommGroup M] [Module ℂ M]

theorem exists_shift (A : Fin n → Fin n → Module.End ℂ S) (B : Fin n → Fin n → Module.End ℂ M)
    (hA : Formalism.REAL.GlRel A) (hB : Formalism.REAL.GlRel B) (L : Y → M →ₗ[ℂ] S) (lam : Fin n → Fin n → ℂ)
    (h : ∀ i j y f, A i j (L y f) = L y (B i j f + lam i j • f)) :
    ∃ c : ℂ, ∀ i j y f, A i j (L y f) =
      L y ((B i j + if i = j then algebraMap ℂ (Module.End ℂ M) c else 0) f) := by
  by_cases h0 : ∀ y f, L y f = 0
  · exact ⟨0, fun i j y f => by rw [h0, h0, map_zero]⟩
  push Not at h0
  obtain ⟨y, f, h0⟩ := h0
  have key : ∀ i j k l, (if j = k then lam i l else 0) = (if l = i then lam k j else 0) := by
    intro i j k l
    have h1 : (A i j * A k l - A k l * A i j) (L y f) = L y ((B i j * B k l - B k l * B i j) f) := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply, h, map_add (f := _), map_smul, map_sub, smul_add]
      module
    rw [hA, hB] at h1
    have h2 : ((if j = k then lam i l else 0) - (if l = i then lam k j else 0)) • L y f = 0 := by
      rw [sub_smul]
      split_ifs at h1 ⊢ <;>
        simp only [LinearMap.sub_apply, LinearMap.zero_apply, h, map_add (f := _), map_smul, map_sub, map_zero,
          zero_smul] at h1 ⊢ <;>
        linear_combination (norm := module) h1
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right h0)
  rcases n with _ | n
  · exact ⟨0, fun i => i.elim0⟩
  refine ⟨lam 0 0, fun i j y f => ?_⟩
  rw [h]
  by_cases c : i = j
  · subst c
    have := key i 0 0 i
    simp only [if_true] at this
    simp [this]
  · have := key i i i j
    simp only [if_true, if_neg (Ne.symm c)] at this
    simp [this, c]

theorem prod_intertwine (L : M →ₗ[ℂ] S) : ∀ (k : ℕ) (a : Fin k → Module.End ℂ S) (b : Fin k → Module.End ℂ M),
    (∀ i f, a i (L f) = L (b i f)) → ∀ f, (List.ofFn a).prod (L f) = L ((List.ofFn b).prod f)
  | 0, _, _, _, f => by simp
  | k + 1, a, b, e, f => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply,
      prod_intertwine L k _ _ fun i => e i.succ, e]

theorem gelfA_intertwine (L : M →ₗ[ℂ] S) (A : Fin n → Fin n → Module.End ℂ S) (B : Fin n → Fin n → Module.End ℂ M)
    (h : ∀ i j f, A i j (L f) = L (B i j f)) (k : ℕ) (f : M) :
    GlobalTheory.SmoothForms.gelfA A k (L f) = L (GlobalTheory.SmoothForms.gelfA B k f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.SmoothForms.gelfA, GlobalTheory.SmoothForms.gelfA, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun idx _ => prod_intertwine L _ _ _ (fun _ => h _ _) f

end Abstract

theorem gelf_kernel : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ (Y M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (Y → GA D V → ℂ)), (∀ f y, κ f y ∈ SmFun θ V) → ∀ (τ : D.what₂.Tau) (Q : Matrix (Fin V.rank) (Fin V.rank) ℂ →ₗ[ℂ] Module.End ℂ M), Formalism.REAL.GlRel (fun i j => Q (Matrix.single i j 1)) → (∀ X ∈ lieAt V τ, ∃ lam : ℂ, ∀ f y g, HasDerivAt (fun t : ℝ => κ f y (g * oneP θ V τ X t)) (κ (Q X f + lam • f) y g) 0) → ∃ c : ℂ, ∀ k f y, gelf θ V τ k (κ f y) = κ (GlobalTheory.SmoothForms.gelfA (fun i j => Q (Matrix.single i j 1) + if i = j then algebraMap ℂ (Module.End ℂ M) c else 0) k f) y := by
  intro D θ hθ V Y M _ _ κ hκ τ Q hQ hd
  choose lam hlam using hd
  have hR : ∀ X (hX : X ∈ lieAt V τ) f y, Rder θ V τ X (κ f y) = κ (Q X f + lam X hX • f) y :=
    fun X hX f y => funext fun g => (hlam X hX f y g).deriv
  have hC : ∀ Z, ∃ l : ℂ, ∀ f y, RderC θ V τ Z (κ f y) = κ (Q Z f + l • f) y := by
    intro Z
    obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
    refine ⟨lam _ h1 + Complex.I * lam _ h2, fun f y => ?_⟩
    rw [RderC, hR _ h1, hR _ h2]
    have e := GlobalTheory.SmoothAutCheck.parts_sum V τ Z
    generalize lam _ h1 = a
    generalize lam _ h2 = b
    generalize (1 / 2 : ℂ) • (Z + conjAt V τ Z) = P at e ⊢
    generalize (1 / (2 * Complex.I)) • (Z - conjAt V τ Z) = P' at e ⊢
    rw [← e]
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply]
    module
  choose l hl using hC
  let L : Y → M →ₗ[ℂ] SmFun θ V := fun y =>
    LinearMap.codRestrict (SmFun θ V) ((LinearMap.proj y).comp κ) fun f => hκ f y
  obtain ⟨c, hc⟩ := exists_shift _ _ (glRel_derEnd hθ V τ) hQ L (fun i j => l (Matrix.single i j 1))
    fun i j y f => Subtype.ext (hl _ f y)
  refine ⟨c, fun k f y => ?_⟩
  have := gelfA_intertwine (L y) _ (fun i j => Q (Matrix.single i j 1) +
    if i = j then algebraMap ℂ (Module.End ℂ M) c else 0) (fun i j => hc i j y) k f
  exact (GlobalTheory.Mem.RealTranslate.gelf_eq hθ τ k (L y f)).trans (congrArg Subtype.val this)

end GlobalTheory.Mem.Lift.OneSide

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricallyIntegral
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier
open scoped TensorProduct

variable {F Ω Ω' : Type} [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']

theorem exists_openImmersion_ringOn (M : RatModel F Ω) {U : M.Z.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set M.Z).Nonempty) : ∃ ι : Sp (M.ringOn U) ⟶ M.Z, IsOpenImmersion ι ∧ Set.range ι = U ∧
      ι ≫ M.s = spMap (algebraMap F (M.ringOn U)) := by
  let e : Γ(M.Z, U) ≅ CommRingCat.of (M.ringOn U) := (M.sectionsEquiv U hne).toCommRingCatIso
  have hx := GlobalTheory.Points.le_preimage_specMap_fromSpec hU e.hom
  have hv : ∀ f, valR (Spec.map e.hom ≫ hU.fromSpec) U f = M.sectionsEquiv U hne f := fun f => by
    rw [GlobalTheory.Points.valR_eq _ U hx, GlobalTheory.Points.valMap_specMap_fromSpec]
    rfl
  refine ⟨Spec.map e.hom ≫ hU.fromSpec, inferInstance, ?_, ?_⟩
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, (Spec.map e.hom).surjective.range_eq,
      Set.image_univ, hU.range_fromSpec]
  · rw [← Spec.map_preimage ((Spec.map e.hom ≫ hU.fromSpec) ≫ M.s)]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun b => ?_))
    rw [← GlobalTheory.Points.valR_constFn M.s _ U hx, hv]
    exact Subtype.ext ((RatModel.coe_sectionsEquiv U hne _).trans (M.valF_constFn hne b))

theorem exists_openImmersion_tensor (M : RatModel F Ω) {U : M.Z.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set M.Z).Nonempty) {K : Type} [Field K] [Algebra F K] {Z : Scheme.{0}} {p : Z ⟶ M.Z} {q : Z ⟶ Sp K}
    (h : IsPullback p q M.s (spMap (algebraMap F K))) :
    ∃ j : Sp (M.ringOn U ⊗[F] K) ⟶ Z, IsOpenImmersion j ∧ Set.range j = p ⁻¹' U := by
  obtain ⟨ι, hι, hr, hs⟩ := exists_openImmersion_ringOn M hU hne
  have h1 := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct F (M.ringOn U) K)
  rw [show Spec.map (CommRingCat.ofHom (algebraMap F (M.ringOn U))) = ι ≫ M.s from hs.symm] at h1
  let j := h.lift (_ ≫ ι) _ ((Category.assoc _ _ _).trans h1.w)
  have h2 : IsPullback j _ p ι :=
    (IsPullback.of_bot (h₁₁ := _) (by simpa [j] using h1) (h.lift_fst _ _ _).symm h).flip
  refine ⟨j, MorphismProperty.of_isPullback h2.flip hι, ?_⟩
  refine Eq.trans ?_ (congrArg (p ⁻¹' ·) hr)
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, by rw [← Scheme.Hom.comp_apply, ← h2.w, Scheme.Hom.comp_apply]⟩
  · rintro ⟨w, hw⟩
    obtain ⟨v, hv, -⟩ := Scheme.exists_preimage_of_isPullback h2 z w hw.symm
    exact ⟨v, hv⟩

theorem nonempty_algEquiv_adjoin (φ : Ω →ₐ[F] Ω') (A : Subalgebra F Ω) {σ : Type} (t : σ → Ω')
    (ht : ∀ P : MvPolynomial σ Ω, MvPolynomial.eval₂ (φ : Ω →+* Ω') t P = 0 → P = 0) :
    Nonempty (MvPolynomial σ A ≃ₐ[F] Algebra.adjoin F (φ '' (A : Set Ω) ∪ Set.range t)) := by
  let ψ : MvPolynomial σ A →ₐ[F] Ω' := MvPolynomial.aevalTower (φ.comp A.val) t
  have hinj : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro P hP
    refine MvPolynomial.map_injective (A.val : A →+* Ω) Subtype.val_injective ?_
    rw [map_zero]
    refine ht _ ?_
    rw [MvPolynomial.eval₂_map]
    exact hP
  have hr : ψ.range = Algebra.adjoin F (φ '' (A : Set Ω) ∪ Set.range t) := by
    refine le_antisymm ?_ (Algebra.adjoin_le ?_)
    · rintro _ ⟨P, rfl⟩
      show ψ P ∈ _
      induction P using MvPolynomial.induction_on with
      | C a => exact Algebra.subset_adjoin (Or.inl ⟨a, a.2, by simp [ψ]⟩)
      | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
      | mul_X P i hP =>
        rw [map_mul]
        exact mul_mem hP (Algebra.subset_adjoin (Or.inr ⟨i, by simp [ψ]⟩))
    · rintro _ (⟨a, ha, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨MvPolynomial.C ⟨a, ha⟩, by simp [ψ]⟩
      · exact ⟨MvPolynomial.X i, by simp [ψ]⟩
  exact ⟨(AlgEquiv.ofInjective ψ hinj).trans (Subalgebra.equivOfEq _ _ hr)⟩

theorem isDomain_mvPolynomial_tensor (A K σ : Type) [CommRing A] [Algebra F A] [CommRing K] [Algebra F K]
    [IsDomain (A ⊗[F] K)] : IsDomain (MvPolynomial σ A ⊗[F] K) := by
  let e1 : MvPolynomial σ A ⊗[F] K ≃ₐ[F] (A ⊗[F] MvPolynomial σ F) ⊗[F] K :=
    Algebra.TensorProduct.congr ((MvPolynomial.algebraTensorAlgEquiv F A).symm.restrictScalars F) AlgEquiv.refl
  let e2 : (A ⊗[F] MvPolynomial σ F) ⊗[F] K ≃ₐ[F] (A ⊗[F] K) ⊗[F] MvPolynomial σ F :=
    (Algebra.TensorProduct.assoc F F F A (MvPolynomial σ F) K).trans
      ((Algebra.TensorProduct.congr AlgEquiv.refl (Algebra.TensorProduct.comm F _ _)).trans
        (Algebra.TensorProduct.assoc F F F A K (MvPolynomial σ F)).symm)
  let e3 := MvPolynomial.algebraTensorAlgEquiv (σ := σ) F (A ⊗[F] K)
  exact (((e1.trans e2).toRingEquiv).trans e3.toRingEquiv).toMulEquiv.isDomain _

theorem AffCover.geometricallyIntegral : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r : ℕ), AffCover M M' φ f r →
    GeometricallyIntegral M.s → GeometricallyIntegral M'.s := by
  intro F Ω Ω' _ _ _ _ _ M M' φ f r h hM
  refine ⟨geometrically_iff_of_commRing.2 fun K _ _ Z p q hZ => ?_⟩
  have hI : IsIntegral (pullback M.s (spMap (algebraMap F K))) :=
    pullback_of_geometrically hM.geometrically_isIntegral K _
  have key : ∀ z' : M'.Z, ∃ (U : M'.Z.Opens) (Y : Scheme.{0}) (j : Y ⟶ Z), z' ∈ U ∧ IsIntegral Y ∧
      IsOpenImmersion j ∧ Set.range j = p ⁻¹' U := by
    intro z'
    obtain ⟨U, W, t, hU, hW, hz, hUW, ht, hR⟩ := h.2 z'
    have hWne : (W : Set M.Z).Nonempty := ⟨_, hUW z' hz⟩
    obtain ⟨i, hi, -⟩ := exists_openImmersion_tensor M hW hWne (IsPullback.of_hasPullback M.s (spMap (algebraMap F K)))
    have : Nontrivial (M.ringOn W ⊗[F] K) := inferInstance
    have : IsIntegral (Sp (M.ringOn W ⊗[F] K)) := isIntegral_of_isOpenImmersion i
    have : IsDomain (M.ringOn W ⊗[F] K) := (affine_isIntegral_iff (CommRingCat.of _)).1 this
    have := isDomain_mvPolynomial_tensor (F := F) (M.ringOn W) K (Fin r)
    obtain ⟨e⟩ := nonempty_algEquiv_adjoin φ (M.ringOn W) t ht
    rw [← hR] at e
    have : IsDomain (M'.ringOn U ⊗[F] K) :=
      (Algebra.TensorProduct.congr e.symm (AlgEquiv.refl (A₁ := K) (R := F))).toMulEquiv.isDomain _
    obtain ⟨j, hj, hr⟩ := exists_openImmersion_tensor M' hU ⟨_, hz⟩ hZ
    exact ⟨U, _, j, hz, inferInstance, hj, hr⟩
  have hred : IsReduced Z := by
    have : ∀ z : Z, _root_.IsReduced (Z.presheaf.stalk z) := fun z => by
      obtain ⟨U, Y, j, hz, hY, hj, hr⟩ := key (p z)
      obtain ⟨y, rfl⟩ : z ∈ Set.range j := hr ▸ hz
      exact isReduced_of_injective (j.stalkMap y).hom (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv.injective
    exact isReduced_of_isReduced_stalk Z
  have hopen : UniversallyOpen p := MorphismProperty.of_isPullback hZ.flip inferInstance
  have hirr : IrreducibleSpace Z := by
    obtain ⟨U, Y, j, hz, hY, hj, hr⟩ := key (genericPoint M'.Z)
    have h1 : IsIrreducible (Set.range j) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ Y).image _ j.continuous.continuousOn
    have h2 : Dense (Set.range j) := by
      rw [hr]
      exact (U.isOpen.dense ⟨_, hz⟩).preimage p.isOpenMap
    have h3 := h1.closure
    rw [h2.closure_eq] at h3
    exact (irreducibleSpace_def Z).2 h3
  exact isIntegral_of_irreducibleSpace_of_isReduced Z

end GlobalTheory.FlagBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlCornerEmbeddingDiagonalTorusEqSnocOne
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem corner_diagT (R : Type) [CommRing R] (m : ℕ) (t : Fin m → Rˣ) :
    corner (diagT R (Fin m) t) = diagT R (Fin (m + 1)) (Fin.snoc t 1) := by
  apply Units.ext
  change (emb₂ R (stdSum (rfl : m + 1 = m + 1)) (diagT R (Fin m) t, 1) : Matrix (Fin (m + 1)) (Fin (m + 1)) R) = (diagT R (Fin (m + 1)) (Fin.snoc t 1) : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
  rw [val_emb₂, val_diagT, val_diagT]
  ext i j
  obtain ⟨i, rfl⟩ := (stdSum (rfl : m + 1 = m + 1)).surjective i
  obtain ⟨j, rfl⟩ := (stdSum (rfl : m + 1 = m + 1)).surjective j
  have hl : ∀ a : Fin m, stdSum (rfl : m + 1 = m + 1) (Sum.inl a) = Fin.castSucc a := fun a => Fin.ext rfl
  have hr : ∀ a : Fin 1, stdSum (rfl : m + 1 = m + 1) (Sum.inr a) = Fin.last m := fun a => by
    apply Fin.ext; simp [stdSum, Subsingleton.elim a 0]
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · rw [hl, hl, fromBlocks_apply₁₁]
    simp only [diagonal_apply, Fin.snoc_castSucc, Fin.castSucc_inj]
  · rw [hl, hr, fromBlocks_apply₁₂, diagonal_apply_ne _ (Fin.castSucc_lt_last i).ne, Matrix.zero_apply]
  · rw [hl, hr, fromBlocks_apply₂₁, diagonal_apply_ne _ (Fin.castSucc_lt_last j).ne', Matrix.zero_apply]
  · rw [hr, hr, fromBlocks_apply₂₂, diagonal_apply_eq, Fin.snoc_last, Subsingleton.elim i j]
    simp

end GlobalTheory.LocLanglands
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlCornerEmbeddingUpperUnitriangularSuperDiagonal
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CornerUnip

theorem corner_symm_castSucc {m : ℕ} (i : Fin m) :
    (stdSum (rfl : m + 1 = m + 1)).symm (Fin.castSucc i) = Sum.inl i := by
  rw [Equiv.symm_apply_eq]; ext; simp [stdSum_inl]

theorem corner_symm_last (m : ℕ) :
    (stdSum (rfl : m + 1 = m + 1)).symm (Fin.last m) = Sum.inr 0 := by
  rw [Equiv.symm_apply_eq]; ext; simp [stdSum_inr]

variable {R : Type} [CommRing R] {m : ℕ}

theorem corner_cc (u : GL (Fin m) R) (i j : Fin m) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.castSucc i) (Fin.castSucc j) = (u : Matrix _ _ R) i j := by
  have val_emb₂ (g : GL (Fin m) R × GL (Fin 1) R) :
      (emb₂ R (stdSum (rfl : m + 1 = m + 1)) g : Matrix (Fin (m+1)) (Fin (m+1)) R) =
        Matrix.reindex (stdSum (rfl : m + 1 = m + 1)) (stdSum (rfl : m + 1 = m + 1)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [emb₂, leviEmb, leviTwo, two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (stdSum (rfl : m + 1 = m + 1)).symm i with a | a <;>
      rcases (stdSum (rfl : m + 1 = m + 1)).symm j with b | b <;> simp
  rw [corner, val_emb₂]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, corner_symm_castSucc]

theorem corner_cl (u : GL (Fin m) R) (i : Fin m) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.castSucc i) (Fin.last m) = 0 := by
  have val_emb₂ (g : GL (Fin m) R × GL (Fin 1) R) :
      (emb₂ R (stdSum (rfl : m + 1 = m + 1)) g : Matrix (Fin (m+1)) (Fin (m+1)) R) =
        Matrix.reindex (stdSum (rfl : m + 1 = m + 1)) (stdSum (rfl : m + 1 = m + 1)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [emb₂, leviEmb, leviTwo, two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (stdSum (rfl : m + 1 = m + 1)).symm i with a | a <;>
      rcases (stdSum (rfl : m + 1 = m + 1)).symm j with b | b <;> simp
  rw [corner, val_emb₂]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, corner_symm_castSucc, corner_symm_last]

theorem corner_lc (u : GL (Fin m) R) (j : Fin m) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.last m) (Fin.castSucc j) = 0 := by
  have val_emb₂ (g : GL (Fin m) R × GL (Fin 1) R) :
      (emb₂ R (stdSum (rfl : m + 1 = m + 1)) g : Matrix (Fin (m+1)) (Fin (m+1)) R) =
        Matrix.reindex (stdSum (rfl : m + 1 = m + 1)) (stdSum (rfl : m + 1 = m + 1)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [emb₂, leviEmb, leviTwo, two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (stdSum (rfl : m + 1 = m + 1)).symm i with a | a <;>
      rcases (stdSum (rfl : m + 1 = m + 1)).symm j with b | b <;> simp
  rw [corner, val_emb₂]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, corner_symm_castSucc, corner_symm_last]

theorem corner_ll (u : GL (Fin m) R) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.last m) (Fin.last m) = 1 := by
  have val_emb₂ (g : GL (Fin m) R × GL (Fin 1) R) :
      (emb₂ R (stdSum (rfl : m + 1 = m + 1)) g : Matrix (Fin (m+1)) (Fin (m+1)) R) =
        Matrix.reindex (stdSum (rfl : m + 1 = m + 1)) (stdSum (rfl : m + 1 = m + 1)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [emb₂, leviEmb, leviTwo, two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (stdSum (rfl : m + 1 = m + 1)).symm i with a | a <;>
      rcases (stdSum (rfl : m + 1 = m + 1)).symm j with b | b <;> simp
  rw [corner, val_emb₂]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, corner_symm_last]

end GlobalTheory.CornerUnip

open GlobalTheory.CornerUnip in
theorem GlobalTheory.CornerUnip.corner_unipB_superDiag : ∀ (R : Type) [CommRing R] (m : ℕ) (u : GL (Fin m) R), u ∈ unipB R (Fin m) → corner u ∈ unipB R (Fin (m + 1)) ∧ superDiag (corner u) = superDiag u := by
  intro R _ m u hu
  rw [mem_unipB] at hu
  obtain ⟨hl, hd⟩ := hu
  refine ⟨?_, ?_⟩
  · rw [mem_unipB]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => exact corner_lc u j
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.2 (Fin.le_last _))
        | cast j =>
          rw [corner_cc]
          exact hl i j (Fin.castSucc_lt_castSucc_iff.1 hij)
    · induction i using Fin.lastCases with
      | last => exact corner_ll u
      | cast i => rw [corner_cc]; exact hd i
  · unfold superDiag
    simp only [Finset.sum_filter]
    simp [Fin.sum_univ_castSucc, corner_cc, corner_cl, corner_lc, corner_ll]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeightLocallyBounded
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiftHeight

theorem height_locally_bounded : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ g₀ : GA D V,
    ∃ C : ℝ, ∀ᶠ g in 𝓝 g₀, (height θ V g : ℝ) ≤ C := by
  intro D θ hθ V g₀
  obtain ⟨C, hC, h⟩ := GlobalTheory.Grow.height_comparison V hθ
  have hc := (GlobalTheory.Grow.continuous_height V).continuousAt (x := g₀)
  refine ⟨C * (GlobalTheory.Grow.height V g₀ + 1), ?_⟩
  filter_upwards [hc.eventually_lt continuousAt_const (lt_add_one _)] with g hg
  exact (h g).1.trans (mul_le_mul_of_nonneg_left hg.le hC.le)

end GlobalTheory.Mem.LiftHeight

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesHasRootOfUnity
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Pj

namespace GlobalTheory.Mem

theorem exp_div_mul_eq_zpow_mul_zpow {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h : Nat.Coprime p q) :
    ∃ a b : ℤ, Complex.exp (2 * Real.pi * Complex.I / ((p * q : ℕ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I / ((p * (p - 1) : ℕ) : ℂ)) ^ a *
        Complex.exp (2 * Real.pi * Complex.I / ((q * (q - 1) : ℕ) : ℂ)) ^ b := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 h
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  refine ⟨v * p', u * q', ?_⟩
  rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  have h1 : (p' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h2 : (q' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h3 : (p' : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  have h4 : (q' : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  have h5 : (u : ℂ) * (p' + 1) + v * (q' + 1) = 1 := by exact_mod_cast huv
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  linear_combination (-1 : ℂ) * h5

theorem Base.exists_root_mul (B : Base) : ∃ y : B.O, B.embLL (B.OtoLL y) =
    Complex.exp (2 * Real.pi * Complex.I / ((B.host.g 0 * B.host.g 1 : ℕ) : ℂ)) := by
  have p0 := B.host.g_prime 0
  have p1 := B.host.g_prime 1
  obtain ⟨z₀, hz₀, e₀⟩ := B.roots_Ks (B.host.g 0 * (B.host.g 0 - 1)) (by simp)
  obtain ⟨z₁, hz₁, e₁⟩ := B.roots_Ks (B.host.g 1 * (B.host.g 1 - 1)) (by simp)
  obtain ⟨a, b, hab⟩ := exp_div_mul_eq_zpow_mul_zpow p0.two_le p1.two_le
    ((Nat.coprime_primes p0 p1).2 B.host.g_ne)
  have hmem : z₀ ^ a * z₁ ^ b ∈ B.Ks := mul_mem (zpow_mem hz₀ a) (zpow_mem hz₁ b)
  have he : B.embLL (z₀ ^ a * z₁ ^ b) =
      Complex.exp (2 * Real.pi * Complex.I / ((B.host.g 0 * B.host.g 1 : ℕ) : ℂ)) := by
    rw [map_mul, map_zpow₀, map_zpow₀, e₀, e₁, hab]
  have hne : B.host.g 0 * B.host.g 1 ≠ 0 := mul_ne_zero p0.ne_zero p1.ne_zero
  have hint : IsIntegral ℤ (B.embLL (z₀ ^ a * z₁ ^ b)) := by
    rw [he]
    exact (Complex.isPrimitiveRoot_exp _ hne).isIntegral (Nat.pos_of_ne_zero hne)
  have hint' : IsIntegral ℤ (z₀ ^ a * z₁ ^ b) :=
    (isIntegral_algHom_iff B.embLL.toIntAlgHom B.embLL.injective).1 hint
  refine ⟨⟨⟨z₀ ^ a * z₁ ^ b, hmem⟩, ?_⟩, he⟩
  exact (isIntegral_algHom_iff (B.Ks.val : B.Ks →+* B.LL).toIntAlgHom Subtype.val_injective).1 hint'

theorem hermitianCodeWordStages_has_rootOfUnity : ∀ X : Stages, OZeta X.toD7 := fun X => X.B.exists_root_mul

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjInvolutive
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem longElt_invT_involution : ∀ (R : Type) [CommRing R] (n : ℕ) (g : GL (Fin n) R), longElt n R * GlobalTheory.CuspRep.invT n R (longElt n R * GlobalTheory.CuspRep.invT n R g * longElt n R) * longElt n R = g := by
  intro R _ n g
  have hw : longElt n R * longElt n R = 1 := Units.ext (antidiag_mul_self n R)
  have hii : ∀ h : GL (Fin n) R, GlobalTheory.CuspRep.invT n R (GlobalTheory.CuspRep.invT n R h) = h := fun h => by
    apply Units.ext
    show (h.valᵀ)ᵀ = h.val
    exact Matrix.transpose_transpose _
  have hwT : GlobalTheory.CuspRep.invT n R (longElt n R) = longElt n R := by
    apply Units.ext
    show (Matrix.of fun i j : Fin n => if j = i.rev then (1 : R) else 0)ᵀ = Matrix.of fun i j : Fin n => if j = i.rev then (1 : R) else 0
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    congr 1
    exact propext ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  rw [map_mul, map_mul, hii, hwT, ← mul_assoc, ← mul_assoc, hw, one_mul, mul_assoc, hw, mul_one]

end GlobalTheory
end

