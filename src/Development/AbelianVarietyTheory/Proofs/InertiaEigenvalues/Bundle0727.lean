module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModule
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0718
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0722
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import GroundTheory.AutomorphicForms.Bundle0027
public import GroundTheory.AutomorphicForms.MeasuresModulus
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionHeisenbergInvariant
public import GroundTheory.GlobalFields.TateThesis.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0715
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModuleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthZeroSupercuspidal_cuspidalModule : ∀ (g : ℕ) [Fact g.Prime], TameGen.DepthZeroCuspidal g := by
  first | exact @GlobalTheory.DepthZeroCusp.depthZeroCuspidal | exact GlobalTheory.DepthZeroCusp.depthZeroCuspidal | (intros; apply GlobalTheory.DepthZeroCusp.depthZeroCuspidal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmptyPiTensorIsSubquotientJacquetModuleDegreeZer
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory

theorem piTensor_isSubquotient_jac_degZero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ), N = 0 → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (π : Representation ℂ (GL (Fin N) k) V) (d : Fin 0 → ℕ) (X : Fin 0 → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (e : (Σ a, Fin (d a)) ≃ Fin N),
    IsSubquotient (piTensor ρ) (jac e π) := by
  intro k _ _ _ _ N hN V _ _ _ π d X _ _ ρ e
  subst hN
  have hK : twKer π (unipRad k e) 1 = ⊥ := by
    refine le_bot_iff.1 (Submodule.span_le.2 ?_)
    rintro w ⟨n, v, rfl⟩
    have h1 : (n : GL (Fin 0) k) = 1 := Subsingleton.elim _ _
    simp [h1]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hx : (Submodule.Quotient.mk v : Jacquet π (unipRad k e)) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero, hK, Submodule.mem_bot]; exact hv
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (Jacquet π (unipRad k e)),
      φ (Submodule.Quotient.mk v) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
  let L : Jacquet π (unipRad k e) →ₗ[ℂ] PiTensorProduct ℂ X :=
    (PiTensorProduct.isEmptyEquiv (Fin 0)).symm.toLinearMap ∘ₗ φ
  refine IsSubquotient.of_surjective ⟨L, fun g => ?_⟩ ?_
  · have hg : g = 1 := Subsingleton.elim _ _
    subst hg
    rw [map_one, map_one]
    rfl
  · have hsurj : Function.Surjective φ := fun c =>
      ⟨(c / φ (Submodule.Quotient.mk v)) • Submodule.Quotient.mk v, by simp [hφ]⟩
    exact (PiTensorProduct.isEmptyEquiv (Fin 0)).symm.surjective.comp hsurj

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdelicExtensionOfAlgebraicWeightDefiniteUnStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_extension_of_algebraicWeight_definiteUnitary : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n), ∃ R : UA L n →* Module.End ℂ a.W, (∀ k ∈ finU (E := L) (n := n), R k = 1) ∧ (∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ → (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → R γ = a.ρ γQ) ∧ ∀ (v : a.W) (μ : Module.Dual ℂ a.W), Continuous fun g : UA L n => μ (R g v) := by
  first | exact @GlobalTheory.WeightRealExt.exists_extension | exact GlobalTheory.WeightRealExt.exists_extension | (intros; apply GlobalTheory.WeightRealExt.exists_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBijectiveOfIsSubquotient
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open GlobalTheory.PRep GlobalTheory.SmGL

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.JacFactor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isIrreducible_comp_surj {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (f : G →* H) (hf : Function.Surjective f) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp f : Representation ℂ G V) := by
  let e : Subrepresentation (ρ.comp f : Representation ℂ G V) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        obtain ⟨x, rfl⟩ := hf g
        exact S.apply_mem_toSubmodule x hv⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  exact e.isSimpleOrder

def piTensorBoolEquiv {R a b : Type} [CommRing R] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {X : Bool → Type} [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)]
    (F : ∀ j, Representation ℂ (GL (Two a b j) R) (X j)) :
    Representation.Equiv ((piTensor F).comp (leviTwo R a b).toMonoidHom :
      Representation ℂ (GL a R × GL b R) (⨂[ℂ] j, X j)) (extTensor (F false) (F true)) :=
  .mk (Exponents.boolTensorEquiv (X := X)) fun g => by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    show Exponents.boolTensorEquiv (X := X) (piTensor F (leviTwo R a b g) (PiTensorProduct.tprod ℂ x)) =
      extTensor (F false) (F true) g (Exponents.boolTensorEquiv (X := X) (PiTensorProduct.tprod ℂ x))
    rw [piTensor_tprod, Exponents.boolTensorEquiv_tprod, Exponents.boolTensorEquiv_tprod, extTensor_tmul]
    rfl

theorem isIrreducible_extTensor {R a b W W' : Type} [CommRing R] [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ (GL a R) W) (ρ : Representation ℂ (GL b R) W')
    (hσ : σ.IsIrreducible) (hρ : ρ.IsIrreducible)
    (hSσ : ∀ φ : W →ₗ[ℂ] W, (∀ g x, φ (σ g x) = σ g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id)
    (hSρ : ∀ φ : W' →ₗ[ℂ] W', (∀ g x, φ (ρ g x) = ρ g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id) :
    (extTensor σ ρ).IsIrreducible := by
  have h1 : (piTensor (Exponents.twoRep σ ρ)).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun j => by cases j <;> assumption)
      (fun j => by cases j <;> assumption)
  have h2 := isIrreducible_comp_surj _ (leviTwo R a b).toMonoidHom (leviTwo R a b).surjective h1
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv (piTensorBoolEquiv (Exponents.twoRep σ ρ)) h2

theorem nontrivial_of_isIrreducible {G Y : Type} [Group G] [AddCommGroup Y] [Module ℂ Y]
    {τ : Representation ℂ G Y} (hτ : τ.IsIrreducible) : Nontrivial Y := by
  haveI : IsSimpleOrder (Subrepresentation τ) := hτ
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply (bot_ne_top : (⊥ : Subrepresentation τ) ≠ ⊤)
  ext v
  exact ⟨fun _ => trivial, fun _ => Subsingleton.elim v 0⟩

end GlobalTheory.JacFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClassMapCorrespondence
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeRec

theorem pull_iso_of_cls_eq {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (σ τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)))
    (h : GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls τ) : Nonempty (pull I k v σ ≅ pull I k v τ) := by
  have h1 : σ.cl = τ.cl := by
    have := (Sigma.mk.inj_iff.1 h).2
    exact eq_of_heq this
  obtain ⟨φ⟩ := GlobalTheory.SmGL.IrrRep.cl_eq_iff.1 h1
  exact ⟨Rep.mkIso (Representation.Equiv.mk φ.toLinearEquiv fun g =>
    φ.toIntertwiningMap.isIntertwining' (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g))⟩

end GlobalTheory.TypeRec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEigenFamily
section
namespace GlobalTheory.EigenFamilyStabilizer

def stab {G V ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (θ : G → ℂ)
    (h1 : θ 1 = 1) (hm : ∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b) (y : ι → V) : Subgroup K where
  carrier := {k | θ k = 1 ∧ ∀ i, ρ k (y i) = y i}
  one_mem' := ⟨by simpa using h1, fun i => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, fun i => ?_⟩
    · rw [Subgroup.coe_mul, hm _ a.2 _ b.2, ha, hb, one_mul]
    · rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb', ha']
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨?_, fun i => ?_⟩
    · have := hm _ (a⁻¹).2 _ a.2
      rw [ha, mul_one, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, h1] at this
      exact this.symm
    · conv_lhs => rw [← ha' i]
      rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul, inv_mul_cancel]
      simp

theorem exists_eigen_family : ∀ {G V W ι : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : AddCommGroup V] [inst_4 : Module ℂ V] [inst_5 : AddCommGroup W] [inst_6 : Module ℂ W] [inst_7 : Fintype ι] {ρ : Representation ℂ G V}, GlobalTheory.PRep.IsSmooth ρ → ∀ {K : Subgroup G}, IsCompact (↑K : Set G) → ∀ {U : Set G}, IsOpen U → (1 : G) ∈ U → ∀ (θ : G → ℂ), (∀ g ∈ U, g ∈ K → θ g = (1 : ℂ)) → (∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b) → ∀ (T : ι → V →ₗ[ℂ] W) (y : ι → V), (∀ k ∈ K, ∑ i : ι, (T i : V → W) (((ρ : G → V →ₗ[ℂ] V) k : V → V) (y i)) = θ k • ∑ i : ι, (T i : V → W) (y i)) → ∃ (u : ι → V), (∀ (j : ι), ∀ h ∈ K, ((ρ : G → V →ₗ[ℂ] V) h : V → V) (u j) = θ h • u j) ∧ ∑ i : ι, (T i : V → W) (u i) = ∑ i : ι, (T i : V → W) (y i) := by
  intro G V W ι _ _ _ _ _ _ _ _ ρ hρ K hK U hU hU1 θ hθ hm T y hy
  classical
  have h1 : θ 1 = 1 := hθ 1 hU1 K.one_mem
  let H : Subgroup K := stab ρ K θ h1 hm y
  have hHo : IsOpen (H : Set K) := by
    apply Subgroup.isOpen_of_mem_nhds H (g := 1)
    have ho : IsOpen (U ∩ ⋂ i, {g : G | ρ g (y i) = y i}) :=
      hU.inter (isOpen_iInter_of_finite fun i => hρ (y i))
    have ho' : IsOpen ((Subtype.val : K → G) ⁻¹' (U ∩ ⋂ i, {g : G | ρ g (y i) = y i})) :=
      ho.preimage continuous_subtype_val
    refine Filter.mem_of_superset (ho'.mem_nhds ?_) ?_
    · refine ⟨hU1, Set.mem_iInter.2 fun i => ?_⟩
      simp
    · rintro k ⟨hk, hk'⟩
      exact ⟨hθ _ hk k.2, fun i => Set.mem_iInter.1 hk' i⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  letI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let f : ι → K → V := fun j k => θ (k⁻¹ : K) • ρ k (y j)
  have hf : ∀ j (k : K) (s : K), s ∈ H → f j (k * s) = f j k := by
    intro j k s hs
    have hs' : θ (s⁻¹ : K) = 1 := (H.inv_mem hs).1
    simp only [f]
    rw [mul_inv_rev, Subgroup.coe_mul, hm _ (s⁻¹).2 _ (k⁻¹).2, hs', one_mul, Subgroup.coe_mul, map_mul,
      Module.End.mul_apply, hs.2 j]
  let F : ι → K ⧸ H → V := fun j q => f j q.out
  have hF : ∀ j (k : K), F j (k : K ⧸ H) = f j k := by
    intro j k
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul H k
    simp only [F]
    rw [hs, hf j k s s.2]
  have hact : ∀ j (h : K) (q : K ⧸ H), ρ h (F j q) = θ h • F j (h • q) := by
    intro j h q
    induction q using QuotientGroup.induction_on with
    | H k =>
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, hF, hF]
      simp only [f]
      rw [map_smul, smul_smul, mul_comm (θ h), ← hm _ ((h * k)⁻¹).2 _ h.2, ← Subgroup.coe_mul,
        Subgroup.coe_mul K h k, map_mul, Module.End.mul_apply]
      congr 3
      group
  have hN : (Fintype.card (K ⧸ H) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨fun j => (Fintype.card (K ⧸ H) : ℂ)⁻¹ • ∑ q, F j q, fun j h hh => ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_smul, map_sum, smul_comm]
      apply congrArg ((Fintype.card (K ⧸ H) : ℂ)⁻¹ • ·)
      rw [Finset.sum_congr rfl fun q _ => hact j ⟨h, hh⟩ q, ← Finset.smul_sum]
      exact congrArg (θ h • ·) (Equiv.sum_comp (MulAction.toPerm (⟨h, hh⟩ : K)) (F j))
  · have hq : ∀ q, ∑ i, T i (F i q) = ∑ i, T i (y i) := by
      intro q
      simp only [F, f, map_smul]
      rw [← Finset.smul_sum, hy _ q.out.2, smul_smul, ← hm _ (q.out⁻¹).2 _ q.out.2, ← Subgroup.coe_mul,
        inv_mul_cancel, Subgroup.coe_one, h1, one_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, Finset.sum_apply]
    rw [← Finset.smul_sum, Finset.sum_comm, Finset.sum_congr rfl fun q _ => hq q, Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN, one_smul]

end GlobalTheory.EigenFamilyStabilizer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChange
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.GalIsoBC

theorem lpTw_lpZero (D : D7) (w : PlE D.host) (s : ℝ) : D.naut.lpTw (D.naut.lpZero w) s = D.naut.lpZero w := by
  have hu : D.naut.unr (D.naut.lpTw (D.naut.lpZero w) s) := (D.naut.unr_tw _ s).2 (D.naut.lpZero_unr w)
  have e3 : D.naut.frobEig (D.naut.lpTw (D.naut.lpZero w) s) = D.naut.frobEig (D.naut.lpZero w) := by
    rw [D.naut.frobEig_tw _ s (D.naut.lpZero_unr w), D.naut.frobEig_zero]; simp
  rw [D.naut.unr_eq_lpUnr _ hu, e3, ← D.naut.unr_eq_lpUnr _ (D.naut.lpZero_unr w)]

theorem lpTw_foldr (D : D7) (w : PlE D.host) {β : Type*} (f : β → D.naut.LP w) (s : ℝ) :
    ∀ L : List β, D.naut.lpTw (L.foldr (fun x acc => D.naut.lpSum (f x) acc) (D.naut.lpZero w)) s =
      L.foldr (fun x acc => D.naut.lpSum (D.naut.lpTw (f x) s) acc) (D.naut.lpZero w)
  | [] => lpTw_lpZero D w s
  | x :: L => by
      simp only [List.foldr_cons]
      rw [D.naut.lpTw_sum, lpTw_foldr D w f s L]

theorem map_list_sum {α γ : Type*} (h : α → γ) :
    ∀ L : List (Multiset α), L.sum.map h = (L.map fun x => x.map h).sum
  | [] => by simp
  | x :: L => by simp [Multiset.map_add (f := _), map_list_sum h L]

theorem le_list_sum {α : Type*} {x : Multiset α} : ∀ {L : List (Multiset α)}, x ∈ L → x ≤ L.sum
  | [], hx => by simp at hx
  | y :: L, hx => by
      rw [List.sum_cons]
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Multiset.le_add_right _ _
      · exact le_trans (le_list_sum hx) (Multiset.le_add_left _ _)

end GlobalTheory.GalIsoBC

namespace GlobalTheory.GalIsoBC

theorem flatMap_single {γ : Type*} (f : ℕ → γ) : ∀ l : List ℕ, List.flatMap (fun a => [f a]) l = l.map f
  | [] => rfl
  | a :: l => by simp [List.flatMap_cons, flatMap_single f l]

theorem spehLoc_eq (D : D7) (p : Formalism.BasicNotions.Part D.naut.CG) (w : PlE D.host) :
    spehLoc D.nd D.naut p w = (List.range p.d).foldr (fun (k : ℕ) acc =>
      D.naut.lpSum (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - (k : ℝ))) acc) (D.naut.lpZero w) := by
  unfold spehLoc
  simp only [bind, pure]
  rw [flatMap_single (fun a : ℕ => (a : ℝ)), List.foldr_map]

theorem isoInf_eq (D : D7) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut Pa τ = (Pa.map fun p => ((List.range p.d).map fun k : ℕ =>
        (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (k : ℂ)))).sum).sum := by
  unfold isoInf
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [bind, pure]
  rw [flatMap_single (fun a : ℕ => (a : ℂ)), List.map_map]
  rfl

end GlobalTheory.GalIsoBC

namespace GlobalTheory.GalIsoBC

end GlobalTheory.GalIsoBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicEquiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.SplitTypeCompl

theorem exists_padic_equiv : ∀ (D : D7) (s : SplitPlace D.host.E), s.v ∈ gPl D →
    ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* s.w.adicCompletion D.host.E), Continuous i := by
  intro D s hs
  obtain ⟨w, hw, k, hk⟩ := hs
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hwk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by simpa [placesOver] using hk
  have hv : ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
    rw [← hw, Ideal.mem_comap, map_natCast]; exact hwk
  have hsw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ s.w.asIdeal := by
    have := hv
    rw [← s.w_under, Ideal.mem_comap, map_natCast] at this
    exact this
  obtain ⟨h1, h2, -⟩ := GlobalTheory.Mem.Chr.splitsC_place (D.host.g_prime k) (D.nd.g_split k) _ hsw
  haveI : CharZero (s.w.adicCompletion D.host.E) :=
    charZero_of_injective_ringHom (algebraMap D.host.E _).injective
  obtain ⟨φ, h, -⟩ := GlobalTheory.QpChar.exists_ringEquiv_padic (s.w.adicCompletion D.host.E) (D.host.g k)
    ((GlobalTheory.LocLanglands.resCard_eq_normV _).trans (by
      simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h1))
    (GlobalTheory.TypeIdent.irreducible_natCast_compl _ hsw h2)
  exact ⟨D.host.g k, inferInstance, φ, h⟩

end GlobalTheory.SplitTypeCompl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
section
noncomputable section

open NumberField IsDedekindDomain Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep Formalism.UG

namespace GlobalTheory.StdCharConductor

variable (E : Type) [Field E] [NumberField E]

def psi : AddChar (Ad E) ℂ := Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)

theorem psi_apply (x : Ad E) : psi E x = (GroundTheory.Global.adelicChar E x : ℂ) := rfl

variable {E}

theorem psi_loc (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    psi E (sFin E (sLoc E w y)) = (GroundTheory.Global.localAdelicChar E w y : ℂ) := by
  classical
  rw [psi_apply, GroundTheory.Global.localAdelicChar_apply]
  congr 2

theorem psi_loc_eq_one_iff (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    psi E (sFin E (sLoc E w y)) = 1 ↔ GroundTheory.Global.localAdelicChar E w y = 1 := by
  rw [psi_loc]
  exact Circle.coe_eq_one

theorem exists_psi_loc_ne_one (w : HeightOneSpectrum (𝓞 E)) :
    ∃ y : w.adicCompletion E, psi E (sFin E (sLoc E w y)) ≠ 1 := by
  by_contra h
  push Not at h
  refine GroundTheory.Global.localAdelicChar_ne_one (K := E) w (DFunLike.ext _ _ fun y => ?_)
  rw [AddChar.one_apply]
  exact (psi_loc_eq_one_iff w y).1 (h y)


variable (E) in
theorem stdPsi_psi : StdPsi (psi E) := by
  have hc : Continuous (psi E) := continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar (K := E))
  have hr : ∀ c : E, psi E (algebraMap E (Ad E) c) = 1 := fun c => by
    rw [psi_apply, GroundTheory.Global.adelicChar_algebraMap]
    rfl
  have hne : psi E ≠ 1 := fun h => GroundTheory.Global.adelicChar_ne_one (K := E) (DFunLike.ext _ _ fun x => by
    have := DFunLike.congr_fun h x
    rw [psi_apply, AddChar.one_apply] at this
    rw [AddChar.one_apply]
    exact Circle.coe_eq_one.1 this)
  letI : Invertible (2 : E) := invertibleOfNonzero two_ne_zero
  letI : Invertible (2 : Ad E) := (Invertible.map (algebraMap E (Ad E)) 2).copy 2 (map_ofNat _ 2).symm
  have h := GlobalTheory.CompanionTheory.AdeleAnn.unitary_and_annihilator_eq E (psi E) hc hne hr
  exact ⟨hc, h.1, hr, h.2, exists_psi_loc_ne_one⟩

end GlobalTheory.StdCharConductor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharLocalEqOneOfTrivialOnNormsSplitStatement
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open _root_.GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_local_eq_one_of_trivial_on_norms_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ε : Formalism.L2.Host.HChar (maximalRealSubfield E)),
    compNorm E ε = 1 → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v →
    ∀ x, ε.loc v x = 1 := by
  first | exact @GlobalTheory.NormKill.loc_eq_one_of_compNorm_eq_one | exact GlobalTheory.NormKill.loc_eq_one_of_compNorm_eq_one | (intros; apply GlobalTheory.NormKill.loc_eq_one_of_compNorm_eq_one <;> assumption)
end
end

