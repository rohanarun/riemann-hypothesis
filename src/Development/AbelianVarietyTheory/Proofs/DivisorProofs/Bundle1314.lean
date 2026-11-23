module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0909
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1279
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1265
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPointResidueNonzero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.PullbackFinitePoint


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.PullbackFinitePoint.residueDegree_ne_zero_iff_finite {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) :
    f.residueDegree x ≠ 0 ↔ (f.residueFieldMap x).hom.Finite := by
  letI := (f.residueFieldMap x).hom.toAlgebra
  unfold Scheme.Hom.residueDegree RingHom.Finite
  constructor
  · intro h
    exact Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)
  · intro h
    exact Module.finrank_pos.ne'

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
private theorem residueFieldMap_surjective_of_surjectiveOnStalks {X Y : Scheme.{0}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : Function.Surjective (f.residueFieldMap x) := by
  intro z
  obtain ⟨s, rfl⟩ := X.residue_surjective x z
  obtain ⟨t, rfl⟩ := f.stalkMap_surjective x s
  refine ⟨Y.residue (f x) t, ?_⟩
  rw [← ConcreteCategory.comp_apply, Scheme.residue_residueFieldMap, ConcreteCategory.comp_apply]


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.PullbackFinitePoint.residueDegree_ne_zero_of_surjectiveOnStalks {X Y : Scheme.{0}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : f.residueDegree x ≠ 0 :=
  (_root_.GlobalTheory.PullbackFinitePoint.residueDegree_ne_zero_iff_finite f x).2
    (RingHom.Finite.of_surjective _ (residueFieldMap_surjective_of_surjectiveOnStalks f x))

end GlobalTheory.PullbackFinitePoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticModelRationalCoordinates
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.RatCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def hat {κ : Type} (w : (κ → F) × (κ → F)) : (κ → AF F) × (κ → AF F) :=
  (fun i => algebraMap F (AF F) (w.1 i), fun i => algebraMap F (AF F) (w.2 i))

theorem hat_injective {κ : Type} : Function.Injective (hat (F := F) (κ := κ)) := by
  intro w w' h
  have hinj := AdeleRing.algebraMap_injective (𝓞 F) F
  simp only [hat, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  ext i
  · exact hinj (congrFun h1 i)
  · exact hinj (congrFun h2 i)

theorem hat_add {κ : Type} (w w' : (κ → F) × (κ → F)) : hat (w + w') = hat w + hat w' := by
  simp only [hat, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add (f := _)]; rfl

theorem hat_smul {κ : Type} (c : F) (w : (κ → F) × (κ → F)) :
    hat (c • w) = algebraMap F (AF F) c • hat w := by
  simp only [hat, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul]; rfl

theorem incM_add {m k : Type} (x x' : Matrix m k E) : incM F (x + x') = incM F x + incM F x' := by
  ext i j; simp [incM]

theorem incM_smul' {m k : Type} (c : F) (x : Matrix m k E) :
    incM F (c • x) = algebraMap F (AF F) c • incM F x := by
  ext i j
  simp only [incM, Matrix.map_apply, Matrix.smul_apply]
  show (1 : AF F) ⊗ₜ[F] (c • x i j) = algebraMap F (AF F) c • ((1 : AF F) ⊗ₜ[F] x i j)
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem incM_injective {m k : Type} : Function.Injective (incM F (E := E) (m := m) (n := k)) := by
  intro x x' h
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)
  ext i j
  exact hinj (congrFun (congrFun h i) j)

end GlobalTheory.RatCoord

open GlobalTheory.RatCoord in
theorem GlobalTheory.RatCoord.ratEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ → Module.finrank F E = 2 → ∃ Φ : Matrix (Fin n) (Fin d) E ≃ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F), ∀ x, M.co.e (incM F x) = ((fun i => algebraMap F (AF F) ((Φ x).1 i)), (fun i => algebraMap F (AF F) ((Φ x).2 i))) := by
  intro F E _ _ _ _ _ σ n d X W M ψ hM hE
  classical
  let Φ₀ : Matrix (Fin n) (Fin d) E → (Fin n × Fin d → F) × (Fin n × Fin d → F) :=
    fun x => ((hM.rat x).choose, (hM.rat x).choose_spec.choose)
  have hΦ₀ : ∀ x, M.co.e (incM F x) = hat (Φ₀ x) := fun x => (hM.rat x).choose_spec.choose_spec
  let L : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F) :=
    { toFun := Φ₀
      map_add' := fun x x' => by
        apply hat_injective
        rw [hat_add, ← hΦ₀, ← hΦ₀, ← hΦ₀, incM_add, map_add (f := _)]
      map_smul' := fun c x => by
        apply hat_injective
        rw [RingHom.id_apply, hat_smul, ← hΦ₀, ← hΦ₀, incM_smul', LinearEquiv.map_smul] }
  have hinj : Function.Injective L := by
    intro x x' h
    apply incM_injective (F := F)
    apply M.co.e.injective
    rw [hΦ₀, hΦ₀]
    exact congrArg hat h
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hrank : Module.finrank F (Matrix (Fin n) (Fin d) E) =
      Module.finrank F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) := by
    rw [Module.finrank_matrix, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hE,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    ring
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj
  refine ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun x => ?_⟩
  exact hΦ₀ x
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOrbitConjCompactModCentralizerUnitary
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise

noncomputable section
namespace GlobalTheory.OrbitU

theorem locCpt (E : Type) [Field E] [NumberField E] (w : Pl E) : LocallyCompactSpace (w.adicCompletion E) := by
  have h : (w.adicCompletionIntegers E : Set (w.adicCompletion E)) =
      ((Valued.v : Valuation (w.adicCompletion E) _).integer : Set (w.adicCompletion E)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]
  have ho : IsOpen (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
    rw [h]; exact Valued.isOpen_integer _
  exact (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w).locallyCompactSpace_of_mem_nhds_of_addGroup
    (ho.mem_nhds (zero_mem _))

theorem glTop (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) : LocallyCompactSpace (GLw n w) ∧ SigmaCompactSpace (GLw n w) := by
  haveI := locCpt E w
  haveI hM : LocallyCompactSpace (Matrix (Fin n) (Fin n) (w.adicCompletion E)) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → w.adicCompletion E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  haveI : ProperSpace (w.adicCompletion E) := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (w.adicCompletion E)) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → w.adicCompletion E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (GLw n w) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (GLw n w) := Units.isClosedEmbedding_embedProduct.isEmbedding.secondCountableTopology
  exact ⟨inferInstance, sigmaCompactSpace_of_locallyCompact_secondCountable⟩

def starU {K : Type} [Field K] {n : ℕ} (σ : K →+* K) (g : GL (Fin n) K) : GL (Fin n) K where
  val := cT σ (g : Matrix (Fin n) (Fin n) K)
  inv := cT σ ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  val_inv := by rw [← cT_mul, Units.inv_mul, cT_one]
  inv_val := by rw [← cT_mul, Units.mul_inv, cT_one]

theorem orbit_cpt_U : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∀ C : Set (UL n w), IsCompact C → ∃ Ω : Set (UL n w), IsCompact Ω ∧ ∀ g : UL n w, g⁻¹ * y * g ∈ C → ∃ t ∈ twCent (MonoidHom.id (UL n w)) y, ∃ ω ∈ Ω, g = t * ω := by
  intro E _ _ _ hE n w y hy C hC
  have hCG : IsCompact (Subtype.val '' C : Set (GLw n w)) := hC.image continuous_subtype_val
  obtain ⟨D, hD, hDg⟩ := GlobalTheory.OrbitCptW.orbit_cpt_w E hE n w y.1 hy _ hCG
  have hcl := (GlobalTheory.LocFinU.isClosed_UL n w).isClosedEmbedding_subtypeVal
  have hgC : ∀ g : UL n w, g⁻¹ * y * g ∈ C → g.1⁻¹ * y.1 * g.1 ∈ (Subtype.val '' C : Set (GLw n w)) :=
    fun g hg => ⟨_, hg, rfl⟩
  by_cases hs : IsSplitAt w
  · have hUL : ∀ g : GLw n w, g ∈ UL n w := fun g => by unfold UL; rw [if_pos hs]; trivial
    refine ⟨Subtype.val ⁻¹' D, hcl.isCompact_preimage hD, fun g hg => ?_⟩
    obtain ⟨z, hz, d, hd, hgd⟩ := hDg g.1 (hgC g hg)
    exact ⟨⟨z, hUL z⟩, Subtype.ext hz, ⟨d, hUL d⟩, hd, Subtype.ext hgd⟩
  obtain ⟨hσc, hσi, -⟩ := GlobalTheory.ConjAtPlace.main E hE w
  set σ := cj w with hσ
  have hmemU : ∀ g : GLw n w, g ∈ UL n w ↔ cT σ g.val * g.val = 1 := by
    intro g; unfold UL; rw [if_neg hs]; show cT σ _ * 1 * _ = 1 ↔ _; rw [Matrix.mul_one]
  have hcTc : Continuous fun M : Matrix (Fin n) (Fin n) (w.adicCompletion E) => cT σ M :=
    (continuous_id.matrix_map hσc).matrix_transpose
  have hcc : ∀ M : Matrix (Fin n) (Fin n) (w.adicCompletion E), cT σ (cT σ M) = M := by
    intro M; ext i j; simp [cT, hσi]
  have hstarc : Continuous (starU σ : GLw n w → GLw n w) := by
    rw [Units.continuous_iff]
    exact ⟨hcTc.comp Units.continuous_val, hcTc.comp Units.continuous_coe_inv⟩
  obtain ⟨lc, sc⟩ := glTop E w n
  let Z : Subgroup (GLw n w) := Subgroup.centralizer {y.1}
  have hZ : ∀ z : GLw n w, z ∈ Z ↔ z.val * y.1.val = y.1.val * z.val := by
    intro z
    rw [Subgroup.mem_centralizer_singleton_iff]
    change z * y.1 = y.1 * z ↔ _
    exact Units.ext_iff
  have hZc : IsClosed (Z : Set (GLw n w)) := by
    have : (Z : Set (GLw n w)) = {z | z * y.1 = y.1 * z} := by
      ext z; exact Subgroup.mem_centralizer_singleton_iff
    rw [this]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  haveI : LocallyCompactSpace Z := hZc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SigmaCompactSpace Z := hZc.isClosedEmbedding_subtypeVal.sigmaCompactSpace
  have hcomm : ∀ a b : Z, a * b = b * a := fun a b => Subtype.ext (Units.ext
    (GlobalTheory.commute_of_commute_separable_charpoly _ n y.1.val a.1.val b.1.val hy ((hZ _).1 a.2) ((hZ _).1 b.2)))
  have hyU : cT σ y.1.val * y.1.val = 1 := (hmemU _).1 y.2
  have hyU' : y.1.val * cT σ y.1.val = 1 := mul_eq_one_comm.1 hyU
  have hst : ∀ z ∈ Z, starU σ z ∈ Z := by
    intro z hz
    rw [hZ] at hz ⊢
    have h1 : cT σ y.1.val * cT σ z.val = cT σ z.val * cT σ y.1.val := by rw [← cT_mul, ← cT_mul, hz]
    show cT σ z.val * y.1.val = y.1.val * cT σ z.val
    calc cT σ z.val * y.1.val = (y.1.val * cT σ y.1.val) * cT σ z.val * y.1.val := by rw [hyU', Matrix.one_mul]
      _ = y.1.val * (cT σ y.1.val * cT σ z.val) * y.1.val := by simp only [Matrix.mul_assoc]
      _ = y.1.val * (cT σ z.val * cT σ y.1.val) * y.1.val := by rw [h1]
      _ = y.1.val * cT σ z.val * (cT σ y.1.val * y.1.val) := by simp only [Matrix.mul_assoc]
      _ = y.1.val * cT σ z.val := by rw [hyU, Matrix.mul_one]
  let τ : Z →* Z :=
    { toFun := fun z => ⟨starU σ z.1, hst _ z.2⟩
      map_one' := Subtype.ext (Units.ext (cT_one σ))
      map_mul' := fun a b => by
        have : (⟨starU σ (a * b).1, hst _ (a * b).2⟩ : Z) = ⟨starU σ b.1, hst _ b.2⟩ * ⟨starU σ a.1, hst _ a.2⟩ :=
          Subtype.ext (Units.ext (by show cT σ (a.1.val * b.1.val) = cT σ b.1.val * cT σ a.1.val; exact cT_mul σ _ _))
        rw [this, hcomm] }
  have hτ : ∀ z : Z, ((τ z : Z) : GLw n w) = starU σ z.1 := fun z => rfl
  have hτc : Continuous τ := continuous_induced_rng.2 (hstarc.comp continuous_subtype_val)
  have hτi : ∀ z, τ (τ z) = z := fun z => Subtype.ext (Units.ext (hcc _))
  have hsq : ∃ W ∈ nhds (1 : Z), ∀ s ∈ W, τ s = s → ∃ r : Z, τ r = r ∧ r * r = s := by
    obtain ⟨W, hW, hWs⟩ : ∃ W ∈ nhds (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)), ∀ s ∈ W, ∃ r : Matrix (Fin n) (Fin n) (w.adicCompletion E), r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) (w.adicCompletion E), a * s = s * a → a * r = r * a) ∧ ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by
      haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
      letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
      exact _root_.GlobalTheory.matrix_sqrt_near_one_ultrametric (w.adicCompletion E) n σ hσc
    refine ⟨(fun z : Z => (z.1 : Matrix (Fin n) (Fin n) _)) ⁻¹' W,
      (Units.continuous_val.comp continuous_subtype_val).continuousAt.preimage_mem_nhds (by simpa using hW), ?_⟩
    intro s hs hτs
    obtain ⟨r, hrr, hrc, hrs⟩ := hWs _ hs
    have hsv : cT σ s.1.val = s.1.val := by
      have h := congrArg (fun u : Z => u.1.val) hτs
      exact h
    have hrr' : r * r = s.1.val := hrr
    have hu : IsUnit r := isUnit_of_mul_isUnit_left (hrr'.symm ▸ s.1.isUnit)
    have hrZ : hu.unit ∈ Z := (hZ _).2 (hrc _ ((hZ _).1 s.2).symm).symm
    refine ⟨⟨hu.unit, hrZ⟩, Subtype.ext (Units.ext (hrs hsv)), Subtype.ext (Units.ext hrr')⟩
  let DZ : Set Z := Subtype.val ⁻¹' ((fun d : GLw n w => starU σ d⁻¹ * d⁻¹) '' D)
  have hDZ : IsCompact DZ := hZc.isClosedEmbedding_subtypeVal.isCompact_preimage
    (hD.image ((hstarc.comp continuous_inv).mul continuous_inv))
  obtain ⟨B, hB, hBz⟩ := _root_.GlobalTheory.InvolutionNorm.exists_compact_mod_kernel Z hcomm τ hτc hτi hsq DZ hDZ
  refine ⟨Subtype.val ⁻¹' ((Subtype.val '' B : Set (GLw n w)) * D),
    hcl.isCompact_preimage ((hB.image continuous_subtype_val).mul hD), fun g hg => ?_⟩
  obtain ⟨z, hz, d, hd, hgd⟩ := hDg g.1 (hgC g hg)
  have hzZ : z ∈ Z := (hZ z).2 (by simpa using congrArg Units.val hz)
  have hgU : cT σ g.1.val * g.1.val = 1 := (hmemU _).1 g.2
  have hN : τ ⟨z, hzZ⟩ * ⟨z, hzZ⟩ ∈ DZ := by
    refine ⟨d, hd, Units.ext ?_⟩
    have hg' : g.1.val = z.val * d.val := by rw [hgd, Units.val_mul]
    rw [hg', cT_mul] at hgU
    have e1 : cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * cT σ d.val = 1 := by
      rw [← cT_mul, Units.mul_inv, cT_one]
    show cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) = cT σ z.val * z.val
    calc cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _)
        = cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * (cT σ d.val * cT σ z.val * (z.val * d.val)) * ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) := by
          rw [hgU, Matrix.mul_one]
      _ = (cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * cT σ d.val) * (cT σ z.val * z.val) * (d.val * ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _)) := by
          simp only [Matrix.mul_assoc]
      _ = cT σ z.val * z.val := by rw [e1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨t, ht, b, hb, hzt⟩ := hBz _ hN
  have htU : t.1 ∈ UL n w := by
    have h := congrArg (fun u : Z => u.1.val) ht
    exact (hmemU _).2 h
  have hgt : g.1 = t.1 * (b.1 * d) := by
    rw [hgd, ← mul_assoc]; exact congrArg (· * d) (congrArg Subtype.val hzt)
  have hωU : b.1 * d ∈ UL n w := by
    have : b.1 * d = t.1⁻¹ * g.1 := by rw [hgt, inv_mul_cancel_left]
    rw [this]; exact (UL n w).mul_mem ((UL n w).inv_mem htU) g.2
  refine ⟨⟨t.1, htU⟩, Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 t.2), ⟨b.1 * d, hωU⟩,
    ⟨b.1, ⟨b, hb, rfl⟩, d, hd, rfl⟩, Subtype.ext hgt⟩

end GlobalTheory.OrbitU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexSupSpanSingletonEqAbsNormStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_sup_span_singleton_eq_absNorm_of_isMaximal : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (N₀ : Submodule (𝓞 F) V) (u : V) (p : Ideal (𝓞 F)), p.IsMaximal → u ∉ N₀ → (∀ π ∈ p, π • u ∈ N₀) → N₀.toAddSubgroup.relIndex (N₀ ⊔ Submodule.span (𝓞 F) {u}).toAddSubgroup = Ideal.absNorm p := by
  first | exact @GlobalTheory.relIndex_sup_span_singleton_eq_absNorm | exact GlobalTheory.relIndex_sup_span_singleton_eq_absNorm | (intros; apply GlobalTheory.relIndex_sup_span_singleton_eq_absNorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMatrixCoefficientCompactSupportFinStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_matrixCoefficient_compactSupport_finitePlace : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : MeasureTheory.Measure (κ → Fv F v))
    [μ.IsAddHaarMeasure], Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    ∀ φ ∈ SB (κ → Fv F v), ∀ g ∈ SB (κ → Fv F v),
    ∃ C : Set ((κ → Fv F v) × (κ → Fv F v)), IsCompact C ∧
      ∀ w, ∫ y, schr ψ₀ w φ y * (starRingEnd ℂ) (g y) ∂μ ≠ 0 → w ∈ C := by
  first | exact @GlobalTheory.SchrSuppFin.support_compact | exact GlobalTheory.SchrSuppFin.support_compact | (intros; apply GlobalTheory.SchrSuppFin.support_compact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetAdelicGLExistsCompactDecomposition
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

open Pointwise _root_.Matrix

namespace GlobalTheory.SiegelSetGL

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

theorem continuous_pInfC : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_mapInf : Continuous (GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_pInfC E))

theorem continuous_mapFin : Continuous (GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))

theorem exists_compact_decomp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ω : Set (AdelicGLn.AdelicGL E a)), IsCompact ω →
    ω ⊆ (adelicBorel (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)) → ∀ t : ℝ, 0 < t →
    ∃ (Ω : Set (GL (Fin a) (Cinf E))) (Kf : Set (GL (Fin a) (Af E))), IsCompact Ω ∧ IsCompact Kf ∧
      ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
        d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ b ∈ ω, ∀ k ∈ maxCompact (K := E) (n := a),
          ∃ c ∈ Ω, ∃ f ∈ Kf, b * infGL E a d * k = infGL E a (d * c) * finGL E a f := by
  intro E _ _ _ a ω hω hωB t ht
  set pI := GeneralLinearGroup.map (n := Fin a) (pInf E)
  set pF := GeneralLinearGroup.map (n := Fin a) (pFin E)
  have hωI : IsCompact (pI '' ω) := hω.image (continuous_mapInf E a)
  have hup : ∀ b ∈ pI '' ω, b.val.BlockTriangular id := by
    rintro _ ⟨b, hb, rfl⟩ i j hij
    have h0 : (b : Matrix (Fin a) (Fin a) (Ad E)) i j = 0 := hωB hb hij
    change pInf E ((b : Matrix (Fin a) (Fin a) (Ad E)) i j) = 0
    rw [h0, map_zero]
  obtain ⟨Ω0, hΩ0, hΩ⟩ := _root_.GlobalTheory.upperCone_conj_compact E a (pI '' ω) hωI hup t ht
  have hK := isCompact_maxCompact (K := E) (n := a)
  refine ⟨Ω0 * pI '' (maxCompact (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)),
    pF '' ω * pF '' (maxCompact (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)),
    hΩ0.mul (hK.image (continuous_mapInf E a)),
    (hω.image (continuous_mapFin E a)).mul (hK.image (continuous_mapFin E a)), ?_⟩
  intro r d hr hrt hd b hb k hk
  refine ⟨(d⁻¹ * pI b * d) * pI k, Set.mul_mem_mul (hΩ r d hr hrt hd _ ⟨b, hb, rfl⟩) ⟨k, hk, rfl⟩,
    pF b * pF k, Set.mul_mem_mul ⟨b, hb, rfl⟩ ⟨k, hk, rfl⟩, ?_⟩
  apply ga_ext
  · change pI (b * infGL E a d * k) = pI (infGL E a (d * (d⁻¹ * pI b * d * pI k)) * finGL E a (pF b * pF k))
    simp only [map_mul, pI, pInf_infGL, pInf_finGL, mul_one]
    group
  · change pF (b * infGL E a d * k) = pF (infGL E a (d * (d⁻¹ * pI b * d * pI k)) * finGL E a (pF b * pF k))
    simp only [map_mul, pF, pFin_infGL, pFin_finGL, mul_one, one_mul]

end GlobalTheory.SiegelSetGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfUniversalFirstOrderTa
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SmoothDimTangent

theorem smoothOfRelativeDimension_of_universal_tangent : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B) (d : ℕ), Smooth s → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), ∃ u : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ X, spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ u = x ∧ u ≫ s = spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ x ≫ s ∧ ∀ v : Sp (DualNumber k) ⟶ X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ s → ∃! c : (Fin d → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u) → SmoothOfRelativeDimension d s := by
  intro B _ X s d hs H
  have loc : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧ SmoothOfRelativeDimension d (W.ι ≫ s) := by
    intro p
    obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth s p
    let _ := (s.appLE U V e).hom.toAlgebra
    have : Algebra.IsStandardSmooth Γ(Sp B, U) Γ(X, V) := h
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := this
    have hP : Algebra.IsStandardSmoothOfRelativeDimension P.dimension Γ(Sp B, U) Γ(X, V) := ⟨_, _, _, ‹_›, P, rfl⟩
    let k := AlgebraicClosure (X.residueField p)
    let x : Sp k ⟶ X := spMap (algebraMap (X.residueField p) k) ≫ X.fromSpecResidueField p
    have hr : Set.range x.base ⊆ (V : Set X) := by
      rintro _ ⟨y, rfl⟩
      have : x.base y ∈ Set.range (X.fromSpecResidueField p).base := ⟨_, (Scheme.Hom.comp_apply _ _ y).symm⟩
      rw [Scheme.range_fromSpecResidueField] at this
      rw [Set.mem_singleton_iff.1 this]
      exact hx
    obtain ⟨φ, ψ, h1, h2, h3⟩ := _root_.GlobalTheory.SchRing.deformation_on_sections B X s U V hU hV e d k x hr (H k x)
    have : Nontrivial Γ(X, V) := φ.domain_nontrivial
    have : Algebra.IsStandardSmooth Γ(Sp B, U) Γ(X, V) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth P.dimension
    have : Module.Free Γ(X, V) Ω[Γ(X, V)⁄Γ(Sp B, U)] := Algebra.IsStandardSmooth.free_kaehlerDifferential
    have hrank : Module.finrank Γ(X, V) (Ω[Γ(X, V)⁄Γ(Sp B, U)]) = P.dimension :=
      Module.finrank_eq_of_rank_eq hP.rank_kaehlerDifferential
    have hd : d = P.dimension := _root_.GlobalTheory.finrank_kaehler_eq_of_universal_tangent _ _ k P.dimension d hrank φ ψ h1 h2 h3
    have h' : RingHom.IsStandardSmoothOfRelativeDimension P.dimension (s.appLE U V e).hom := hP
    have : IsAffine U := hU
    have : IsAffine V := hV
    have : SmoothOfRelativeDimension P.dimension (s.resLE U V e) :=
      (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension P.dimension)).2
        (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
          ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso s U V e)).2 h'))
    have : SmoothOfRelativeDimension (P.dimension + 0) (V.ι ≫ s) := by
      rw [← Scheme.Hom.resLE_comp_ι s e]; infer_instance
    refine ⟨V, hx, ?_⟩
    rw [hd]; exact this
  choose W hW hd using loc
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) := HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) hd

end GlobalTheory.SmoothDimTangent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulDetSpanSupLeDetSpanLatticeStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smul_detSpan_sup_le_detSpan_lattice : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (d : ℕ) (b : Module.Basis (Fin d) F V) (N : Submodule (𝓞 F) V) (u : V) (π : 𝓞 F), π • u ∈ N → ∀ y ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ N ⊔ Submodule.span (𝓞 F) {u}) ∧ y = b.det v}, π • y ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ N) ∧ y = b.det v} := by
  first | exact @GlobalTheory.DetColon.smul_detSpan_sup_le | exact GlobalTheory.DetColon.smul_detSpan_sup_le | (intros; apply GlobalTheory.DetColon.smul_detSpan_sup_le <;> assumption)
end

