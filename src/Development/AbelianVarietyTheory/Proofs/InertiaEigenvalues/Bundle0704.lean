module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0701
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartSchurComplementExtension
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionClassBound
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0699
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOpenSubgroup
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0700
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsMulInfiniteAdelicGLStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGLProjections_mul_infiniteAdelicGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E a) (y : GL (Fin a) (Cinf E)), prS S a (g * infGL E a y) = prS S a g * infGL E a y ∧ prO S a (g * infGL E a y) = prO S a g := by
  first | (exact @GlobalTheory.SchurExt.prS_prO_mul_infGL) | (exact GlobalTheory.SchurExt.prS_prO_mul_infGL) | (intros; apply GlobalTheory.SchurExt.prS_prO_mul_infGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsOnSupportedAtPlacesStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGLProjections_on_supportedAtPlaces : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, prS S a g = g ∧ prO S a g = 1) ∧ ∀ g, prS S a g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S := by
  first | (exact @GlobalTheory.SchurExt.prS_prO_supS) | (exact GlobalTheory.SchurExt.prS_prO_supS) | (intros; apply GlobalTheory.SchurExt.prS_prO_supS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsUpperUnitriangularGenericCharStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGLProjections_upperUnitriangular_genericChar : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := a), prS S a u ∈ GlobalTheory.JSW.NA (E := E) (a := a) ∧ prO S a u ∈ GlobalTheory.JSW.NA (E := E) (a := a) ∧ GlobalTheory.JSW.psiN (prS S a u) * GlobalTheory.JSW.psiN (prO S a u) = GlobalTheory.JSW.psiN u := by
  first | (exact @GlobalTheory.SchurExt.prS_prO_NA_psiN) | (exact GlobalTheory.SchurExt.prS_prO_NA_psiN) | (intros; apply GlobalTheory.SchurExt.prS_prO_NA_psiN  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDiagGLMemAdelicGLSupportedAtFinitePlacesStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockDiagGL_mem_adelicGLSupportedAtFinitePlaces : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S := by
  first | (exact @GlobalTheory.SchurExt.blockGL_mem_supS) | (exact GlobalTheory.SchurExt.blockGL_mem_supS) | (intros; apply GlobalTheory.SchurExt.blockGL_mem_supS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CasimirEigenOrthogonal
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

noncomputable section

namespace GlobalTheory.CapOrth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} {μ : Measure (GA E N)}
  {W : Submodule ℂ (Sm E N)} (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1)


open Classical in
def cls (x : Sm E N) : L2 (latticeGL E N) μ := if hx : x ∈ W then toL2ₗ μ W h ⟨x, hx⟩ else 0

theorem cls_mk {x : Sm E N} (hx : x ∈ W) : cls h x = toL2ₗ μ W h ⟨x, hx⟩ := dif_pos hx

theorem cls_add {x y : Sm E N} (hx : x ∈ W) (hy : y ∈ W) : cls h (x + y) = cls h x + cls h y := by
  rw [cls_mk h (W.add_mem hx hy), cls_mk h hx, cls_mk h hy, ← map_add (f := _)]; rfl

theorem cls_smul (c : ℂ) {x : Sm E N} (hx : x ∈ W) : cls h (c • x) = c • cls h x := by
  rw [cls_mk h (W.smul_mem c hx), cls_mk h hx, ← map_smul]; rfl

theorem cls_sub {x y : Sm E N} (hx : x ∈ W) (hy : y ∈ W) : cls h (x - y) = cls h x - cls h y := by
  rw [cls_mk h (W.sub_mem hx hy), cls_mk h hx, cls_mk h hy, ← map_sub]; rfl

variable (J : Submodule ℂ (Sm E N))

variable [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

end GlobalTheory.CapOrth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartSchurComplementExtensionStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_chart_schurComplementExtension : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∀ g, ContDiffOn ℝ ∞ (chart β g) (invSet E (m + 1))) → (∀ g, ContDiffOn ℝ ∞ (chart b₁ g) (invSet E (r + 1))) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ContDiff ℝ ∞ χ → ∀ g, ContDiffOn ℝ ∞ (chart (schurF β b₁ χ) g) (invSet E (m + r + 1 + 1)) := by
  first | (exact @GlobalTheory.SchurExt.contDiffOn_chart_schurF) | (exact GlobalTheory.SchurExt.contDiffOn_chart_schurF) | (intros; apply GlobalTheory.SchurExt.contDiffOn_chart_schurF  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionClassBoundStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_extension_class_bound : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admitted D HW F → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; TBat S E := by
  first | exact @GlobalTheory.Cyc.ClassBound.class_bound | exact GlobalTheory.Cyc.ClassBound.class_bound | (intros; apply GlobalTheory.Cyc.ClassBound.class_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbTypeUeIffLocalEmbeddingInCMHalfTypeStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embTypeUe_iff_localEmbeddingInCMHalfType : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (ep : Bool) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw), EmbeddingTypes.EmbTypeUe (i := i) (w := w) (hw := hw) ep τ ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.EmbIn (N := D.nd) D.nbr i ep w hw τ := by
  first | exact @GlobalTheory.TypeUeHalf.main | exact GlobalTheory.TypeUeHalf.main | (intros; apply GlobalTheory.TypeUeHalf.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyAdelicGLProjectionsFiniteNearOneStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_adelicGLProjections_finite_near_one : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (V V' : Set (GL (Fin a) (Af E))), V ∈ 𝓝 (1 : GL (Fin a) (Af E)) → V' ∈ 𝓝 (1 : GL (Fin a) (Af E)) → ∀ᶠ k in 𝓝 (1 : GL (Fin a) (Af E)), (∃ k' ∈ V, prS S a (finGL E a k) = finGL E a k') ∧ ∃ k'' ∈ V', prO S a (finGL E a k) = finGL E a k'' := by
  first | (exact @GlobalTheory.SchurExt.eventually_prS_prO_finGL) | (exact GlobalTheory.SchurExt.eventually_prS_prO_finGL) | (intros; apply GlobalTheory.SchurExt.eventually_prS_prO_finGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLabelInertiaEigenvalues
section
noncomputable section

namespace GlobalTheory.PendOf.LabIneAll

open _root_.Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations _root_.Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module
open Polynomial GlobalTheory.Pass GlobalTheory.PendOf GlobalTheory.WeilDeligne

section Alg

theorem charpoly_pow_of_prod {K ι : Type} [Field K] [IsAlgClosed K] {r : ℕ} (A : Matrix (Fin r) (Fin r) K)
    (s : Multiset ι) (f : ι → K) (h : A.charpoly = (s.map fun x => X - C (f x)).prod) (n : ℕ) :
    (A ^ n).charpoly = (s.map fun x => X - C (f x ^ n)).prod := by
  have h1 : A.charpoly.roots = s.map f := by
    rw [h, ← roots_multiset_prod_X_sub_C (s.map f), Multiset.map_map]
    rfl
  have h2 := GlobalTheory.CharpolyPow.roots_charpoly_pow K r n A
  rw [(IsAlgClosed.splits (A ^ n).charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic _), h2, h1,
    Multiset.map_map, Multiset.map_map]
  rfl

theorem teich_zero {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : t 0 = 0 := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  by_contra h0
  have h1 : t 0 * t x = t 0 * t 1 := by rw [← map_mul, ← map_mul, zero_mul, zero_mul]
  exact hx.2 (ht x 1 hx.1 one_ne_zero (mul_left_cancel₀ h0 h1))

end Alg

section Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω}

theorem mem_of_isOpen {H : Subgroup (Ine (F := E) A)} (hH : IsOpen (H : Set (Ine (F := E) A)))
    {γ : G E Ω} (hγ : TameGenAt A γ) (h1 : (⟨γ, hγ.1⟩ : Ine (F := E) A) ∈ H)
    (hw : ∀ σ : Ine (F := E) A, (σ : G E Ω) ∈ Wild E A → σ ∈ H) (σ : Ine (F := E) A) : σ ∈ H := by
  have hK : IsClosed ((H.map (Ine (F := E) A).subtype : Subgroup (G E Ω)) : Set (G E Ω)) :=
    (isClosed_Ine A).isClosedEmbedding_subtypeVal.isClosedMap _ (H.isClosed_of_isOpen hH)
  have hle : Subgroup.closure (insert γ (Wild E A : Set (G E Ω))) ≤ H.map (Ine (F := E) A).subtype := by
    rw [Subgroup.closure_le]
    rintro u (rfl | hu)
    · exact ⟨⟨u, hγ.1⟩, h1, rfl⟩
    · exact ⟨⟨u, Wild_le_Ine hu⟩, hw _ hu, rfl⟩
  obtain ⟨u, hu, e⟩ := closure_minimal (SetLike.coe_subset_coe.mpr hle) hK (hγ.2 σ.2)
  rwa [← Subtype.ext (a1 := u) (a2 := σ) e]

theorem isOfFinOrder_of_isOpen {M : Type} [Group M] (φ : Ine (F := E) A →* M)
    (hφ : IsOpen (φ.ker : Set (Ine (F := E) A))) (σ : Ine (F := E) A) : IsOfFinOrder (φ σ) := by
  have : CompactSpace (Ine (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  have : Finite (Ine (F := E) A ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ hφ
  have : φ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨φ.ker.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, ?_⟩
  rw [← map_pow]
  exact φ.ker.pow_index_mem σ


open Classical in
theorem charpoly_eq_of_gen {n : ℕ} (ρ : Ine (F := E) A →* GL (Fin n) ℂ)
    (hρ : ∃ U : Subgroup (G E Ω), IsOpen (U : Set (G E Ω)) ∧
      ∀ σ : Ine (F := E) A, (σ : G E Ω) ∈ U → ρ σ = 1)
    {ι : Type} (s : Multiset ι) (χ : ι → G E Ω → ℂ)
    (h1 : ∀ x ∈ s, χ x 1 = 1)
    (hmul : ∀ x ∈ s, ∀ σ ∈ Ine (F := E) A, ∀ σ' ∈ Ine (F := E) A, χ x (σ * σ') = χ x σ * χ x σ')
    (hwild : ∀ x ∈ s, ∀ σ ∈ Wild E A, χ x σ = 1)
    (hopen : ∀ x ∈ s, ∃ U : Subgroup (G E Ω), IsOpen (U : Set (G E Ω)) ∧
      ∀ σ ∈ U, σ ∈ Ine (F := E) A → χ x σ = 1)
    {γ : G E Ω} (hγ : TameGenAt A γ)
    (hρw : ∀ σ : Ine (F := E) A, (σ : G E Ω) ∈ Wild E A →
      ((ρ σ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly = (X - 1) ^ n)
    (hργ : ((ρ ⟨γ, hγ.1⟩ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly =
      (s.map fun x => X - C (χ x γ)).prod)
    (σ : Ine (F := E) A) :
    ((ρ σ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly = (s.map fun x => X - C (χ x σ)).prod := by
  let T := s.toFinset
  let c : T → (Ine (F := E) A →* ℂˣ) := fun x => MonoidHom.toHomUnits
    { toFun := fun σ => χ x (σ : G E Ω)
      map_one' := h1 x (Multiset.mem_toFinset.1 x.2)
      map_mul' := fun σ σ' => hmul x (Multiset.mem_toFinset.1 x.2) σ σ.2 σ' σ'.2 }
  have hc : ∀ x σ, ((c x σ : ℂˣ) : ℂ) = χ x (σ : G E Ω) := fun _ _ => rfl
  let Φ : Ine (F := E) A →* GL (Fin n) ℂ × (T → ℂˣ) := ρ.prod (Pi.monoidHom c)
  obtain ⟨U, hU, hUρ⟩ := hρ
  choose V hV hVχ using fun x : T => hopen x (Multiset.mem_toFinset.1 x.2)
  let W : Set (Ine (F := E) A) := Subtype.val ⁻¹' ((U : Set (G E Ω)) ∩ ⋂ x, (V x : Set (G E Ω)))
  have hWo : IsOpen W := continuous_subtype_val.isOpen_preimage _ (hU.inter (isOpen_iInter_of_finite hV))
  have hWk : ∀ σ ∈ W, Φ σ = 1 := by
    intro σ hσ
    refine Prod.ext (hUρ σ hσ.1) (funext fun x => Units.ext ?_)
    show χ x (σ : G E Ω) = 1
    exact hVχ x σ (Set.mem_iInter.1 hσ.2 x) σ.2
  have h1W : (1 : Ine (F := E) A) ∈ W := ⟨U.one_mem, Set.mem_iInter.2 fun x => (V x).one_mem⟩
  have hker : IsOpen (Φ.ker : Set (Ine (F := E) A)) :=
    Subgroup.isOpen_of_mem_nhds _ (g := 1)
      (Filter.mem_of_superset (hWo.mem_nhds h1W) fun σ hσ => MonoidHom.mem_ker.2 (hWk σ hσ))
  have hkerρ : IsOpen (ρ.ker : Set (Ine (F := E) A)) :=
    Subgroup.isOpen_mono (H₁ := Φ.ker) (fun σ hσ => MonoidHom.mem_ker.2 (congrArg Prod.fst (MonoidHom.mem_ker.1 hσ)))
      hker
  let γ' : Ine (F := E) A := ⟨γ, hγ.1⟩
  let H := (Subgroup.zpowers (Φ γ')).comap Φ
  have hH : IsOpen (H : Set (Ine (F := E) A)) :=
    Subgroup.isOpen_mono (H₁ := Φ.ker) (fun σ hσ => Subgroup.mem_comap.2 (by
      rw [MonoidHom.mem_ker.1 hσ]; exact one_mem _)) hker
  have hσH : σ ∈ H := by
    refine mem_of_isOpen hH hγ (Subgroup.mem_comap.2 (Subgroup.mem_zpowers _)) (fun τ hτ => ?_) σ
    refine Subgroup.mem_comap.2 ?_
    have hρ1 : ρ τ = 1 := by
      obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_isOpen ρ hkerρ τ)
      exact Units.ext (GlobalTheory.FinOrd.eq_one_of_pow_eq_one_of_charpoly ℂ n _
        ⟨m, hm, by rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]⟩ (hρw τ hτ))
    have hΦ1 : Φ τ = 1 := by
      refine Prod.ext hρ1 (funext fun x => Units.ext ?_)
      show χ x (τ : G E Ω) = 1
      exact hwild x (Multiset.mem_toFinset.1 x.2) τ hτ
    rw [hΦ1]
    exact one_mem _
  obtain ⟨m, hm⟩ := ((isOfFinOrder_of_isOpen Φ hker γ').mem_powers_iff_mem_zpowers).2 (Subgroup.mem_comap.1 hσH)
  have hρm : ρ σ = ρ γ' ^ m := by
    have := congrArg Prod.fst hm
    simpa [Φ] using this.symm
  have hχm : ∀ x ∈ s, χ x γ ^ m = χ x σ := by
    intro x hx
    have := congrArg (fun p : GL (Fin n) ℂ × (T → ℂˣ) => ((p.2 ⟨x, Multiset.mem_toFinset.2 hx⟩ : ℂˣ) : ℂ)) hm
    simp only [Φ, MonoidHom.prod_apply, Prod.pow_snd, Pi.pow_apply, Units.val_pow_eq_pow_val,
      Pi.monoidHom_apply] at this
    exact this
  rw [hρm, Units.val_pow_eq_pow_val, charpoly_pow_of_prod _ s (fun x => χ x γ) hργ m]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun x hx => by rw [hχm x hx])

end Local

theorem main : ∀ D : D7, IneRep D → LabDepth D → LabGen D → ∃ Ω : TameOm D, LabIne Ω := by
  intro D hR hD hG
  obtain ⟨γ, hγ, hlab⟩ := hG
  obtain ⟨Ω, hΩ⟩ := GlobalTheory.PendOf.Model.exists_tameOm D γ hγ
  refine ⟨Ω, fun k w hw L hL => ?_⟩
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  intro σ hσ
  obtain ⟨ρ, hρ, hρP⟩ := hR k w hw L
  have hT : TameLP D L := ((hD k w hw L).2).1 hL
  have hγw := hγ.2 k w hw
  have hlabγ := hlab k w hw L hL
  have hs0 : ∀ x ∈ Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w L), x ≠ 0 := by
    intro x hx h0
    subst h0
    have hdvd : X ∣ ((ρ ⟨γ k w, hγw.1⟩ : GL (Fin (D.naut.lpDim L)) ℂ) :
        Matrix (Fin (D.naut.lpDim L)) (Fin (D.naut.lpDim L)) ℂ).charpoly := by
      rw [← hρP ⟨γ k w, hγw.1⟩]
      rw [show ((⟨γ k w, hγw.1⟩ : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w))) : GE D.nd) = γ k w from rfl, hlabγ]
      have := Multiset.dvd_prod (Multiset.mem_map_of_mem (fun x => X - C (D.ntypes.teichC k x)) hx)
      simpa [teich_zero (D.ntypes.teichC k) (D.ntypes.teichC_inj k)] using this
    rw [X_dvd_iff] at hdvd
    have hdet := Matrix.isUnits_det_units (ρ ⟨γ k w, hγw.1⟩)
    rw [Matrix.det_eq_sign_charpoly_coeff, hdvd, mul_zero] at hdet
    exact not_isUnit_zero hdet
  refine (hρP ⟨σ, hσ⟩).trans (charpoly_eq_of_gen ρ hρ _ (fun x τ => Ω.om k w x τ)
    (fun x hx => Ω.om_one k w x (hs0 x hx))
    (fun x hx => Ω.om_mul k w x (hs0 x hx))
    (fun x hx τ hτ => Ω.om_wild k w hw x (hs0 x hx) τ hτ)
    (fun x hx => Ω.om_open k w x (hs0 x hx)) hγw
    (fun τ hτ => (hρP τ).symm.trans (hT τ τ.2 hτ)) ?_ ⟨σ, hσ⟩)
  rw [← hρP ⟨γ k w, hγw.1⟩]
  refine hlabγ.trans (congrArg Multiset.prod (Multiset.map_congr rfl fun x hx => ?_))
  rw [hΩ k w hw x (hs0 x hx)]

end GlobalTheory.PendOf.LabIneAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroupStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localExtension_of_finiteIndex_weilSubgroup : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (H : Subgroup (Weil h)), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∃ (L : IntermediateField E Ω), FiniteDimensional E L ∧ IsLocalExt L h ∧ ∀ σ : Weil h, σ ∈ H ↔ ∀ x : L, (σ : G E Ω) (x : Ω) = x := by
  first | exact @GlobalTheory.LocalExtField.exists_localExt_of_finiteIndex | exact GlobalTheory.LocalExtField.exists_localExt_of_finiteIndex | (intros; apply GlobalTheory.LocalExtField.exists_localExt_of_finiteIndex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNewPlaceFrobeniusConjugateModOpenNormalSubStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_newPlace_frobeniusConjugate_modOpenNormalSubgroup : Cheb → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → n < R → ∀ (H : Subgroup (GE N)) (S : Finset (PlE D.host)), AdmFam X i M H S d → L ≤ H → ∀ (U : Subgroup (GE N)) (h : GE N), IsOpen (U : Set (GE N)) → U.Normal → U ≤ L → h ∈ L → (∀ b : Fin R, b.val < n → d (P (.inl b)) h = 1) → (∀ b : Fin R, n ≤ b.val → Ine (F := D.host.E) (N.plOm.1 (P (.inl b))) ≤ U) → ∃ P' : Fin R ⊕ Fin (n + 1) → PlE D.host, Ext P P' ∧ PiLocalization₂ i M d A₀ L z P' ∧ ∃ σ γ g : GE N, NewPl i M L (P' (.inr (Fin.last n))) (d (P' (.inr (Fin.last n)))) σ γ ∧ d (P' (.inr (Fin.last n))) σ = 1 ∧ g * σ * g⁻¹ * h⁻¹ ∈ U := by
  first | exact @GlobalTheory.NewPrimePick.exists_newPlace | exact GlobalTheory.NewPrimePick.exists_newPlace | (intros; apply GlobalTheory.NewPrimePick.exists_newPlace <;> assumption)
end

