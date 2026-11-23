module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.BlockMatrixIdentity.BlockMatOne
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0215
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0224
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0329
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0320
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0319
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0321
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0327
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingRestrictionNatural
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusReciprocityNonzero
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.FrobInv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem mk_parab (e : (Σ a, m a) ≃ n) (τ : Representation ℂ (GL n k) V) (p : parab k e) (w : V) :
    (Submodule.Quotient.mk (τ (p : GL n k) w) : Jacquet τ (unipRad k e)) =
      Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) w) := by
  obtain ⟨u, hu, hp⟩ := exists_levi_mul_unip k e p
  have key : ∀ y : V, (Submodule.Quotient.mk (τ u y) : Jacquet τ (unipRad k e)) = Submodule.Quotient.mk y := by
    intro y
    rw [Submodule.Quotient.eq]
    apply Submodule.subset_span
    refine Set.mem_ofPred.mpr ⟨⟨u, hu⟩, y, ?_⟩
    simp
  have hL : ∀ y : V, (Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) y) : Jacquet τ (unipRad k e)) =
      ((deltaHalf k m (leviProj k e p) : ℂˣ) : ℂ) • jac e τ (leviProj k e p) (Submodule.Quotient.mk y) := by
    intro y
    rw [jac_mk, smul_smul, Units.mul_inv, one_smul]
  have e1 : τ (p : GL n k) w = τ (leviEmb k e (leviProj k e p)) (τ u w) := by
    first
    | (rw [hp, map_mul]; rfl)
    | rw [hp, map_mul]
  rw [e1, hL, hL, key]

def frobFun (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (jac e τ).IntertwiningMap ρ) (v : V) : GL n k → W :=
  fun g => f (Submodule.Quotient.mk (τ g v))

theorem frobFun_law (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (jac e τ).IntertwiningMap ρ) (v : V) (p : parab k e) (g : GL n k) :
    frobFun e f v (p * g) = (deltaHalf k m (leviProj k e p) : ℂ) • ρ (leviProj k e p) (frobFun e f v g) := by
  have h1 : frobFun e f v (p * g) =
      f (Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) (τ g v))) := by
    show f (Submodule.Quotient.mk (τ ((p : GL n k) * g) v)) = _
    rw [map_mul]
    exact congrArg f (mk_parab e τ p (τ g v))
  have h2 := LinearMap.congr_fun (f.isIntertwining' (leviProj k e p)) (Submodule.Quotient.mk (τ g v))
  simp only [LinearMap.comp_apply] at h2
  rw [h1]
  show f.toLinearMap (Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) (τ g v))) =
    ((deltaHalf k m (leviProj k e p) : ℂˣ) : ℂ) • ρ (leviProj k e p) (f.toLinearMap (Submodule.Quotient.mk (τ g v)))
  rw [← h2, jac_mk, map_smul, smul_smul, Units.mul_inv, one_smul]

theorem frobFun_mem (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (jac e τ).IntertwiningMap ρ) (v : V) :
    frobFun e f v ∈ indSpace (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)) := by
  show ∀ (h : ↥(parab k e)) (g : GL n k),
    frobFun e f v (↑h * g) = ((twist ρ (deltaHalf k m)).comp (leviProj k e)) h (frobFun e f v g)
  intro p x
  rw [frobFun_law, MonoidHom.comp_apply, twist_apply]

theorem frobFun_translate (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (jac e τ).IntertwiningMap ρ) (v : V) (h x : GL n k) :
    frobFun e f v (x * h) = frobFun e f (τ h v) x := by
  show f (Submodule.Quotient.mk (τ (x * h) v)) = f (Submodule.Quotient.mk (τ x (τ h v)))
  first
  | (rw [map_mul]; rfl)
  | rw [map_mul]

theorem frobFun_smooth (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (jac e τ).IntertwiningMap ρ) (v : V) :
    (⟨frobFun e f v, frobFun_mem e f v⟩ : indSpace (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e))) ∈
      smoothPart (ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e))) := by
  show IsOpen {g : GL n k | (ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e))) g
    ⟨frobFun e f v, frobFun_mem e f v⟩ = ⟨frobFun e f v, frobFun_mem e f v⟩}
  set F : indSpace (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)) :=
    ⟨frobFun e f v, frobFun_mem e f v⟩ with hF
  set R := ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)) with hR
  have hstab : ∀ s, τ s v = v → R s F = F := by
    intro s hs
    apply Subtype.ext
    funext x
    show frobFun e f v (x * s) = frobFun e f v x
    rw [frobFun_translate, hs]
  rw [isOpen_iff_forall_mem_open]
  intro g0 hg0
  refine ⟨(fun g => g0⁻¹ * g) ⁻¹' {g | τ g v = v}, ?_, IsOpen.preimage (continuous_const_mul g0⁻¹) (hτ v), ?_⟩
  · intro g hg
    have h1 : R (g0 * (g0⁻¹ * g)) F = R g0 (R (g0⁻¹ * g) F) := by
      first
      | (rw [map_mul]; rfl)
      | rw [map_mul]
    rw [mul_inv_cancel_left] at h1
    show R g F = F
    rw [h1, hstab _ hg]
    exact hg0
  · show τ (g0⁻¹ * g0) v = v
    rw [inv_mul_cancel, map_one]
    rfl

def frobInv (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (jac e τ).IntertwiningMap ρ) :
    τ.IntertwiningMap (parInd e ρ) where
  toLinearMap :=
    { toFun := fun v => ⟨⟨frobFun e f v, frobFun_mem e f v⟩, frobFun_smooth e hτ f v⟩
      map_add' := fun v w => by
        refine Subtype.ext (Subtype.ext (funext fun g => ?_))
        show f (Submodule.Quotient.mk (τ g (v + w))) = f (Submodule.Quotient.mk (τ g v)) + f (Submodule.Quotient.mk (τ g w))
        rw [map_add (f := _), Submodule.Quotient.mk_add, map_add (f := _)]
      map_smul' := fun c v => by
        refine Subtype.ext (Subtype.ext (funext fun g => ?_))
        show f (Submodule.Quotient.mk (τ g (c • v))) = c • f (Submodule.Quotient.mk (τ g v))
        rw [map_smul, Submodule.Quotient.mk_smul, map_smul] }
  isIntertwining' g := by
    refine LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => ?_))
    exact (frobFun_translate e f v g x).symm

theorem frobInv_one (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (jac e τ).IntertwiningMap ρ) (v : V) :
    (frobInv e hτ f v).1.1 1 = f (Submodule.Quotient.mk v) := by
  show f (Submodule.Quotient.mk (τ 1 v)) = f (Submodule.Quotient.mk v)
  first
  | (rw [map_one]; rfl)
  | rw [map_one]

theorem exists_frobInv_ne_zero (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (jac e τ).IntertwiningMap ρ) (hf : ∃ v, f v ≠ 0) :
    ∃ v, frobInv e hτ f v ≠ 0 := by
  obtain ⟨w, hw⟩ := hf
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  refine ⟨v, fun h => hw ?_⟩
  have h1 := frobInv_one e hτ f v
  rw [h] at h1
  exact h1.symm

theorem exists_map_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin N) k) V) (hτ : IsSmooth τ)
    (f : (jac (stdBlocks (fun a => (x a).1) hd) τ).IntertwiningMap (piTensor fun a => (x a).rep))
    (hf : ∃ v, f v ≠ 0) : ∃ g : τ.IntertwiningMap (prodIrr x hd), ∃ v, g v ≠ 0 := by
  exact ⟨frobInv (stdBlocks (fun a => (x a).1) hd) hτ f, exists_frobInv_ne_zero _ hτ f hf⟩

end GlobalTheory.CompanionTheory.FrobInv

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOnFundamentalDomain
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl PositivityTheory.Affgl.CT Topology Matrix
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.ConstTerm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_map_pFin :
    Continuous (GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd :
    Continuous fun x : InfiniteAdeleRing E × IsDedekindDomain.FiniteAdeleRing (𝓞 E) E => x.2))

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)).comp
    (continuous_fst : Continuous fun x : InfiniteAdeleRing E × IsDedekindDomain.FiniteAdeleRing (𝓞 E) E => x.1)

theorem continuous_map_pInf :
    Continuous (GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf)

theorem continuous_of_isOpen_stab (φ : Sm E a) (hU : IsOpen {k | finRep E a k φ = φ}) : Continuous φ.1 := by
  rw [continuous_iff_continuousAt]
  intro g
  have hF : ContinuousAt (fun h : GA E a => chart φ.1 g (toL (GeneralLinearGroup.map (pInf E) h).val)) 1 := by
    have h1 : ContinuousAt (chart φ.1 g) (toL ((GeneralLinearGroup.map (pInf E) (1 : GA E a)).val)) := by
      rw [map_one]
      exact (contDiffAt_chart φ.2 g isUnit_one).continuousAt
    have h0 : Continuous (fun h : GA E a =>
        ((GeneralLinearGroup.map (n := Fin a) (pInf E) h : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))) :=
      Units.continuous_val.comp continuous_map_pInf
    have h2 : Continuous (fun h : GA E a => toL (GeneralLinearGroup.map (pInf E) h).val) := h0
    exact ContinuousAt.comp (f := fun h : GA E a => toL (GeneralLinearGroup.map (pInf E) h).val) h1 h2.continuousAt
  have hev : ∀ᶠ h in 𝓝 (1 : GA E a), GeneralLinearGroup.map (pFin E) h ∈ {k | finRep E a k φ = φ} := by
    refine (continuous_map_pFin.continuousAt (x := (1 : GA E a))).eventually (hU.mem_nhds ?_)
    rw [map_one]
    change finRep E a 1 φ = φ
    simp
  have hG : ContinuousAt (fun h : GA E a => φ.1 (g * h)) 1 := by
    refine hF.congr ?_
    filter_upwards [hev] with h hh
    have e := congrArg (fun ψ : Sm E a => ψ.1 (g * infGL E a (GeneralLinearGroup.map (pInf E) h))) hh
    change φ.1 (g * infGL E a _ * finGL E a _) = φ.1 _ at e
    rw [mul_assoc, infGL_mul_finGL] at e
    rw [e, chart_val]
  have h2 : ContinuousAt (fun x : GA E a => g⁻¹ * x) g := (continuous_const.mul continuous_id).continuousAt
  have h3 : ContinuousAt (fun h : GA E a => φ.1 (g * h)) (g⁻¹ * g) := by rwa [inv_mul_cancel]
  simpa [Function.comp_def] using h3.comp h2


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_unip : Continuous (unip : (BlockIx a r → Ad E) → GA E a) := by
  have hn : Continuous (fun x : BlockIx a r → Ad E => (nilM x : Matrix (Fin a) (Fin a) (Ad E))) :=
    continuous_matrix fun i j => by
      simp only [nilM, Matrix.of_apply]
      split_ifs with h
      · exact continuous_apply _
      · exact continuous_const
  exact Units.continuous_iff.2 ⟨continuous_const.add hn, continuous_const.sub hn⟩


omit [_root_.NumberField.IsTotallyComplex E] in
theorem exists_isCompact_sub_mem :
    ∃ C : Set (BlockIx a r → Ad E), IsCompact C ∧ ∀ x, ∃ n ∈ ratN E a r, x - n ∈ C := by
  obtain ⟨K, hK, h⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  choose y hy using h
  refine ⟨Set.pi Set.univ fun _ => K, isCompact_univ_pi fun _ => hK, fun x => ?_⟩
  exact ⟨fun p => algebraMap E (Ad E) (y (x p)), ⟨fun p => y (x p), rfl⟩, fun p _ => hy (x p)⟩


omit [_root_.NumberField.IsTotallyComplex E] in
theorem periodic_integrand (φ : GA E a → ℂ) (hl : ∀ (γ : GL (Fin a) E) (g : GA E a), φ (ratGL E a γ * g) = φ g)
    (g : GA E a) {n : BlockIx a r → Ad E} (hn : n ∈ ratN E a r) (x : BlockIx a r → Ad E) :
    φ (unip (n + x) * g) = φ (unip x * g) := by
  obtain ⟨y, rfl⟩ := hn
  have e : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) y =
      fun p => algebraMap E (Ad E) (y p) := rfl
  rw [e, unip_add, unip_algebraMap, mul_assoc, hl]

theorem integrableOn_fundamentalDomain :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (φ : Sm E a),
      (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) →
      IsOpen {k | finRep E a k φ = φ} →
      ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
        (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratN E a r) 𝓕 μ →
        μ 𝓕 < ⊤ ∧ ∀ g : GA E a, IntegrableOn (fun x => φ.1 (unip x * g)) 𝓕 μ := by
  intro E _ _ _ a r φ hl hU _ _ μ 𝓕 hμ hF
  obtain ⟨C, hC, hcov⟩ := exists_isCompact_sub_mem (E := E) (a := a) (r := r)
  have hφ := continuous_of_isOpen_stab φ hU
  haveI : Countable (ratN E a r) := by
    have : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.countable_iff.2 inferInstance
    exact Function.Surjective.countable
      (f := (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)).rangeRestrict)
      (AddMonoidHom.rangeRestrict_surjective _)
  have hfin : μ 𝓕 < ⊤ := by
    have h1 : 𝓕 ⊆ ⋃ n : ratN E a r, (n +ᵥ C) ∩ 𝓕 := fun x hx => by
      obtain ⟨n, hn, h⟩ := hcov x
      refine Set.mem_iUnion.2 ⟨⟨n, hn⟩, ⟨x - n, h, ?_⟩, hx⟩
      simp [AddSubgroup.vadd_def]
    calc μ 𝓕 ≤ ∑' n : ratN E a r, μ ((n +ᵥ C) ∩ 𝓕) := (measure_mono h1).trans (measure_iUnion_le _)
      _ = μ C := (hF.measure_eq_tsum C).symm
      _ < ⊤ := hC.measure_lt_top
  refine ⟨hfin, fun g => ?_⟩
  have hc : Continuous fun x : BlockIx a r → Ad E => φ.1 (unip x * g) :=
    hφ.comp (continuous_unip.mul continuous_const)
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  refine Measure.integrableOn_of_bounded hfin.ne hc.aestronglyMeasurable (M := B) (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨n, hn, h⟩ := hcov x
  have := periodic_integrand φ.1 hl g hn (x - n)
  rw [add_sub_cancel] at this
  rw [this]
  exact hB _ h

end GlobalTheory.CompanionTheory.ConstTerm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LaplacianCasimirRelation
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.FcSmooth

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_sub_fun (X : Mat n) {u v : Mat n → V} (hu : ContDiffOn ℝ ∞ u (GLs n)) (hv : ContDiffOn ℝ ∞ v (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (fun y => u y - v y) g = Rd X u g - Rd X v g := by
  have h1 := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hu hg
  have h2 := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hv hg
  exact DFunLike.congr_fun (h1.hasFDerivAt.sub h2.hasFDerivAt).fderiv (g * X)

theorem Rd_add_fun (X : Mat n) {u v : Mat n → V} (hu : ContDiffOn ℝ ∞ u (GLs n)) (hv : ContDiffOn ℝ ∞ v (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (fun y => u y + v y) g = Rd X u g + Rd X v g := by
  have h1 := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hu hg
  have h2 := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hv hg
  exact DFunLike.congr_fun (h1.hasFDerivAt.add h2.hasFDerivAt).fderiv (g * X)

theorem Rd_sq_sub (X X' : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd (X - X') (Rd (X - X') f) g =
      Rd X (Rd X f) g - Rd X (Rd X' f) g - (Rd X' (Rd X f) g - Rd X' (Rd X' f) g) := by
  have e : Rd (X - X') f = fun y => Rd X f y - Rd X' f y := funext fun y => GlobalTheory.CompanionTheory.SecBd.Rd_sub X X' f y
  have h1 := GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf
  have h2 := GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X' hf
  rw [e, GlobalTheory.CompanionTheory.SecBd.Rd_sub, Rd_sub_fun X h1 h2 hg, Rd_sub_fun X' h1 h2 hg]

theorem Rd_sq_add (X X' : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd (X + X') (Rd (X + X') f) g =
      Rd X (Rd X f) g + Rd X (Rd X' f) g + (Rd X' (Rd X f) g + Rd X' (Rd X' f) g) := by
  have e : Rd (X + X') f = fun y => Rd X f y + Rd X' f y := funext fun y => GlobalTheory.CompanionTheory.SecBd.Rd_add X X' f y
  have h1 := GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf
  have h2 := GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X' hf
  rw [e, GlobalTheory.CompanionTheory.SecBd.Rd_add, Rd_add_fun X h1 h2 hg, Rd_add_fun X' h1 h2 hg]

abbrev skY (a c : Fin n) : Mat n := Matrix.single a c (1 : ℂ) - Matrix.single c a (1 : ℂ)

abbrev skZ (a c : Fin n) : Mat n := Matrix.single a c Complex.I + Matrix.single c a Complex.I

theorem Lap_eq (hO : OmFormula) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Lap f g = -Om f g + (-(1 / 2 : ℂ)) • ∑ a, ∑ c,
      (Rd (skY a c) (Rd (skY a c) f) g + Rd (skZ a c) (Rd (skZ a c) f) g) := by
  set P : Fin n → Fin n → V := fun a c =>
    Rd (Matrix.single a c (1 : ℂ)) (Rd (Matrix.single a c (1 : ℂ)) f) g with hP
  set Q : Fin n → Fin n → V := fun a c =>
    Rd (Matrix.single a c Complex.I) (Rd (Matrix.single a c Complex.I) f) g with hQ
  set M : Fin n → Fin n → V := fun a c =>
    Rd (Matrix.single a c (1 : ℂ)) (Rd (Matrix.single c a (1 : ℂ)) f) g with hM
  set N : Fin n → Fin n → V := fun a c =>
    Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a Complex.I) f) g with hN
  have hY : ∀ a c, Rd (skY a c) (Rd (skY a c) f) g = P a c - M a c - (M c a - P c a) := fun a c =>
    Rd_sq_sub _ _ hf hg
  have hZ : ∀ a c, Rd (skZ a c) (Rd (skZ a c) f) g = Q a c + N a c + (N c a + Q c a) := fun a c =>
    Rd_sq_add _ _ hf hg
  have hS : ∑ p, Rd (bs p) (Rd (bs p) f) g = ∑ a, ∑ c, P a c + ∑ a, ∑ c, Q a c := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, GlobalTheory.CompanionTheory.SecBd.basis_true_eq_single, GlobalTheory.CompanionTheory.SecBd.bs_f,
      Finset.sum_add_distrib, hP, hQ]
  have hOm : Om f g = ∑ a, ∑ c, M a c - ∑ a, ∑ c, N a c := by
    rw [hO n V f hf g hg]
    simp only [Finset.sum_sub_distrib, hM, hN]
  have swap : ∀ F : Fin n → Fin n → V, ∑ a, ∑ c, F c a = ∑ a, ∑ c, F a c := fun F => Finset.sum_comm
  have hT : ∑ a, ∑ c, (Rd (skY a c) (Rd (skY a c) f) g + Rd (skZ a c) (Rd (skZ a c) f) g) =
      (2 : ℂ) • (∑ a, ∑ c, P a c) - (2 : ℂ) • (∑ a, ∑ c, M a c) +
        ((2 : ℂ) • (∑ a, ∑ c, Q a c) + (2 : ℂ) • (∑ a, ∑ c, N a c)) := by
    simp only [hY, hZ, Finset.sum_add_distrib, Finset.sum_sub_distrib, swap M, swap P, swap N, swap Q]
    module
  show -∑ p, Rd (bs p) (Rd (bs p) f) g = _
  rw [hS, hOm, hT]
  module

theorem lap_sec : ∀ (n : ℕ) (E : KMod n), RCalc → OmFormula → ∃ Q : E.V →L[ℂ] E.V, ∀ f ∈ CE E, ∀ g ∈ GLs n,
    GlobalTheory.CompanionTheory.FcSmooth.Lap f g = -Om f g + Q (f g) := by
  intro n E _ hO
  choose BY hBY using fun a c : Fin n => GlobalTheory.CompanionTheory.WaveSpd.rd_skew_eq_const E _ (GlobalTheory.CompanionTheory.SecBd.skewY a c)
  choose BZ hBZ using fun a c : Fin n => GlobalTheory.CompanionTheory.WaveSpd.rd_skew_eq_const E _ (GlobalTheory.CompanionTheory.SecBd.skewZ a c)
  have sq : ∀ (Y : Mat n) (B : E.V →L[ℂ] E.V), (∀ f ∈ CE E, ∀ g ∈ GLs n, Rd Y f g = B (f g)) →
      ∀ f ∈ CE E, ∀ g ∈ GLs n, Rd Y (Rd Y f) g = (B * B) (f g) := by
    intro Y B h f hf g hg
    have e : Set.EqOn (Rd Y f) (fun y => B (f y)) (GLs n) := fun y hy => h f hf y hy
    rw [GlobalTheory.CompanionTheory.RCalc.Rd_congr Y e hg, GlobalTheory.CompanionTheory.SobOpsPf.Rd_post Y B hf.1 hg, h f hf g hg]
    rfl
  refine ⟨(-(1 / 2 : ℂ)) • ∑ a, ∑ c, (BY a c * BY a c + BZ a c * BZ a c), fun f hf g hg => ?_⟩
  rw [Lap_eq hO hf.1 hg]
  congr 1
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [sq _ _ (hBY a c) f hf g hg, sq _ _ (hBZ a c) f hf g hg]

end GlobalTheory.CompanionTheory.FcSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientIntegrableSquareStatement
section
open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coefficient_integrable_square : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (ρ : Γ → (B →L[ℂ] B)), IsU ρ → ∀ v : B, Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν → ∀ b : B,
    Integrable (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) ν ∧
    ∫ g, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.GodementCoeff.sq_integrable_and_bound | exact GlobalTheory.CompanionTheory.GodementCoeff.sq_integrable_and_bound | (intros; apply GlobalTheory.CompanionTheory.GodementCoeff.sq_integrable_and_bound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MoyPrasadJacquetIso
section
noncomputable section

namespace GlobalTheory.CompanionTheory.MoyPrasadTop

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead _root_.Topology

theorem moyPrasadJacquetIso : GlobalTheory.Published.MoyPrasadJacquetIso := by
  intro k _ _ _ _ n s d e V _ _ π hπ
  refine ⟨mapsTo_fixed_jacU e π _, ?_, ?_⟩
  · intro v hv w hw h
    have h0 : (Submodule.Quotient.mk (v - w) : Jacquet π (unipRad k e)) = 0 := by
      rw [Submodule.Quotient.mk_sub]
      exact sub_eq_zero.2 h
    exact sub_eq_zero.1 (GlobalTheory.CompanionTheory.DepthZeroJac.fixed_inj_smooth k n s d e V π hπ.1 (v - w) (sub_mem hv hw) h0)
  · intro y hy
    obtain ⟨v, hv, hvy⟩ := GlobalTheory.CompanionTheory.JacquetCentral.exists_fixed_mk_eq_of_commute π hπ (Gx k e) (unipRad k e) (GlobalTheory.CompanionTheory.MoyPrasad.isOpen_Gx k n s d e)
      (_root_.GlobalTheory.CompanionTheory.MoyPrasad.isCompact_Gx k n s d e) (leviEmb k e) (leviEmb_mem_normalizer k e) ((Gx k e).comap (leviEmb k e))
      (fun _ hm => hm) (lowC k e) (_root_.GlobalTheory.CompanionTheory.MoyPrasad.factor_Gx k n s d e)
      (fun U hU => by
        refine (_root_.GlobalTheory.CompanionTheory.MoyPrasad.lowC_central_contract k n s d e U hU).imp ?_
        intro t ht
        exact ⟨fun m _ => ht.1 m, ht.2⟩) y hy
    exact ⟨v, hv, hvy⟩

end GlobalTheory.CompanionTheory.MoyPrasadTop

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingRestrictionNaturalStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_restriction_natural : MVBij → ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] (P : ℕ → Cx.{1} K) (Q T : ℕ → Sy.{1} K ι) (pr : ∀ (S : Finset ι) {a a' c : ℕ}, a + a' = c → CxPairing (P a) ((Q a').K S) ((T c).K S)), (∀ {S S' : Finset ι} (h : S ⊆ S') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : (P a).X i) (y : ((Q a').K S).X j), ((T c).res h).f n ((pr S ha).μ hn x y) = (pr S' ha).μ hn x (((Q a').res h).f j y)) → (∀ a, (Q a).Desc) → (∀ c, (T c).Desc) → (∀ S : Finset ι, S.Nonempty → KunE (P := P) (Q := fun a => (Q a).K S) (T := fun c => (T c).K S) (fun {a a' c} ha => pr S ha)) → KunE (P := P) (Q := fun a => (Q a).K ∅) (T := fun c => (T c).K ∅) (fun {a a' c} ha => pr ∅ ha) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.kun_glue | exact GlobalTheory.CompanionTheory.KunGlue.kun_glue | (intros; apply GlobalTheory.CompanionTheory.KunGlue.kun_glue <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentTermInjective
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegTerm

theorem term_injective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) : Function.Injective Δ.term :=
  Segment.term_injective Δ

end GlobalTheory.CompanionTheory.SegTerm
end

