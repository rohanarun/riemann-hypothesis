module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0494
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0499
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0488

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnDifferentiableOnIntegral
section
open MeasureTheory Filter
open scoped Topology

namespace GlobalTheory.CompanionTheory.Param

theorem continuousOn_differentiableOn_integral :
    ∀ {Y T : Type} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
      [TopologicalSpace T] [FirstCountableTopology T] (μ : Measure Y) (U : Set ℂ), IsOpen U →
      ∀ F : ℂ → T → Y → ℂ,
      ContinuousOn (fun u : ℂ × T × Y => F u.1 u.2.1 u.2.2) (U ×ˢ Set.univ) →
      (∀ t y, DifferentiableOn ℂ (fun z => F z t y) U) →
      (∀ z₀ ∈ U, ∀ t₀ : T, ∃ V ∈ 𝓝 z₀, ∃ N ∈ 𝓝 t₀, ∃ w : Y → ℝ, Integrable w μ ∧
        ∀ z ∈ V, ∀ t ∈ N, ∀ y, ‖F z t y‖ ≤ w y) →
      ContinuousOn (fun u : ℂ × T => ∫ y, F u.1 u.2 y ∂μ) (U ×ˢ Set.univ) ∧
        ∀ t, DifferentiableOn ℂ (fun z => ∫ y, F z t y ∂μ) U := by
  intro Y T _ _ _ _ _ μ U hU F hF hdiff hdom
  have hGat : ∀ z ∈ U, ∀ (t : T) (y : Y),
      ContinuousAt (fun u : ℂ × T × Y => F u.1 u.2.1 u.2.2) (z, t, y) := fun z hz t y =>
    hF.continuousAt ((hU.prod isOpen_univ).mem_nhds (Set.mk_mem_prod hz (Set.mem_univ _)))
  have hslice : ∀ z ∈ U, ∀ t : T, Continuous (fun y => F z t y) := fun z hz t =>
    hF.comp_continuous (f := fun y : Y => (z, t, y)) (by fun_prop)
      fun y => Set.mk_mem_prod hz (Set.mem_univ _)
  refine ⟨?_, fun t => ?_⟩
  · rintro ⟨z₀, t₀⟩ ⟨hz₀, -⟩
    obtain ⟨V, hV, N, hN, w, hw, hbound⟩ := hdom z₀ hz₀ t₀
    refine ContinuousAt.continuousWithinAt ?_
    refine MeasureTheory.continuousAt_of_dominated (bound := w) ?_ ?_ hw ?_
    · have hmem : U ×ˢ (Set.univ : Set T) ∈ 𝓝 (z₀, t₀) :=
        (hU.prod isOpen_univ).mem_nhds (Set.mk_mem_prod hz₀ (Set.mem_univ _))
      filter_upwards [hmem] with x hx
      exact (hslice x.1 hx.1 x.2).aestronglyMeasurable
    · have hmem : V ×ˢ N ∈ 𝓝 (z₀, t₀) := by
        rw [nhds_prod_eq]
        exact Filter.prod_mem_prod hV hN
      filter_upwards [hmem] with x hx
      exact Filter.Eventually.of_forall fun y => hbound x.1 hx.1 x.2 hx.2 y
    · exact Filter.Eventually.of_forall fun y =>
        ContinuousAt.comp_of_eq (f := fun x : ℂ × T => (x.1, x.2, y)) (hGat z₀ hz₀ t₀ y)
          (by fun_prop) rfl
  · obtain ⟨h, -⟩ := GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated (μ := μ)
      (F := fun y z => F z t y) hU (fun z hz => (hslice z hz t).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => hdiff t y) (fun z hz => by
        obtain ⟨V, hV, N, hN, w, hw, hb⟩ := hdom z hz t
        exact ⟨V, hV, w, hw, Filter.Eventually.of_forall fun y z' hz' =>
          hb z' hz' t (mem_of_mem_nhds hN) y⟩)
    exact h

end GlobalTheory.CompanionTheory.Param
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneColumnJoinProduct
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.ProdCovol

open scoped Pointwise

theorem isAddFundamentalDomain_prod {A B : Type*} [AddGroup A] [AddGroup B] [MeasurableSpace A]
    [MeasurableSpace B] {Γ : AddSubgroup A} {Δ : AddSubgroup B} {μ : Measure A} {ν : Measure B} [SFinite μ]
    [SFinite ν] {s : Set A} {t : Set B} (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) := by
  refine ⟨hs.nullMeasurableSet.prod ht.nullMeasurableSet, ?_, ?_⟩
  · have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hs.ae_covers
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae ht.ae_covers
    filter_upwards [h1, h2] with p hp hq
    obtain ⟨g, hg⟩ := hp
    obtain ⟨h, hh⟩ := hq
    exact ⟨⟨((g : A), (h : B)), AddSubgroup.mem_prod.2 ⟨g.2, h.2⟩⟩, hg, hh⟩
  · intro g h hgh
    change μ.prod ν ((g +ᵥ s ×ˢ t) ∩ (h +ᵥ s ×ˢ t)) = 0
    let g1 : Γ := ⟨(g : A × B).1, (AddSubgroup.mem_prod.1 g.2).1⟩
    let h1 : Γ := ⟨(h : A × B).1, (AddSubgroup.mem_prod.1 h.2).1⟩
    let g2 : Δ := ⟨(g : A × B).2, (AddSubgroup.mem_prod.1 g.2).2⟩
    let h2 : Δ := ⟨(h : A × B).2, (AddSubgroup.mem_prod.1 h.2).2⟩
    by_cases e1 : g1 = h1
    · have e2 : g2 ≠ h2 := fun e2 => hgh (Subtype.ext (Prod.ext (congrArg Subtype.val e1) (congrArg Subtype.val e2)))
      have h0 : ν ((g2 +ᵥ t) ∩ (h2 +ᵥ t)) = 0 := ht.aedisjoint e2
      refine measure_mono_null (t := Set.univ ×ˢ ((g2 +ᵥ t) ∩ (h2 +ᵥ t))) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨Set.mem_univ _, ?_, ?_⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.2
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.2
      · rw [Measure.prod_prod, h0, mul_zero]
    · have h0 : μ ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) = 0 := hs.aedisjoint e1
      refine measure_mono_null (t := ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) ×ˢ Set.univ) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.1
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.1
      · rw [Measure.prod_prod, h0, zero_mul]

variable {D : D7} {m r s : ℕ}

def joinAdd (D : D7) (m r s : ℕ) : Mx D m r × Mx D m s ≃+ Mx D m (r + s) :=
  { joinEquiv with map_add' := fun a b => colJoin_add a.1 b.1 a.2 b.2 }

theorem joinAdd_apply (z : Mx D m r × Mx D m s) : joinAdd D m r s z = colJoin z.1 z.2 := rfl

theorem continuous_joinAdd : Continuous (joinAdd D m r s) := by
  refine continuous_matrix fun i k => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · have : (fun z : Mx D m r × Mx D m s => joinAdd D m r s z i (Fin.castAdd s j)) = fun z => z.1 i j :=
      funext fun z => colJoin_castAdd z.1 z.2 i j
    rw [this]
    exact (continuous_apply_apply i j).comp continuous_fst
  · have : (fun z : Mx D m r × Mx D m s => joinAdd D m r s z i (Fin.natAdd r j)) = fun z => z.2 i j :=
      funext fun z => colJoin_natAdd z.1 z.2 i j
    rw [this]
    exact (continuous_apply_apply i j).comp continuous_snd

theorem continuous_joinAdd_symm : Continuous (joinAdd D m r s).symm := by
  refine Continuous.prodMk ?_ ?_
  · exact continuous_matrix fun i j => continuous_apply_apply i (Fin.castAdd s j)
  · exact continuous_matrix fun i j => continuous_apply_apply i (Fin.natAdd r j)

theorem joinAdd_mem_iff (z : Mx D m r × Mx D m s) :
    joinAdd D m r s z ∈ ratMx D m (r + s) ↔ z ∈ (ratMx D m r).prod (ratMx D m s) := by
  rw [AddSubgroup.mem_prod]
  constructor
  · rintro h
    obtain ⟨γ, hγ⟩ := mem_ratMx.1 h
    refine ⟨mem_ratMx.2 ⟨colL γ, ?_⟩, mem_ratMx.2 ⟨colR γ, ?_⟩⟩
    · ext i j
      have := congrFun (congrFun hγ i) (Fin.castAdd s j)
      rw [joinAdd_apply, colJoin_castAdd] at this
      exact this
    · ext i j
      have := congrFun (congrFun hγ i) (Fin.natAdd r j)
      rw [joinAdd_apply, colJoin_natAdd] at this
      exact this
  · rintro ⟨h1, h2⟩
    obtain ⟨p, hp⟩ := mem_ratMx.1 h1
    obtain ⟨q, hq⟩ := mem_ratMx.1 h2
    exact mem_ratMx.2 ⟨colJoin p q, by rw [rat_colJoin, hp, hq, joinAdd_apply]⟩

theorem isCovolOne_colJoin : ∀ (D : D7) (m r s : ℕ) (μr : Measure (Mx D m r)) (𝓕r : Set (Mx D m r))
    (μs : Measure (Mx D m s)) (𝓕s : Set (Mx D m s)), IsCovolOne (ratMx D m r) μr 𝓕r → IsCovolOne (ratMx D m s) μs 𝓕s →
    IsCovolOne (ratMx D m (r + s)) ((μr.prod μs).map fun z => colJoin z.1 z.2)
      ((fun z : Mx D m r × Mx D m s => colJoin z.1 z.2) '' (𝓕r ×ˢ 𝓕s)) := by
  intro D m r s μr 𝓕r μs 𝓕s hr hs
  obtain ⟨a1, a2, a3, a4, a5, -⟩ := lattice_Mx D m r
  obtain ⟨b1, b2, b3, b4, b5, -⟩ := lattice_Mx D m s
  obtain ⟨c1, c2, c3, c4, c5, -⟩ := lattice_Mx D m (r + s)
  haveI : BorelSpace (Mx D m r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D m s) := ⟨rfl⟩
  haveI : BorelSpace (Mx D m (r + s)) := ⟨rfl⟩
  obtain ⟨hHr, hFr, h1r⟩ := hr
  obtain ⟨hHs, hFs, h1s⟩ := hs
  haveI := hHr
  haveI := hHs
  let e := joinAdd D m r s
  have he : Continuous e := continuous_joinAdd
  have he' : Continuous e.symm := continuous_joinAdd_symm
  let f : (Mx D m r × Mx D m s) ≃ₜ Mx D m (r + s) :=
    { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  have hemb : MeasurableEmbedding e := f.measurableEmbedding
  have hfun : (fun z : Mx D m r × Mx D m s => colJoin z.1 z.2) = e := rfl
  rw [hfun]
  refine ⟨e.isAddHaarMeasure_map _ he he', ?_, ?_⟩
  · let g : ratMx D m (r + s) ≃ (ratMx D m r).prod (ratMx D m s) :=
      { toFun := fun γ => ⟨e.symm γ, (joinAdd_mem_iff _).1 (by
          change e (e.symm γ) ∈ _
          rw [e.apply_symm_apply]; exact γ.2)⟩
        invFun := fun γ => ⟨e γ, (joinAdd_mem_iff _).2 γ.2⟩
        left_inv := fun γ => Subtype.ext (e.apply_symm_apply _)
        right_inv := fun γ => Subtype.ext (e.symm_apply_apply _) }
    refine (isAddFundamentalDomain_prod hFr hFs).image_of_equiv e.toEquiv ?_ g fun γ x => ?_
    · refine ⟨he'.measurable.aemeasurable, ?_⟩
      have : ((μr.prod μs).map e).map e.symm = μr.prod μs := by
        rw [Measure.map_map he'.measurable he.measurable]
        have : (e.symm ∘ e : Mx D m r × Mx D m s → Mx D m r × Mx D m s) = id := funext e.symm_apply_apply
        rw [this, Measure.map_id]
      exact this.absolutelyContinuous
    · change e (e.symm γ + x) = γ + e x
      rw [map_add (f := _), e.apply_symm_apply]
  · rw [hemb.map_apply, Set.preimage_image_eq _ e.injective, Measure.prod_prod, h1r, h1s, one_mul]

end GlobalTheory.CompanionTheory.EisUnfold.ProdCovol

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
section
noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame NumberField IsDedekindDomain MeasureTheory _root_.Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def tupIn {M n : ℕ} (L : Set (R ⊗[F] E)) : Set (Fin n → Fin M → R ⊗[F] E) :=
  {X | ∀ i k, X i k ∈ L}

def eMat {n : ℕ} (l : Fin n) (a : Fin n → R ⊗[F] E) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)).updateCol l a

def dMat {n : ℕ} (l : Fin n) (s : R ⊗[F] E) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  Matrix.diagonal (Function.update 1 l s)

def cjM (σ : E →ₐ[F] E) {n : ℕ} (g y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (g.map (sigR R σ))ᵀ * y * g

def nearNF {M n : ℕ} (O L : Set (R ⊗[F] E)) (t : R ⊗[F] E) (j : ℕ) : Set (Fin n → Fin M → R ⊗[F] E) :=
  {X | X ∈ tupIn R L ∧ ∃ (l : Fin n) (a : Fin n → R ⊗[F] E), (∀ i, a i ∈ O) ∧ a l = 1 ∧
    ∀ k, ∑ i, X i k * a i ∈ (fun x => t ^ j * x) '' L}

def goodT {M n : ℕ} (O L : Set (R ⊗[F] E)) (S : Finset ((R ⊗[F] E)ˣ × (R ⊗[F] E))) (j : ℕ) :
    Set (Fin n → Fin M → R ⊗[F] E) :=
  tupIn R L \ ⋃ p ∈ S, nearNF R O L (p.1 : R ⊗[F] E) j

def gramIn (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (Y : Set (HermR R σ n)) :
    Set (Fin n → Fin M → R ⊗[F] E) :=
  {X | ∃ y ∈ Y, gramR R σ J X = (y : Matrix (Fin n) (Fin n) (R ⊗[F] E))}

def cjPre (σ : E →ₐ[F] E) {n : ℕ} (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (Y : Set (HermR R σ n)) :
    Set (HermR R σ n) :=
  {y | ∃ z ∈ Y, cjM R σ g (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = (z : Matrix (Fin n) (Fin n) (R ⊗[F] E))}

variable [TopologicalSpace R] [MeasurableSpace R]

def IsOrdData (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (O : Subring (R ⊗[F] E)) (S : Finset ((R ⊗[F] E)ˣ × (R ⊗[F] E))) : Prop :=
  IsCompact (O : Set (R ⊗[F] E)) ∧ IsOpen (O : Set (R ⊗[F] E)) ∧ (∀ x ∈ O, sigR R σ x ∈ O) ∧
  (∀ p ∈ S, (p.1 : R ⊗[F] E) ∈ O ∧ p.2 ≠ 0 ∧ (∀ x, p.2 * x = 0 → (p.1 : R ⊗[F] E) * x = x) ∧
    Filter.Tendsto (fun j : ℕ => p.2 * (p.1 : R ⊗[F] E) ^ j) Filter.atTop (nhds 0) ∧
    ∃ θ : ℝ≥0, θ < 1 ∧ ∀ Y : Set (R ⊗[F] E),
      coordK R b lam ((fun x => (p.1 : R ⊗[F] E) * x) '' Y) = θ * coordK R b lam Y) ∧
  ∀ (n M : ℕ) (X : Fin n → Fin M → R ⊗[F] E), ¬ LinearIndependent (R ⊗[F] E) X →
    ∃ p ∈ S, ∃ (l : Fin n) (a : Fin n → R ⊗[F] E), (∀ i, a i ∈ O) ∧ a l = 1 ∧
      ∀ k, p.2 * ∑ i, X i k * a i = 0

end Alg

section Help

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem rmul_mul {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (g h : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    rmul R (rmul R X g) h = rmul R X (g * h) := by
  funext a i
  simp only [rmul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => mul_assoc _ _ _

theorem hR_sum_right (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin M → R ⊗[F] E)
    (y : Fin n → Fin M → R ⊗[F] E) (w : Fin n → R ⊗[F] E) :
    hR R σ J x (fun k => ∑ e, y e k * w e) = ∑ e, hR R σ J x (y e) * w e := by
  simp only [hR, hform, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hR_sum_left (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin n → Fin M → R ⊗[F] E)
    (y : Fin M → R ⊗[F] E) (w : Fin n → R ⊗[F] E) :
    hR R σ J (fun k => ∑ c, x c k * w c) y = ∑ c, sigR R σ (w c) * hR R σ J (x c) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, hform, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem gramR_rmul (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    gramR R σ J (rmul R X g) = cjM R σ g (gramR R σ J X) := by
  ext a c
  change hR R σ J (fun i => ∑ e, X e i * g e a) (fun i => ∑ e, X e i * g e c) = _
  rw [hR_sum_right]
  simp only [hR_sum_left]
  rfl

theorem cjM_mul (σ : E →ₐ[F] E) {n : ℕ} (g h y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    cjM R σ (g * h) y = cjM R σ h (cjM R σ g y) := by
  simp only [cjM, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem cjM_one (σ : E →ₐ[F] E) {n : ℕ} (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    cjM R σ 1 y = y := by
  simp [cjM, Matrix.map_one, map_zero, map_one]

theorem cjM_mem (σ : E →ₐ[F] E) (hσ : ∀ x, sigR R σ (sigR R σ x) = x) {n : ℕ}
    (g y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (hy : y ∈ HermR R σ n) : cjM R σ g y ∈ HermR R σ n := by
  intro a c
  have hy' : ∀ a c, sigR R σ (y c a) = y a c := hy
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cjM, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_mul, hσ, hy']
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def negCol {n : ℕ} (l : Fin n) (a : Fin n → R ⊗[F] E) : Fin n → R ⊗[F] E :=
  fun i => if i = l then 1 else - a i

theorem eMat_mul_negCol {n : ℕ} (l : Fin n) (a : Fin n → R ⊗[F] E) (hl : a l = 1) :
    eMat R l a * eMat R l (negCol R l a) = 1 := by
  ext i k
  simp only [Matrix.mul_apply, eMat, Matrix.updateCol_apply, Matrix.one_apply]
  by_cases hk : k = l
  · subst hk
    simp only [if_true, negCol]
    have : ∀ c, (if c = k then a i else if i = c then (1 : R ⊗[F] E) else 0) * (if c = k then 1 else - a c) =
        (if c = k then a i else 0) + (if c = i then (if i = k then 0 else - a i) else 0) := by
      intro c
      by_cases h1 : c = k
      · subst h1
        by_cases h2 : c = i
        · subst h2; simp
        · simp [h2]
      · by_cases h2 : c = i
        · subst h2; simp [h1]
        · simp [h1, h2, Ne.symm h2]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h : i = k
    · subst h; simp [hl]
    · simp [h]
  · simp only [hk, if_false]
    have : ∀ c, (if c = l then a i else if i = c then (1 : R ⊗[F] E) else 0) * (if c = k then 1 else 0) =
        if c = k then (if i = k then 1 else 0) else 0 := by
      intro c
      by_cases h1 : c = k
      · subst h1; simp [hk]
      · simp [h1]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem dMat_mul {n : ℕ} (l : Fin n) (s t : R ⊗[F] E) (h : s * t = 1) : dMat R l s * dMat R l t = 1 := by
  rw [dMat, dMat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases hi : i = l
  · subst hi; simpa using h
  · simp [Function.update_of_ne hi]

theorem sigR_sigR (σ : E →ₐ[F] E) (h : ∀ e, σ (σ e) = e) (x : R ⊗[F] E) : sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, h]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem isCompact_tupIn [TopologicalSpace (R ⊗[F] E)] {M n : ℕ} {L : Set (R ⊗[F] E)} (hL : IsCompact L) :
    IsCompact (tupIn (M := M) (n := n) R L) := by
  have : tupIn (M := M) (n := n) R L = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => L := by
    ext X
    simp [tupIn]
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hL

end Help

end GlobalTheory.CompanionTheory.AvgFree
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHermitianIntegralUnfolding
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.NegStep

theorem integral_neg_of_secondCountable {G E : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure G) [μ.IsAddHaarMeasure] (f : G → E) :
    ∫ x, f (-x) ∂μ = ∫ x, f x ∂μ := by
  have : μ.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μ
  exact integral_neg_eq_self f μ

theorem colJoin_zero_mul {R : Type*} [NonUnitalNonAssocSemiring R] {m r s : ℕ} (p : Matrix (Fin m) (Fin r) R)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) R) (c : Matrix (Fin r) (Fin (r + s)) R)
    (h : ∀ j : Fin r, a (Fin.castAdd s j) = c j) :
    colJoin p (0 : Matrix (Fin m) (Fin s) R) * a = p * c := by
  ext i k
  simp [Matrix.mul_apply, Fin.sum_univ_add, h]

theorem inner_neg_neg {D : D7} (V : HSp D) {n : ℕ} (t : Mx D V.rank n) : inner V (-t) (-t) = inner V t t := by
  unfold GlobalTheory.StdUnn.inner
  rw [adj_neg]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]

theorem integral_colJoin_neg_eq_J : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (r s : ℕ) (μr : Measure (Mx D V.rank r))
    (𝓕r : Set (Mx D V.rank r)), IsCovolOne (ratMx D V.rank r) μr 𝓕r →
    ∀ (c : Matrix (Fin r) (Fin (r + s)) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsCompl c a →
    ∀ (b : HermE D r) (Φ : Mx D V.rank (r + s) → ℂ),
      ∫ t, ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) ∂μr = J ψ V μr (pull c Φ) b := by
  intro D ψ V r s μr 𝓕r hcov c a hca b Φ
  obtain ⟨h1, h2, h3, h4, -⟩ := lattice_Mx D V.rank r
  have hB : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  have hH : μr.IsAddHaarMeasure := hcov.1
  have hrow : ∀ j : Fin r, rat a (Fin.castAdd s j) = rat c j := by
    intro j
    have := hca.2 (Fin.castAdd s j) j.isLt
    funext k
    show incA D (a (Fin.castAdd s j) k) = incA D (c j k)
    rw [this]
    rfl
  have key : ∀ t : Mx D V.rank r,
      ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) =
      (fun y : Mx D V.rank r => pull c Φ y * ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V y y) : Mx D r r)))) (-t) := by
    intro t
    have e : (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a) : Mx D V.rank (r + s)) = HMul.hMul (-t) (rat c) :=
      colJoin_zero_mul (-t) (rat a) (rat c) hrow
    show _ = Φ (HMul.hMul (-t) (rat c)) * _
    rw [e, inner_neg_neg, mul_comm]
  exact (integral_congr_ae (Filter.Eventually.of_forall key)).trans
    (integral_neg_of_secondCountable (E := ℂ) μr
      (fun y : Mx D V.rank r => pull c Φ y * ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V y y) : Mx D r r)))))

end GlobalTheory.CompanionTheory.EisUnfold.NegStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLubinTateCharacterUnitary
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTHodge

theorem exists_lubinTateChar : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l), ∃ χ : ↥(GK K) →* (↥K.1)ˣ, IsLTChar K χ ∧
    Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) ∧ ∀ g, ‖(((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)‖ = 1 :=
  fun K => GlobalTheory.CompanionTheory.LTHodge.CharEx.exists_ltChar K

end GlobalTheory.CompanionTheory.LTHodge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterEtaCondition
section
open PositivityTheory.Rg.Rsw

namespace GlobalTheory.CompanionTheory.HeckeEtaExist

theorem heckeEta : HeckeEta :=
  GlobalTheory.RawLift.exists_hecke_resEta

end GlobalTheory.CompanionTheory.HeckeEtaExist
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleBoundOfJointAnisotropicStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_bound_of_joint_anisotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (M : Type) [Finite M] (H : M → Matrix (Fin n) (Fin n) E) (L : Set (GAd σ J)), (∀ ξ : Fin n → E, (∀ j, hE σ (H j) ξ ξ = 0) → ξ = 0) → (∀ g ∈ L, ∀ j, ∃ s : GroundTheory.Global.IdeleGroup F, 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule F s : ℝ) ∧ ∀ ξ : Fin n → E, hR (AF F) σ (H j) ((matHom _ σ J g⁻¹).1 *ᵥ ratV F ξ) ((matHom _ σ J g⁻¹).1 *ᵥ ratV F ξ) = algebraMap (AF F) (AF F ⊗[F] E) (s : AF F) * inclR (F := F) (AF F) (hE σ (H j) ξ ξ)) → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ L, ∀ ξ : Fin n → E, ξ ≠ 0 → ε ≤ hgt σ J g ξ := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.FormHeight.exists_pos_le_hgt_of_forms | exact GlobalTheory.CompanionTheory.ParCocompact.FormHeight.exists_pos_le_hgt_of_forms | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.FormHeight.exists_pos_le_hgt_of_forms <;> assumption)
end

