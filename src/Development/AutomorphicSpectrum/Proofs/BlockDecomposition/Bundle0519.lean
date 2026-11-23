module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ProperRatH
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0497
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0499

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactIsOpenCosVN
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.PfSWUS.FockSplit.Box

open NumberField IsDedekindDomain GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec
open PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport
open scoped _root_.Topology

variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def lvN (v : HeightOneSpectrum (𝓞 F)) (P : AddSubgroup (Fv F v)) (n M : ℕ) :
    AddSubgroup (Fin n → Fin M → Fv F v ⊗[F] E) where
  carrier := {Z | ∀ a i k, crd b (Fv F v) (Z a i) k ∈ P}
  add_mem' hx hy a i k := by
    rw [Pi.add_apply, Pi.add_apply, crd_add]
    exact add_mem (hx a i k) (hy a i k)
  zero_mem' a i k := by
    rw [Pi.zero_apply, Pi.zero_apply, crd_zero]
    exact zero_mem P
  neg_mem' hx a i k := by
    rw [Pi.neg_apply, Pi.neg_apply, crd_neg]
    exact neg_mem (hx a i k)

theorem isClopen_lvN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) (n M : ℕ) :
    IsClopen (lvN b v (P : AddSubgroup (Fv F v)) n M : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  have hc : ∀ (x : Fin n) (i : Fin M) (k : Fin d),
      Continuous (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k) :=
    fun x i k => (continuous_crd b (Fv F v) k).comp ((continuous_apply i).comp (continuous_apply x))
  have e : (lvN b v (P : AddSubgroup (Fv F v)) n M : Set (Fin n → Fin M → Fv F v ⊗[F] E)) = ⋂ x, ⋂ i, ⋂ k,
      (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k) ⁻¹' (P : Set (Fv F v)) := by
    ext Y
    simp [lvN]
  rw [e]
  exact ⟨isClosed_iInter fun x => isClosed_iInter fun i => isClosed_iInter fun k =>
    P.isClosed.preimage (hc x i k), isOpen_iInter_of_finite fun x =>
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => P.isOpen.preimage (hc x i k)⟩

theorem isCompact_lvN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) (hP : P ≤ intSub v) (n M : ℕ) :
    IsCompact (lvN b v (P : AddSubgroup (Fv F v)) n M : Set (Fin n → Fin M → Fv F v ⊗[F] E)) :=
  (isCompact_latV b v n M).of_isClosed_subset (isClopen_lvN b v P n M).isClosed
    fun _ hZ a i k => hP (hZ a i k)

theorem projV_subN (v : HeightOneSpectrum (𝓞 F)) {n M : ℕ} (X Y : Fin n → Fin M → Af F ⊗[F] E) :
    projV v (X - Y) = projV v X - projV v Y := by
  funext a i
  simp [projV, map_sub]

def cosVN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) {n M : ℕ}
    (a : Fin n → Fin M → Fv F v ⊗[F] E) : Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
  {Z | Z - a ∈ lvN b v (P : AddSubgroup (Fv F v)) n M}

theorem isCompact_isOpen_cosVN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) (hP : P ≤ intSub v)
    {n M : ℕ} (a : Fin n → Fin M → Fv F v ⊗[F] E) : IsCompact (cosVN b v P a) ∧ IsOpen (cosVN b v P a) := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have e : cosVN b v P a = (Homeomorph.subRight a) ⁻¹' (lvN b v (P : AddSubgroup (Fv F v)) n M : Set _) := rfl
  rw [e]
  exact ⟨(Homeomorph.subRight a).isCompact_preimage.2 (isCompact_lvN b v P hP n M),
    (isClopen_lvN b v P n M).isOpen.preimage (Homeomorph.subRight a).continuous⟩

theorem cosVN_intSub (v : HeightOneSpectrum (𝓞 F)) {n M : ℕ} {a : Fin n → Fin M → Fv F v ⊗[F] E}
    (ha : a ∈ latV b v) : cosVN b v (intSub v) a = latV b v := by
  have ha' : a ∈ lvN b v ((intSub v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M := ha
  ext Z
  have e1 : Z ∈ cosVN b v (intSub v) a ↔ Z - a ∈ lvN b v ((intSub v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M :=
    Iff.rfl
  have e2 : Z ∈ latV b v ↔ Z ∈ lvN b v ((intSub v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M := Iff.rfl
  rw [e1, e2, sub_eq_add_neg]
  exact add_mem_cancel_right (neg_mem ha')

theorem exists_box_combN {n M : ℕ} (g : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (hg : IsSB g) :
    ∃ (s : Finset (Fin n → Fin M → Af F ⊗[F] E))
      (A : (Fin n → Fin M → Af F ⊗[F] E) → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
      (S : Finset (HeightOneSpectrum (𝓞 F))),
      (∀ a v, IsCompact (A a v) ∧ IsOpen (A a v)) ∧ (∀ a ∈ s, ∀ v, v ∉ S → A a v = latV b v) ∧
        ∀ Y, g Y = ∑ a ∈ s, g a * (boxF (A a)).indicator (fun _ => (1 : ℂ)) Y := by
  classical
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have hU := invariant_mem_nhds hg.1 hg.2
  let Lc : (Fin n → Fin M → Fin d → Af F) → (Fin n → Fin M → Af F ⊗[F] E) :=
    fun c x i => ∑ k, c x i k • ((1 : Af F) ⊗ₜ[F] b k)
  have hL : Continuous Lc := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk
        continuous_const)
  have hL0 : Lc (fun _ _ _ => 0) = 0 := by
    funext x i
    simp [Lc]
  have hp : Lc ⁻¹' {u | ∀ x, g (x + u) = g x} ∈ 𝓝 (fun _ => fun _ => fun _ => (0 : Af F)) :=
    hL.continuousAt.preimage_mem_nhds (by rw [hL0]; exact hU)
  obtain ⟨W1, hW1, h1⟩ := exists_nhds_of_pi hp
  obtain ⟨W2, hW2, h2⟩ := exists_nhds_of_pi hW1
  obtain ⟨W, hW, h3⟩ := exists_nhds_of_pi hW2
  obtain ⟨T, P, hPO, hPT, hsub⟩ := exists_box_subset hW
  let B : AddSubgroup (Af F) :=
    { carrier := {y | ∀ v, y v ∈ P v}
      add_mem' := fun hx hy v => add_mem (hx v) (hy v)
      zero_mem' := fun v => zero_mem (P v)
      neg_mem' := fun hx v => neg_mem (hx v) }
  have hBo : IsOpen (B : Set (Af F)) := by
    have e : (B : Set (Af F)) = {y : Af F | ∀ v, y v ∈ v.adicCompletionIntegers F} ∩
        ⋂ v ∈ T, (fun y : Af F => y v) ⁻¹' (P v : Set (Fv F v)) := by
      ext y
      constructor
      · intro hy
        exact ⟨fun v => hPO v (hy v), Set.mem_iInter₂.2 fun v _ => hy v⟩
      · rintro ⟨hy1, hy2⟩ v
        by_cases hv : v ∈ T
        · exact Set.mem_iInter₂.1 hy2 v hv
        · rw [hPT v hv]
          exact hy1 v
    rw [e]
    refine IsOpen.inter ?_ (T.finite_toSet.isOpen_biInter fun v _ => (P v).isOpen.preimage
      (RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v))
    exact RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  let L : AddSubgroup (Fin n → Fin M → Af F ⊗[F] E) :=
    { carrier := {X | ∀ a i k, crd b (Af F) (X a i) k ∈ B}
      add_mem' := fun {x y} hx hy a i k => by
        rw [Pi.add_apply, Pi.add_apply, crd_add]
        exact add_mem (hx a i k) (hy a i k)
      zero_mem' := fun a i k => by
        rw [Pi.zero_apply, Pi.zero_apply, crd_zero]
        exact zero_mem B
      neg_mem' := fun {x} hx a i k => by
        rw [Pi.neg_apply, Pi.neg_apply, crd_neg]
        exact neg_mem (hx a i k) }
  have hLo : IsOpen (L : Set (Fin n → Fin M → Af F ⊗[F] E)) := by
    have e : (L : Set (Fin n → Fin M → Af F ⊗[F] E)) = ⋂ a, ⋂ i, ⋂ k,
        (fun X : Fin n → Fin M → Af F ⊗[F] E => crd b (Af F) (X a i) k) ⁻¹' (B : Set (Af F)) := by
      ext X
      simp [L]
    rw [e]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k =>
      hBo.preimage ((continuous_crd b (Af F) k).comp ((continuous_apply i).comp (continuous_apply a)))
  have hinv : ∀ x, ∀ l ∈ L, g (x + l) = g x := by
    intro x l hl
    have hl' : l = Lc fun a i k => crd b (Af F) (l a i) k := by
      funext a i
      exact eq_sum_crd b (Af F) (l a i)
    rw [hl']
    refine h1 _ (fun a => h2 _ fun i => h3 _ fun k => hsub (hl a i k)) x
  obtain ⟨s, hs⟩ := eq_sum_cosets hg.2 L hLo hinv
  have hbad : ∀ a : Fin n → Fin M → Af F ⊗[F] E, {v | ¬ projV v a ∈ latV b v}.Finite := fun a =>
    Filter.eventually_cofinite.1 (eventually_mem_latV b a)
  refine ⟨s, fun a v => cosVN b v (P v) (projV v a), T ∪ s.biUnion fun a => (hbad a).toFinset,
    fun a v => isCompact_isOpen_cosVN b v (P v) (hPO v) _, fun a ha v hv => ?_, fun Y => ?_⟩
  · have hvT : v ∉ T := fun h => hv (Finset.mem_union_left _ h)
    have hva : projV v a ∈ latV b v := by
      by_contra h
      exact hv (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨a, ha, (hbad a).mem_toFinset.2 h⟩))
    show cosVN b v (P v) (projV v a) = latV b v
    rw [hPT v hvT]
    exact cosVN_intSub b v hva
  · rw [hs Y]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 2
    ext X
    show X - a ∈ L ↔ ∀ v, projV v X - projV v a ∈ lvN b v ((P v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M
    constructor
    · intro h v i j k
      rw [← projV_subN]
      have := crd_projV b (X - a) v i j k
      rw [this]
      exact h i j k v
    · intro h i j k v
      have := crd_projV b (X - a) v i j k
      rw [← this, projV_subN]
      exact h v i j k

end GlobalTheory.CompanionTheory.PfSWUS.FockSplit.Box

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFundamentalDomainRangeProdMap
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.PairDom

theorem isFundamentalDomain_range_prodMap {A B X Y : Type} [Group A] [Group B] [Group X] [Group Y]
    [TopologicalSpace X] [TopologicalSpace Y] [IsTopologicalGroup X] [IsTopologicalGroup Y]
    [SecondCountableTopology X] [SecondCountableTopology Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant] (f : A →* X) (g : B →* Y) (F : Set X) (G : Set Y)
    (hF : IsFundamentalDomain f.range F μ) (hG : IsFundamentalDomain g.range G ν) :
    IsFundamentalDomain (f.prodMap g).range (F ×ˢ G) (μ.prod ν) := by
  have hmp : ∀ z : X × Y, MeasurePreserving (z * ·) (μ.prod ν) (μ.prod ν) := fun z =>
    measurePreserving_mul_left (μ.prod ν) z
  refine IsFundamentalDomain.mk'' (hF.nullMeasurableSet.prod hG.nullMeasurableSet) ?_ ?_
    (fun γ => (hmp γ).quasiMeasurePreserving)
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hF.ae_covers,
      Measure.quasiMeasurePreserving_snd.ae hG.ae_covers] with z h1 h2
    obtain ⟨⟨_, a, rfl⟩, ha⟩ := h1
    obtain ⟨⟨_, b, rfl⟩, hb⟩ := h2
    exact ⟨⟨(f a, g b), (a, b), rfl⟩, ha, hb⟩
  · rintro ⟨_, ⟨a, b⟩, rfl⟩ hγ
    by_cases ha : f a = 1
    · have hb : (⟨g b, b, rfl⟩ : g.range) ≠ 1 := by
        intro h
        apply hγ
        apply Subtype.ext
        exact Prod.ext ha (congrArg Subtype.val h)
      have h3 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).preimage_null (hG.aedisjoint hb)
      refine measure_mono_null ?_ h3
      rintro z ⟨⟨w, hw, rfl⟩, hz⟩
      exact ⟨⟨w.2, hw.2, rfl⟩, ⟨_, hz.2, one_smul _ _⟩⟩
    · have ha' : (⟨f a, a, rfl⟩ : f.range) ≠ 1 := by
        intro h
        exact ha (congrArg Subtype.val h)
      have h3 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).preimage_null (hF.aedisjoint ha')
      refine measure_mono_null ?_ h3
      rintro z ⟨⟨w, hw, rfl⟩, hz⟩
      exact ⟨⟨w.1, hw.1, rfl⟩, ⟨_, hz.1, one_smul _ _⟩⟩

theorem exists_measure_of_eq {X Y : Type} [Group X] [Group Y] [TopologicalSpace X] [TopologicalSpace Y]
    [IsTopologicalGroup X] [IsTopologicalGroup Y] [LocallyCompactSpace X] [LocallyCompactSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y] (μ₁ : Measure X) (μ₂ : Measure Y)
    [μ₁.IsHaarMeasure] [μ₂.IsHaarMeasure] [μ₁.IsMulRightInvariant] [μ₂.IsMulRightInvariant]
    (Γ : Subgroup (X × Y)) (F : Set (X × Y)) (hF : IsFundamentalDomain Γ F (μ₁.prod μ₂))
    (m : MeasurableSpace (X × Y)) (e : Prod.instMeasurableSpace = m) :
    ∃ μ : @Measure (X × Y) m,
      (@Measure.IsMulLeftInvariant _ m _ μ ∧ @Measure.IsMulRightInvariant _ m _ μ ∧
        @Measure.IsOpenPosMeasure _ _ m μ ∧ @IsLocallyFiniteMeasure _ m _ μ) ∧
      @IsFundamentalDomain Γ (X × Y) _ _ m F μ ∧
      ∀ f : X × Y → ℂ, @integral _ _ _ _ m (@Measure.restrict _ m μ F) f =
        @integral _ _ _ _ Prod.instMeasurableSpace ((μ₁.prod μ₂).restrict F) f := by
  subst e
  haveI : SigmaFinite μ₁ := sigmaFinite_of_locallyFinite
  haveI : SigmaFinite μ₂ := sigmaFinite_of_locallyFinite
  exact ⟨μ₁.prod μ₂, ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hF, fun _ => rfl⟩

theorem isMulRightInvariant_GA (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    [m : MeasurableSpace (GA E a)] [hm : BorelSpace (GA E a)] (μ : Measure (GA E a)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  obtain ⟨ν, h1, h2⟩ := GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant E a
  have e : m = CuspidalL2GL.measurableSpace_GA E a := hm.measurable_eq
  subst e
  haveI := CuspidalL2GL.t2Space_GA E a
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  letI := h2
  rw [Measure.isMulLeftInvariant_eq_smul μ ν]
  exact MeasureTheory.isMulRightInvariant_smul (μ := ν) _

theorem prodDom : RatProper → ProdDom := by
  intro _ E _ _ _ a b _ _ _ _ μ₁ _ μ₂ _ F₁ F₂ h₁ h₂
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.locallyCompactSpace_GA E b
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E b
  haveI := isMulRightInvariant_GA E a μ₁
  haveI := isMulRightInvariant_GA E b μ₂
  haveI : SigmaFinite μ₁ := sigmaFinite_of_locallyFinite
  haveI : SigmaFinite μ₂ := sigmaFinite_of_locallyFinite
  obtain ⟨μ, hh, hf, hi⟩ := exists_measure_of_eq μ₁ μ₂ (ratH E a b) (F₁ ×ˢ F₂)
    (isFundamentalDomain_range_prodMap μ₁ μ₂ (ratGL E a) (ratGL E b) F₁ F₂ h₁ h₂) (borelH E a b)
    Prod.borelSpace.measurable_eq
  exact ⟨⟨μ, hh, F₁ ×ˢ F₂, hf⟩, rfl, fun f => hi f⟩

end GlobalTheory.CompanionTheory.PairDom
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

section Lat

variable (K : Type) [Field K] [NumberField K]

def intVec (m : ℕ) : Submodule (𝓞 K) (Fin m → K) where
  carrier := {v | ∀ i, ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = v i}
  add_mem' := by
    intro v w hv hw i
    obtain ⟨o, ho⟩ := hv i
    obtain ⟨p, hp⟩ := hw i
    exact ⟨o + p, by simp [ho, hp]⟩
  zero_mem' := fun _ => ⟨0, by simp⟩
  smul_mem' := by
    intro a v hv i
    obtain ⟨o, ho⟩ := hv i
    exact ⟨a * o, by simp [ho, Algebra.smul_def]⟩

abbrev FQ : Type := (Fin 1 → K) ⧸ intVec K 1

def den (x : K) : Ideal (𝓞 K) :=
  Ideal.torsionOf (𝓞 K) (FQ K) (Submodule.Quotient.mk fun _ => x)

def idx (c : Submodule (𝓞 K) K) : ℕ :=
  (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex c.toAddSubgroup

def zetaR (r : ℝ) : ℝ := ∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-r)

variable {K}

def lam {m : ℕ} (c : Matrix (Fin m) (Fin m) K) : Submodule (𝓞 K) (Fin m → K) :=
  intVec K m ⊔ (intVec K m).map (c.mulVecLin.restrictScalars (𝓞 K))

def IsLat {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) : Prop :=
  L.FG ∧ Submodule.span K (L : Set (Fin m → K)) = ⊤

def tor {m : ℕ} (c : Matrix (Fin m) (Fin m) K) (u : Fin m → K) : Ideal (𝓞 K) :=
  Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ lam c) (Submodule.Quotient.mk u)

def lastFib {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : Submodule (𝓞 K) K :=
  (lam C).comap (LinearMap.single (𝓞 K) (fun _ : Fin (m + 1) => K) (Fin.last m))

theorem isLat_intVec (m : ℕ) : IsLat (intVec K m) := by
  refine ⟨?_, ?_⟩
  · have h : intVec K m = (⊤ : Submodule (𝓞 K) (Fin m → 𝓞 K)).map
        (LinearMap.compLeft (Algebra.linearMap (𝓞 K) K) (Fin m)) := by
      ext v
      simp only [Submodule.mem_map, Submodule.mem_top, true_and]
      constructor
      · intro hv
        choose o ho using hv
        exact ⟨o, funext fun i => ho i⟩
      · rintro ⟨o, rfl⟩ i
        exact ⟨o i, rfl⟩
    rw [h]
    exact Submodule.FG.map _ Module.Finite.fg_top
  · rw [eq_top_iff]
    intro v _
    have hv : v = ∑ i, v i • (Pi.single i (1 : K) : Fin m → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    intro j
    by_cases h : j = i
    · subst h
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Pi.single_apply, h]⟩

end Lat

section GlobalTheory

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def blk {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) E := fun i j =>
  Fin.lastCases (motive := fun _ => E)
    (Fin.lastCases (motive := fun _ => E) d (fun b => σ (u b)) j)
    (fun a => Fin.lastCases (motive := fun _ => E) (u a) (fun b => c a b) j) i

variable [NumberField E]

def sO (σ : E →ₐ[F] E) : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)

end GlobalTheory

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSplitK
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

section Gen

variable {V H : Type} [MeasurableSpace V] [MeasurableSpace H]

def DenLE (μ : Measure V) (ν : Measure H) (q : V → H) (S : Set V) (C : ℝ≥0∞) : Prop :=
  ∀ Y, MeasurableSet Y → μ (S ∩ q ⁻¹' Y) ≤ C * ν Y

end Gen

section Box

variable {K W : Type} [CommRing K] [Fintype W] {n M : ℕ}

def boxK (κ : K ≃+* (W → ℂ)) (r : Fin n → W → ℝ) : Set (Fin n → Fin M → K) :=
  {X | ∀ a i w, ‖κ (X a i) w‖ ≤ r a w}

def nearK (κ : K ≃+* (W → ℂ)) (w : W) (s : Fin n → ℂ) (ε : ℝ) : Set (Fin n → Fin M → K) :=
  {X | ∀ i, ‖∑ b, s b * κ (X b i) w‖ < ε}

def goodK (κ : K ≃+* (W → ℂ)) (R ε : ℝ) : Set (Fin n → Fin M → K) :=
  boxK κ (fun _ _ => R) \ ⋃ w : W, ⋃ a : Fin n, ⋃ s ∈ {s : Fin n → ℂ | s a = 1 ∧ ∀ b, ‖s b‖ ≤ 1}, nearK κ w s ε

def shearK (a : Fin n) (s : Fin n → K) (X : Fin n → Fin M → K) : Fin n → Fin M → K :=
  Function.update X a (fun i => X a i + ∑ b, s b * X b i)

def shearM (a : Fin n) (s : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  1 + Matrix.of fun b c => if c = a then s b else 0

end Box

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def IsSplitK (e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ)) (σ : E →ₐ[F] E)
    (κ : Ainf F ⊗[F] E ≃+* (NumberField.InfinitePlace F → ℂ)) : Prop :=
  IsHomeomorph κ ∧ (∀ x w, κ (sigR (Ainf F) σ x) w = (starRingEnd ℂ) (κ x w)) ∧
    ∀ a w, κ (algebraMap (Ainf F) (Ainf F ⊗[F] E) a) w = (e a w : ℂ)

end Split

end GlobalTheory.CompanionTheory.WhitFree.AvgInf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorGlRelations
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.Clozel

theorem glRel_EopV : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (τ : E →+* ℂ), Formalism.REAL.GlRel (EopV π τ) := by
  intro E _ _ _ a π τ i j k l
  have key := GlobalTheory.CompanionTheory.ClozelPurity.EopV_val E a π τ
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  have h := LinearMap.congr_fun (glRel_Eop (a := a) τ i j k l) φ.1
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, key] at h ⊢
  split_ifs at h ⊢ <;> simpa [key] using h

end GlobalTheory.CompanionTheory.Clozel
end

