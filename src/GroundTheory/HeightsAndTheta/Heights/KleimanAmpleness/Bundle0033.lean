module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsHomogOfMemQuotPartAlt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseComap
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

noncomputable def baseComap (F : Type) [Field F] {K : Type} {ι : K → Type} (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    (W : Ideal (NumbersDVR.MRing ι F)) : Ideal (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) F) :=
  W.comap (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k))

def ModelCurves.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ d : ℕ,
        (∀ W : Ideal (NumbersDVR.MRing ι F), NumbersDVR.IsMultiProjPrime W → mIdealOver F y ≤ W →
          relDim W = ((d : ℕ) : WithBot (WithTop ℤ)) →
            NumbersDVR.IsMultiProjPrime (baseComap F k₀ e W) ∧
              mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) ≤ baseComap F k₀ e W ∧
              relDim (baseComap F k₀ e W) = ((d : ℕ) : WithBot (WithTop ℤ))) ∧
        (∀ P : Ideal (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) F), NumbersDVR.IsMultiProjPrime P →
          mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) ≤ P → relDim P = ((d : ℕ) : WithBot (WithTop ℤ)) →
            ∃ W : Ideal (NumbersDVR.MRing ι F), NumbersDVR.IsMultiProjPrime W ∧ mIdealOver F y ≤ W ∧
              relDim W = ((d : ℕ) : WithBot (WithTop ℤ)) ∧ baseComap F k₀ e W = P)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechDMemLocPart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH renaming Cell → KHCell
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cellMon CechC cellRes faceSign cechD locPart cechCc cechZc cechBc cechHc
  mIdealOver quotPart)

noncomputable section

namespace CellLocEval

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)

theorem face_subset (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (l : K) :
    Function.update I k ((I k).erase i) l ⊆ I l := by
  by_cases hl : l = k
  · subst hl
    rw [Function.update_self]
    exact Finset.erase_subset _ _
  · rw [Function.update_of_ne hl]


open Classical in
theorem cechD_apply' {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (n : ℕ) (f : CechC S ι M n)
    (I : KHCell K ι (n + 1)) :
    cechD S ι M n f I = ∑ k, ∑ i ∈ I.1 k,
      if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
          ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
        faceSign I.1 k i • cellRes S M _ I.1 (f ⟨Function.update I.1 k ((I.1 k).erase i), h⟩)
      else 0 := by
  simp only [cechD, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl

theorem cechD_mem_locPart (γ : K → ℤ) (n : ℕ) {f : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n}
    (hf : f ∈ cechCc ι (quotPart S (mIdealOver S y)) γ n) (I : KHCell K ι (n + 1)) :
    cechD S ι _ n f I ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) γ := by
  rw [cechD_apply']
  refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i _ => ?_
  split_ifs with hc
  · have hJ : f ⟨Function.update I.1 k ((I.1 k).erase i), hc⟩ ∈ locPart ι (quotPart S (mIdealOver S y))
        (cellMon S (Function.update I.1 k ((I.1 k).erase i))) γ :=
      Submodule.mem_pi.mp hf ⟨Function.update I.1 k ((I.1 k).erase i), hc⟩ (Set.mem_univ _)
    have hm := cellRes_mem_locPart (J := Function.update I.1 k ((I.1 k).erase i)) (I := I.1)
      (cellMon_mono (face_subset I.1 k i)) γ hJ
    exact zsmul_mem hm _
  · exact Submodule.zero_mem _

theorem cechD_mem_cechCc (γ : K → ℤ) (n : ℕ) {f : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n}
    (hf : f ∈ cechCc ι (quotPart S (mIdealOver S y)) γ n) :
    cechD S ι _ n f ∈ cechCc ι (quotPart S (mIdealOver S y)) γ (n + 1) :=
  Submodule.mem_pi.mpr fun I _ => cechD_mem_locPart y γ n hf I

def evC (n : ℕ) : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n →ₗ[S] (KHCell K ι n → Ω) :=
  LinearMap.pi fun I => (evMap y I.1).comp (LinearMap.proj (R := S)
    (φ := fun J : KHCell K ι n => LocalizedModule (cellMon S J.1) (MRingOver S ι ⧸ mIdealOver S y)) I)

theorem evC_apply (n : ℕ) (w : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n) (I : KHCell K ι n) :
    evC y n w I = evMap y I.1 (w I) := rfl

theorem evC_cechD (n : ℕ) (w : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n) :
    evC y (n + 1) (cechD S ι _ n w) = cellD S y n (evC y n w) := by
  funext I
  rw [evC_apply]
  by_cases hI : CellMeets y I.1
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [cechD_apply', map_sum]
    simp only [cellD, LinearMap.pi_apply, hI, if_true, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hc
    · rw [map_zsmul]
      exact congrArg _ (evMap_cellRes (face_subset I.1 k i) hI _)
    · simp
  · rw [evMap_of_not y hI]
    simp only [cellD, LinearMap.pi_apply, hI, if_false, LinearMap.zero_apply]

variable (γ : K → ℤ)

theorem evC_mem (n : ℕ) {w : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n}
    (hw : w ∈ cechCc ι (quotPart S (mIdealOver S y)) γ n) : evC y n w ∈ cellC S y γ n := by
  refine Submodule.mem_pi.mpr fun I _ => ?_
  rw [evC_apply]
  by_cases hI : CellMeets y I.1
  · rw [← map_evMap_locPart y hI γ]
    exact Submodule.mem_map_of_mem (Submodule.mem_pi.mp hw I (Set.mem_univ _))
  · rw [evMap_of_not y hI]
    exact Submodule.zero_mem _

theorem evC_lift (n : ℕ) {w' : KHCell K ι n → Ω} (hw' : w' ∈ cellC S y γ n) :
    ∃ w ∈ cechCc ι (quotPart S (mIdealOver S y)) γ n, evC y n w = w' := by
  have h : ∀ I : KHCell K ι n, ∃ x ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) γ,
      evMap y I.1 x = w' I := by
    intro I
    have hI' : w' I ∈ cellSec S y γ I.1 := Submodule.mem_pi.mp hw' I (Set.mem_univ _)
    by_cases hI : CellMeets y I.1
    · rw [← map_evMap_locPart y hI γ] at hI'
      exact Submodule.mem_map.mp hI'
    · unfold cellSec at hI'
      rw [if_neg hI, Submodule.mem_bot] at hI'
      exact ⟨0, Submodule.zero_mem _, by rw [map_zero, hI']⟩
  choose w hw hφw using h
  exact ⟨w, Submodule.mem_pi.mpr fun I _ => hw I, funext hφw⟩

theorem evC_injOn (n : ℕ) :
    Set.InjOn (evC (S := S) y n) (cechCc ι (quotPart S (mIdealOver S y)) γ n) := by
  intro w hw w' hw' h
  funext I
  have h' := congrFun h I
  rw [evC_apply, evC_apply] at h'
  by_cases hI : CellMeets y I.1
  · exact evMap_injOn y hI γ (Submodule.mem_pi.mp hw I (Set.mem_univ _))
      (Submodule.mem_pi.mp hw' I (Set.mem_univ _)) h'
  · have := subsingleton_of_not (S := S) y hI
    exact Subsingleton.elim _ _

theorem evC_mem_cellZ (n : ℕ) {z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n}
    (hz : z ∈ cechZc ι (quotPart S (mIdealOver S y)) γ n) : evC y n z ∈ cellZ S y γ n := by
  obtain ⟨hC, hK⟩ := Submodule.mem_inf.mp hz
  rw [Submodule.restrictScalars_mem, LinearMap.mem_ker] at hK
  refine Submodule.mem_inf.mpr ⟨evC_mem y γ n hC, ?_⟩
  rw [LinearMap.mem_ker, ← evC_cechD, hK, map_zero]

theorem evC_mem_cellB (n : ℕ) {z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n}
    (hz : z ∈ cechBc ι (quotPart S (mIdealOver S y)) γ n) : evC y n z ∈ cellB S y γ n := by
  cases n with
  | zero =>
    change z ∈ (⊥ : Submodule S _) at hz
    change evC y 0 z ∈ (⊥ : Submodule S _)
    rw [Submodule.mem_bot] at hz ⊢
    rw [hz, map_zero]
  | succ n =>
    change z ∈ (cechCc ι (quotPart S (mIdealOver S y)) γ n).map
      ((cechD S ι (MRingOver S ι ⧸ mIdealOver S y) n).restrictScalars S) at hz
    change evC y (n + 1) z ∈ (cellC S y γ n).map (cellD S y n)
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hz
    exact Submodule.mem_map.mpr ⟨evC y n w, evC_mem y γ n hw, (evC_cechD y n w).symm⟩

theorem mem_cechBc_of (n : ℕ) {z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n}
    (hz : z ∈ cechCc ι (quotPart S (mIdealOver S y)) γ n) (h : evC y n z ∈ cellB S y γ n) :
    z ∈ cechBc ι (quotPart S (mIdealOver S y)) γ n := by
  cases n with
  | zero =>
    change evC y 0 z ∈ (⊥ : Submodule S _) at h
    change z ∈ (⊥ : Submodule S _)
    rw [Submodule.mem_bot] at h ⊢
    exact evC_injOn y γ 0 hz (Submodule.zero_mem _) (h.trans (map_zero _).symm)
  | succ n =>
    change evC y (n + 1) z ∈ (cellC S y γ n).map (cellD S y n) at h
    change z ∈ (cechCc ι (quotPart S (mIdealOver S y)) γ n).map
      ((cechD S ι (MRingOver S ι ⧸ mIdealOver S y) n).restrictScalars S)
    obtain ⟨w', hw', hd⟩ := Submodule.mem_map.mp h
    obtain ⟨w, hw, rfl⟩ := evC_lift y γ n hw'
    refine Submodule.mem_map.mpr ⟨w, hw, ?_⟩
    exact evC_injOn y γ (n + 1) (cechD_mem_cechCc y γ n hw) hz ((evC_cechD y n w).trans hd)

def evZ (n : ℕ) : cechZc ι (quotPart S (mIdealOver S y)) γ n →ₗ[S] cellZ S y γ n :=
  (evC (S := S) y n).restrict fun _ hz => evC_mem_cellZ y γ n hz

def evH (n : ℕ) : cechHc ι (quotPart S (mIdealOver S y)) γ n →ₗ[S] cellH S y γ n :=
  Submodule.mapQ _ _ (evZ (S := S) y γ n) fun _ hz => evC_mem_cellB (S := S) y γ n hz

theorem evH_mk (n : ℕ) (z : cechZc ι (quotPart S (mIdealOver S y)) γ n) :
    evH (S := S) y γ n (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (p := (cellB S y γ n).comap (cellZ S y γ n).subtype) (evZ y γ n z) := rfl

theorem evH_bijective (n : ℕ) : Function.Bijective (evH (S := S) y γ n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' := (Submodule.Quotient.mk_eq_zero _).mp ((evH_mk y γ n z).symm.trans hx)
    rw [Submodule.Quotient.mk_eq_zero]
    exact mem_cechBc_of y γ n (Submodule.mem_inf.mp z.2).1 hx'
  · intro q
    obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨hC, hK⟩ := Submodule.mem_inf.mp z'.2
    obtain ⟨w, hw, hwz⟩ := evC_lift y γ n hC
    have hdw : cechD S ι _ n w = 0 := by
      refine evC_injOn y γ (n + 1) (cechD_mem_cechCc y γ n hw) (Submodule.zero_mem _) ?_
      rw [evC_cechD, hwz, map_zero]
      exact LinearMap.mem_ker.mp hK
    have hwZ : w ∈ cechZc ι (quotPart S (mIdealOver S y)) γ n :=
      Submodule.mem_inf.mpr ⟨hw, by rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]; exact hdw⟩
    refine ⟨Submodule.Quotient.mk ⟨w, hwZ⟩, ?_⟩
    exact (evH_mk y γ n ⟨w, hwZ⟩).trans (congrArg Submodule.Quotient.mk (Subtype.ext hwz))

theorem proof : CellLocEval.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y γ n
  exact ⟨(LinearEquiv.ofBijective (evH (S := S) y γ n) (evH_bijective (S := S) y γ n)).symm⟩

end CellLocEval

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ConstVanishHypSegment
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH renaming Cell → KHCell
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (faceSign)


open Classical in
def constD (K : Type*) [Fintype K] [LinearOrder K] (ι : K → Type*) [∀ k, LinearOrder (ι k)] (V : Type*)
    [AddCommGroup V] (n : ℕ) (f : KHCell K ι n → V) : KHCell K ι (n + 1) → V :=
  fun I => ∑ k, ∑ i ∈ I.1 k,
    if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
      faceSign I.1 k i • f ⟨Function.update I.1 k ((I.1 k).erase i), h⟩
    else 0

def CechConstVanish.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, LinearOrder (ι k)] (V : Type) [AddCommGroup V]
    (G : ∀ k, Finset (ι k)) (z : KHCell K ι 1 → V),
    (∀ I : KHCell K ι 2, (∀ k, I.1 k ⊆ G k) → constD K ι V 1 z I = 0) →
    ∃ f : KHCell K ι 0 → V, ∀ J : KHCell K ι 1, (∀ k, J.1 k ⊆ G k) → constD K ι V 0 f J = z J

theorem constVanish_hyp_segment :
    ∀ I : KHCell Unit (fun _ => Fin 2) 2, (∀ k, I.1 k ⊆ Finset.univ) →
      constD Unit (fun _ => Fin 2) ℤ 1 (fun _ => 1) I = 0 := by
  intro I _
  exfalso
  have h : (I.1 ()).card - 1 = 2 := by simpa using I.2.2
  have hc : (I.1 ()).card ≤ 2 := by simpa using Finset.card_le_univ (I.1 ())
  omega

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutOneGeneratorSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def CutOneGenerator.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω), IsSubvar x pp (n + 1) →
    IsVeryAmple L.toSubSystem → s ∈ L.secs →
    ¬ ∀ (j : Fin (N + 1)) (hj : x j ≠ 0), L.sub (singleChart hj) ≤
      (L.twist (idealSys x pp)).sub (singleChart hj) ⊔
        Submodule.span (chartRing k x (singleChart hj)) {s}

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver secOver secMOver)

def ReindexDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [Algebra F Ω] (x' : κ → Ω) (N : ℕ)
    (e : κ ≃ Fin (N + 1)),
    ringKrullDim (NumbersDVR.MRing (fun _ : Unit => κ) F ⧸ mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')) =
      ringKrullDim (Kleiman.Poly F N ⧸ Kleiman.primeOf (S := F) (x' ∘ e.symm))

section Inhabitants

open IndefiniteRowSideFullHecke.Kleiman2

variable (F : Type) [Field F]

end Inhabitants

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def ModelTwistGenerated.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IsNoetherianRing S → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → ∀ β : K → ℤ,
      ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c → IndefiniteRowSideFullHecke.Kleiman2.IsGenerated S y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def ModelDimEq.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ d : ℕ,
      (Kleiman.IsSubvar (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)
          (Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) d ↔
        relDim (mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ)))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestSide
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver secOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)

def ResidueGen.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (K' : Type) [Field K'] [Algebra F K'] (y' : (Σ k, ι k) → K'),
    mIdealOver F y ≤ mIdealOver F y' →
    ∀ (R : Subalgebra F Ω) (σ : R →ₐ[F] K'),
      (∀ (f g : MRingOver F ι) (n : K → ℕ), IsMultiHomog f n → IsMultiHomog g n → aeval y' g ≠ 0 →
        ∃ h : aeval y f / aeval y g ∈ R, σ ⟨_, h⟩ = aeval y' f / aeval y' g) →
      (∀ d : ∀ k, ι k, (∀ k, y' ⟨k, d k⟩ ≠ 0) → ∀ z ∈ chartRingOver F y d,
        ∃ h : z ∈ R, σ ⟨z, h⟩ ∈ chartRingOver F y' d) →
    ∀ β : K → ℤ, IndefiniteRowSideFullHecke.Kleiman2.IsGenerated F y β → ∀ d₀ : ∀ k, ι k, (∀ k, y' ⟨k, d₀ k⟩ ≠ 0) →
      ∃ ρ : Ω → K',
        (∀ h ∈ secOver F y β, ∃ hh : h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k) ∈ R,
          σ ⟨_, hh⟩ = ρ h * ∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)) ∧
        ∀ c : ∀ k, ι k, (∀ k, y' ⟨k, c k⟩ ≠ 0) →
          Submodule.span (chartRingOver F y' c) (ρ '' (secOver F y β : Set Ω)) =
            Submodule.span (chartRingOver F y' c) {(∏ k, y' ⟨k, c k⟩ ^ (-β k))⁻¹}

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)

def ResidueMap.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (K' : Type) [Field K'] [Algebra F K'] (y' : (Σ k, ι k) → K'),
    mIdealOver F y ≤ mIdealOver F y' →
    ∃ (R : Subalgebra F Ω) (σ : R →ₐ[F] K'),
      (∀ (f g : MRingOver F ι) (n : K → ℕ), IsMultiHomog f n → IsMultiHomog g n → aeval y' g ≠ 0 →
        ∃ h : aeval y f / aeval y g ∈ R, σ ⟨_, h⟩ = aeval y' f / aeval y' g) ∧
      (∀ (k : K) (f g : MvPolynomial (ι k) F) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m →
        aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k) g ≠ 0 →
        ∃ h : aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k) f / aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k) g ∈ R,
          σ ⟨_, h⟩ = aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k) f / aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k) g) ∧
      (∀ d : ∀ k, ι k, (∀ k, y' ⟨k, d k⟩ ≠ 0) → ∀ z ∈ chartRingOver F y d,
        ∃ h : z ∈ R, σ ⟨z, h⟩ ∈ chartRingOver F y' d)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SectionsPoly.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∃ P : MvPolynomial K ℚ, FieldNumbers.EventuallyPoly (NumbersDVR.hilbFn (mIdealOver F y)) P ∧
        ∀ β : K → ℤ, ∀ᶠ c : ℕ in Filter.atTop,
          (Module.finrank F (secOver F y (β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) : ℚ) =
            eval (fun k => (((β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k : ℤ) : ℚ)) P

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

