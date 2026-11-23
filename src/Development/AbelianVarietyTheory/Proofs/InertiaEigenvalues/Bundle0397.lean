module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0269
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0373
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankFiniteLeExponentialCocycles
section
noncomputable section

namespace GlobalTheory.HyodoFE

open _root_.Formalism Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HyodoDef TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mem_Dcris_iff (x : V ⊗[Qp] B) : x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem φVB_mem_Dcris {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ := by
  rw [mem_Dcris_iff] at hx ⊢
  intro g
  rw [← GlobalTheory.CobCrisLift.φVB_act, hx g]

def oneSubφ : Dcris PD ρ →ₗ[LL] Dcris PD ρ :=
  (LinearMap.id - φVB PD (LL := LL) (V := V)).restrict (p := Dcris PD ρ) (q := Dcris PD ρ)
    (fun x hx => (Dcris PD ρ).sub_mem hx (φVB_mem_Dcris PD ρ hx))

variable [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

def pairs : Submodule LL ((G → V) × (V ⊗[Qp] B)) where
  carrier := {p | p.1 ∈ continuousCocycles ρ ∧ ∀ g, p.1 g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g p.2 - p.2}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, hx⟩ ⟨hb, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, fun g => ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_tmul, hx, hy, map_add (f := _)]
    abel
  smul_mem' := by
    rintro c a ⟨ha, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, fun g => ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

def projZ : pairs PD ρ →ₗ[LL] finiteCocycles PD ρ :=
  LinearMap.codRestrict (finiteCocycles PD ρ) ((LinearMap.fst LL (G → V) (V ⊗[Qp] B)).comp (pairs PD ρ).subtype)
    (fun p => ⟨p.2.1, p.1.2, p.2.2⟩)

theorem projZ_surjective : Function.Surjective (projZ PD ρ) := by
  rintro ⟨c, hc, x, hx⟩
  exact ⟨⟨(c, x), hc, hx⟩, rfl⟩

def toDcris : pairs PD ρ →ₗ[LL] Dcris PD ρ :=
  LinearMap.codRestrict (Dcris PD ρ)
    (((LinearMap.id - φVB PD (LL := LL) (V := V)).comp (LinearMap.snd LL (G → V) (V ⊗[Qp] B))).comp
      (pairs PD ρ).subtype)
    (fun p => GlobalTheory.CobCrisLift.sub_φ_mem_Dcris PD ρ p.1.1 p.1.2 p.2.2)

theorem fst_mem_exponential_cocycles (p : pairs PD ρ) (hp : toDcris PD ρ p ∈ LinearMap.range (oneSubφ PD ρ)) :
    (p : (G → V) × (V ⊗[Qp] B)).1 ∈ crystallineCocycles PD ρ := by
  obtain ⟨e, he⟩ := hp
  have he' : (e : V ⊗[Qp] B) - φVB PD (LL := LL) (V := V) e
      = p.1.2 - φVB PD (LL := LL) (V := V) p.1.2 := congrArg Subtype.val he
  refine ⟨p.2.1, p.1.2 - e, ?_, fun g => ?_⟩
  · rw [map_sub]
    calc φVB PD (LL := LL) (V := V) p.1.2 - φVB PD (LL := LL) (V := V) e
        = (p.1.2 - (e : V ⊗[Qp] B)) + (((e : V ⊗[Qp] B) - φVB PD (LL := LL) (V := V) e)
          - (p.1.2 - φVB PD (LL := LL) (V := V) p.1.2)) := by abel
      _ = p.1.2 - e := by rw [he', sub_self, add_zero]
  · have hg := (mem_Dcris_iff PD ρ e).1 e.2 g
    rw [p.2.2 g, map_sub, hg]
    abel

theorem finrank_finite_cocycles_le [Module.Finite LL (Dcris PD ρ)] :
    finrank LL (finiteCocycles PD ρ) ≤ finrank LL (crystallineCocycles PD ρ) +
      finrank LL ↥(Dcris PD ρ ⊓ LinearMap.ker (φVB PD (LL := LL) (V := V) - LinearMap.id)) := by
  by_cases hf : Module.Finite LL (finiteCocycles PD ρ)
  swap
  · rw [Module.finrank_of_not_finite hf]; exact Nat.zero_le _
  obtain ⟨s, hs⟩ := (projZ PD ρ).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 (projZ_surjective PD ρ))
  set N := LinearMap.range (oneSubφ PD ρ) with hN
  let T : finiteCocycles PD ρ →ₗ[LL] (Dcris PD ρ ⧸ N) := N.mkQ ∘ₗ toDcris PD ρ ∘ₗ s
  have hle : crystallineCocycles PD ρ ≤ finiteCocycles PD ρ := fun c ⟨hc, x, _, hx⟩ => ⟨hc, x, hx⟩
  haveI : Module.Finite LL (crystallineCocycles PD ρ) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have hmem : ∀ k : LinearMap.ker T, ((k : finiteCocycles PD ρ) : G → V) ∈ crystallineCocycles PD ρ := by
    intro k
    have hk : T k = 0 := LinearMap.mem_ker.1 k.2
    have h := fst_mem_exponential_cocycles PD ρ (s k) ((Submodule.Quotient.mk_eq_zero N).1 hk)
    have hsk : projZ PD ρ (s k) = k := LinearMap.congr_fun hs k
    have hv : ((s k : pairs PD ρ) : (G → V) × (V ⊗[Qp] B)).1 = ((k : finiteCocycles PD ρ) : G → V) :=
      congrArg Subtype.val hsk
    rwa [hv] at h
  have h1 : finrank LL (LinearMap.ker T) ≤ finrank LL (crystallineCocycles PD ρ) := by
    let j : LinearMap.ker T →ₗ[LL] crystallineCocycles PD ρ :=
      LinearMap.codRestrict (crystallineCocycles PD ρ) ((finiteCocycles PD ρ).subtype ∘ₗ (LinearMap.ker T).subtype) hmem
    have hj : Function.Injective j := by
      intro a b hab
      have h := congrArg Subtype.val hab
      simp only [j, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h
      exact Subtype.ext (Subtype.ext h)
    exact LinearMap.finrank_le_finrank_of_injective hj
  have h2 : finrank LL (LinearMap.range T) ≤ finrank LL (Dcris PD ρ ⧸ N) := Submodule.finrank_le _
  have h3 := Submodule.finrank_quotient_add_finrank N
  have h4 := LinearMap.finrank_range_add_finrank_ker (oneSubφ PD ρ)
  have h5 := LinearMap.finrank_range_add_finrank_ker T
  set W := Dcris PD ρ ⊓ LinearMap.ker (φVB PD (LL := LL) (V := V) - LinearMap.id) with hW
  haveI : Module.Finite LL W :=
    Module.Finite.of_injective (Submodule.inclusion (inf_le_left : W ≤ Dcris PD ρ))
      (Submodule.inclusion_injective _)
  have hmemW : ∀ k : LinearMap.ker (oneSubφ PD ρ), ((k : Dcris PD ρ) : V ⊗[Qp] B) ∈ W := by
    intro k
    have hk : oneSubφ PD ρ k = 0 := LinearMap.mem_ker.1 k.2
    have hk' : ((k : Dcris PD ρ) : V ⊗[Qp] B) - φVB PD (LL := LL) (V := V) (k : Dcris PD ρ) = 0 :=
      congrArg Subtype.val hk
    refine Submodule.mem_inf.2 ⟨(k : Dcris PD ρ).2, ?_⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
    rw [sub_eq_zero] at hk' ⊢
    exact hk'.symm
  have h6 : finrank LL (LinearMap.ker (oneSubφ PD ρ)) ≤ finrank LL W := by
    let j : LinearMap.ker (oneSubφ PD ρ) →ₗ[LL] W :=
      LinearMap.codRestrict W ((Dcris PD ρ).subtype ∘ₗ (LinearMap.ker (oneSubφ PD ρ)).subtype) hmemW
    have hj : Function.Injective j := by
      intro a b hab
      have h := congrArg Subtype.val hab
      simp only [j, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h
      exact Subtype.ext (Subtype.ext h)
    exact LinearMap.finrank_le_finrank_of_injective hj
  have h7 : finrank LL N = finrank LL (LinearMap.range (oneSubφ PD ρ)) := rfl
  omega

end Generic

end GlobalTheory.HyodoFE

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

theorem GlobalTheory.HyodoFE.finrank_finite_le_exponential_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v, Continuous fun g => ρ g v) → IsDR (P.PD K) ρ → finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) ≤ finrank ℚ_[l] ↥(crystallineCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(Dcris (P.PD K) ρ ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V) - LinearMap.id)) := by
  intro l _ P AI _ K V _ _ _ _ _ _ _ ρ _ hdR
  haveI := GlobalTheory.DcrisFin.dcris_finite_of_isDR l P K V ρ hdR
  exact GlobalTheory.HyodoFE.finrank_finite_cocycles_le (P.PD K) ρ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixOfStabilizerTrivial
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass
open scoped Pointwise

noncomputable section

namespace GlobalTheory.TypeDegOne

theorem fix_of_stabilizer_trivial {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] [IsGalois ℚ E]
    (c : E →+* PadicAlgCl l) (P : Ideal (𝓞 E)) (hc : ∀ x : 𝓞 E, x ∈ P ↔ ‖c (x : E)‖ < 1)
    (hP : ∀ σ : E ≃ₐ[ℚ] E, σ • P = P → σ = 1) (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (x : E) :
    τ (c x) = c x := by
  letI : Algebra E (PadicAlgCl l) := c.toAlgebra
  haveI : IsScalarTower ℚ E (PadicAlgCl l) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let φ : E →ₐ[ℚ] PadicAlgCl l := ((τ : PadicAlgCl l →+* PadicAlgCl l).comp c).toRatAlgHom
  let σ : E ≃ₐ[ℚ] E := φ.restrictNormal' E
  have hσ : ∀ y, c (σ y) = τ (c y) := fun y => φ.restrictNormal_commutes E y
  have h1 : σ⁻¹ • P = P := by
    ext y
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, hc, hc]
    have e : ((σ • y : 𝓞 E) : E) = σ (y : E) := rfl
    have hn : ‖τ (c y)‖ = ‖c y‖ := (spectralNorm_eq_of_equiv τ _).symm
    rw [e, hσ, hn]
  have h2 : σ = 1 := inv_eq_one.1 (hP _ h1)
  rw [← hσ, h2]
  rfl

theorem eq_bot_of_subset_closure {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (S : Set (PadicAlgCl l)) (hK : (K : Set (PadicAlgCl l)) ⊆ closure S)
    (hS : ∀ (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∀ y ∈ S, τ y = y) : K = ⊥ := by
  haveI : IsGalois ℚ_[l] (PadicAlgCl l) := IsAlgClosure.isGalois _ _
  refine eq_bot_iff.2 fun y hy => (InfiniteGalois.mem_bot_iff_fixed y).2 fun τ => ?_
  have hc : Continuous τ :=
    (AddMonoidHomClass.isometry_of_norm τ fun x => (spectralNorm_eq_of_equiv τ x).symm).continuous
  exact closure_minimal (fun y hy => hS τ y hy) (isClosed_eq hc continuous_id) (hK hy)

theorem mem_place_iff (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : 𝓞 D.host.E) :
    x ∈ w.asIdeal ↔ ‖(D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (x : D.host.E))‖ < 1 := by
  rw [← D.nd.plOm.2 w x]
  set y := algebraMap D.host.E D.nd.Om (x : D.host.E)
  by_cases hy : y = 0
  · simp [hy]
  have hj : 0 < ‖(D.nbr i w hw).j y‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 hy)
  have h := D.nbr_ind i w hw y⁻¹
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hj,
    inv_le_one₀ (zero_lt_iff.2 ((_root_.map_ne_zero _).2 hy))] at h
  rw [← not_le, ← not_le, h]

theorem degree_one : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → (placesOver D.host.E (D.nd.l i)).ncard = 2 * D.R.f ∧ ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 := by
  intro D i k hk
  have hs : (placesOver D.host.E (D.nd.l i)).ncard = finrank ℚ D.host.E := by
    rw [hk]; exact D.nd.g_split k
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  refine ⟨?_, fun w hw => ?_⟩
  · have h1 : finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
    have h5 : D.R.f = 2 * D.R.ord := rfl
    rw [hs, h1, h5]; ring
  · have hP := (GlobalTheory.Mem.Chr.splitsC_place (p := D.nd.l i) Fact.out hs w hw).2.2
    have hb : (D.nbr i w hw).Kw.1 = ⊥ := by
      refine eq_bot_of_subset_closure _ _ (D.nbr i w hw).j_dense ?_
      rintro τ _ ⟨x, rfl⟩
      exact fix_of_stabilizer_trivial ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) w.asIdeal
        (mem_place_iff D i w hw) hP τ x
    exact IntermediateField.finrank_eq_one_iff.2 hb

end GlobalTheory.TypeDegOne

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAinfMatrixFrobeniusGaloisEqsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_ainf_matrix_frobenius_galois_eqs : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → Y.map WittVector.frobenius = Y * F.A.map bk.ev ∧ (∀ g : ↥(GK K), τ ^ N • ((ρ g).map (Per.zA l) * Y.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • (Y * F.ε g)) ∧ ∀ g : ↥(GK K), bk.ev bk.E ^ N • (F.ε g * F.A.map (fun s => Per.σA (g : GQ l) (bk.ev s))) = Per.σA (g : GQ l) (bk.ev bk.E) ^ N • (F.A.map bk.ev * (F.ε g).map WittVector.frobenius) := by
  first | (exact @GlobalTheory.FrameEq.frame_Y_eqs) | (exact GlobalTheory.FrameEq.frame_Y_eqs) | (intros; apply GlobalTheory.FrameEq.frame_Y_eqs  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFactorTiltLogBdRPlusStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_factor_tilt_log_bdRPlus : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (x : Per.Fl l) (g : GQ l) (c : ℤ_[l]),
    (∀ m : ℕ, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) →
    ∃ e : Per.Fl l, Per.σF g x = x * e ∧ e.untilt = 1 ∧
      Per.IsLog l e (aDp l (Per.zA l c) * C.j C.t) := by
  first | (exact @GlobalTheory.InertiaEigenvalues.TiltGalLog.gal_factor_log) | (exact GlobalTheory.InertiaEigenvalues.TiltGalLog.gal_factor_log) | (intros; apply GlobalTheory.InertiaEigenvalues.TiltGalLog.gal_factor_log  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepTupleRelationMemPowSpan
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.CovKer

theorem kerB : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (c N : ℕ) (cs : Fin m → Om l), (∀ (n : ℕ) (f : Γ →₀ ℤ_[l]), (∀ g, ‖((f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) * ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + c)) → ∃ f' : Γ →₀ ℤ_[l], (f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) = (l : Om l) ^ n • (f'.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)))) → (∀ g, ‖trc r g - ∑ k, cs k * trc (ρs k) g‖ ≤ ((l : ℝ)⁻¹) ^ (N + c)) → ∀ G : Γ →₀ ℤ_[l], (G.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) = 0 → ∃ f' : Γ →₀ ℤ_[l], (G.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) = (l : Om l) ^ N • (f'.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) := by
  intro l _ Γ _ a r m ρs c N cs hdiv happ G hG
  apply hdiv N G
  intro g

  have hk : ∀ k, ∑ h ∈ G.support, zOm l (G h) * trc (ρs k) (h * g) = 0 := by
    intro k
    have h0 := congrFun hG k
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, GlobalTheory.TraceConjugationCover.tup, Pi.zero_apply] at h0
    have h1 := congrArg (fun M : Matrix (Fin a) (Fin a) (Om l) =>
      (M * ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace) h0
    simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      Matrix.zero_mul, Matrix.trace_zero] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp [trc, map_mul, Units.val_mul]
  have htr : ((G.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) *
      ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace =
      ∑ h ∈ G.support, zOm l (G h) * (trc r (h * g) - ∑ k, cs k * trc (ρs k) (h * g)) := by
    have e2 : ∑ h ∈ G.support, zOm l (G h) * (∑ k, cs k * trc (ρs k) (h * g)) = 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ => ?_
      have := congrArg (fun x => cs k * x) (hk k)
      simp only [mul_zero, Finset.mul_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun h _ => by ring
    simp only [mul_sub, Finset.sum_sub_distrib, e2, sub_zero]
    simp only [Finsupp.sum, Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp [trc, map_mul, Units.val_mul]
  rw [htr]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun h _ => ?_
  rw [norm_mul]
  calc ‖zOm l (G h)‖ * ‖trc r (h * g) - ∑ k, cs k * trc (ρs k) (h * g)‖
      ≤ 1 * ((l : ℝ)⁻¹) ^ (N + c) :=
        mul_le_mul (GlobalTheory.TraceConjugationCover.norm_zOm_le _) (happ (h * g)) (norm_nonneg _) zero_le_one
    _ = ((l : ℝ)⁻¹) ^ (N + c) := one_mul _

end GlobalTheory.CovKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepTupleSpanSaturationBound
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.CovSat

theorem satA : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))), (∀ k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t k, zOm l (c' y) • y = 1) → (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → ∃ u : ℕ, ∀ N M : ℕ, N + u ≤ M → ∀ H : Γ →₀ ℤ_[l], (H.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) ∈ GlobalTheory.TraceConjugationCover.latL t M → ∃ H' : Γ →₀ ℤ_[l], (H.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) = (l : Om l) ^ N • (H'.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) := by
  intro l _ Γ _ a m ρs t h1 hst
  classical
  let E : Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l)) :=
    Submodule.span ℤ_[l] (Set.range (GlobalTheory.TraceConjugationCover.tup ρs))
  let Λ := GlobalTheory.TraceConjugationCover.latL t 0
  have hsumE : ∀ H : Γ →₀ ℤ_[l], (H.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) ∈ E := by
    intro H
    rw [Finsupp.mem_span_range_iff_exists_finsupp]
    exact ⟨H, by simp only [GlobalTheory.TraceConjugationCover.zOm_smul]⟩
  have hEsum : ∀ x ∈ E, ∃ H' : Γ →₀ ℤ_[l], x = H'.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g := by
    intro x hx
    obtain ⟨H', hH'⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hx
    exact ⟨H', by rw [← hH']; simp only [GlobalTheory.TraceConjugationCover.zOm_smul]⟩
  have hc : ∀ (n : ℕ) (w : Fin m → Matrix (Fin a) (Fin a) (Om l)), (l : Om l) ^ n • w = (l : ℤ_[l]) ^ n • w := by
    intro n w
    rw [← GlobalTheory.TraceConjugationCover.zOm_smul, map_pow, map_natCast]
  have hsingle : ∀ k, ∀ z ∈ t k, Pi.single k z ∈ Λ := by
    intro k z hz
    exact Submodule.subset_span (Set.mem_iUnion.2 ⟨k, z, hz, by simp⟩)
  have hlat : ∀ M, ∀ x ∈ GlobalTheory.TraceConjugationCover.latL t M, ∃ y ∈ Λ, x = ((l : ℤ_[l]) ^ M) • y := by
    intro M x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx
      obtain ⟨z, hz, rfl⟩ := hk
      refine ⟨Pi.single k z, hsingle k z hz, ?_⟩
      rw [← hc]
      ext i : 1
      by_cases hi : i = k
      · subst hi; simp
      · simp [Pi.single_apply, hi]
    | zero => exact ⟨0, Λ.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨x' + y', Λ.add_mem hx' hy', by rw [smul_add]⟩
    | smul c x _ hx =>
      obtain ⟨x', hx', rfl⟩ := hx
      exact ⟨c • x', Λ.smul_mem c hx', by rw [smul_comm]⟩
  have hspan : ∀ k (c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l]),
      (∑ y ∈ t k, zOm l (c y) • y) ∈ Submodule.span ℤ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l))) := by
    intro k c
    refine Submodule.sum_mem _ fun y hy => ?_
    rw [GlobalTheory.TraceConjugationCover.zOm_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hy)
  have hρ : ∀ k g, ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) ∈
      Submodule.span ℤ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l))) := by
    intro k g
    obtain ⟨c', hc'⟩ := h1 k
    rw [← mul_one ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)), ← hc', Finset.mul_sum]
    refine Submodule.sum_mem _ fun y hy => ?_
    rw [Matrix.mul_smul]
    obtain ⟨c'', hc''⟩ := hst k g y hy
    rw [hc'', GlobalTheory.TraceConjugationCover.zOm_smul]
    exact Submodule.smul_mem _ _ (hspan k c'')
  have hspanΛ : ∀ k, Submodule.span ℤ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l))) ≤
      Λ.comap (LinearMap.single ℤ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k) := by
    intro k
    rw [Submodule.span_le]
    intro z hz
    exact hsingle k z hz
  have hEΛ : E ≤ Λ := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    rw [← Finset.univ_sum_single (GlobalTheory.TraceConjugationCover.tup ρs g)]
    exact Submodule.sum_mem _ fun k _ => hspanΛ k (hρ k g)
  have hfg : Λ.FG := Submodule.fg_span (Set.finite_iUnion fun k => (t k).finite_toSet.image _)
  haveI : IsNoetherian ℤ_[l] Λ := isNoetherian_of_fg_of_noetherian Λ hfg
  let f : ℕ →o Submodule ℤ_[l] Λ :=
    ⟨fun v => (E.comap Λ.subtype).comap (((l : ℤ_[l]) ^ v) • LinearMap.id), by
      intro v w hvw y hy
      simp only [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, map_smul,
        Submodule.subtype_apply] at hy ⊢
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hvw
      rw [pow_add, mul_comm, mul_smul]
      exact E.smul_mem _ hy⟩
  have hf : ∀ v (y : Λ), y ∈ f v ↔ ((l : ℤ_[l]) ^ v) • (y : Fin m → Matrix (Fin a) (Fin a) (Om l)) ∈ E := by
    intro v y
    show y ∈ (E.comap Λ.subtype).comap (((l : ℤ_[l]) ^ v) • LinearMap.id) ↔ _
    simp only [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, map_smul,
      Submodule.subtype_apply]
  obtain ⟨u, hu⟩ := monotone_stabilizes_iff_noetherian.2 inferInstance f
  refine ⟨u, fun N M hNM H hx => ?_⟩
  obtain ⟨y, hyΛ, hxy⟩ := hlat M _ hx
  have hyM : (⟨y, hyΛ⟩ : Λ) ∈ f M := by
    rw [hf]
    show ((l : ℤ_[l]) ^ M) • y ∈ E
    rw [← hxy]
    exact hsumE H
  rw [← hu M (by omega), hf] at hyM
  have hz : ((l : ℤ_[l]) ^ (M - N - u)) • (((l : ℤ_[l]) ^ u) • y) ∈ E := E.smul_mem _ hyM
  obtain ⟨H', hH'⟩ := hEsum _ hz
  refine ⟨H', ?_⟩
  rw [hxy, ← hH', hc, smul_smul, smul_smul, ← pow_add, ← pow_add]
  congr 2
  omega

end GlobalTheory.CovSat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTauPowFrameAinfStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_tauPow_frame_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → ∀ g : ↥(GK K), τ ^ N • ((ρ g).map (Per.zA l) * Y.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • (Y * F.ε g) := by
  first | (exact @GlobalTheory.BKLim.gal_tauPow_frame) | (exact GlobalTheory.BKLim.gal_tauPow_frame) | (intros; apply GlobalTheory.BKLim.gal_tauPow_frame  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeStructureOfAdaptedInvariantFamilyStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_structure_of_adapted_invariant_family : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (x : Fin d → Fin d → P.R.BdR) (h : Fin d → ℤ), (∀ j (g : ↥(GK K)), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (x j i)) = x j) → (∀ j i, x j i ∈ (P.PD K).Fil (h j)) → (∀ y : Fin d → P.R.BdR, (∀ i, y i ∈ (P.PD K).Fil 0) → ∃ c : Fin d → P.R.BdR, (∀ j, c j ∈ (P.PD K).Fil (-h j)) ∧ y = ∑ j, c j • x j) → ∃ H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K, ∀ i, (H.p i : ℤ) - H.q = h i := by
  first | (exact @GlobalTheory.BKLim.hodge_of_adapted) | (exact GlobalTheory.BKLim.hodge_of_adapted) | (intros; apply GlobalTheory.BKLim.hodge_of_adapted  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeIffIsBaseChangeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (M : Type) [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N] (u : M →ₛₗ[algebraMap A B] N) (u' : M →ₗ[A] N), (∀ x, u' x = u x) → (SemiBC u ↔ IsBaseChange B u') := by
  first | exact @GlobalTheory.BSP.semiBC_iff_isBaseChange | exact GlobalTheory.BSP.semiBC_iff_isBaseChange | (intros; apply GlobalTheory.BSP.semiBC_iff_isBaseChange <;> assumption)
end

