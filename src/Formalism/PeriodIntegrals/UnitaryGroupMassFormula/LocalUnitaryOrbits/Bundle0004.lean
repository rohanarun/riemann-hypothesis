module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IsCompactSpanRange

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfOpen
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

end PI.OmLocU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ExistsIntBasis
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.VolStabSW
  PI.VolStabSW.PositiveNearLattice PI.VolStabSW.SdDualW
open scoped TensorProduct

section Top

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def oevS : AddSubgroup (Fv F v ⊗[F] E) :=
  (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).toAddSubgroup

theorem coe_oevS : (oevS (E := E) v : Set (Fv F v ⊗[F] E)) = OEv (E := E) v := rfl

theorem inclR_mem_oev (x : 𝓞 E) : inclR (F := F) (Fv F v) (x : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨x, Set.mem_univ _, rfl⟩

theorem exists_int_basis : ∃ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ k, IsIntegral ℤ (b k) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  classical
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image (Module.finBasis F E))
  have hyF : IsUnit ((y : F)) := by
    rw [isUnit_iff_ne_zero]
    exact_mod_cast hy
  refine ⟨_, (Module.finBasis F E).isUnitSMul (fun _ => hyF), fun k => ?_⟩
  rw [Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]
  exact hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))

theorem latA_le_oevS [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (hb : ∀ k, IsIntegral ℤ (b k)) : latA v b ≤ oevS (E := E) v := by
  intro z hz
  have hz' : ∀ k, crd b (Fv F v) z k ∈ v.adicCompletionIntegers F := hz
  rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply]
  have hm : inclR (F := F) (Fv F v) (((⟨b k, hb k⟩ : 𝓞 E)) : E) ∈ OEv (E := E) v :=
    inclR_mem_oev v (⟨b k, hb k⟩ : 𝓞 E)
  exact Submodule.smul_mem _ (⟨_, hz' k⟩ : v.adicCompletionIntegers F) hm

theorem isOpen_oev : IsOpen (OEv (E := E) v) := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨d, b, hb⟩ := exists_int_basis (F := F) (E := E)
  rw [← coe_oevS]
  exact AddSubgroup.isOpen_mono (latA_le_oevS v b hb) (isOpen_latA v b)

theorem isCompact_oev : IsCompact (OEv (E := E) v) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  set g : Fin m → Fv F v ⊗[F] E := fun i => inclR (F := F) (Fv F v) ((s i : 𝓞 E) : E) with hg
  have e : OEv (E := E) v = (fun c : Fin m → Fv F v => ∑ i, c i • g i) ''
      Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext z
    constructor
    · intro hz
      have h1 : z ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range g) := by
        refine (Submodule.span_le.2 ?_) hz
        rintro _ ⟨x, _, rfl⟩
        have hx : x ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; exact Submodule.mem_top
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact Submodule.subset_span ⟨i, rfl⟩
        | zero => simpa using Submodule.zero_mem _
        | add p q _ _ hp hq =>
          have e1 : inclR (F := F) (Fv F v) (((p + q : 𝓞 E)) : E) =
              inclR (F := F) (Fv F v) (p : E) + inclR (F := F) (Fv F v) (q : E) := by
            rw [← map_add (f := _)]
            rfl
          show inclR (F := F) (Fv F v) (((p + q : 𝓞 E)) : E) ∈ _
          rw [e1]
          exact Submodule.add_mem _ (hp trivial) (hq trivial)
        | smul r p _ hp =>
          have e1 : inclR (F := F) (Fv F v) (((r • p : 𝓞 E)) : E) =
              r • inclR (F := F) (Fv F v) (p : E) := by
            rw [show ((r • p : 𝓞 E) : E) = r • (p : E) from map_zsmul (algebraMap (𝓞 E) E) r p,
              map_zsmul]
          show inclR (F := F) (Fv F v) (((r • p : 𝓞 E)) : E) ∈ _
          rw [e1]
          exact zsmul_mem (hp trivial) r
      rw [Submodule.mem_span_range_iff_exists_fun] at h1
      obtain ⟨c, rfl⟩ := h1
      exact ⟨fun i => (c i : Fv F v), fun i _ => (c i).2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ (⟨c i, hc i (Set.mem_univ _)⟩ : v.adicCompletionIntegers F)
          (inclR_mem_oev v (s i))
  rw [e]
  exact (isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image
    (continuous_finsetSum _ fun i _ => by fun_prop)

variable (σ : E →ₐ[F] E)

theorem coe_HO (a : ℕ) : (HO σ v a : Set (HermR (Fv F v) σ a)) =
    Subtype.val ⁻¹' (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a => OEv (E := E) v) := by
  ext S
  constructor
  · intro h
    rw [SetLike.mem_coe, mem_HO] at h
    exact fun i _ j _ => h i j
  · intro h
    rw [SetLike.mem_coe, mem_HO]
    exact fun i j => h i (Set.mem_univ _) j (Set.mem_univ _)

theorem topH_holds (a : ℕ) : TopH σ v a := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a => OEv (E := E) v) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_oev v
  have := locallyCompact_Fv F v
  refine ⟨?_, ?_⟩
  · rw [coe_HO]
    exact (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal.isCompact_preimage hK
  · rw [coe_HO]
    exact (isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => isOpen_oev v).preimage continuous_subtype_val

end Top

end PI.OmLocU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.FibTop
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem omLocU_of' (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (hU : UnifEx v)
    (h1 : OrbAll σ J ψ v Λ a Y) (h2 : FibU' σ J ψ v Λ a Y) (h3 : CountU σ J ψ v Λ a Y)
    (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y := by
  have h2' : FibU σ J ψ v Λ a Y := by
    intro hG hfib ϖ hϖ
    obtain ⟨hW, hH⟩ := hSd hG.1
    exact h2 hG hW hH hfib ϖ hϖ
  exact omLocU_of σ J ψ v Λ a Y hSd hOm hU h1 h2' h3 h4 h5

theorem omLocU_of_fib (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a)
    (h1 : OrbAll σ J ψ v Λ a Y) (hL : LamOC v Λ a) (hH : HermOC σ v a) (hHe : FibHens σ J ψ v Λ a Y)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of' σ J ψ v Λ a Y hSd hOm (unifEx_holds v) h1 (fibU'_of σ J ψ v Λ a Y hL hH hHe) h3 h4 h5

theorem omLocU_of_hens (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (h1 : OrbAll σ J ψ v Λ a Y)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hHe : FibHens σ J ψ v Λ a Y)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of_fib σ J ψ v Λ a Y hSd hOm h1 (lamOC_holds v Λ a hFull) (hermOC_holds v σ a) hHe h3 h4 h5

end PI.OmLocU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfNorm
section
noncomputable section

namespace PI.OmLocU.Orb

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem sigma_invol (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  apply τ.toRingHom.injective
  have h1 := hcm.2.2.2 τ.toRingHom (σ x)
  have h2 := hcm.2.2.2 τ.toRingHom x
  rw [h1, h2, star_star]

theorem sigR_invol (hcm : IsCMExt F E σ) (z : Fv F v ⊗[F] E) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.map_tmul, sigma_invol σ hcm]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sigR_inclR (e : E) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (inclR (F := F) (Fv F v) e) = inclR (F := F) (Fv F v) (σ e) := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]

theorem hR_conj (hcm : IsCMExt F E σ) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → Fv F v ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (hR (Fv F v) σ J x y) = hR (Fv F v) σ J y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, hform, map_sum, map_mul, sigR_invol σ v hcm, JR, Matrix.map_apply, sigR_inclR, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def NormOne : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ u ∈ OEv (E := E) v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ u = u →
    (∃ u' ∈ OEv (E := E) v, u * u' = 1) →
    ∃ l ∈ OEv (E := E) v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ l * l * u = 1

def UnitNorm : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E), (∀ i, X i ∈ latLoc (E := E) v Λ) →
      UniG σ J v X → Fintype.card ι < n →
      ∃ p ∈ PerpG σ J v Λ X, ∃ u' ∈ OEv (E := E) v, hR (Fv F v) σ J p p * u' = 1

theorem unitV_of (hN : NormOne σ J ψ v) (hUN : UnitNorm σ J ψ v Λ) : UnitV σ J ψ v Λ := by
  intro hstd hL hsd hun ι _ _ X hX hUX hc
  obtain ⟨p, hp, u', hu'0, hu'⟩ := hUN hstd hL hsd hun ι X hX hUX hc
  have hcm := hstd.1
  have hJ := hstd.2.1.1
  have hu0 : hR (Fv F v) σ J p p ∈ OEv (E := E) v := (hsd p).1 hp.1 p hp.1
  obtain ⟨l, hl0, hl⟩ := hN hstd hun _ hu0 (hR_conj σ J v hcm hJ p p) ⟨u', hu'0, hu'⟩
  have hXl : ∀ i, hR (Fv F v) σ J (X i) (l • p) = 0 := by
    intro i
    rw [hR_smul_right, hp.2 i, mul_zero]
  refine ⟨l • p, ⟨oSmul v Λ hL l hl0 p hp.1, hXl⟩, ?_, ?_⟩
  · rw [hR_smul_left, hR_smul_right, ← mul_assoc]
    exact hl
  · intro i
    rw [← hR_conj σ J v hcm hJ, hXl i, map_zero]

theorem orbAll_of_norm (a : ℕ) (Y : TupV (E := E) v n a) (hN : NormOne σ J ψ v)
    (hUN : UnitNorm σ J ψ v Λ) : OrbAll σ J ψ v Λ a Y :=
  orbAll_of_unitV σ J ψ v Λ a Y (unitV_of σ J ψ v Λ hN hUN)

end PI.OmLocU.Orb
end
end

