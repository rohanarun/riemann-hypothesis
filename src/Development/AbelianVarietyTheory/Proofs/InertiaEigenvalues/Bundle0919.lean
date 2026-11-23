module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0912
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0913
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondField
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharValuesInNumberField
public import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameMatrixIntegralOfConjugateHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAdjInt

open Formalism.IndefR.Fin.LevelGroupLemmas.Lat Matrix

set_option synthInstance.maxHeartbeats 400000

theorem cA_smul_genE {D : D7} {S T : HSp D} (e : AE D) (c : EAf D) (τ : Fin T.rank → EAf D)
    (σ : Fin S.rank → EAf D) :
    cA D e • genE (S := S) (T := T) c τ σ = genE (sR D (toEAf D e) * c) τ σ := by
  ext i j
  simp only [genE, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_liftE, toEAf_cA, mul_assoc]


set_option maxHeartbeats 4000000 in
theorem frMapAdj_int_of_half : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ u : WO S T, u ∈ latO S T ΛS ΛT (fun _ => True) → IsHalf (cA D e) u → IsIntM (frMapAdj S T βS βT u) := by
  intro D S T ΛS ΛT βS βT hS hT fS fT P e he hP u hu hh
  have hx : cA D e • u = u := Matrix.ext fun i j => hh i j
  rw [← hx]
  clear hx hh
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, _, a, ha, s, hs, t, ht, rfl⟩ := hw
    show IsIntM (frMapAdj S T βS βT (cA D e • genL S T α a s t))
    rw [genL_eq_genE, cA_smul_genE, frMapAdj_genE]
    intro i j
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    have h1 : sR D (sR D (toEAf D e) * (eToEAf D a * ((1 : D.host.E) ⊗ₜ[D.host.F] α))) =
        (toEAf D e * eToEAf D (D.sp.cm.sig a)) * ((1 : D.host.E) ⊗ₜ[D.host.F] α) := by
      rw [map_mul, map_mul, sR_sR, sR_eTo, mul_assoc]
      congr 2
      show (star (1 : D.host.E)) ⊗ₜ[D.host.F] α = _
      rw [star_one]
    rw [h1]
    refine mul_mem (mul_mem (GlobalTheory.IdemIntegral.conj_mem_intAf D e P he hP a ha)
      (Subring.subset_closure (Or.inr ⟨⟨α, fun v => hα v⟩, rfl⟩))) (mul_mem ?_ ?_)
    · exact (fS _).1 (mem_hatL_of_mem hs) i
    · rw [Matrix.vecMul_vecMul]
      have hcol : (fun l => (GE T * (βT : Matrix (Fin T.rank) (Fin T.rank) (EAf D))) l j) =
          GE T *ᵥ (fun i => (βT : Matrix (Fin T.rank) (Fin T.rank) (EAf D)) i j) := by
        funext l; rw [Matrix.mul_apply]; rfl
      show (fun k => sR D (eToEAf D (t k))) ⬝ᵥ
        (fun l => (GE T * (βT : Matrix (Fin T.rank) (Fin T.rank) (EAf D))) l j) ∈ _
      rw [hcol]
      exact hform_int hT ht (col_mem_hatL fT j)
  | zero =>
    rw [smul_zero, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_zero]
    exact fun _ _ => zero_mem _
  | add x y _ _ hx hy =>
    rw [smul_add, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_add]
    exact isIntM_add hx hy
  | neg x _ hx =>
    rw [smul_neg, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_neg]
    exact fun i j => neg_mem (hx i j)

end GlobalTheory.HalfAdjInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AuxiliaryPrimeNeTypePrime
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.TwInputs.SmallField

theorem star_mem_of_normal {L : Type} [Field L] [CharZero L] [StarRing L] [IsGalois ℚ L] (M : IntermediateField ℚ L) (hM : IsGalois ℚ M)
    (x : L) (hx : x ∈ M) : star x ∈ M := by
  have h := (IntermediateField.normal_iff_forall_map_le (K := M)).1 hM.to_normal (starRingEnd L).toRatAlgHom
  exact h ⟨x, hx, rfl⟩

theorem exists_over (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ w.asIdeal :=
  _root_.GlobalTheory.HeightOnePrimeMembership.exists_heightOne_mem E hp

end GlobalTheory.TwInputs.SmallField

namespace GlobalTheory.TwInputs.SmallField

theorem exists_finset_rayIn (hR : GlobalTheory.NT.RayField) (P : Pre) : ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ B : Base, B.toPre = P → (∀ z ∈ S, z ∈ B.fixedCoefficientFieldInComplex) → ∀ C W V S' N G,
      GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn (assemble B C W V S' N G) (B.host.g 0 * B.host.g 1 * B.host.pde * B.host.pde')
        (embLL0 (assemble B C W V S' N G)).fieldRange := by
  let φK : P.host.K →+* ℂ := P.host.φ₀.comp (algebraMap P.host.K P.host.E)
  obtain ⟨Rf, hRf⟩ := Fld.exists_isRayFieldIn φK hR (Fld.natIdeal_ne_bot (E := P.host.K) (Fld.modulus_ne_zero P))
  haveI : NumberField Rf := hRf.numberField
  let b := Module.finBasis ℚ Rf
  refine ⟨Finset.univ.image (fun i => (b i : ℂ)), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    have h : IsAlgebraic ℚ (b i) := Algebra.IsAlgebraic.isAlgebraic _
    exact h.algHom Rf.val
  · intro B hB hS C W V S' N G
    subst hB
    have hle : Rf ≤ B.fixedCoefficientFieldInComplex := by
      intro z hz
      have hsum := congrArg Subtype.val (b.sum_repr ⟨z, hz⟩)
      rw [IntermediateField.coe_sum] at hsum
      simp only [IntermediateField.coe_smul] at hsum
      rw [← hsum]
      exact sum_mem fun i _ => IntermediateField.smul_mem _ (hS _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
    obtain ⟨hm, hNF, hray⟩ := hRf
    letI := Fld.algOf φK Rf hm
    refine ⟨Rf, inferInstance, hNF, Fld.algOf φK Rf hm, hray.1, hray.2, Rf.val.toRingHom, ?_, fun x => ?_⟩
    · ext x
      exact Fld.algOf_apply φK Rf hm x
    · obtain ⟨y, hy, e⟩ := hle x.2
      exact ⟨⟨y, hy⟩, e⟩

end GlobalTheory.TwInputs.SmallField

namespace GlobalTheory.TwInputs.SmallField

theorem one_lt_cond (P : Pre) : 1 < P.host.QS * P.host.q * P.host.d :=
  lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd (Nat.pos_of_ne_zero P.host.condN_ne_zero) P.host.sixteen_dvd_condN)

theorem exists_finset_lam (P : Pre) : ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ B : Base, B.toPre = P → (∀ z ∈ S, z ∈ B.fixedCoefficientFieldInComplex) → ∀ C W V S' N G,
      (∀ k, AbsolutelyIrreducibleSpan.q0 (assemble B C W V S' N G) ≠ B.host.g k) → ∀ cf : CharFrame (assemble B C W V S' N G),
        ∃ Z : GlobalTheory.LamTie.LamDat (assemble B C W V S' N G), Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧
          Z.q0 = AbsolutelyIrreducibleSpan.q0 (assemble B C W V S' N G) ∧ ∀ a, (Z.chi a).ValuesIn 0 (embLL0 (assemble B C W V S' N G)) := by
  classical
  by_cases hq : ∀ k, GlobalTheory.EX.DC.q0H P.host ≠ P.host.g k
  swap
  · refine ⟨∅, by simp, fun B hB _ C W V S' N G h => ?_⟩
    subst hB
    exact absurd h hq
  have hqp := (GlobalTheory.EX.DC.globalTwisting_spec_fact P.host).1
  obtain ⟨w0, hw0⟩ := exists_over P.host.E hqp
  have hmod : ∀ p ∈ [P.host.g 0, P.host.g 1, P.host.pde, P.host.pde', GlobalTheory.EX.DC.q0H P.host],
      p ≡ 1 [MOD P.host.QS * P.host.q * P.host.d] := by
    intro p hp
    rw [Nat.ModEq, Nat.mod_eq_of_lt (one_lt_cond P)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    exacts [P.g_cond 0, P.g_cond 1, P.pde_cond.1, P.pde_cond.2, GlobalTheory.EX.DC.mod_cond _]
  obtain ⟨hPl, -⟩ := GlobalTheory.LamTie.placesOk_of_modEq_one P.R P.host _ w0 hqp hmod (fun k => hq k)
    (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' _).1 (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' _).2 hw0
  obtain ⟨χ, hχ, hT⟩ := GlobalTheory.LamTie.TeichEx.exists_auxiliaryHeckeCharacter_trivial_tame_part P.R P.host _ w0
    (fun g => (BlochKatoReduction.Gen.NFun P.R : ℤ) + 2 + ∑ j : Fin P.R.m, ⌈|(P.hc g).e j|⌉) hPl
    (UpperTheory.Mu.w_add_one_lt P.host hqp.one_lt 1 (by rw [one_mul]; exact GlobalTheory.EX.DC.mod_cond _))
  obtain ⟨n, hn, hinf⟩ := hχ.inf
  obtain ⟨cc, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm P.R P.host
  obtain ⟨M, hM, hv⟩ := GlobalTheory.Mem.ValAlg.values_in_numberField P.host.F P.host.E cc P.R.Psi (embPsi P.host) hcm χ n 0 hinf
    (fun g => by
      have h1 : (n g : ℚ) = 2 * (((BlochKatoReduction.Gen.NFun P.R : ℤ) + 2 + ∑ j : Fin P.R.m, ⌈|(P.hc g).e j|⌉ : ℤ) : ℚ) := hn g
      have h2 : n g = 2 * ((BlochKatoReduction.Gen.NFun P.R : ℤ) + 2 + ∑ j : Fin P.R.m, ⌈|(P.hc g).e j|⌉) := by exact_mod_cast h1
      exact ⟨(BlochKatoReduction.Gen.NFun P.R : ℤ) + 2 + ∑ j : Fin P.R.m, ⌈|(P.hc g).e j|⌉, by omega⟩)
  rw [Int.cast_zero, zero_div] at hv
  haveI := hM
  obtain ⟨α, hα, gα⟩ := GlobalTheory.Mem.DatHecke.exists_gen M
  refine ⟨{α}, by simpa using hα, fun B hB hS C W V S' N G _ cf => ?_⟩
  subst hB
  obtain ⟨x, hx, ex⟩ := hS α (Finset.mem_singleton_self _)
  have hM' : ∀ z ∈ M, ∃ y, embLL0 (assemble B C W V S' N G) y = z := gα B.LL0 (embLL0 (assemble B C W V S' N G)) ⟨⟨x, hx⟩, by exact ex⟩
  refine ⟨⟨cf, _, w0, fun _ g => (BlochKatoReduction.Gen.NFun B.R : ℤ) + 2 + ∑ j : Fin B.R.m, ⌈|(B.hc g).e j|⌉, fun _ => χ⟩,
    ⟨hPl, fun _ => hχ, fun j a g => ?_⟩, fun _ => hT, rfl, rfl, fun _ => GlobalTheory.Mem.Col2.InEx.valuesIn_of hv _ hM'⟩
  show (BlochKatoReduction.Gen.NFun B.R : ℚ) + 1 < (B.hc g).e j + (((BlochKatoReduction.Gen.NFun B.R : ℤ) + 2 + ∑ j : Fin B.R.m, ⌈|(B.hc g).e j|⌉ : ℤ) : ℚ)
  have h1 : ⌈|(B.hc g).e j|⌉ ≤ ∑ j' : Fin B.R.m, ⌈|(B.hc g).e j'|⌉ :=
    Finset.single_le_sum (f := fun j' => ⌈|(B.hc g).e j'|⌉) (fun j' _ => Int.ceil_nonneg (abs_nonneg _)) (Finset.mem_univ j)
  have h2 : -(B.hc g).e j ≤ ((⌈|(B.hc g).e j|⌉ : ℤ) : ℚ) := (neg_le_abs _).trans (Int.le_ceil _)
  have h3 : ((⌈|(B.hc g).e j|⌉ : ℤ) : ℚ) ≤ ((∑ j' : Fin B.R.m, ⌈|(B.hc g).e j'|⌉ : ℤ) : ℚ) := by exact_mod_cast h1
  push_cast at h3 ⊢
  linarith

end GlobalTheory.TwInputs.SmallField

namespace GlobalTheory.TwInputs.SmallField

theorem lg_rayIn (hR : GlobalTheory.NT.RayField) (K : Ctx) : large₂ K fun B _ _ => ∀ C W V S' N G,
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn (assemble B C W V S' N G) (B.host.g 0 * B.host.g 1 * B.host.pde * B.host.pde')
      (embLL0 (assemble B C W V S' N G)).fieldRange := by
  choose S hS gS using exists_finset_rayIn hR
  exact ⟨fun B _ _ => S B, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun B _ _ => hS B, by simp,
    fun B _ _ _ hH _ _ => gS B.toPre B rfl hH.1⟩

theorem lg_lam (K : Ctx) : large₂ K fun B _ _ => ∀ C W V S' N G,
    (∀ k, AbsolutelyIrreducibleSpan.q0 (assemble B C W V S' N G) ≠ B.host.g k) → ∀ cf : CharFrame (assemble B C W V S' N G),
      ∃ Z : GlobalTheory.LamTie.LamDat (assemble B C W V S' N G), Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧
        Z.q0 = AbsolutelyIrreducibleSpan.q0 (assemble B C W V S' N G) ∧ ∀ a, (Z.chi a).ValuesIn 0 (embLL0 (assemble B C W V S' N G)) := by
  choose S hS gS using exists_finset_lam
  exact ⟨fun B _ _ => S B, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun B _ _ => hS B, by simp,
    fun B _ _ _ hH _ _ => gS B.toPre B rfl hH.1⟩

theorem lg_fieldOk (hR : GlobalTheory.NT.RayField) (K : Ctx) : large₂ K fun B f _ => ∀ C W V S' N G,
    ValLL0 (assemble B C W V S' N G) (Fr.at ⟨B, C, W, V, S', N, G⟩ f) ∧
    (∀ X : RealSide (assemble B C W V S' N G), X.R.C = Fr.at ⟨B, C, W, V, S', N, G⟩ f → FieldOk X) ∧
    ((∀ k, AbsolutelyIrreducibleSpan.q0 (assemble B C W V S' N G) ≠ B.host.g k) →
      ∃ Z : GlobalTheory.LamTie.LamDat (assemble B C W V S' N G), Z.Ok ∧ Z.Teich ∧ Z.C = Fr.at ⟨B, C, W, V, S', N, G⟩ f ∧
        Z.q0 = AbsolutelyIrreducibleSpan.q0 (assemble B C W V S' N G) ∧ ∀ a, (Z.chi a).ValuesIn 0 (embLL0 (assemble B C W V S' N G))) := by
  refine (((GlobalTheory.Mem.Col2.InEx.lg_colIn K).inter (lg_rayIn hR K)).inter (lg_lam K)).imp fun B f T _ h C W V S' N G => ?_
  obtain ⟨⟨⟨-, hval, -⟩, hray⟩, hlam⟩ := h
  refine ⟨hval C W V S' N G, fun X hX => ⟨B.coeffGaloisSubfield_isGalois, fun x => star_mem_of_normal B.LL0 B.coeffGaloisSubfield_isGalois _ x.2, ?_,
    hray C W V S' N G, fun k z hz => ?_,
    ⟨B.toPre.level_split _ B.host.pde_level.1, B.toPre.level_split _ B.host.pde_level.2⟩⟩, fun hq => hlam C W V S' N G hq _⟩
  · rw [hX]
    exact hval C W V S' N G
  · have h0 : B.host.g k * (B.host.g k - 1) ≠ 0 :=
      mul_ne_zero (B.host.g_prime k).ne_zero (by have := (B.host.g_prime k).two_le; omega)
    obtain ⟨x, hx, e⟩ := B.roots_Ks (B.host.g k * (B.host.g k - 1)) (by fin_cases k <;> simp)
    obtain ⟨y, hy⟩ := GlobalTheory.Mem.Col2.InEx.root_mem (embLL0 (assemble B C W V S' N G)) h0 ⟨⟨x, B.Ks_le hx⟩, e⟩ hz
    exact ⟨y, hy⟩

end GlobalTheory.TwInputs.SmallField

namespace GlobalTheory.TwInputs.SmallField

open Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem auxiliary_prime_ne_type_prime (K : Ctx) (C5 c6 Cb : ℝ) (h : K.Good C5 c6 Cb) (P : Pre) (hP : K.Over P) (k : Fin 2) :
    GlobalTheory.EX.DC.q0H P.host ≠ P.host.g k := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := hP
  exact h.ok.small.2.2.2.1 k

theorem cf_eq_at (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) :
    TC.cf w.I w.l Z = Fr.at (w.st Z) f := by
  obtain ⟨px, I, ok, rfl, S_eq, xr, pins, l, l0, δ, ex, fld, val⟩ := w
  rfl

end GlobalTheory.TwInputs.SmallField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChoiceSideWithE
section
noncomputable section

namespace GlobalTheory.ChoiceRead

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section Choice

variable {D : D7}

abbrev Tgt (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ) : Type :=
  FractionRing (c.Oe w) ⊗[D.ntw.Ok (c.twI w) (c.k' w)]
    D.nexp.MtV (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w)))

def BasisAt (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ)
    (e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j) : Prop :=
  ∀ b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j),
    LinearIndependent (FractionRing (c.Oe w)) (fun i => e (b i)) ∧
      Submodule.span (FractionRing (c.Oe w)) (Set.range fun i => e (b i)) = ⊤

def latT (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ) : Submodule (c.Oe w) (Tgt c w j) :=
  Submodule.span (c.Oe w)
      ((TensorProduct.mk (D.ntw.Ok (c.twI w) (c.k' w)) (FractionRing (c.Oe w))
          (D.nexp.MtV (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w)))) 1) ''
        (D.nexp.MtLat (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))) :
          Set (D.nexp.MtV (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))))))

def latS (w : D.what₂.places.Pl) (j : ℕ) : Set (D.what₂.MtL (D.what₂.muTw w) j) :=
  {x | D.what₂.jMt (D.what₂.muTw w) j x ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen}

def LatAt (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ)
    (e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j) (t : FractionRing (c.Oe w)) : Prop :=
  Submodule.span (c.Oe w) (e '' latS w j) = Submodule.span (c.Oe w) ((fun y => t • y) '' (latT c w j : Set (Tgt c w j)))

theorem BasisAt.smul {c : NChoice D} {w : D.what₂.places.Pl} {j : ℕ}
    {e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j} (h : BasisAt c w j e) (u : (FractionRing (c.Oe w))ˣ) :
    BasisAt c w j ((u : FractionRing (c.Oe w)) • e) := by
  intro b
  obtain ⟨h1, h2⟩ := h b
  refine ⟨?_, ?_⟩
  · exact h1.units_smul (fun _ => u)
  · have h3 : (Set.range fun i => ((u : FractionRing (c.Oe w)) • e) (b i)) =
        (u : FractionRing (c.Oe w)) • Set.range fun i => e (b i) := by
      rw [← Set.range_smul]; rfl
    rw [h3, Submodule.span_smul_eq_of_isUnit _ _ u.isUnit, h2]

theorem LatAt.smul_inv {c : NChoice D} {w : D.what₂.places.Pl} {j : ℕ}
    {e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j} (u : (FractionRing (c.Oe w))ˣ)
    (h : LatAt c w j e (u : FractionRing (c.Oe w))) :
    Submodule.span (c.Oe w) ((((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • e) '' latS w j) = latT c w j := by
  let f : Tgt c w j →ₗ[c.Oe w] Tgt c w j :=
    { toFun := fun y => ((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • y
      map_add' := fun _ _ => smul_add _ _ _
      map_smul' := fun r y => by
        simp only [RingHom.id_apply]
        rw [← algebraMap_smul (FractionRing (c.Oe w)) r y, ← algebraMap_smul (FractionRing (c.Oe w)) r,
          smul_smul, smul_smul, mul_comm] }
  have h1 : ((((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • e) '' latS w j) = f '' (e '' latS w j) := by
    rw [Set.image_image]; rfl
  rw [h1, Submodule.span_image, h, ← Submodule.span_image, Set.image_image]
  have h2 : (fun y => f ((u : FractionRing (c.Oe w)) • y)) = id := by
    funext y
    show ((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • ((u : FractionRing (c.Oe w)) • y) = y
    rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [h2, Set.image_id, Submodule.span_eq]

def withE (c : NChoice D) (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j) : NChoice D :=
  { c with
    eMt := E
    eMt_basis := fun w j hw h1 h2 b => hb w j hw h1 h2 b
    eMt_lat := fun w j hw h1 h2 => hl w j hw h1 h2 }

def tupWithE {cf : CharFrame D} {c : NChoice D} (tp : TupTied D cf c) (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j) : TupTied D cf (withE c E hb hl) :=
  { tp with }

theorem choiceSide_withE {cf : CharFrame D} {mt : MtFam D} {exp : NExpTied D} {c : NChoice D} {tp : TupTied D cf c}
    (h : GlobalTheory.HeightCounting.ChoiceSide D cf mt exp c tp) (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j) :
    GlobalTheory.HeightCounting.ChoiceSide D cf mt exp (withE c E hb hl) (tupWithE tp E hb hl) :=
  ⟨⟨h.nct.twOf_eq, h.nct.twSide_eq, h.nct.Q_eq, h.nct.psi_eq, h.nct.embedding_baseField_condition⟩,
    ⟨h.choice.twI_conj, h.choice.sd_place, h.choice.emb_side, h.choice.sd_conj, h.choice.one, h.choice.conj⟩,
    h.off, h.adm, h.psi, h.eMt_level⟩


open Classical in
def pick (c : NChoice D)
    (G : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ i : Fin D.R.m,
      D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1)) :
    ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j
  | w, 0 => c.eMt w 0
  | w, k + 1 => if h : D.what₂.muAt w ≠ D.what₂.mu0 ∧ k < D.R.m then G w h.1 ⟨k, h.2⟩ else c.eMt w (k + 1)

theorem pick_eq (c : NChoice D)
    (G : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ i : Fin D.R.m,
      D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1))
    (w : D.what₂.places.Pl) (hw : D.what₂.muAt w ≠ D.what₂.mu0) (i : Fin D.R.m) : pick c G w (i.1 + 1) = G w hw i := by
  simp only [pick, dite_eq_left (And.intro hw i.2)]

theorem pick_prop (c : NChoice D)
    (G : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ i : Fin D.R.m,
      D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1))
    (p : ∀ w j, (D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j) → Prop)
    (h : ∀ w hw (i : Fin D.R.m), p w (i.1 + 1) (G w hw i)) :
    ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → p w j (pick c G w j) := by
  intro w j hw h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have := h w hw ⟨k, by omega⟩
  rwa [← pick_eq c G w hw ⟨k, by omega⟩] at this

end Choice

section Rows

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {S : RatDat D.ntw}

def ThetaAt (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (YS : NExpRealS R cG S) (c : NChoice D) (w : D.what₂.places.Pl)
    (i : Fin D.R.m) (e : D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1)) (t : FractionRing (c.Oe w)) :
    Prop :=
  ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (i.1 + 1), ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK S (i.1 + 1)),
    (R.FW i).j (sg0 D A3.A) ((YS.fi i).e (∑ k, a k • (show ↥(S.A (i.1 + 1)).WK from f k).1)) =
      Y.mj.eW i (D.what₂.thetaP (D.what₂.muTw w) (i.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (i.1 + 1) x)) →
    NChoice.thPe D c w (i.1 + 1) (e x) =
      t • ∑ k, c.embW w (a k) ⊗ₜ[D.ntw.O (c.twI w)]
        (YS.eF (c.twI w) (i.1 + 1) (c.sd w) (by omega) (by omega)).symm ((1 : KB S (c.twI w) (c.sd w)) ⊗ₜ[S.Ks] f k)

theorem ThetaAt.smul_inv {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {YS : NExpRealS R cG S} {c : NChoice D}
    {w : D.what₂.places.Pl} {i : Fin D.R.m} {e : D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1)}
    (u : (FractionRing (c.Oe w))ˣ) (h : ThetaAt Y YS c w i e (u : FractionRing (c.Oe w))) :
    ThetaAt Y YS c w i ((((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w))) • e) 1 := by
  intro x hx n a f hf
  rw [one_smul, LinearMap.smul_apply, map_smul, h x hx n a f hf, smul_smul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_smul]

theorem emtTheta_withE {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {YS : NExpRealS R cG S} {c : NChoice D}
    (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j)
    (h : ∀ w (i : Fin D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 → ThetaAt Y YS c w i (E w (i.1 + 1)) 1) :
    GlobalTheory.HeightCounting.EMtTheta Y YS (withE c E hb hl) := by
  intro w i hw x hx n a f hf
  have := h w i hw x hx n a f hf
  rw [one_smul] at this
  exact this

end Rows

end GlobalTheory.ChoiceRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsShiftedVectorShintaniFormulaRamifiedStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_shifted_vector_shintani_formula_ramified : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (π : CuspSub E (m + 1)), π.IsUnitary → ∀ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ),
    (∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∃ F ∈ GlobalTheory.JSW.mspanR π, ∃ l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, l₀.1 w (Fin.last m) = 0) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧
      (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
        (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, F (g * k) = F g) ∧
      GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
        GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * p ∈ C) ∧
      ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
        GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ (l₀.1 + l.1)) = GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) *
          ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else
            GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (l.1 w)) := by
  first
  | exact @GlobalTheory.RamShift.exists_shifted_bump_shintani
  | exact GlobalTheory.RamShift.exists_shifted_bump_shintani
  | (intros; apply GlobalTheory.RamShift.exists_shifted_bump_shintani <;> assumption)
end

