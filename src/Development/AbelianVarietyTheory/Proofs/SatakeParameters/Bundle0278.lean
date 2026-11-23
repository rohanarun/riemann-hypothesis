module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0268
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0272
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0249
public import Formalism.LocalToGlobal.Columns.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
public import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PNeatB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0159
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0267
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MqRowSGUnif
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.LatSOfLocBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterization
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0008
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormCharacterGaloisCofinite
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
open Pointwise

namespace GlobalTheory

theorem trivial_on_ext_of_frob_eq_normChar : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] (η : HChar K), UpperTheory.V.Published.IsNormChar M η → ∀ χ : G K Ω →* ℂˣ, IsOpen (χ.ker : Set (G K Ω)) → (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∀ (A : ValuationSubring Ω) (σ : G K Ω), IsPlaceOver A v → IsFrob A (normV v) σ → χ σ = η.val v) → ∀ g : G K Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) → χ g = 1 := by
  intro Ω _ K _ _ _ _ M _ _ _ _ _ _ η hη χ hχo hχ g hg
  classical
  let r : G M Ω →* G K Ω := AlgEquiv.restrictScalarsHom K
  have hr : Continuous r := GlobalTheory.WeilRes.continuous_res
  let u : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 K) := fun w => w.under (𝓞 K)
  have hu : ∀ w : HeightOneSpectrum (𝓞 M), w.asIdeal.LiesOver (u w).asIdeal := fun w => ⟨rfl⟩
  have hS := Filter.eventually_cofinite.1 hχ
  have hT₁ := Filter.eventually_cofinite.1 hη.2.2
  let T : Set (HeightOneSpectrum (𝓞 M)) :=
    {w | ¬ ∀ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f → η.val (w.under (𝓞 K)) ^ f = 1} ∪
      u ⁻¹' {v | ¬ ∀ (A : ValuationSubring Ω) (σ : G K Ω), IsPlaceOver A v → IsFrob A (normV v) σ → χ σ = η.val v}
  have hT : T.Finite := hT₁.union (hS.preimage' (f := u) fun v _ => by
    have := v.isMaximal
    refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).preimage
      (f := fun w : HeightOneSpectrum (𝓞 M) => w.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro w rfl
    exact ⟨w.isPrime, hu w⟩)
  have hdense := GlobalTheory.Published.chebotarevDegreeOne'.dense (F := M) (Ω := Ω) hT
  let H : Subgroup (G M Ω) := (χ.comp r).ker
  have hHc : IsClosed (H : Set (G M Ω)) := H.isClosed_of_isOpen (by exact hχo.preimage hr)
  have hsub : {σ : G M Ω | ∃ w : HeightOneSpectrum (𝓞 M), w ∉ T ∧ w.asIdeal.inertiaDeg ℤ = 1 ∧
      ∃ B : ValuationSubring Ω, IsPlaceOver B w ∧ IsFrob B (normV w) σ} ⊆ H := by
    rintro σ ⟨w, hw, hd, B, hB, hσ⟩
    have hw1 : ∀ f : ℕ, normV w = normV (u w) ^ f → η.val (u w) ^ f = 1 := by
      by_contra h; exact hw (Or.inl h)
    have hw2 : ∀ (A : ValuationSubring Ω) (σ : G K Ω), IsPlaceOver A (u w) → IsFrob A (normV (u w)) σ →
        χ σ = η.val (u w) := by
      by_contra h; exact hw (Or.inr h)
    have hp : (Ideal.absNorm w.asIdeal).Prime :=
      ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified M).1 w).2 hd
    have hn : Ideal.absNorm (u w).asIdeal = Ideal.absNorm w.asIdeal := by
      haveI := hu w
      have h := Ideal.absNorm_pow_inertiaDeg (u w).asIdeal w.asIdeal
      have h1 := Nat.Prime.eq_one_of_pow (h ▸ hp)
      rw [h1, pow_one] at h
      exact h
    have hnv : normV w = normV (u w) := by
      simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
      exact hn.symm
    have hBv : IsPlaceOver B (u w) := fun x => by
      have e : algebraMap K Ω (x : K) = algebraMap M Ω ((algebraMap (𝓞 K) (𝓞 M) x : 𝓞 M) : M) := by
        rw [IsScalarTower.algebraMap_apply K M Ω]; rfl
      rw [e]
      exact hB _
    have hrσ : IsFrob B (normV (u w)) (r σ) := by
      refine ⟨?_, fun x hx => ?_⟩
      · have h : σ • B = B := hσ.1
        show (σ.restrictScalars K) • B = B
        ext x
        conv_rhs => rw [← h]
        rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
          ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
        rfl
      · rw [← hnv]; exact hσ.2 x hx
    have h1 : χ (r σ) = η.val (u w) := hw2 B (r σ) hBv hrσ
    have h2 : η.val (u w) ^ 1 = 1 := hw1 1 (by rw [pow_one]; exact hnv)
    rw [pow_one] at h2
    show χ (r σ) = 1
    rw [h1, h2]
  have hall : ∀ τ : G M Ω, τ ∈ H := fun τ => hHc.closure_subset_iff.2 hsub (hdense τ)
  let τ : G M Ω := { g.toRingEquiv with commutes' := hg }
  have hτ : r τ = g := AlgEquiv.ext fun _ => rfl
  have := hall τ
  show χ g = 1
  rw [← hτ]
  exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodBoundOfJetLoss
section
noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound

section Val

variable {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

theorem vAdd_mul_of_ne {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy), neg_add]

theorem vAdd_pow_eq (x : K) (n : ℕ) : vAdd w (x ^ n) = n * vAdd w x := by
  unfold vAdd
  rw [map_pow, WithZero.log_pow]
  simp

theorem vAdd_prod_of_ne {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i, f i ≠ 0) :
    vAdd w (∏ i ∈ s, f i) = ∑ i ∈ s, vAdd w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vAdd]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, vAdd_mul_of_ne w (h a) (Finset.prod_ne_zero_iff.2 fun i _ => h i), ih]

theorem vAdd_nonneg_of_le {x : K} (hx : x ≠ 0) (h : w.valuation K x ≤ 1) : 0 ≤ vAdd w x := by
  unfold vAdd
  have := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 hx) one_ne_zero).2 h
  rw [WithZero.log_one] at this
  omega

theorem mem_of_vAdd_pos {a : 𝓞 K} (h : 0 < vAdd w (a : K)) : a ∈ w.asIdeal := by
  by_contra hn
  have h1 : w.valuation K (a : K) = 1 := (w.valuation_eq_one_iff_notMem (K := K)).2 hn
  rw [vAdd, h1, WithZero.log_one] at h
  omega

end Val

theorem sum_nuW_nonneg {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (u : Pr.Word) {j : ℕ} (hj : j < R.m)
    (τ : X.Tau) : 0 ≤ ∑ a, (W.nuW u (j + 1) τ).w a := by
  obtain ⟨s, s', ⟨h1, h2, -⟩, h3⟩ := chainWeights X Pr R W u j hj
  refine Finset.sum_nonneg fun a _ => ?_
  have h4 := (W.lamTrue u (j + 1) τ).anti (show Fin.castLE (N_lt_succ R j).le a ≤ ⟨R.N j, N_lt_succ R j⟩ from a.2.le)
  rw [h2 τ _ le_rfl] at h4
  rw [← h3, ← h1]
  omega

theorem recWts_ok {D : D7} (EX : ErrX D) : (recWts EX).Ok := by
  exact
    { row_ok τ := ⟨D.hc τ, rfl⟩
      hc_row := recWts_row EX
      u_first u u' τ h := (D.hcW_first u τ h).trans (D.hcW_first u' τ h).symm
      u_last u u' τ h := (D.hcW_last u τ (by omega)).trans (D.hcW_last u' τ (by omega)).symm }

theorem emb_star_piG {D : D7} (EX : ErrX D) (i : Fin 2) (τ : D.what₂.Tau) :
    (recFields D).emb τ (@star _ (recFields D).starE.toStar (((recPrimes EX).piG i : 𝓞 D.host.E) : D.host.E)) = tauPib EX i τ := by
  have h : ∀ x : D.host.E, @star _ (recFields D).starE.toStar x = D.host.conj x := fun x => by
    apply D.host.φ₀.injective
    let _ := D.host.isCMField_hostE
    change D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
    rw [NumberField.IsCMField.complexEmbedding_complexConj]
    exact (D.host.toHostAx.conjE_apply D.host.φ₀ x).symm
  rw [h]
  rfl

theorem vG_loss_le {D : D7} (L : SizeData₂ D) (EX : ErrX D) (hPr : (recPrimes EX).Ok) (i : Fin 2) (w : LiftErrorLocal.Pl D)
    (hw : LiftErrorLocal.Over D i w) (u : D.what₂.Word) :
    (∀ j, lossAt (Pr := recPrimes EX) (recWts EX) i u j ≠ 0) ∧
    LiftErrorLocal.vG D w (∏ j ∈ Finset.range D.R.m, lossAt (Pr := recPrimes EX) (recWts EX) i u j) ≤
      (∑ j ∈ LiftErrorLocal.lifts D, vNN EX i u j w) + LiftErrorLocal.errC D L := by
  have hg0 : (D.host.g i : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero
  have hπ : ∀ τ, tauPib EX i τ ≠ 0 := by
    intro τ h
    have h1 : (recFields D).emb τ (((recFields D).conjO (EX.piG i) : 𝓞 D.host.E) : D.host.E) = 0 :=
      (emb_star_piG EX i τ).trans h
    have h2 : (recFields D).conjO (EX.piG i) = 0 := RingOfIntegers.ext ((map_eq_zero _).1 h1)
    have h3 := hPr.piG_norm i
    change EX.piG i * (recFields D).conjO (EX.piG i) = _ at h3
    rw [h2, mul_zero] at h3
    exact (hPr.g_prime i).ne_zero (by exact_mod_cast h3.symm)
  have e : ∀ j, lossAt (Pr := recPrimes EX) (recWts EX) i u j = (D.host.g i : D.what₂.LL) ^ (D.R.f * D.R.N j * D.R.N (j + 1)) *
      ∏ τ, tauPib EX i τ ^ (∑ a, ((recWts EX).nuW u (j + 1) τ).w a).toNat := fun j => by
    rw [← D.what₂.card_Tau]
    simp only [← emb_star_piG]
    rfl
  have hne : ∀ j, lossAt (Pr := recPrimes EX) (recWts EX) i u j ≠ 0 := fun j => by
    rw [e]
    exact mul_ne_zero (pow_ne_zero _ hg0) (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (hπ τ))
  refine ⟨hne, ?_⟩
  have hw' : D.what₂.places.resChar w = D.host.g i := hw
  have hvg : vAdd (D.plEq w) (D.host.g i : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := by
    have h1 := D.what₂.places.val_resChar w
    rw [hw', D.val_eq w _ hg0] at h1
    exact_mod_cast h1
  have he : (0 : ℝ) < D.what₂.places.ramIdx w := by exact_mod_cast D.what₂.places.ramIdx_pos w
  have h1 : ∀ j ∈ Finset.range D.R.m, (vAdd (D.plEq w) (lossAt (Pr := recPrimes EX) (recWts EX) i u j) : ℝ) / D.what₂.places.ramIdx w ≤
      vNN EX i u (1 + j) w + D.R.f * (D.R.N D.R.m * (D.R.N D.R.m + D.R.t)) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have h2 : (D.R.f : ℝ) * D.R.N j * D.R.N (j + 1) ≤ D.R.f * D.R.N D.R.m * (D.R.N D.R.m + D.R.t) := by
      exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.exp_le D j hj'
    have h3 : ∀ τ, (((∑ a, ((recWts EX).nuW u (j + 1) τ).w a).toNat : ℕ) : ℝ) = nuAbs D u (1 + j) τ := fun τ => by
      rw [add_comm 1 j, partitionSize D EX u j hj' τ, ← Int.cast_natCast,
        Int.toNat_of_nonneg (sum_nuW_nonneg (Pr := recPrimes EX) (recWts EX) u hj' τ)]
    rw [e, vAdd_mul_of_ne _ (pow_ne_zero _ hg0) (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (hπ τ)),
      vAdd_prod_of_ne _ _ _ fun τ => pow_ne_zero _ (hπ τ)]
    simp only [vAdd_pow_eq, hvg]
    push_cast
    simp only [h3]
    rw [add_div, mul_div_assoc, div_self he.ne', mul_one, vNN]
    linarith
  have h4 : 0 ≤ (D.R.f : ℝ) * ((D.R.m : ℝ) ^ 3 * L.etaSz) := by
    have := L.etaSz_pos.le
    positivity
  unfold LiftErrorLocal.vG
  rw [vAdd_prod_of_ne _ _ _ hne, Int.cast_sum, Finset.sum_div]
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, LiftErrorLocal.lifts, LiftErrorLocal.errC,
    ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  nlinarith

end GlobalTheory.ColPeriod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceSubgroupMemLevelTwistPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_congruence_subgroup_mem_level_twist_prime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ},
    X.Ok → Pr.Ok → L.Ok Ch sel mu cst G m2 → ∀ {j : ℕ}, j ≤ m2 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
    ∀ C : GLint X.E (R.N j) P.1, C ∈ GlobalTheory.TopStep.prinCong (R.N j) P.1 (cst.D P) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (C.1 x)) ∧
        chiInv Ch sel mu cst j P (L.h j b P) r = 1 := by
  first | exact @GlobalTheory.TwistCong.cong_mem_prCat_twist | exact GlobalTheory.TwistCong.cong_mem_prCat_twist | (intros; apply GlobalTheory.TwistCong.cong_mem_prCat_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledLatticeVectorMemDualBaseLatticeCompletion
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col GlobalTheory.TwU Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.MemDual

theorem prV_inclE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e) = inclE (F := F) (v.adicCompletion F) e := by
  simp [prV, inclE]

theorem prV_sigR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (sigR σ (FiniteAdeleRing (𝓞 F) F) x) = sigR σ (v.adicCompletion F) (prV (E := E) v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
  | tmul a b => simp [prV, sigR]

theorem bc_prV_mem_UPts {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    {k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hk : k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    bc (prV (E := E) v) k ∈ UPts σ J (v.adicCompletion F) := by
  have hg' : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (k : Matrix (Fin n) (Fin n) _) *
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * (k : Matrix (Fin n) (Fin n) _) =
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := hk
  change cT (sigR σ (v.adicCompletion F)) ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) *
      J.map (inclE (F := F) (v.adicCompletion F)) * ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) =
      J.map (inclE (F := F) (v.adicCompletion F))
  have h1 : cT (sigR σ (v.adicCompletion F)) ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) =
      (cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (k : Matrix (Fin n) (Fin n) _)).map (prV (E := E) v) := by
    ext i j
    simp [cT, prV_sigR]
  have hJ' : (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).map (prV (E := E) v) =
      J.map (inclE (F := F) (v.adicCompletion F)) := by
    ext i j
    simp [prV_inclE]
  rw [h1, ← hJ', ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem pullV_ratA_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (c : GL (Fin N) E) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (y : Fin N → E) :
    pullV (F := F) (ratA F c * x) ((c : Matrix (Fin N) (Fin N) E) *ᵥ y) =
      ((x⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) *ᵥ fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y i) := by
  unfold pullV
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  congr 1
  have hc : (((ratA F c)⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) =
      ((c⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := by
    rw [← map_inv]; rfl
  rw [hc]
  ext i
  have := RingHom.map_mulVec (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))
    ((c⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) ((c : Matrix (Fin N) (Fin N) E) *ᵥ y) i
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  rw [this]; rfl

end GlobalTheory.MemDual

namespace GlobalTheory.MemDual

theorem mem_latS_dual_of_latCo : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), IsUnit J.det → ∀ (c : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F) →
    ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    (∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb) → ∀ (v : HeightOneSpectrum (𝓞 F)) (y : Fin N → E),
    y ∈ latCo sp J c a x Lb →
    (fun l => prV (E := E) v (pullV (F := F) (ratA F c * x) y l)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)) := by
  intro R F E _ _ _ _ _ _ sp N J hJ c a x hx Lb hfin hspan hdual v y hy
  obtain ⟨y', hy', rfl⟩ := hy
  set σ : E →ₐ[F] E := sp.cm.sig with hσ
  set Λ := latAd x Lb with hΛ
  set xv := bc (prV (E := E) v) x with hxv
  have hLb : Submodule.IsFullLattice E Lb := {
    toIsLattice := Submodule.IsLattice.of_fg E (Module.Finite.iff_fg.mp hfin)
    span_eq_top := hspan }
  have hLam : Submodule.IsFullLattice E Λ := by
    have hlat : Formalism.L2.PairingIndexBounds.F.latAd x Lb = Formalism.UG.CS.globLat x Lb := Submodule.span_eq (Formalism.UG.CS.globLat x Lb)
    rw [hΛ, hlat]
    exact Formalism.UG.P.csGlob_lattice Lb hfin hspan x
  have hxU : xv ∈ UPts σ J (v.adicCompletion F) := bc_prV_mem_UPts σ J v hx
  have hcarry := GlobalTheory.LocCarry.mem_latS_latAd_iff x Lb hfin hspan v

  have hpull : (fun l => prV (E := E) v (pullV (F := F) (ratA F c * x) ((c : Matrix (Fin N) (Fin N) E) *ᵥ y') l)) =
      ((xv⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) *ᵥ fun i => inclE (F := F) (v.adicCompletion F) (y' i) := by
    rw [pullV_ratA_mul, GlobalTheory.LocCarry.prV_mulVec, hxv, GlobalTheory.LocCarry.coe_bc_inv]
    congr 1
  show (fun l => prV (E := E) v (pullV (F := F) (ratA F c * x) ((c : Matrix (Fin N) (Fin N) E) *ᵥ y') l)) ∈ _
  rw [hpull]

  have hsub : compan (sp := sp) J a Λ ≤ Λ ⊔ dualL (σ : E →+* E) J Λ :=
    sup_le_sup_left (Submodule.smul_le_right) _
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp (hsub hy')
  have hadd : (fun i => inclE (F := F) (v.adicCompletion F) ((p + q) i)) =
      (fun i => inclE (F := F) (v.adicCompletion F) (p i)) + fun i => inclE (F := F) (v.adicCompletion F) (q i) := by
    ext i; simp
  rw [hadd, Matrix.mulVec_add]
  have hmono : latS (F := F) (v.adicCompletion F) (intV E v) Lb ≤
      latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J Lb) :=
    Submodule.span_mono (Set.image_mono fun z hz => Submodule.subset_span (hdual z hz))
  refine add_mem ?_ ?_
  · exact hmono ((hcarry _).1 (Submodule.subset_span ⟨p, hp, rfl⟩))
  · exact (GlobalTheory.DualCompletion.dual_move F E σ N J v Λ Lb xv hJ hLam hLb hxU hcarry _).1
      (Submodule.subset_span ⟨q, hq, rfl⟩)

end GlobalTheory.MemDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalUnitaryOrthonormalCoordsIsColumnIsometry
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwRat

theorem ratUnitCol : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) →
      ∃ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹) := by
  intro D _ _ _ _ _ _ _ _ t u μ St A dtU a hP _ i hi γ hγ
  exact _root_.GlobalTheory.TwU.UnitaryFrom.exists_uf_seamGL_eq t.seam t.seam_ok (A.crd i hi * γ * (A.crd i hi)⁻¹)
    (GlobalTheory.unitary_conj_orthonormal D _ _ _ (hP.crd_orth i hi) hγ)

end GlobalTheory.TwRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepPointPulledDualVectorMemLocalBaseLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct

namespace GlobalTheory.ZDual

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}

theorem pullV_dual_mem_latS_gen (σ : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det)
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb)
    (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (v : HeightOneSpectrum (𝓞 F)) (l : Fin N → E) (hl : l ∈ dualSet (σ : E →+* E) J (latAd x Lb)) :
    (fun k => prV (E := E) v (pullV (F := F) x l k)) ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J Lb)) := by
  have hU : cT (sigR σ (v.adicCompletion F)) (bc (prV (E := E) v) x).val *
      J.map (inclE (F := F) (v.adicCompletion F)) * (bc (prV (E := E) v) x).val =
      J.map (inclE (F := F) (v.adicCompletion F)) := Formalism.UG.P.afsplit_bc_mem σ J v x hx
  have hy : (fun k => prV (E := E) v (pullV (F := F) x l k)) =
      ((bc (prV (E := E) v) x)⁻¹).val *ᵥ (fun k => inclE (F := F) (v.adicCompletion F) (l k)) := by
    rw [GlobalTheory.LocCarry.coe_bc_inv]
    funext k
    unfold pullV
    rw [RingHom.map_mulVec]
    rfl
  rw [hy]
  refine GlobalTheory.St.G.Dual.bwd_loc σ J hJ.ne_zero Lb ⟨hfin, hspan⟩ v _ fun b hb => ?_
  unfold GlobalTheory.St.G.hR
  have key := Formalism.UG.P.hform_mulVec (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F)))
    (bc (prV (E := E) v) x).val (fun k => inclE (F := F) (v.adicCompletion F) (b k))
    (((bc (prV (E := E) v) x)⁻¹).val *ᵥ (fun k => inclE (F := F) (v.adicCompletion F) (l k)))
  rw [hU, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at key
  rw [← key]
  refine Formalism.L2.G.RelativeIndexFlags.pair_int v σ J (latAd x Lb) l hl _ ?_
  rw [GlobalTheory.LocCarry.mem_latS_latAd_iff x Lb hfin hspan v, Matrix.mulVec_mulVec, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  exact Submodule.subset_span ⟨b, hb, rfl⟩

end Gen


attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem pullV_dual_mem_latS : ∀ {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (l : Fin (D.R.N i) → D.host.E), l ∈ dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (latAd x.1 lev.Lb) →
    (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)) ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) := by
  intro D i hi T f bad lev x v l hl
  exact pullV_dual_mem_latS_gen (sigD D) (gramN D i hi) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) lev.Lb lev.Lb_fin
    lev.Lb_span x.1 x.2 v l hl

end GlobalTheory.ZDual
end

