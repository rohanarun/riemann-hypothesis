module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0398
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeAdaptedBasisInvariantMatrixRatioStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeAdaptedBasis_invariant_matrix_ratio : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), C.InvdR → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (Q : Matrix (Fin d) (Fin d) (Per.BdR l)), IsUnit Q → (∀ g : ↥(GK K), (ρ g).map (Per.zD l) * Q.map (Per.σD (g : GQ l)) = Q) → ∀ H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K, ∃ c c' : Matrix (Fin d) (Fin d) (Om l), (∀ i j, c i j ∈ K.1) ∧ (∀ i j, c' i j ∈ K.1) ∧ c * c' = 1 ∧ H.Q = Q * c.map C.oD := by
  first | (exact @GlobalTheory.BKLim.invMatrix_ratio) | (exact GlobalTheory.BKLim.invMatrix_ratio) | (intros; apply GlobalTheory.BKLim.invMatrix_ratio  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeBasisOfAdaptedInvariantFamily
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

namespace GlobalTheory.HodgeAt

theorem hodge_of_adapted : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (K K' : FinExt l) (a : ℕ) (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (w : Fin a → Fin a → P.R.BdR) (k : Fin a → ℤ), (∀ i j, w i j ∈ (P.PD K).Fil (k i)) → (∀ j, ∃ u : Fin a → P.R.BdR, (∀ i, u i ∈ (P.PD K).Fil (-k i)) ∧ ∑ i, u i • w i = Pi.single j 1) → (∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → ∀ i, (ρ g).map (algebraMap (Om l) P.R.BdR) *ᵥ (fun j => P.actQdR (g : GQ l) (w i j)) = w i) → ∃ H : Hodge C ξ ρ K', ∀ n : ℤ, ((Finset.univ.filter fun i => (H.p i : ℤ) - H.q = n).card : ℤ) = ∑ i, if k i = n then 1 else 0 := by
  intro l _ P AI T C hFit ξ hξ K K' a ρ w k hw hspan hinv
  classical
  set ι := algebraMap (Per.BdRp l) (Per.BdR l) with hι
  obtain ⟨-, hinj, -, -⟩ := BdRField.bdR_isField l

  have hE : IsUnit (ι (aDp l ξ)) := by
    have hxiker : xi C.ε ∈ Ideal.span {ξ} := by
      rw [hξ, C.ker_theta]; exact Ideal.mem_span_singleton_self _
    obtain ⟨c0, hc0⟩ := Ideal.mem_span_singleton'.1 hxiker
    have h1 := GlobalTheory.MemLoc.TiedUnif.isUnit_xi (core_isEps l C)
    rw [← hc0, map_mul, map_mul] at h1
    exact isUnit_of_mul_isUnit_right h1

  set q : ℕ := ∑ i, (k i).natAbs with hq
  have hkq : ∀ i, 0 ≤ k i + q := by
    intro i
    have h1 : (k i).natAbs ≤ q := Finset.single_le_sum (f := fun i => (k i).natAbs) (by simp) (Finset.mem_univ i)
    omega
  set p : Fin a → ℕ := fun i => (k i + q).toNat with hp
  have hkp : ∀ i, k i + q = (p i : ℤ) := fun i => (Int.toNat_of_nonneg (hkq i)).symm

  have hV0 : ∀ i j, ∃ v : Per.BdRp l, ι (aDp l ξ) ^ q * T.eD (w j i) = ι (aDp l ξ ^ p j * v) :=
    fun i j => exists_xi_pow_mul l P AI T C ξ hξ K (k j) q (p j) (hkp j) (w j i) (hw j i)
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin a) (Fin a) (Per.BdRp l), ∀ i j, ι (aDp l ξ) ^ q * T.eD (w j i) = ι (aDp l ξ ^ p j * V i j) :=
    ⟨fun i j => Classical.choose (hV0 i j), fun i j => Classical.choose_spec (hV0 i j)⟩

  choose u hu hsum using hspan
  have hz0 : ∀ j i, ∃ z : Per.BdRp l, ι (aDp l ξ) ^ p i * T.eD (u j i) = ι (aDp l ξ ^ q * z) :=
    fun j i => exists_xi_pow_mul l P AI T C ξ hξ K (-k i) (p i) q (by have := hkp i; omega) (u j i) (hu j i)
  choose z hz using hz0
  have key : ∀ j j', ∑ i, z j i * V j' i = if j' = j then 1 else 0 := by
    intro j j'
    apply hinj
    have hs := congrFun (hsum j) j'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
    have h1 : ι (aDp l ξ) ^ q * ι (∑ i, z j i * V j' i) =
        ι (aDp l ξ) ^ q * T.eD (∑ i, u j i * w i j') := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have ha := hV j' i
      have hb := hz j i
      simp only [map_mul, map_pow] at ha hb ⊢
      calc ι (aDp l ξ) ^ q * (ι (z j i) * ι (V j' i))
          = (ι (aDp l ξ) ^ q * ι (z j i)) * ι (V j' i) := by ring
        _ = (ι (aDp l ξ) ^ p i * T.eD (u j i)) * ι (V j' i) := by rw [hb]
        _ = T.eD (u j i) * (ι (aDp l ξ) ^ p i * ι (V j' i)) := by ring
        _ = T.eD (u j i) * (ι (aDp l ξ) ^ q * T.eD (w i j')) := by rw [ha]
        _ = ι (aDp l ξ) ^ q * (T.eD (u j i) * T.eD (w i j')) := by ring
    rw [(hE.pow q).mul_left_cancel h1, hs, Pi.single_apply]
    split_ifs <;> simp
  set N : Matrix (Fin a) (Fin a) (Per.BdRp l) := Matrix.of fun i j => z j i with hN
  have hVN : V * N = 1 := by
    ext j' j
    rw [Matrix.mul_apply, Matrix.one_apply, ← key j j']
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hN, Matrix.of_apply]; ring
  have hNV : N * V = 1 := mul_eq_one_comm.1 hVN
  refine ⟨⟨V, ⟨⟨V, N, hVN, hNV⟩, rfl⟩, p, q, Matrix.of fun i j => T.eD (w j i), fun i j => by simpa using hV i j, ?_⟩, ?_⟩
  · intro g hg
    ext r c
    have h := congrArg T.eD (congrFun (hinv g hg c) r)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, T.actD, hFit.o] at h
    rw [Matrix.mul_apply]
    simpa [Matrix.map_apply, Matrix.of_apply, GlobalTheory.MemLoc.Core.oD] using h
  · intro n
    have hf : (Finset.univ.filter fun i => ((p i : ℕ) : ℤ) - (q : ℤ) = n) = Finset.univ.filter fun i => k i = n := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := hkp i
      omega
    show ((Finset.univ.filter fun i => ((p i : ℕ) : ℤ) - (q : ℤ) = n).card : ℤ) = _
    rw [hf, Finset.card_filter]
    push_cast
    rfl

end GlobalTheory.HodgeAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeOfAttached
section
noncomputable section

namespace GlobalTheory.TripleGal.HodgeOfAtt

open GlobalTheory.TripleGal _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem not_mem_placesOver_of_ne {D : D7} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (v : HeightOneSpectrum (𝓞 D.host.E)) (h1 : v ∈ placesOver D.host.E p) : v ∉ placesOver D.host.E q := fun h2 => by
  have hc : IsCoprime (p : 𝓞 D.host.E) (q : 𝓞 D.host.E) := ((Nat.coprime_primes hp hq).mpr hne).cast
  obtain ⟨a, b, hab⟩ := hc
  refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
  exact hab ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left a h1) (v.asIdeal.mul_mem_left b h2)

theorem not_mem_pD (D : D7) (i : D.ntw.Tw) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : v ∈ placesOver D.host.E (D.ntw.l i)) : v ∉ D.ntw.pD i := by
  intro hp
  have hv' : v ∈ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← D.ntw.pD_eq i]; exact hp
  have hl : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  split_ifs at hv' with h
  · exact not_mem_placesOver_of_ne D.host.pde'_prime hl (h ▸ D.host.pde_ne.symm) v hv' hv
  · exact not_mem_placesOver_of_ne D.host.pde_prime hl (Ne.symm h) v hv' hv

end GlobalTheory.TripleGal.HodgeOfAtt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateSymbolMatrixEquivariantStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateSymbolMatrix_equivariant : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {K LL : FinExt l} {m : ℕ} (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1) (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ), (∀ i j, u i j ∈ (P.PD K).Fil (k i)) → ∀ g : ↥(GK K), (∀ i, ((r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (embF P LL)).mulVec (fun j => P.actQdR (g : GQ l) (u i j)) = u i) → (r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) * (colHT J u k).map (Per.σC (g : GQ l)) = colHT J u k * Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])) := by
  first | (exact @GlobalTheory.HTBasis.colHT_equivariant) | (exact GlobalTheory.HTBasis.colHT_equivariant) | (intros; apply GlobalTheory.HTBasis.colHT_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateSymbolMatrixIsUnitDetStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateSymbolMatrix_isUnit_det : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {K : FinExt l} {m : ℕ} (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ), (∀ i j, u i j ∈ (P.PD K).Fil (k i)) → (∀ (n : ℤ) (y : Fin m → P.R.BdR), (∀ j, y j ∈ (P.PD K).Fil n) → ∃ f : Fin m → P.R.BdR, (∀ i, f i ∈ (P.PD K).Fil (n - k i)) ∧ y = ∑ i, f i • u i) → LinearIndependent P.R.BdR u → IsUnit (colHT J u k).det := by
  first | (exact @GlobalTheory.HTBasis.colHT_isUnit_det) | (exact GlobalTheory.HTBasis.colHT_isUnit_det) | (intros; apply GlobalTheory.HTBasis.colHT_isUnit_det  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostRamificationIdxEqOne
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem host_ramificationIdx_eq_one :
    ∀ (D : D7) (p : ℕ), p.Prime → p ∉ D.host.small → p ≠ D.host.q → p ≠ D.host.d → ∀ P ∈ placesOver D.host.E p, P.asIdeal.ramificationIdx ℤ = 1 :=
  fun D _ hp h2 hq hd P hP => GlobalTheory.HubLoc.ramIdx_eq_one D.host hp (UpperTheory.Small.not_dvd_condN D.host hp h2 hq hd) P hP

end GlobalTheory.TripleGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupEigenspaceEqTopOfAeval
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

namespace GlobalTheory.JointDiag

theorem aeval_restrict_coe {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (W : Submodule K V) (hW : ∀ x ∈ W, T x ∈ W) (q : K[X]) (y : W) :
    ((aeval (T.restrict hW) q y : W) : V) = aeval T q (y : V) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Module.End.pow_restrict,
      LinearMap.restrict_apply, Submodule.coe_smul]
    rw [Module.End.pow_restrict n hW]
    rfl

theorem ker_prod {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    (f : Module.End K M) (s : Finset K) :
    LinearMap.ker (aeval f (∏ r ∈ s, (X - C r))) = ⨆ r ∈ s, f.eigenspace r := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
    exact LinearMap.ker_id
  · intro a s ha ih
    rw [Finset.prod_insert ha, ← sup_ker_aeval_eq_ker_aeval_mul_of_coprime, ih, Finset.iSup_insert]
    · congr 1
      rw [Module.End.eigenspace_def, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
    · exact IsCoprime.prod_right fun i hi =>
        (pairwise_coprime_X_sub_C (K := K) (s := id) Function.injective_id) (fun h => ha (h ▸ hi))

theorem iSup_eigenspace_eq_top_of_aeval {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    (f : Module.End K M) (p : K[X]) (hs : p.Separable) (hp : p.Splits) (h0 : aeval f p = 0) :
    ⨆ μ, f.eigenspace μ = ⊤ := by
  classical
  have hne : p ≠ 0 := hs.ne_zero
  let s : Finset K := ⟨p.roots, nodup_roots hs⟩
  have hprod : ∏ r ∈ s, (X - C r) = (p.roots.map (X - C ·)).prod := rfl
  have hc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hne
  have hker : LinearMap.ker (aeval f (∏ r ∈ s, (X - C r))) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 := LinearMap.congr_fun h0 x
    rw [hp.eq_prod_roots, ← hprod, map_mul, aeval_C, Module.End.mul_apply,
      Module.algebraMap_end_apply, LinearMap.zero_apply, smul_eq_zero] at h1
    exact h1.resolve_left hc
  rw [ker_prod] at hker
  rw [eq_top_iff, ← hker]
  exact iSup₂_le fun r _ => le_iSup (fun μ => f.eigenspace μ) r

theorem le_iSup_jointEigenspace_inf : ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (T : ι → Module.End K V) (W : Submodule K V), (∀ a c, Commute (T a) (T c)) → (∀ a, ∀ x ∈ W, T a x ∈ W) → (∀ a, ∃ p : K[X], p.Separable ∧ p.Splits ∧ ∀ x ∈ W, Polynomial.aeval (T a) p x = 0) → W ≤ ⨆ ev : ι → K, ((⨅ a, LinearMap.ker (T a - ev a • LinearMap.id)) ⊓ W) := by
  intro K V ι _ _ _ _ T W hc hW hp
  let S : ι → Module.End K W := fun a => (T a).restrict (hW a)
  have hS0 : ∀ a, ∃ p : K[X], p.Separable ∧ p.Splits ∧ aeval (S a) p = 0 := by
    intro a
    obtain ⟨p, hs, hsp, hx⟩ := hp a
    refine ⟨p, hs, hsp, LinearMap.ext fun y => Subtype.ext ?_⟩
    rw [aeval_restrict_coe]
    simpa using hx y y.2
  have hmax : ∀ a μ, (S a).maxGenEigenspace μ = (S a).eigenspace μ := by
    intro a μ
    obtain ⟨p, hs, _, h0⟩ := hS0 a
    exact (Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree h0).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have hdiag : ∀ a, ⨆ μ, (S a).maxGenEigenspace μ = ⊤ := by
    intro a
    obtain ⟨p, hs, hsp, h0⟩ := hS0 a
    simp_rw [hmax]
    exact iSup_eigenspace_eq_top_of_aeval (S a) p hs hsp h0
  have hcomm : Pairwise fun i j => Commute (S i) (S j) := fun i j _ =>
    LinearMap.restrict_commute (hc i j) (hW i) (hW j)
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute S hcomm hdiag
  simp_rw [hmax] at htop
  have hle : Submodule.map W.subtype (⨆ χ : ι → K, ⨅ a, (S a).eigenspace (χ a)) ≤
      ⨆ ev : ι → K, ((⨅ a, LinearMap.ker (T a - ev a • LinearMap.id)) ⊓ W) := by
    rw [Submodule.map_iSup]
    refine iSup_mono fun χ => ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨?_, y.2⟩
    rw [SetLike.mem_coe] at hy ⊢
    rw [Submodule.mem_iInf]
    intro a
    have h := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hy a)
    have h' := congrArg Subtype.val h
    simp only [S, LinearMap.restrict_apply, Submodule.coe_smul] at h'
    rw [LinearMap.mem_ker, Submodule.subtype_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, h', sub_self]
  intro x hx
  have hmem : (⟨x, hx⟩ : W) ∈ ⨆ χ : ι → K, ⨅ a, (S a).eigenspace (χ a) := by
    rw [htop]; trivial
  exact hle ⟨⟨x, hx⟩, hmem, rfl⟩

end GlobalTheory.JointDiag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducesWAndExistsEmb
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.LocalEmbedding

theorem norm_algHom {l : ℕ} [Fact l.Prime] {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (φ : ↥K →ₐ[ℚ_[l]] ↥L) (y : ↥K) : ‖((φ y : ↥L) : PadicAlgCl l)‖ = ‖(y : PadicAlgCl l)‖ := by
  have h1 : minpoly ℚ_[l] ((φ y : ↥L) : PadicAlgCl l) = minpoly ℚ_[l] y :=
    minpoly.algHom_eq (L.val.comp φ) (L.val.comp φ).toRingHom.injective y
  have h2 : minpoly ℚ_[l] (y : PadicAlgCl l) = minpoly ℚ_[l] y :=
    minpoly.algHom_eq K.val K.val.toRingHom.injective y
  change spectralNorm ℚ_[l] (PadicAlgCl l) _ = spectralNorm ℚ_[l] (PadicAlgCl l) _
  unfold spectralNorm
  rw [h1, h2]

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

theorem inducesW_and_exists_emb : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (LL' : FinExt (D.nd.l i)) (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (τ : D.host.E →+* Qbar (D.nd.l i)), (∀ x : D.host.E, τ x = ((τ' (Br.cEw D.nbr i w hw x) : ↥LL'.1) : Om (D.nd.l i))) → InducesW D.nd i τ w ∧ ∃ g : D.R.GG, (D.naut.iotaQC i).toRingHom.comp τ = D.host.emb g := by
  intro D i w hw LL' τ' τ h
  refine ⟨fun x => ?_, ?_⟩
  · rw [mem_place_iff D i w hw x, h, norm_algHom τ']
    exact Iff.rfl
  · obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 ((D.naut.iotaQC i).toRingHom.comp τ)
    exact ⟨g, hg.symm⟩

end GlobalTheory.LocalEmbedding

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveAndRangeOfPrismCover
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

noncomputable def matCoordMap {A B : Type} [CommRing A] [CommRing B] {d : ℕ} (q : A →+* B)
    (M : Matrix (Fin d) (Fin d) B) : (Fin d → A) →ₛₗ[q] (Fin d → B) where
  toFun z := M.mulVec fun i => q (z i)
  map_add' x y := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp
  map_smul' a x := by
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp

theorem Eval.effective_of_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (h : Hom B C) (f : Hom bk.prism C), Cover h → Function.Injective (V.v h f) ∧ ∀ z : Fin d → C.A, (∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → (fun i => p.f (z i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (z i)) → ∃ y, V.v h f y = z := by
  intro l _ K bk d S B C N _ _ V h f hc
  obtain ⟨D, p, q, hpo⟩ := hc.stable.po C h
  obtain ⟨hinj, hrange⟩ := _root_.GlobalTheory.BSP.cover_injective_and_descent l _ B C h hc
  haveI := V.fin
  haveI := V.proj
  have hcomm : p.f.comp h.f = q.f.comp h.f := congrArg Hom.f hpo.comm
  have key := _root_.GlobalTheory.BSP.ProjDescent.descent B.A C.A D.A h.f p.f q.f hcomm hinj (hrange D p q hpo) N (Fin d → C.A) (Fin d → D.A)
    (V.v h f) (matCoordMap p.f 1) (matCoordMap q.f (S.ε (p.comp f) (q.comp f))) (V.v (p.comp h) (p.comp f))
    (V.bc h f) (V.bc (p.comp h) (p.comp f))
    (fun x => by
      change V.v (p.comp h) (p.comp f) x = (1 : Matrix (Fin d) (Fin d) D.A).mulVec fun i => p.f (V.v h f x i)
      rw [Matrix.one_mulVec]
      funext i
      exact V.v_nat p h f x i)
    (fun x => by
      change V.v (p.comp h) (p.comp f) x = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (V.v h f x i)
      have e : ∀ a a' : Hom B D, a = a' → V.v a (q.comp f) x = V.v a' (q.comp f) x := by
        intro a a' e; subst e; rfl
      rw [V.v_ε (p.comp h) (p.comp f) (q.comp f) x, e _ _ hpo.comm]
      congr 1
      funext i
      exact V.v_nat q h f x i)
  refine ⟨key.1, fun z hz => key.2 z ?_⟩
  change (1 : Matrix (Fin d) (Fin d) D.A).mulVec (fun i => p.f (z i)) =
    (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (z i)
  rw [Matrix.one_mulVec]
  exact hz D p q hpo.comm

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsVanishAtPrimeOfAdmissibleStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariants_vanish_at_prime_of_admissible : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; H0at S E := by
  first | exact @GlobalTheory.Cyc.InvKilled.invariants_killed | exact GlobalTheory.Cyc.InvKilled.invariants_killed | (intros; apply GlobalTheory.Cyc.InvKilled.invariants_killed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysCharacterOfCrystallineVectors
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.LetterCrys

theorem isCrys_of_letters : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → ∀ d : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ, (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)), ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ) ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ + 1)) → IsCrys (P.PD K) (charRep μ) := by
  intro l _ P AI hT K LL hA μ hμ d hw
  haveI := LL.2
  haveI := K.2
  obtain ⟨hgood, -⟩ := GlobalTheory.LocalIntegers.good_integers l LL
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := ↥LL.1
      ρ := charRep μ
      cont := fun x => (hμ.mul continuous_const :
        Continuous fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1) * x) }
  obtain ⟨⟨hfin, hle⟩, -, -⟩ :=
    GlobalTheory.Per.FontaineTied.fontCore_all_of_tied l P AI hT K ↥LL.1 ↥(OL LL) hgood A
  haveI : Module.Finite ↥LL.1 ↥(Dcris (P.PD K) (charRep μ)) := hfin
  unfold IsCrys
  refine le_antisymm hle ?_
  have hcard : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 :=
    Formalism.MainNotions.N.JsetEmb.card_emb_good hA.2.2
  have e : K0 K = K.1 := inf_eq_left.2 hA.1
  have hfr : finrank ℚ_[l] ↥(K0 K) = finrank ℚ_[l] ↥K.1 :=
    (IntermediateField.equivOfEq e).toLinearEquiv.finrank_eq
  have hsurj : Function.Surjective (algebraMap ↥(K0 K) ↥K.1) := fun x =>
    ⟨⟨x, x.2, hA.1 x.2⟩, rfl⟩
  let f : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) := fun τ =>
    τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)
  have hf : Function.Injective f := fun τ τ' h => AlgHom.ext fun x => by
    obtain ⟨y, rfl⟩ := hsurj x
    exact AlgHom.congr_fun h y
  choose w hwmem hw1 hw2 using hw
  have hne : ∀ τ, w τ ≠ 0 := fun τ h0 => hw2 τ (by rw [h0, map_zero]; exact Submodule.zero_mem _)
  have hind : iSupIndep fun τ => DcrisL (P.PD K) (charRep μ) (f τ) :=
    (GlobalTheory.NL.PhiD.iSupIndep_letter (P.PD K) (charRep μ)).comp hf
  have hli : LinearIndependent ↥LL.1 w := iSupIndep.linearIndependent _ hind hwmem hne
  let w' : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ↥(Dcris (P.PD K) (charRep μ)) := fun τ => ⟨w τ, (hwmem τ).1⟩
  have hli' : LinearIndependent ↥LL.1 w' :=
    LinearIndependent.of_comp (Dcris (P.PD K) (charRep μ)).subtype hli
  have hpos : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) ≠ 0 := by
    rw [hcard]; exact Module.finrank_pos.ne'
  haveI : Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Nat.finite_of_card_ne_zero hpos
  haveI := Fintype.ofFinite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
  have h2 := hli'.fintype_card_le_finrank
  rw [← Nat.card_eq_fintype_card, hcard] at h2
  rw [Module.finrank_self, mul_one, hfr]
  exact h2

end GlobalTheory.LetterCrys
end

