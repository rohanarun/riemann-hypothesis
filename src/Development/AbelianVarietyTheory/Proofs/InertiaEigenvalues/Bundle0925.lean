module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0919
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0341
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0109
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0215

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeHalfIffFrameMatrixIntegral
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.HalfOInt

open Formalism.IndefR.Fin.LevelGroupLemmas.Lat Matrix

theorem idem_mem_at (D : D7) (e : AE D) (PP : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E))
    (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (hP : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (a : D.host.E) (ha : a ∈ D.host.AA) :
    toEAf D e * eToEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  set n : ℕ := Ideal.absNorm D.host.𝔟 with hn
  have hnP : (n : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro h
    obtain ⟨p, hp, hpP⟩ := GlobalTheory.HalfCompare.exists_prime_under PP
    exact hP ((hpP _).2 (((GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hp).1 ((hpP _).1 h)).mul_right _))
  have hn0 : (n : 𝓞 D.host.E) ≠ 0 := fun h => hnP (h ▸ zero_mem _)
  have hn0' : (n : D.host.E) ≠ 0 := by
    intro h
    apply hn0
    have : n = 0 := by exact_mod_cast h
    rw [this, Nat.cast_zero]
  have h1 : finPart D (e * incA D (((n : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hnP ((he.2 _ hn0).2 h)
  have h2 := GlobalTheory.IdemIntegral.toEAf_mem_of_finPart h1
  obtain ⟨c, hc⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem D.host.𝔟) ha
  have h3 := mul_mem h2 (GlobalTheory.IdemIntegral.eToEAf_int D c)
  rw [map_mul, GlobalTheory.IdemIntegral.toEAf_incA, mul_assoc, ← map_mul] at h3
  convert h3 using 3
  have hc' : (c : D.host.E) = a * n := hc
  have hcast : ((n : 𝓞 D.host.E) : D.host.E) = n := map_natCast (algebraMap (𝓞 D.host.E) D.host.E) n
  rw [hc', hcast]
  field_simp

theorem idem_mem_intAf (D : D7) (e : AE D) (P : Finset (Pl D.host.E)) (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (a : D.host.E) (ha : a ∈ D.host.AA) :
    toEAf D e * eToEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul]
  exact sum_mem fun PP hPP => idem_mem_at D _ PP (hes PP hPP) (hP PP hPP) a ha

theorem smul_genE {D : D7} {S T : HSp D} (e : AE D) (c : EAf D) (τ : Fin T.rank → EAf D)
    (σ : Fin S.rank → EAf D) :
    e • genE (S := S) (T := T) c τ σ = genE (toEAf D e * c) τ σ := by
  ext i j
  simp only [genE, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_liftE, mul_assoc]

end GlobalTheory.HalfOInt

namespace GlobalTheory.HalfOInt
open Formalism.IndefR.Fin.LevelGroupLemmas.Lat Matrix


set_option maxHeartbeats 4000000 in
theorem frMapO_int_of_half {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    {u : WO S T} (hu : u ∈ latO S T ΛS ΛT (fun _ => True)) (hh : IsHalf e u) :
    IsIntM (frMapO S T βS βT u) := by
  have hx : e • u = u := Matrix.ext fun i j => hh i j
  rw [← hx]
  clear hx hh
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, _, a, ha, s, hs, t, ht, rfl⟩ := hw
    show IsIntM (frMapO S T βS βT (e • genL S T α a s t))
    rw [genL_eq_genE, smul_genE, genE, frMapO_mapLiftE, mul_vecMulVec_mul]
    intro i j
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    refine mul_mem ?_ (mul_mem ?_ ?_)
    · rw [← mul_assoc]
      exact mul_mem (idem_mem_intAf D e P he hP a ha)
        (Subring.subset_closure (Or.inr ⟨⟨α, fun v => hα v⟩, rfl⟩))
    · exact (fT _).1 (mem_hatL_of_mem ht) i
    · rw [Matrix.vecMul_vecMul]
      have e : (fun l => (S.gram.map (eToEAf D) * (βS : Matrix (Fin S.rank) (Fin S.rank) (EAf D))) l j) =
          S.gram.map (eToEAf D) *ᵥ (fun i => (βS : Matrix (Fin S.rank) (Fin S.rank) (EAf D)) i j) := by
        funext l; rw [Matrix.mul_apply]; rfl
      show (fun k => sR D (eToEAf D (s k))) ⬝ᵥ
        (fun l => (S.gram.map (eToEAf D) * (βS : Matrix (Fin S.rank) (Fin S.rank) (EAf D))) l j) ∈ _
      rw [e]
      exact hform_int hS hs (col_mem_hatL fS j)
  | zero =>
    rw [smul_zero, frMapO_zero]
    exact fun _ _ => zero_mem _
  | add x y _ _ hx hy =>
    rw [smul_add, frMapO_add]
    exact isIntM_add hx hy
  | neg x _ hx =>
    rw [smul_neg, frMapO_neg]
    exact fun i j => neg_mem (hx i j)

end GlobalTheory.HalfOInt

namespace GlobalTheory.HalfOInt
open Formalism.IndefR.Fin.LevelGroupLemmas.Lat Matrix

theorem sum_decomp {R : Type} [CommRing R] {m n N : ℕ} (M : Matrix (Fin m) (Fin n) R) (g Y : Fin N → Fin n → R)
    (hb : ∑ k, vecMulVec (g k) (Y k) = 1) (c z : R) (hM : (c * z) • M = M) :
    ∑ k, c • vecMulVec (z • (M *ᵥ g k)) (Y k) = M := by
  have h : ∀ k, c • vecMulVec (z • (M *ᵥ g k)) (Y k) = (c * z) • (M * vecMulVec (g k) (Y k)) := by
    intro k
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Matrix.mul_apply,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl fun k _ => h k, ← Finset.smul_sum, ← Matrix.mul_sum, hb, Matrix.mul_one, hM]


set_option maxHeartbeats 4000000 in
theorem mem_latO_of_int {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    {t : WO S T} (ht : IsHalf e t) (hN : IsIntM (frMapO S T βS βT t)) :
    t ∈ latO S T ΛS ΛT (fun _ => True) := by
  have ha := GlobalTheory.HalfAdjLattice.natCast_mem_AA (D := D) (D.host.QS * D.host.q)
  generalize D.host.QS * D.host.q * Ideal.absNorm D.host.ccK = n at hP ha
  obtain ⟨N, g, s, hg, hs, hb⟩ := GlobalTheory.HalfAdjLattice.exists_dual_families S hS
  have hz := GlobalTheory.HalfAdjLattice.toEAf_int (GlobalTheory.HalfAdjLattice.idem_div_int he hP)
  have hze := GlobalTheory.HalfAdjLattice.natCast_mul_idem_div he hP
  generalize e * incA D (n : D.host.E)⁻¹ = z at hz hze
  set M : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := Matrix.map t (toEAf D) with hMdef
  have hN' : IsIntM ((βT⁻¹).val * M * βS.val) := hN
  have hb' : ∑ k, vecMulVec (fun i => eToEAf D (g k i))
      (vecMul (fun a => sR D (eToEAf D (s k a))) (S.gram.map (eToEAf D))) = 1 := by
    ext i j
    have h1 := congrArg (eToEAf D) (congrFun (hb (Pi.single j 1)) i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_apply, map_sum] at h1
    rw [Matrix.sum_apply]
    have h2 : eToEAf D ((Pi.single j 1 : Fin S.rank → D.host.E) i) = (1 : Matrix (Fin S.rank) (Fin S.rank) (EAf D)) i j := by
      rw [Pi.single_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [← h2, ← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mulVec_single_one]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [vecMulVec_apply, vecMul, dotProduct, map_apply, sR_eTo, Pi.smul_apply, smul_eq_mul, map_mul, map_sum,
      Matrix.col, transpose_apply]
    exact mul_comm _ _
  have hM : ((eToEAf D (n : D.host.E) * ((1 : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F))) * toEAf D z) • M = M := by
    have h1 : (eToEAf D (n : D.host.E) * ((1 : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F))) * toEAf D z = toEAf D e := by
      rw [← hze, map_mul, toEAf_incA, ← Algebra.TensorProduct.one_def, mul_one]
    rw [h1]
    ext i j
    simp only [hMdef, Matrix.smul_apply, map_apply, smul_eq_mul]
    rw [← map_mul, ht i j]
  have key := sum_decomp M (fun k i => eToEAf D (g k i))
    (fun k => vecMul (fun a => sR D (eToEAf D (s k a))) (S.gram.map (eToEAf D))) hb' _ _ hM
  have hdec : t = ∑ k, genE (S := S) (T := T)
      (eToEAf D (n : D.host.E) * ((1 : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)))
      (toEAf D z • (M *ᵥ fun i => eToEAf D (g k i))) (fun a => eToEAf D (s k a)) := by
    ext i j
    have h1 := congrFun (congrFun key i) j
    rw [Matrix.sum_apply] at h1
    rw [Matrix.sum_apply]
    unfold genE
    simp only [map_apply]
    rw [← liftE_sum, h1]
    have h0 : infPart D (t i j) = 0 := by rw [← ht i j, map_mul, infPart_of_idemSum he, zero_mul]
    exact (liftE_toEAf _ h0).symm
  rw [hdec]
  refine AddSubgroup.sum_mem _ fun k _ => genE_mem ?_ ha ?_ (mem_hatL_of_mem (hs k))
  · intro v; rw [map_one]; exact one_mem _
  · exact Submodule.smul_mem _ (⟨_, hz⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E)
      (GlobalTheory.HalfAdjLattice.mulVec_mem_hatL fT fS hN' (mem_hatL_of_mem (hg k)))

end GlobalTheory.HalfOInt

namespace GlobalTheory.HalfOInt

theorem mem_latO_iff_frMapO_int : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ w : WO S T, IsHalf e w → (w ∈ latO S T ΛS ΛT (fun _ => True) ↔ IsIntM (frMapO S T βS βT w)) := by
  intro D S T ΛS ΛT βS βT hS _ fS fT P e he hP w hw
  exact ⟨fun hu => frMapO_int_of_half hS fS fT he hP hu hw, fun hN => mem_latO_of_int hS fS fT he hP hw hN⟩

end GlobalTheory.HalfOInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
section
noncomputable section

namespace GlobalTheory.LiftRef

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up Formalism.AUTREP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def autOf {D : D7} {μt : D.what₂.Tup} {j : ℕ} (Mr : MtReal D μt j) (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W))
    (hS : NG.IsIrrRep Mr.wt.ρ S) : NG.AutRep D.host.E D.R.nV :=
  { Mr.wt with S := S, irrS := hS }

theorem evG_and {p q : Ctx → Prop} (hp : EvG p) (hq : EvG q) : EvG fun K => p K ∧ q K := by
  obtain ⟨a, ha, hp⟩ := hp
  obtain ⟨b, hb, hq⟩ := hq
  refine ⟨min a b, lt_min ha hb, fun e C8 C5 c6 Cb he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 C5 c6 Cb he (hle.trans (min_le_left _ _)) h52 h8
  obtain ⟨K', hK'⟩ := hq e C8 C5 c6 Cb he (hle.trans (min_le_right _ _)) h52 h8
  refine ⟨K.sup K', fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 (fc_large_of_sup hL).1
  obtain ⟨b1, hb1⟩ := hK' C hC hC8 (fc_large_of_sup hL).2
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  exact ⟨max a3 b3, fun X h1 h2 h3 h4 hx hg =>
    ⟨ha3 X h1 h2 h3 h4 (le_trans (le_max_left _ _) hx) hg, hb3 X h1 h2 h3 h4 (le_trans (le_max_right _ _) hx) hg⟩⟩

theorem evG_mono {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : EvG p) : EvG q := by
  obtain ⟨a, ha, hp⟩ := hp
  refine ⟨a, ha, fun e C8 C5 c6 Cb he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 C5 c6 Cb he hle h52 h8
  refine ⟨K, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun X h1 h2 h3 h4 hx hg => h X (ha3 X h1 h2 h3 h4 hx hg)⟩

theorem overRows_and_mono {p q r : RowP} (hp : OverRows p) (hq : OverRows q)
    (h : ∀ K B f T w Z Wt hX z p0 Y, p K B f T w Z Wt hX z p0 Y → q K B f T w Z Wt hX z p0 Y → r K B f T w Z Wt hX z p0 Y) :
    OverRows r := by
  unfold OverRows EvLgG at *
  refine evG_mono (fun K hK => ?_) (evG_and hp hq)
  refine large₂.mono (fun B f T _ hpq hKP w hw Z Wt hX z p0 Y h1 h2 h3 h4 h5 => ?_) (large₂.and hK.1 hK.2)
  exact h _ _ _ _ _ _ _ _ _ _ _ (hpq.1 hKP w hw Z Wt hX z p0 Y h1 h2 h3 h4 h5) (hpq.2 hKP w hw Z Wt hX z p0 Y h1 h2 h3 h4 h5)

end GlobalTheory.LiftRef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParameterLawsEmpty
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.ParLawsBare

open GlobalTheory.RowTie GlobalTheory.NPin Polynomial

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem heckeCharTie_of_side {D : D7} {cf : CharFrame D} (cs : CharSide D cf) :
    GlobalTheory.HeckeSplitRow.HeckeCharTie D.nd D.naut :=
  ⟨fun π => (cs.e1 π).1, fun _ _ h => cs.e1.injective (Subtype.ext h), cs.unr_iff, cs.frob⟩

theorem heckeSplitOne_of_side {D : D7} {cf : CharFrame D} (cs : CharSide D cf) : GlobalTheory.RowCopy.HeckeSplitOne D :=
  fun ν ν' hw => GlobalTheory.HeckeSplitRow.heckeSplitOne_of_tie D.nd D.naut (heckeCharTie_of_side cs) ν ν' hw

theorem cancel_of_tie {D : D7} (T : WDTie D.nd D.naut) :
    ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b := by
  intro w a b c h
  apply (T.e w).injective
  refine GlobalTheory.WeilDeligne.WD.lpSum_cancel_right _ _ _ _ _ _ _ (T.e w c) ?_
  rw [← T.sum, ← T.sum, h]


open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil in
theorem locG_rankOne_eq_rcAt {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} (T : WDTie D.nd D.naut)
    (cg : CGTrue hL D T) (cs : CharSide D cf) (π : D.naut.CG 1) (w : PlE D.host)
    (ξ : (w.adicCompletion D.host.E)ˣ →* ℂˣ) (h : IsComp (cs.e1 π).1 w ξ) :
    T.e w (D.naut.locG π w) = rcAt hL D w 1 (GlobalTheory.SplitRead.Irr.ofDet 1 ξ h.1) := by
  haveI := host_isCMField D.host
  set χ' := (CGu.equivChar D.host.E (cg.e 1 π)).1 with hχ'
  set χ := (cs.e1 π).1 with hχ
  have hloc : ∀ v, T.e v (D.naut.locG π v) = GlobalTheory.CuspRep.ParLaws.locPar hL (CG.ofChar χ') (D.nd.plOm.2 v) := fun v => by
    rw [cg.loc, hχ', CGu.ofChar_equivChar]; rfl
  have unr' : ∀ v, D.naut.unr (D.naut.locG π v) ↔ χ'.UnrAt v := fun v => by
    rw [T.unr, hloc v]; exact GlobalTheory.RankOneComp.locPar_ofChar_unr_iff hL χ' _
  have hchar : χ' = χ := by
    rw [← mul_inv_eq_one]
    apply GlobalTheory.HeckeSplitRow.eq_one_of_split D.host
    filter_upwards [D.naut.locG_unr_ae π] with v hv _
    have u1 := (cs.unr_iff π v).1 hv
    have u2 := (unr' v).1 hv
    refine ⟨fun x hx => ?_, ?_⟩
    · change χ'.loc v x * (χ.loc v x)⁻¹ = 1
      rw [u1 x hx, u2 x hx, inv_one, mul_one]
    · have hf := cs.frob π v u1
      have hf' : D.naut.frobEig (D.naut.locG π v) = {(((χ'.val v)⁻¹ : ℂˣ) : ℂ)} := by
        rw [T.frobEig _ _ hv, hloc v]; exact GlobalTheory.RankOneComp.locPar_ofChar_frob hL χ' _ u2
      rw [hf', Multiset.singleton_inj, Units.val_inj, inv_inj] at hf
      rw [HChar.val_mul, HChar.val_inv, hf, mul_inv_cancel]
  have hcomp : IsComp χ w (χ.loc w) := ⟨GlobalTheory.CuspRep.ParLaws.isSmoothChar_loc χ w, fun x => rfl⟩
  obtain ⟨ξ₀, -, huniq, -⟩ := _root_.GlobalTheory.HeckeComp.main D.host.E χ w
  have hξ : ξ = χ.loc w := (huniq _ h).trans (huniq _ hcomp).symm
  subst hξ
  rw [hloc, GlobalTheory.CuspRep.ParLaws.locPar_ofChar, rcAt]
  rw [hchar]
  rfl


open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil in
theorem rankOneUnitary {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} (T : WDTie D.nd D.naut)
    (cg : CGTrue hL D T) (cs : CharSide D cf) : RankOneUnitary T := by
  intro π w σ _ α hα
  obtain ⟨ξ, hξ, -, hξu⟩ := GlobalTheory.HeckeComp.main D.host.E (cs.e1 π).1 w
  have he := locG_rankOne_eq_rcAt T cg cs π w ξ hξ
  rw [WDTie.eig, he] at hα
  unfold WD.inePol at hα
  split_ifs at hα with hσ
  · exact GlobalTheory.LocLanglands.IsRec.recUnit (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 w)) ξ
      (GlobalTheory.SplitRead.Irr.ofDet 1 ξ hξ.1) (hξu (cs.e1 π).2) ⟨Representation.Equiv.refl _⟩ ⟨σ, hσ⟩ α hα
  · simp at hα


open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LocGL in
theorem rankTwo (hAF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hT : GlobalTheory.Published.CohomologicalCsdTempered)
    (hRP : GlobalTheory.Published.RegularAlgebraicPurity) {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (T : WDTie D.nd D.naut)
    (cg : CGTrue hL D T) (a : ℕ) (π : D.naut.CG a) (ha : 2 ≤ a) (hc : D.naut.csd π) (hr : D.naut.ralg π)
    (w : PlE D.host) : D.naut.tempered (D.naut.locG π w) := by
  have := host_isCMField D.host
  have ha1 : 1 ≤ a := by omega
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (cg.e a π).1
  have hmk : CG.mk π₀ = (cg.e a π).1 := hπ₀
  have hc₀ : π₀.IsCsd := by
    have h1 := (cg.csd a π).1 hc
    rw [CGu.IsCsd, ← hmk] at h1
    exact h1
  have hinf : ∀ τ, D.naut.infG π τ = (CG.mk π₀).infChar τ := fun τ => by
    rw [cg.inf, CGu.infChar, ← hmk]
  have hr₀ : (CG.mk π₀).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [hinf] at this
  have hcoh := (hRP D.host.E a ha1 π₀ hr₀).2
  obtain ⟨σ₀, hσ₀, -⟩ := LocEx.exists_isLocComp hAF D.host.E a π₀ w
  have htG := hT D.host.E a ha π₀ hc₀ hcoh w σ₀ hσ₀
  rw [T.tempered, cg.loc]
  show (GlobalTheory.CuspRep.ParLaws.locPar hL (cg.e a π).1 (D.nd.plOm.2 w)).tempered
  rw [← hmk, GlobalTheory.CuspRep.ParLaws.locPar_mk hL hσ₀ (D.nd.plOm.2 w)]
  exact GlobalTheory.T.tempered_rep_tempered_parameter D.host.E D.nd.Om _ w (D.nd.plOm.2 w) _ (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 w)) a
    (GlobalTheory.CuspRep.ParLaws.toRep σ₀) htG

theorem tieAut_of_side {D : D7} {cf : CharFrame D} (cs : CharSide D cf) (hE : IsEmpty D.nd.Loc) :
    Formalism.MainNotions.SumRepresentations.At.TieAut D.nd D.naut := by
  have hcsd : IsCSD D.host cf.eta := GlobalTheory.EtaSelfDual.isCSD_of_isEtaT _ _ _ cf.isEta
  have hE1 : (cs.e1 D.naut.etaT).1.HasInfQ (embPsi D.host) (fun _ => (1 / 2 : ℚ)) :=
    ⟨fun _ => 1, fun _ => by norm_num, by rw [cs.etaT]; exact cf.isEta.inf⟩
  have hE' : (cs.e1 D.naut.etaTinv).1.HasInfQ (embPsi D.host) (fun _ => (-(1 / 2) : ℚ)) :=
    ⟨fun _ => -1, fun _ => by norm_num, by rw [cs.etaTinv]; exact GlobalTheory.AutomorphismSplitting.hasInf_inv cf.isEta.inf⟩
  refine ⟨⟨?_, ?_⟩, fun τ => ?_, fun w => ?_, fun i _ => isEmptyElim i⟩
  · rw [cs.csd, cs.etaT]; exact hcsd
  · rw [cs.csd, cs.etaTinv]; exact GlobalTheory.AutomorphismSplitting.isCSD_inv' hcsd
  · obtain ⟨ρ, hρ⟩ := (GlobalTheory.VolRatioCheck.place_bijective D).2 (InfinitePlace.mk τ)
    rcases InfinitePlace.mk_eq_iff.1 hρ with h | h
    · have ht : τ = embPsi D.host (D.eTau ρ) := h.symm
      rw [ht, (cs.infG _ _ hE1 (D.eTau ρ)).1, (cs.infG _ _ hE' (D.eTau ρ)).1]
      refine ⟨Or.inl (by push_cast; rfl), ?_⟩
      rw [Multiset.map_singleton]; push_cast; rfl
    · have ht : τ = (starRingEnd ℂ).comp (embPsi D.host (D.eTau ρ)) := by
        rw [← h]; ext x; rfl
      rw [ht, (cs.infG _ _ hE1 (D.eTau ρ)).2, (cs.infG _ _ hE' (D.eTau ρ)).2]
      refine ⟨Or.inr (by push_cast; rfl), ?_⟩
      rw [Multiset.map_singleton]; push_cast; ring_nf
  · have hu : D.naut.unr (D.naut.locG D.naut.etaT w) := D.naut.etaT_unr w
    rw [D.naut.tempered_unr _ hu, cs.frob _ w ((cs.unr_iff _ w).1 hu)]
    intro α hα
    rw [Multiset.mem_singleton] at hα
    subst hα
    have h1 : ‖(((cs.e1 D.naut.etaT).1.val w : ℂˣ) : ℂ)‖ = 1 := (cs.e1 D.naut.etaT).2 _
    rw [Units.val_inv_eq_inv_val, norm_inv, h1, inv_one]

theorem tieGal_bare {D : D7} (hE : IsEmpty D.nd.Loc) : Formalism.MainNotions.SumRepresentations.At.TieGal D.nd D.naut :=
  ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, fun i => isEmptyElim i, fun i => isEmptyElim i⟩

theorem tieLab_of_lab {D : D7} (T : WDTie D.nd D.naut) (lab : LabTrue D T) : Formalism.MainNotions.SumRepresentations.tieLab D := by
  let γ : Fin 2 → PlE D.host → Formalism.ConjugateSelfDual.G D.host.E D.nd.Om :=
    fun k => Function.extend (D.naut.plGw k) (D.ntypes.tg k) (fun _ => 1)
  have hγ : ∀ k v, γ k (D.naut.plGw k v) = D.ntypes.tg k v := fun k v => (D.naut.plGw_inj k).extend_apply _ _ v
  have hT : GlobalTheory.LabLaws.LabTie T D.ntypes.teichC γ := by
    intro k v
    rw [hγ k v]
    exact ⟨D.ntypes.teichC_inj k, D.ntypes.tg_gen k v, lab k v⟩
  exact GlobalTheory.LabLaws.tieLab_of_labTie hT

theorem main : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ∀ (D : D7) (cf : CharFrame D) rep Rw,
    IsEmpty D.nd.Loc → ParIn hL D cf rep Rw → ParLaws D := by
  intro hP hL D cf rep Rw hE X
  have hrig : IsobaricRigid D.nd D.naut := by
    have := GlobalTheory.CuspRep.host_isCMField D.host
    exact GlobalTheory.RowPar.isobaricRigid_of_jacquetShalika hP.what₂.js.1 (GlobalTheory.HeightCounting.Blocks.readsCusp hP.what₂.fin X.cg)
  have han1 := GlobalTheory.RowClose.isobaricCuspidalMultiplicityOne_of_twisted _ _ _ D.nd D.naut hrig
  have han2 := GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne _ _ _ D.nd D.naut hrig
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb D
  have ha5 : Formalism.MainNotions.SumRepresentations.adm5 D := (Formalism.MainNotions.SumRepresentations.condition_iff_additive_maps D).2 ⟨han1, han2, fun Sg hSg => by
    have hd := (hcheb hSg.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]⟩
  have htie0 : Formalism.MainNotions.SumRepresentations.tie0 D :=
    ⟨GlobalTheory.RowTieLP.main D X.T, tieAut_of_side X.chr hE, tieGal_bare hE⟩
  have ha7 : Formalism.MainNotions.SumRepresentations.adm7 D :=
    GlobalTheory.RowTie.admissible_of_rank_one_unitary D X.T (rankOneUnitary X.T X.cg X.chr)
      (fun a π ha hc hr w => rankTwo hP.what₂.fin hP.what₂.temp hP.what₂.clo X.T X.cg a π ha hc hr w)
  exact ⟨htie0, ha5, ha7, tieLab_of_lab X.T X.lab, heckeSplitOne_of_side X.chr, cancel_of_tie X.T,
    fun k v => GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v⟩

end GlobalTheory.ParLawsBare

end
end

