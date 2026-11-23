module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationBoundOfPrimePowDvdMuPowAcris
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionZeroOneProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0410
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0436
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0437

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisLpowDvdBoundTeichmullerMonoid
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.AcrisMonBound

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_pow_bound {ϖ : OCb l} (hϖ : ϖ.untilt = (l : Per.OC l)) {c : OCb l} (hc : c ≠ 0) :
    ∃ K : ℕ, ∀ k : ℕ, ϖ ^ k ∣ c → k < K := by
  set a := ‖((c.untilt : Per.OC l) : ℂ_[l])‖
  set b := ‖((l : ℕ) : ℂ_[l])‖
  have ha : 0 < a := by
    refine norm_pos_iff.2 fun h => hc (GlobalTheory.TiltAbs.eq_zero_of_untilt c ?_)
    exact Subtype.ext (by simpa using h)
  have hb1 : b < 1 := GlobalTheory.RingBasics.norm_p_lt
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one ha hb1
  refine ⟨K, fun k hk => ?_⟩
  by_contra hkK
  obtain ⟨d, hd⟩ := map_dvd (PreTilt.untilt (O := Per.OC l) (p := l)) hk
  rw [map_pow, hϖ] at hd
  have h1 := congrArg (fun z : Per.OC l => ‖(z : ℂ_[l])‖) hd
  push_cast at h1
  rw [norm_mul, norm_pow] at h1
  have h2 : a ≤ b ^ k := by
    change ‖((c.untilt : Per.OC l) : ℂ_[l])‖ ≤ _
    rw [h1]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (GlobalTheory.TiltAbs.norm_le_one d)
  have h3 : b ^ k ≤ b ^ K := pow_le_pow_of_le_one (norm_nonneg _) hb1.le (not_lt.1 hkK)
  linarith

end GlobalTheory.AcrisMonBound

namespace GlobalTheory.AcrisMonBound

theorem main : ∀ (l : ℕ) [Fact l.Prime] (y : Ainf l), WittVector.constantCoeff y ≠ 0 → ∃ C : ℕ, ∀ (z : ℤ_[l]) (N : ℕ), z ≠ 0 → (l : Per.Acris l) ^ N ∣ ainfToAcris l y * algebraMap ℤ_[l] (Per.Acris l) z → N ≤ z.valuation + C := by
  intro l hl y hy
  have hl2 : 2 ≤ l := hl.out.two_le
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l (l : Per.OC l)
  obtain ⟨K, hK⟩ := exists_pow_bound hϖ hy
  refine ⟨K, fun z N hz h => ?_⟩
  set u := PadicInt.unitCoeff hz
  set v := z.valuation
  rcases le_or_gt N v with hNv | hNv
  · omega
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hNv.le
  set y' := y * algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l])
  have hza : algebraMap ℤ_[l] (Per.Acris l) z =
      (l : Per.Acris l) ^ v * algebraMap ℤ_[l] (Per.Acris l) (u : ℤ_[l]) := by
    conv_lhs => rw [PadicInt.unitCoeff_spec hz]
    rw [map_mul, map_pow, map_natCast, mul_comm]
  have hy' : ainfToAcris l y' = ainfToAcris l y * algebraMap ℤ_[l] (Per.Acris l) (u : ℤ_[l]) := by
    simp only [y', map_mul]
    congr 1
  have h2 : (l : Per.Acris l) ^ n' ∣ ainfToAcris l y' := by
    obtain ⟨w, hw⟩ := h
    refine ⟨w, ?_⟩
    have h3 : ((l ^ v : ℕ) : Per.Acris l) * (ainfToAcris l y' - (l : Per.Acris l) ^ n' * w) = 0 := by
      rw [hza] at hw
      rw [hy']
      push_cast
      rw [mul_sub]
      linear_combination hw
    exact sub_eq_zero.1 (acris_nat_cancel (pow_ne_zero _ hl.out.ne_zero) h3)
  have h4 := GlobalTheory.AcrisMuBound.pow_dvd_cc hl2 hϖ h2
  have hu : IsUnit (WittVector.constantCoeff (algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l]))) :=
    (u.isUnit.map _).map _
  rw [show y' = y * algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l]) from rfl, map_mul, hu.dvd_mul_right] at h4
  have h5 := hK _ h4
  have h6 : n' ≤ (l - 1) * n' := Nat.le_mul_of_pos_left n' (by omega)
  omega

end GlobalTheory.AcrisMonBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleDictionaryOfParams
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

namespace GlobalTheory.BridgeAdmDict

theorem sz_eq (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) :
    AdmissibleParameterJ.sz D (D.nd.j i) ρ = (D.hc ρ).e (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.liftIdx D i) := by
  have := D.nd.j_range i
  unfold AdmissibleParameterJ.sz
  rw [dite_eq_left (by omega)]
  rfl

theorem PPm_eq (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) :
    AdmissibleParameterJ.PPm D (D.nd.j i) ρ = GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.PP D i ρ := by
  unfold AdmissibleParameterJ.PPm GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.PP GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.param GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.run
  rw [sz_eq, Finset.range_val]

theorem mem_placesOver (D : D7) (i : D.nd.Loc) (τ₀ : D.host.E →+* Qbar (D.nd.l i))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (h : InducesW D.nd i τ₀ w) :
    w ∈ placesOver D.host.E (D.nd.l i) := by
  have h1 := (h ((D.nd.l i : ℕ) : 𝓞 D.host.E)).1
  show ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
  apply h1
  have e : τ₀ (((D.nd.l i : ℕ) : 𝓞 D.host.E) : D.host.E) = algebraMap ℚ_[D.nd.l i] (PadicAlgCl (D.nd.l i)) (D.nd.l i : ℚ_[D.nd.l i]) := by
    simp
  rw [e, PadicAlgCl.norm_extends]
  simpa using (Padic.norm_p_lt_one (p := D.nd.l i))

end GlobalTheory.BridgeAdmDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleShapeAndEpsilonAtEveryLocalisationStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_shape_and_epsilon_at_every_localisation : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.CyclotomicCompletionAdmissible (D := D) i ∧ TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i := by
  first | exact @GlobalTheory.admissible_shape_and_epsilon_at_every_localisation.main | exact GlobalTheory.admissible_shape_and_epsilon_at_every_localisation.main | (intros; apply GlobalTheory.admissible_shape_and_epsilon_at_every_localisation.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalRootOfUnityMulKummerRootMinpoly
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.MinpolyKummerUr

open Polynomial

theorem minpoly_eq {l : ℕ} [Fact l.Prime] {M : ℕ} (hM : 0 < M) {ρ : Om l}
    (hρ : ρ ^ M = -(l : Om l)) :
    minpoly (↥(MaximalUnramifiedExtension l)) ρ = Polynomial.X ^ M + Polynomial.C ((l : ℕ) : ↥(MaximalUnramifiedExtension l)) := by
  set F := MaximalUnramifiedExtension l
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hQ : (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).Monic := by
    apply Polynomial.monic_X_pow_add_C _ hM.ne'
  have hQdeg : (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).natDegree = M := by
    rw [Polynomial.natDegree_X_pow_add_C]
  have haeval : Polynomial.aeval ρ (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)) = 0 := by
    simp [hρ]
  have hint : IsIntegral F ρ := by
    refine ⟨_, hQ, ?_⟩
    rwa [← Polynomial.aeval_def]
  have hdvd : minpoly F ρ ∣ Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F) := minpoly.dvd _ _ haeval
  have hmon := minpoly.monic hint
  have hpos : 0 < (minpoly F ρ).natDegree := minpoly.natDegree_pos hint
  have hle : (minpoly F ρ).natDegree ≤ M := by
    rw [← hQdeg]
    exact Polynomial.natDegree_le_of_dvd hdvd hQ.ne_zero

  have hnρ : ‖ρ‖ ^ M = (l : ℝ)⁻¹ := by
    rw [← norm_pow, hρ, norm_neg, Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l]
  set P := (minpoly F ρ).map (algebraMap F (Om l)) with hP
  have hsp : P.Splits := IsAlgClosed.splits P
  have hPm : P.Monic := hmon.map _
  have hroots : ∀ a ∈ P.roots, ‖0 - a‖ = ‖ρ‖ := by
    intro a ha
    have h1 : P ∣ (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).map (algebraMap F (Om l)) := Polynomial.map_dvd _ hdvd
    have h2 : ((Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).map (algebraMap F (Om l))).IsRoot a :=
      (Polynomial.isRoot_of_mem_roots ha).dvd h1
    have h3 : a ^ M = -(l : Om l) := by
      simp [Polynomial.IsRoot] at h2
      linear_combination h2
    have h4 : ‖a‖ ^ M = ‖ρ‖ ^ M := by
      rw [← norm_pow, ← norm_pow, h3, hρ]
    rw [zero_sub, norm_neg]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hM.ne').1 h4
  have heval : ‖P.eval 0‖ = ‖ρ‖ ^ (minpoly F ρ).natDegree := by
    rw [hsp.eval_eq_prod_roots_of_monic hPm, ← Polynomial.natDegree_map (algebraMap F (Om l)), ← hP,
      hsp.natDegree_eq_card_roots]
    have h3 := map_multiset_prod (normHom : Om l →*₀ ℝ) (P.roots.map (fun a => 0 - a))
    have h4 : ‖(P.roots.map (fun a => 0 - a)).prod‖
        = ((P.roots.map (fun a => 0 - a)).map (normHom : Om l →*₀ ℝ)).prod := h3
    have h5 : Multiset.map ((normHom : Om l →*₀ ℝ) ∘ fun a => 0 - a) P.roots
        = Multiset.map (fun _ => ‖ρ‖) P.roots :=
      Multiset.map_congr rfl (fun a ha => by simpa using hroots a ha)
    rw [h4, Multiset.map_map, h5, Multiset.map_const', Multiset.prod_replicate]
  have hy : P.eval 0 = (((minpoly F ρ).eval 0 : F) : Om l) := by
    rw [hP, Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]
    rfl
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hρ
    have : ((l : ℕ) : Om l) ≠ 0 := by
      intro h
      have := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l (l := l)
      rw [h, norm_zero] at this
      exact (inv_pos.2 hl0).ne this
    exact this (neg_eq_zero.1 hρ.symm)
  have hnρpos : 0 < ‖ρ‖ := norm_pos_iff.2 hρ0
  have hy0 : (((minpoly F ρ).eval 0 : F) : Om l) ≠ 0 := by
    rw [← hy, ← norm_pos_iff, heval]
    exact pow_pos hnρpos _
  obtain ⟨m, hm⟩ := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow ((minpoly F ρ).eval 0 : F).2 hy0
  rw [← hy, heval] at hm
  have h8 : (l : ℝ) ^ (m * (M : ℤ)) = (l : ℝ) ^ (-((minpoly F ρ).natDegree : ℤ)) := by
    rw [_root_.zpow_mul, ← hm, zpow_natCast, ← pow_mul, mul_comm, pow_mul, hnρ, _root_.zpow_neg, zpow_natCast, inv_pow]
  have h9 : m * (M : ℤ) = -((minpoly F ρ).natDegree : ℤ) :=
    zpow_right_injective₀ hl0 hl1.ne' h8
  have h10 : (M : ℤ) ∣ ((minpoly F ρ).natDegree : ℤ) := ⟨-m, by linarith⟩
  have hdeg : (minpoly F ρ).natDegree = M :=
    le_antisymm hle (Nat.le_of_dvd hpos (Int.natCast_dvd_natCast.1 h10))
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon hQ hdvd (by rw [hdeg, hQdeg])).symm

theorem aeval_mul_root (l : ℕ) [Fact l.Prime] (M : ℕ) : 0 < M → ∀ (ρ ξ : Om l),
    ρ ^ M = -(l : Om l) → ξ ^ M = 1 → Polynomial.aeval (ξ * ρ) (minpoly ↥(MaximalUnramifiedExtension l) ρ) = 0 := by
  intro hM ρ ξ hρ hξ
  rw [minpoly_eq hM hρ]
  simp [mul_pow, hξ, hρ]

end GlobalTheory.MinpolyKummerUr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDvdOfClosedDiscDvdEisensteinPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscDvd

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem ρ₀_pos_lt (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg hl (by rw [neg_lt_zero]; positivity)

theorem complete_max (bk : BK K) :
    IsAdicComplete (IsLocalRing.maximalIdeal (Wq l bk.a)) (Wq l bk.a) := by
  haveI : IsAdicComplete (Ideal.span {(l : Wq l bk.a)}) (Wq l bk.a) := WittVector.isAdicCompleteIdealSpanP
  have hsurj : Function.Surjective (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) :=
    fun x => ⟨WittVector.teichmuller l x, by simp⟩
  have hm : IsLocalRing.maximalIdeal (Wq l bk.a) = Ideal.span {(l : Wq l bk.a)} := by
    rw [← WittVector.ker_constantCoeff]
    haveI := RingHom.ker_isMaximal_of_surjective _ hsurj
    exact (IsLocalRing.eq_maximalIdeal this).symm
  exact hm ▸ inferInstance

theorem dvd_E (bk : BK K) (s : bk.S) (h : toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ s) :
    bk.E ∣ s := by
  haveI := complete_max bk
  have hg : PowerSeries.map (IsLocalRing.residue (Wq l bk.a)) bk.E ≠ 0 := by
    intro h0
    have h1 := congrArg (PowerSeries.coeff bk.Ep.natDegree) h0
    rw [PowerSeries.coeff_map, BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree, map_one,
      map_zero] at h1
    exact one_ne_zero h1
  have e1 := s.eq_mul_weierstrassDiv_add_weierstrassMod hg
  set r := s %ʷ bk.E
  have e2 := Polynomial.modByMonic_add_div r bk.Ep
  have e3 : s = bk.E * (s /ʷ bk.E + ((r /ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S)) +
      ((r %ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S) := by
    conv_lhs => rw [e1, ← e2]
    rw [Polynomial.coe_add, Polynomial.coe_mul]
    simp only [BK.E]; ring
  have h3 : toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ ((r %ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S) := by
    have : ((r %ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S) =
        s - bk.E * (s /ʷ bk.E + ((r /ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S)) := by
      rw [eq_sub_iff_add_eq, add_comm, ← e3]
    rw [this, map_sub, map_mul]
    exact dvd_sub h (dvd_mul_right _ _)
  have h4 := GlobalTheory.BSP.DiscRem.eq_zero_of_dvd l K bk _ (Polynomial.degree_modByMonic_lt r bk.monic) h3
  rw [e3, h4, Polynomial.coe_zero, add_zero]
  exact dvd_mul_right _ _

theorem dvd_X (bk : BK K) (s : bk.S) (h : toDisc l (X : bk.S) bk.ρ₀ X ∣ toDisc l (X : bk.S) bk.ρ₀ s) :
    (X : bk.S) ∣ s := by
  rw [PowerSeries.X_dvd_iff]
  have hh : ‖toDisc l (0 : Wq l bk.a) 1 ((PowerSeries.constantCoeff : bk.S →+* Wq l bk.a) X)‖ ≤ bk.ρ₀ := by
    rw [PowerSeries.constantCoeff_X, map_zero, norm_zero]; exact NNReal.coe_nonneg _
  have hm := isDiscMap_map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := (0 : Wq l bk.a)) (ρ' := 1)
    (PowerSeries.constantCoeff : bk.S →+* Wq l bk.a) hh
  obtain ⟨z, hz⟩ := h
  have h1 := congrArg (Disc.map (PowerSeries.constantCoeff : bk.S →+* Wq l bk.a) hh) hz
  rw [map_mul, hm.ext, hm.ext, PowerSeries.constantCoeff_X, map_zero, zero_mul] at h1
  exact (GlobalTheory.BSP.disc_zero_one l K bk).2.2.1 (h1.trans (map_zero _).symm)

theorem toDisc_inj (bk : BK K) : Function.Injective (toDisc l (X : bk.S) bk.ρ₀) := by
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  exact (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk bk.S (RingHom.id bk.S) Unit (TopBasis.self bk.J) bk.ρ₀
    (ρ₀_pos_lt bk).1 (ρ₀_pos_lt bk).2).1

theorem mem_nzd (bk : BK K) {x : bk.DS bk.ρ₀} (hx : x ≠ 0) : x ∈ nonZeroDivisors (bk.DS bk.ρ₀) := by
  refine mem_nonZeroDivisors_iff.2 ⟨fun y hy => ?_, fun y hy => ?_⟩
  · have := GlobalTheory.BSP.GaussMul.norm_mul l K bk bk.ρ₀ (ρ₀_pos_lt bk).1 (ρ₀_pos_lt bk).2 x y
    rw [hy, norm_zero] at this
    exact norm_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_left (norm_ne_zero_iff.2 hx))
  · have := GlobalTheory.BSP.GaussMul.norm_mul l K bk bk.ρ₀ (ρ₀_pos_lt bk).1 (ρ₀_pos_lt bk).2 y x
    rw [hy, norm_zero] at this
    exact norm_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_right (norm_ne_zero_iff.2 hx))

theorem dvd_E_pow (bk : BK K) (m : ℕ) : ∀ s : bk.S,
    toDisc l (X : bk.S) bk.ρ₀ bk.E ^ m ∣ toDisc l (X : bk.S) bk.ρ₀ s → bk.E ^ m ∣ s := by
  induction m with
  | zero => intro s _; rw [pow_zero]; exact one_dvd _
  | succ m ih =>
    intro s h
    obtain ⟨s', rfl⟩ := dvd_E bk s ((dvd_pow_self _ (Nat.succ_ne_zero m)).trans h)
    obtain ⟨z, hz⟩ := h
    have hE : toDisc l (X : bk.S) bk.ρ₀ bk.E ≠ 0 := fun h0 =>
      bk.E_ne_zero (toDisc_inj bk (h0.trans (map_zero _).symm))
    rw [map_mul, pow_succ', mul_assoc] at hz
    have := (mul_cancel_left_mem_nonZeroDivisors (mem_nzd bk hE)).1 hz
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih s' ⟨z, this⟩)

end GlobalTheory.BSP.DiscDvd

namespace GlobalTheory.BSP.DiscDvd

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem lift (bk : BK K) (g : bk.S) (hreg : toDisc l (X : bk.S) bk.ρ₀ g ∈ nonZeroDivisors (bk.DS bk.ρ₀))
    (hdiv : ∀ s : bk.S, toDisc l (X : bk.S) bk.ρ₀ g ∣ toDisc l (X : bk.S) bk.ρ₀ s → g ∣ s)
    (a : Ainf l) (h : bk.iS g ∣ bk.iA a) : bk.ev g ∣ a := by
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  obtain ⟨h0, h1⟩ := ρ₀_pos_lt bk
  have hj : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 h0
  have hjm := isDiscMap_map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := bk.ev X) (ρ' := bk.ρ₀) bk.ev hj
  obtain ⟨cD, hc1, hc2, -, hc4, -⟩ :=
    GlobalTheory.BSP.disc_coefficients l K bk (Ainf l) bk.ev ι TB bk.ρ₀ h0 h1 _ hjm
  obtain ⟨y, hy⟩ := h
  have hiS : bk.iS g = Disc.map bk.ev hj (toDisc l (X : bk.S) bk.ρ₀ g) := (hjm.ext g).symm
  have hq : ∀ i, ∃ q : bk.S, TB.c i a = g * q ∧ toDisc l (X : bk.S) bk.ρ₀ q = cD i y := by
    intro i
    have e : toDisc l (X : bk.S) bk.ρ₀ (TB.c i a) = toDisc l (X : bk.S) bk.ρ₀ g * cD i y := by
      rw [← hc1, show toDisc l (bk.ev X) bk.ρ₀ a = bk.iA a from rfl, hy, hiS, hc2]
    obtain ⟨q, hq⟩ := hdiv _ ⟨_, e⟩
    refine ⟨q, hq, ?_⟩
    rw [hq, map_mul] at e
    exact (mul_cancel_left_mem_nonZeroDivisors hreg).1 e
  choose q hq1 hq2 using hq
  classical
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  have hsmall := (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk bk.S (RingHom.id bk.S) Unit
    (TopBasis.self bk.J) bk.ρ₀ h0 h1).2.1
  have hfin : ∀ n, {i | q i ∉ bk.J ^ n}.Finite := by
    intro n
    obtain ⟨r, hr, hr'⟩ := hsmall n
    have hev : ∀ᶠ i in Filter.cofinite, ‖cD i y‖ < r :=
      (hc4 y).norm.eventually (gt_mem_nhds (by simpa using hr))
    refine (Filter.eventually_cofinite.1 hev).subset fun i hi hlt => hi ?_
    have h5 : ‖toDisc l (X : bk.S) bk.ρ₀ (q i)‖ ≤ r := by rw [hq2 i]; exact hlt.le
    have h6 := hr' (q i) h5
    rwa [Ideal.map_id] at h6
  let F : ℕ → Finset ι := fun n => (hfin n).toFinset
  have hF : ∀ n i, i ∉ F n → q i ∈ bk.J ^ n := fun n i hi => by
    simpa [F] using hi
  let I : Ideal (Ainf l) := bk.J.map bk.ev
  have key : ∀ n i, i ∉ F n → bk.ev (q i) ∈ I ^ n := fun n i hi => by
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ (hF n i hi)
  let f : ℕ → Ainf l := fun n => ∑ i ∈ F n, bk.ev (q i) * TB.b i
  have hmono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := fun {m n} hmn i hi => by
    simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    exact fun hn => hi (Ideal.pow_le_pow_right hmn hn)
  have hsm : ∀ n : ℕ, (I ^ n • (⊤ : Submodule (Ainf l) (Ainf l))) = I ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD I ^ m • (⊤ : Submodule (Ainf l) (Ainf l))] := by
    intro m n hmn
    rw [SModEq.sub_mem, hsm]
    have e : f m - f n = -∑ i ∈ F n \ F m, bk.ev (q i) * TB.b i := by
      simp only [f]
      rw [← Finset.sum_sdiff (hmono hmn)]; ring
    rw [e]
    refine neg_mem (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (key m i ?_))
    exact (Finset.mem_sdiff.1 hi).2
  haveI : IsAdicComplete I (Ainf l) := TB.complete
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I (Ainf l)) hcauchy
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff I (Ainf l)) _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, hsm]
  have happ := TB.approx a n (F n) fun i hi => by rw [hq1 i]; exact Ideal.mul_mem_left _ _ (hF n i hi)
  rw [Ideal.map_pow] at happ
  have hs : ∑ i ∈ F n, bk.ev (TB.c i a) * TB.b i = bk.ev g * f n := by
    simp only [f, Finset.mul_sum, hq1, map_mul, mul_assoc]
  rw [hs] at happ
  have hLn := hL n
  rw [SModEq.sub_mem, hsm] at hLn
  have e : a - bk.ev g * L = (a - bk.ev g * f n) + bk.ev g * (f n - L) := by ring
  rw [e]
  exact add_mem happ (Ideal.mul_mem_left _ _ hLn)

end GlobalTheory.BSP.DiscDvd

namespace GlobalTheory.BSP

theorem ainf_dvd_of_disc_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (a : Ainf l),
    (∀ m : ℕ, bk.iS bk.E ^ m ∣ bk.iA a → bk.ev bk.E ^ m ∣ a) ∧ (bk.iS X ∣ bk.iA a → bk.ev X ∣ a) := by
  intro l _ K bk a
  have hE : toDisc l (X : bk.S) bk.ρ₀ bk.E ≠ 0 := fun h0 =>
    bk.E_ne_zero (DiscDvd.toDisc_inj bk (h0.trans (map_zero _).symm))
  have hX : toDisc l (X : bk.S) bk.ρ₀ X ≠ 0 := fun h0 =>
    PowerSeries.X_ne_zero (DiscDvd.toDisc_inj bk (h0.trans (map_zero _).symm))
  refine ⟨fun m h => ?_, fun h => DiscDvd.lift bk X (DiscDvd.mem_nzd bk hX) (DiscDvd.dvd_X bk) a h⟩
  rw [← map_pow] at h ⊢
  refine DiscDvd.lift bk (bk.E ^ m) ?_ (fun s hs => DiscDvd.dvd_E_pow bk m s ?_) a h
  · rw [map_pow]; exact pow_mem (DiscDvd.mem_nzd bk hE) m
  · rwa [map_pow] at hs

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCharactersTypePrimeProof
section
noncomputable section

namespace GlobalTheory.Pass.HfCharStep

open _root_.Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem main : StepHfChar := fun D _ HW F h hI i _ _ h2 w hw h1 =>
  GlobalTheory.HfCharProof.hfChar D HW F h hI i w hw h2 ((IntermediateField.finrank_eq_one_iff.mp h1).le.trans bot_le)

end GlobalTheory.Pass.HfCharStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDetMemHeckeAlgebraOfHeckeSpan
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

theorem blockDet_mem : ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep → ∀ (g : ℕ) (Θ : Fin g → Fin g → X → Matrix (Fin n) (Fin n) O), (∀ p q, InRing T rep (Θ p q)) → (fun x => Matrix.det (Matrix.of fun (pa qb : Fin g × Fin n) => Θ pa.1 qb.1 x pa.2 qb.2)) ∈ T := by
  intro Γ X O _ _ n T rep hc g Θ hΘ
  exact GlobalTheory.BlockDet.main T n (ringR T rep)
    (fun m a ha d => _root_.GlobalTheory.SpanRing.coeff_det_generic_sum_mem_of_inRing T rep hc m a (fun k => (mem_ringR T rep _).1 (ha k)) d)
    g Θ (fun p q => (mem_ringR T rep _).2 (hΘ p q))

end GlobalTheory.SpanRing
end

