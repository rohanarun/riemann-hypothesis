module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalRingCardinality.SpanPowerMembership.GatTies
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittUnramified.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0114
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0120
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLocalEigenGaloisPolynomialSplit
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.PtLocalEig
open _root_.Formalism.L2

theorem not_bad_of_genAt {D : D7} {M : Formalism.L2.MtFam D} (T : Formalism.L2.NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl)
    (i : D.nd.Loc) (h : i ∈ D.nd.locs j w) (v : PlE D.host) (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (hvk : Formalism.L2.GenAt D (D.what₂.places.resChar w) (T.B.Qc j w) v k) (hc : IsConjPl D.host v s.w) :
    s.v ∉ Formalism.L2.badPl D i := by
  intro hmem
  obtain ⟨w', hover, hw'⟩ := hmem
  obtain ⟨-, e2⟩ := (D.nd.locs_mem j w i).1 h
  have hl : D.nd.l i = D.what₂.places.resChar w := by rw [← D.nd.w_l i, e2]
  have hp : ∀ p : ℕ, w' ∈ placesOver D.host.E p → v ∈ placesOver D.host.E p := by
    intro p hp
    have h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        w'.asIdeal := by rw [map_natCast]; exact hp
    have h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← hover]; exact h1
    have h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        s.w.asIdeal := by
      rw [← Ideal.mem_comap, s.w_under]; exact h2
    rw [map_natCast] at h3
    exact (hc (p : 𝓞 D.host.E) (p : 𝓞 D.host.E) (by simp)).2 h3
  rcases hw' with hQ | ⟨kk, hg⟩ | hpd
  · rw [T.Q_eq j w i h] at hQ
    have hsw : s.w ∈ T.B.Qc j w := T.B.Qc_over j w w' s.w hQ ⟨s.v, hover, s.w_under⟩
    exact hvk.2.2.2.1 (T.B.Qc_conj j w v s.w hsw hc)
  · apply hvk.2.2.1
    refine ⟨?_, hvk.2.1⟩
    have hv := hp _ hg
    fin_cases kk
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  · apply hvk.2.2.1
    refine ⟨?_, hvk.2.1⟩
    rw [hl] at hpd
    exact Or.inr (Or.inr (hp _ hpd))

theorem main : ∀ (D : D7) (M : Formalism.L2.MtFam D), Formalism.L2.HeckeTied D M → Formalism.L2.HeckeRational D M → Formalism.L2.AVTied D M → Formalism.L2.NormalizedLocalCompatibility D M → ∀ i : D.nd.Loc, (∀ (P : D.naut.AV i) (w : PlE D.host), SplitOut D.nd i w → ∃ lam : ℕ → ℂ, galPol D.naut (D.naut.lpTw (D.naut.locV i P w) ((1 - (D.R.nV : ℝ)) / 2)) = X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV, C ((-1) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * lam k) * X ^ (D.R.nV - k) ∧ ∀ (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host w s.w → Formalism.AUTREP.IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ D.naut.typeV i P, Formalism.L2.NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = lam k • (M.loc i).real y) → GlobalTheory.ThetaExh.PtLocal D.nd D.naut i := by
  intro D M HT HR AV NL i hyp P x hcong
  classical
  have tN0 : ∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ),
      Formalism.L2.NG.tN (M.loc i).J s ϖ k (0 : Formalism.AUTREP.GAf D.host.E D.R.nV → (M.loc i).wt.W) = 0 := by
    intro s ϖ k; ext g; simp [Formalism.L2.NG.tN, Formalism.L2.NG.heckeD]
  by_cases hP0 : D.naut.typeV i P = ⊥
  · refine ⟨x, (AV.ptV i P x).2 ?_⟩
    intro v k s ϖ _ _ _ _ _ y hy
    rw [hP0, Submodule.mem_bot] at hy
    subst hy
    rw [map_zero, smul_zero, tN0]
  obtain ⟨y0, hy0, hy0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have h : i ∈ D.nd.locs (D.nd.j i) (D.nd.w i) := (D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  let lamF : PlE D.host → ℕ → ℂ := fun v =>
    if hv : SplitOut D.nd i v then Classical.choose (hyp P v hv) else 0
  have hlamF : ∀ v (hv : SplitOut D.nd i v), lamF v = Classical.choose (hyp P v hv) := fun v hv => dif_pos hv
  have hinjO : Function.Injective (iotaO D.nd D.naut i) := by
    unfold iotaO
    simp only [RingHom.coe_comp]
    exact (D.naut.iotaQC i).injective.comp ((D.naut.iotaQ i).injective.comp
      (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))))
  have hcoef : ∀ v k, SplitOut D.nd i v → 1 ≤ k → k ≤ D.R.nV → ∃ a : D.nd.O i,
      iotaO D.nd D.naut i a = lamF v k ∧
      IsLocalRing.residue (D.nd.O i) a = IsLocalRing.residue (D.nd.O i) ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) := by
    intro v k hv hk1 hk2
    obtain ⟨p, hp1, hp2⟩ := hcong v hv
    have e1 := (Classical.choose_spec (hyp P v hv)).1
    rw [← hlamF v hv] at e1
    exact coeff_extract (iotaO D.nd D.naut i) hinjO D.R.nV (normV v) (normV_unit D i v hv.2.1) p (lamF v)
      (fun k => (D.nd.hT i v k : D.nd.X i → D.nd.O i) x) (hp1.trans e1) hp2 k hk1 hk2
  let aF : PlE D.host → ℕ → D.nd.O i := fun v k =>
    if hv : SplitOut D.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV then Classical.choose (hcoef v k hv.1 hv.2.1 hv.2.2) else 0
  have haF : ∀ v k (hv : SplitOut D.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV), iotaO D.nd D.naut i (aF v k) = lamF v k ∧
      IsLocalRing.residue (D.nd.O i) (aF v k) =
        IsLocalRing.residue (D.nd.O i) ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) := by
    intro v k hv
    simp only [aF, dif_pos hv]
    exact Classical.choose_spec (hcoef v k hv.1 hv.2.1 hv.2.2)
  have hiotaC : ∀ z, iotaO D.nd D.naut i z = NL.iotaC _ _ (NL.phO _ _ i h z) := NL.iotaC_coh _ _ i h
  have hinjC : Function.Injective (NL.iotaC (D.nd.j i) (D.nd.w i)) := by
    intro a b hab
    have e2 : (NL.phO _ _ i h).symm a = (NL.phO _ _ i h).symm b := hinjO (by
      rw [hiotaC, hiotaC, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]; exact hab)
    simpa using congrArg (NL.phO _ _ i h) e2
  let φ : FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)) →+* ℂ := IsFractionRing.lift hinjC
  have hφalg : ∀ z, φ (algebraMap _ _ z) = NL.iotaC _ _ z := fun z => IsFractionRing.lift_algebraMap hinjC z
  have hφK : φ.comp (NL.phK _ _ i h).toRingHom = (D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (D.nd.O i))
    ext z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, NL.phK_alg, hφalg]
    rw [← hiotaC]
    rfl
  have hφ : ∀ y, φ (NL.B.ec _ _ y) = D.what₂.embLL y := by
    intro y
    rw [← NL.phK_emb _ _ i h y, ← D.naut.iota_LL i y]
    exact congrArg (fun f : FractionRing (D.nd.O i) →+* ℂ => f (D.nd.embK i y)) hφK
  let κ : PlE D.host → ℕ → FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)) := fun v k =>
    algebraMap _ _ (NL.phO _ _ i h (aF v k))
  have hκ : ∀ v k, SplitOut D.nd i v → 1 ≤ k → k ≤ D.R.nV → φ (κ v k) = lamF v k := by
    intro v k hv hk1 hk2
    simp only [κ, hφalg]
    rw [← hiotaC]
    exact (haF v k ⟨hv, hk1, hk2⟩).1
  obtain ⟨e, hene, he⟩ := _root_.GlobalTheory.PtLocalEig.eig_descends D M NL.B (D.nd.j i) (D.nd.w i) (D.nd.mu i) (D.nd.j_range i).1
    (D.nd.j_range i).2 (D.nd.mu_w i) φ hφ κ y0 hy0ne (by
      intro v k hvk
      obtain ⟨hv, hk1, hk2⟩ := (Formalism.L2.genAt_iff NL h v k).2 hvk
      obtain ⟨s, ϖ, hc, hu⟩ := _root_.GlobalTheory.SplitConjPlace.splitEx_all D v hv.1
      have hbad : s.v ∉ Formalism.L2.badPl D i := not_bad_of_genAt NL _ _ i h v k s hvk hc
      have hfin := _root_.GlobalTheory.TSetFin.finite_image_tSet D.host.E D.R.nV (M.loc i).J (M.loc i).χ (Formalism.L2.badPl D i) (HT.J_hyp i)
        s ϖ k hbad hu
      refine ⟨s, ϖ, hc, hu, ?_, ?_⟩
      · intro c f f'
        show Formalism.L2.NG.tN (M.loc i).J s ϖ k (c • f + f') =
          c • Formalism.L2.NG.tN (M.loc i).J s ϖ k f + Formalism.L2.NG.tN (M.loc i).J s ϖ k f'
        simp only [Formalism.L2.NG.tN]
        rw [heckeD_add _ _ _ _ hfin c f f', smul_add, smul_comm]
      · rw [hκ v k hv hk1 hk2]
        have e3 := (Classical.choose_spec (hyp P v hv)).2 k s ϖ hc hu hk1 hk2 y0 hy0
        rw [← hlamF v hv] at e3
        exact e3)
  have hinjK : Function.Injective (algebraMap (NL.B.Oc (D.nd.j i) (D.nd.w i))
      (FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)))) := IsFractionRing.injective _ _
  obtain ⟨ψ, hψ, hψW⟩ := pt_of_eigvec (Formalism.L2.heckeGens NL.B (D.nd.j i) (D.nd.w i)) e hene hinjK (by
    rintro _ ⟨v, k, hvk, rfl⟩
    exact ⟨NL.phO _ _ i h (aF v k), he v k hvk⟩)
  have hψv : ∀ v k (hvk : Formalism.L2.GenAt D (D.what₂.places.resChar (D.nd.w i)) (NL.B.Qc (D.nd.j i) (D.nd.w i)) v k),
      ψ ⟨NL.B.hK _ _ v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ = NL.phO _ _ i h (aF v k) := by
    intro v k hvk
    apply hinjK
    have h1 := hψ ⟨NL.B.hK _ _ v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩
    have h2 := he v k hvk
    change NL.B.hK _ _ v k e = _ at h1
    rw [h2] at h1
    exact (smul_left_injective _ hene h1).symm
  have hcls : Formalism.L2.NCov.cls ψ = NL.mx _ _ i := by
    refine (cls_eq_of_residue _ ψ (NL.ptX _ _ i h x).1 ?_).trans (NL.ptX _ _ i h x).2.1
    rintro _ ⟨v, k, hvk, rfl⟩
    rw [hψv v k hvk, ← NL.ptX_hT _ _ i h x v k hvk]
    obtain ⟨hv, hk1, hk2⟩ := (Formalism.L2.genAt_iff NL h v k).2 hvk
    exact residue_map_equiv (NL.phO _ _ i h) (haF v k ⟨hv, hk1, hk2⟩).2
  have hW : Formalism.L2.NCov.W (Formalism.L2.heckeAlg NL.B _ _) (Formalism.L2.NCov.pt ψ) ≠ ⊥ := by
    intro h0
    apply hene
    have h3 := hψW
    rw [h0] at h3
    exact (Submodule.mem_bot _).1 h3
  refine ⟨(NL.ptX _ _ i h).symm ⟨ψ, hcls, hW⟩, (AV.ptV i P _).2 ?_⟩
  intro v k s ϖ hv hc hu hk1 hk2 y hy
  have hvk := (Formalism.L2.genAt_iff NL h v k).1 ⟨hv, hk1, hk2⟩
  have e1 := (Classical.choose_spec (hyp P v hv)).2 k s ϖ hc hu hk1 hk2 y hy
  rw [← hlamF v hv] at e1
  rw [e1]
  congr 1
  show lamF v k = iotaO D.nd D.naut i _
  rw [hiotaC, NL.ptX_hT _ _ i h _ v k hvk, Equiv.apply_symm_apply]
  show lamF v k = NL.iotaC _ _ (ψ ⟨NL.B.hK _ _ v k, _⟩)
  rw [hψv v k hvk, ← hiotaC]
  exact (haF v k ⟨hv, hk1, hk2⟩).1.symm

end GlobalTheory.PtLocalEig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ServedPrimeProperties
section
noncomputable section

namespace GlobalTheory.TwU.Served

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical NumberField

theorem hP_ne_zero (D : D7) (p : ℕ) (hp : p.Prime) (hc : IsResidueClassZero D p) (hn : HNeZero D.host p) : hP D p ≠ 0 := by
  obtain ⟨P, hP', hL, σ, hσ⟩ := Formalism.BasicNotions.Examples₂.LevelValuationRings.exists_frob D.host p hp hc
  have hne : ∃ g, g ∈ frobSet D p := ⟨_, P, hP', hL, σ, hσ, rfl⟩
  obtain ⟨P₂, h1, h2, σ₂, hσ₂, he⟩ := Classical.epsilon_spec hne
  have h3 := @HNeZero.ne_one _ _ _ hn P₂ h1 h2 σ₂ hσ₂
  intro h0
  apply h3
  rw [he]
  have h4 := Formalism.HC.Frame.iota_iotaInv D.R.toFrame (Classical.epsilon (fun g => g ∈ frobSet D p)).2
  unfold hP at h0
  rw [h0, Formalism.HC.Frame.iota_zero] at h4
  exact h4.symm

theorem jacobi_eq_neg_one (D : D7) (p : ℕ) (hp : p.Prime) (hc : IsResidueClassZero D p) :
    jacobiSym (-(D.host.d : ℤ)) p = -1 := by
  obtain ⟨h2, hq, hd, hjd, -⟩ := Formalism.BasicNotions.Examples₂.LevelValuationRings.of_cls D.host p hc
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcop : (-(D.host.d : ℤ)).gcd (p : ℤ) = 1 := by
    rw [Int.neg_gcd, Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes D.host.hyp.2.1 hp).2 (Ne.symm hd)
  rcases jacobiSym.trichotomy (-(D.host.d : ℤ)) p with h | h | h
  · exact absurd hcop (jacobiSym.eq_zero_iff_not_coprime.1 h)
  · exact absurd h hjd
  · exact h

theorem coprime_absNorm_ccK (D : D7) (p : ℕ) (hp : p.Prime) (hc : IsResidueClassZero D p) :
    Nat.Coprime (Ideal.absNorm D.host.ccK) p := by
  obtain ⟨-, -, -, hjd, -⟩ := Formalism.BasicNotions.Examples₂.LevelValuationRings.of_cls D.host p hc
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_)
  obtain ⟨P, hpP, hdvd⟩ := GlobalTheory.HalfCompare.exists_place_of_dvd_absNorm hp D.host.ccK h
  obtain ⟨hNP, hj⟩ := D.host.ccK_split P.asIdeal P.isPrime (Ideal.le_of_dvd hdvd)
  obtain ⟨l, hl, hlP⟩ := GlobalTheory.HalfCompare.exists_prime_under P
  have hlp : l = p := (Nat.prime_dvd_prime_iff_eq hl hp).1 ((hlP p).1 hpP)
  have hlN : l = Ideal.absNorm P.asIdeal :=
    (Nat.prime_dvd_prime_iff_eq hl hNP).1 ((hlP _).1 (Ideal.absNorm_mem P.asIdeal))
  rw [← hlN, hlp] at hj
  exact hjd hj

theorem served_facts : ∀ (D : D7) (p : ℕ), p.Prime → IsResidueClassZero D p → HNeZero D.host p →
    hP D p ≠ 0 ∧ jacobiSym (-(D.host.d : ℤ)) p = -1 ∧ Nat.Coprime (Ideal.absNorm D.host.ccK) p :=
  fun D p hp hc hn => ⟨hP_ne_zero D p hp hc hn, jacobi_eq_neg_one D p hp hc, coprime_absNorm_ccK D p hp hc⟩

end GlobalTheory.TwU.Served
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SigWSubPowDvd
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

noncomputable section

namespace GlobalTheory.TwU

variable {p : ℕ} [Fact p.Prime]

theorem pow_card_sub_dvd {n : ℕ} {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (hirr : Irreducible (p : W)) (hcard : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n) (x : W) :
    (p : W) ∣ x ^ (p ^ n) - x := by
  haveI : (Ideal.span {(p : W)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hirr
  letI : Field (W ⧸ Ideal.span {(p : W)}) := Ideal.Quotient.field _
  haveI : Finite (W ⧸ Ideal.span {(p : W)}) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  letI := Fintype.ofFinite (W ⧸ Ideal.span {(p : W)})
  have h := FiniteField.pow_card (Ideal.Quotient.mk (Ideal.span {(p : W)}) x)
  rw [← Nat.card_eq_fintype_card, hcard, ← map_pow, ← sub_eq_zero, ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
  exact h

theorem sigW_sub_pow_dvd (y : Formalism.L2.G.Pend.WW p) : (p : Formalism.L2.G.Pend.WW p) ∣ Formalism.MainNotions.FormalGroupSystem.sigW p y - y ^ p := by
  have h0 : WittVector.constantCoeff (Formalism.MainNotions.FormalGroupSystem.sigW p y - y ^ p) = 0 := by
    rw [map_sub, map_pow]
    show (WittVector.frobenius y).coeff 0 - y.coeff 0 ^ p = 0
    rw [WittVector.coeff_frobenius_charP, sub_self]
  have hnu : ¬ IsUnit (Formalism.MainNotions.FormalGroupSystem.sigW p y - y ^ p) := fun hu => by
    have := hu.map (WittVector.constantCoeff (p := p) (R := Formalism.L2.G.Pend.kb p))
    rw [h0] at this
    exact not_isUnit_zero this
  have hm := (IsLocalRing.mem_maximalIdeal _).2 hnu
  rwa [(WittVector.irreducible p (k := Formalism.L2.G.Pend.kb p)).maximalIdeal_eq, Ideal.mem_span_singleton] at hm

abbrev sigRes (G : Formalism.MainNotions.G.GAtP p) (v : Fin G.P.nV) : G.P.W v →+* G.P.W v :=
  haveI := (G.P.setting v).frac_alt
  PI.WittUnramWork.sigW (IsFractionRing.injective (G.P.W v) (G.P.Qq v)) (G.P.σ v) (G.P.setting v).frob

theorem sigRes_spec (G : Formalism.MainNotions.G.GAtP p) (v : Fin G.P.nV) (x : G.P.W v) :
    algebraMap (G.P.W v) (G.P.Qq v) (sigRes G v x) = G.P.σ v (algebraMap (G.P.W v) (G.P.Qq v) x) :=
  haveI := (G.P.setting v).frac_alt
  PI.WittUnramWork.sigW_spec _ _ _ x

theorem sigRes_pow (G : Formalism.MainNotions.G.GAtP p) (v : Fin G.P.nV) (s : ℕ) (x : G.P.W v) :
    (G.P.σ v ^ s) (algebraMap (G.P.W v) (G.P.Qq v) x) = algebraMap (G.P.W v) (G.P.Qq v) ((sigRes G v)^[s] x) := by
  induction s generalizing x with
  | zero => rfl
  | succ s ih =>
    rw [pow_succ]
    show (G.P.σ v ^ s) (G.P.σ v (algebraMap (G.P.W v) (G.P.Qq v) x)) = _
    rw [← sigRes_spec, ih, ← Function.iterate_succ_apply]

theorem map_sigRes (G : Formalism.MainNotions.G.GAtP p) (v : Fin G.P.nV) (r : G.P.W v →+* Formalism.L2.G.Pend.WW p) (x : G.P.W v) :
    r (sigRes G v x) = Formalism.MainNotions.FormalGroupSystem.sigW p (r x) := by
  have hS := G.P.setting v
  have hq : ∀ x : G.P.W v, (p : G.P.W v) ∣ x ^ (p ^ G.P.n' v) - x := pow_card_sub_dvd hS.p_unif hS.res_card
  have h := GlobalTheory.T.ringHom_witt_algClosure_eq_of_congr_mod_prime p (G.P.n' v) (G.P.W v) (by have := hS.two_le; omega) hq (r.comp (sigRes G v)) ((Formalism.MainNotions.FormalGroupSystem.sigW p).comp r)
    (fun y => by
      obtain ⟨z, hz⟩ := haveI := hS.frac_alt
        PI.WittUnramWork.sigW_lift (IsFractionRing.injective (G.P.W v) (G.P.Qq v)) (G.P.σ v) hS.frob y
      obtain ⟨c, hc⟩ := sigW_sub_pow_dvd (r y)
      refine ⟨r z - c, ?_⟩
      simp only [RingHom.comp_apply]
      rw [hz, map_add (f := _), map_mul, map_pow, map_natCast]
      rw [sub_eq_iff_eq_add] at hc
      rw [hc]
      ring)
  exact congrArg (fun f => f x) h

theorem nonempty_cEmbC : ∀ (p : ℕ) [Fact p.Prime] (G : GAtP p), 0 < G.P.nV → Nonempty (CEmbC G) := by
  intro p _ G hV
  obtain ⟨E⟩ := _root_.GlobalTheory.nonempty_cEmb_of_pos_nV p G hV
  let φ : ∀ v, G.P.W v →+* ℂ_[p] := fun v => (E.iK.comp (G.P.ι v)).comp (algebraMap (G.P.W v) (G.P.Qq v))
  have hφ1 : ∀ v x, ‖φ v x‖ ≤ 1 := fun v x => by
    show ‖E.iK (G.P.ι v (algebraMap _ _ x))‖ ≤ 1
    rw [(G.P.setting v).ι_comp]
    exact E.int _
  have hφr : ∀ v x, φ v x ∈ (Formalism.L2.G.Pend.wToC p).range := fun v x => by
    have hS := G.P.setting v
    exact _root_.GlobalTheory.mem_range_wToC_of_pow_congr p (G.P.n' v) (G.P.W v) (by have := hS.two_le; omega) (pow_card_sub_dvd hS.p_unif hS.res_card)
      hS.eq_sum_herm_smul_frame_of_inW (φ v) (hφ1 v) x
  let eW : Formalism.L2.G.Pend.WW p ≃+* (Formalism.L2.G.Pend.wToC p).range :=
    RingEquiv.ofBijective (Formalism.L2.G.Pend.wToC p).rangeRestrict
      ⟨fun a b h => Formalism.L2.G.Pend.wToC_injective p (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let rd : ∀ v, G.P.W v →+* Formalism.L2.G.Pend.WW p := fun v =>
    eW.symm.toRingHom.comp ((φ v).codRestrict (Formalism.L2.G.Pend.wToC p).range (hφr v))
  have hrd : ∀ v x, Formalism.L2.G.Pend.wToC p (rd v x) = φ v x := fun v x => by
    have := congrArg Subtype.val (eW.apply_symm_apply ((φ v).codRestrict (Formalism.L2.G.Pend.wToC p).range (hφr v) x))
    exact this
  refine ⟨⟨E, rd, ?_⟩⟩
  intro v s x
  have hit : ∀ y, rd v ((sigRes G v)^[s] y) = (Formalism.MainNotions.FormalGroupSystem.sigW p)^[s] (rd v y) := by
    induction s with
    | zero => intro y; rfl
    | succ s ih => intro y; rw [Function.iterate_succ_apply, ih, map_sigRes, ← Function.iterate_succ_apply]
  rw [sigRes_pow, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap, ← hit, hrd]
  rfl

end GlobalTheory.TwU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitHeckeElementLabelZerosThenNegOnes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3Split

theorem splitLab_pairwise (n k : ℕ) : (splitLab n k).Pairwise (fun a b => b ≤ a) := by
  unfold splitLab
  rw [List.pairwise_append]
  refine ⟨by simp, by simp, fun a ha b hb => ?_⟩
  rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
  norm_num

theorem isLabElt_of_isTEnv : ∀ {D : D7} (V : HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ) (x : Bridge.Gf V), (i.2 ≤ V.rank → isTEnv V pl ok i x → IsLabElt V (pl i.1) (splitLab V.rank i.2) x) ∧ (isLocEnv V pl ok i x → IsLocElt V (pl i.1) x) ∧ (splitLab V.rank i.2).Pairwise (fun a b => b ≤ a) := by
  intro D V Pl0 pl ok i x
  refine ⟨fun hk h => ?_, fun h => ?_, splitLab_pairwise _ _⟩
  · obtain ⟨α, ⟨e, ϖ, he, h1, h2, hα⟩, hx⟩ := h hk
    have hI : IsPrimeIdem (pl i.1) e (e + cA D e) := Or.inl ⟨he, rfl⟩
    have H := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
    obtain ⟨hf1, hf2, -⟩ := H.2.2.1 _ _ _ hI
    obtain ⟨⟨L, hL⟩, -⟩ := H.1 _ hf1 hf2
    exact ⟨e, e + cA D e, ϖ, α⁻¹, hI, h1, h2, inv_mem hα.1, hx, (hL _).1 (inv_mem ((hL _).2 hα.2.1)),
      GlobalTheory.SplitDivisors.divAt_inv_of_isHeckeElt V _ e ϖ _ α he h1 h2 hk hα⟩
  · obtain ⟨e, α, he, hα, hs, hx⟩ := h
    exact ⟨e, e + cA D e, α, Or.inl ⟨he, rfl⟩, hα, hx, hs⟩

end GlobalTheory.Hk3Split
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumAltSignRange
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.TwV.Xc

theorem sum_alt_sign_range (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), (if i % 2 = 1 then (-1 : ℤ) else 1) = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : (2 * m) % 2 = 0 := by omega
    have h2 : (2 * m + 1) % 2 = 1 := by omega
    simp [h1, h2]

theorem sum_alt_sign_pos (n' : ℕ) (hn : Even n') :
    ∑ s : Fin n', (if IsOddPos s then (-1 : ℤ) else 1) = 0 := by
  obtain ⟨m, rfl⟩ := hn
  calc (∑ s : Fin (m + m), (if IsOddPos s then (-1 : ℤ) else 1))
        = ∑ i ∈ Finset.range (m + m), (if i % 2 = 1 then (-1 : ℤ) else 1) := by
          rw [← Fin.sum_univ_eq_sum_range]; rfl
    _ = 0 := by simpa [two_mul] using sum_alt_sign_range m

theorem vm_eq_of_shift (p : ℕ) [Fact p.Prime] (X : Sys p) (v : X.Pl) (l : ℕ) (e : Fin (X.G.P.n' v) → ℤ) (k : ℤ)
    (hk : ∀ s, X.w v l s = e s - k) :
    X.vm v l = ∑ s : Fin (X.G.P.n' v), (if IsOddPos s then -1 else 1) * e s := by
  have hw : ∑ s : Fin (X.G.P.n' v), (if IsOddPos s then -1 else 1) * X.w v l s = X.vm v l := by
    unfold Sys.vm
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : IsOddPos s <;> simp [h]
  rw [← hw]
  have e1 : ∀ s, (if IsOddPos s then (-1 : ℤ) else 1) * X.w v l s =
      (if IsOddPos s then -1 else 1) * e s - (if IsOddPos s then (-1 : ℤ) else 1) * k := by
    intro s; rw [hk s]; ring
  rw [Finset.sum_congr rfl (fun s _ => e1 s), Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_alt_sign_pos _ (X.G.P.setting v).even, zero_mul, sub_zero]

theorem vm_shift_cancels : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (v : X.Pl) (l : ℕ) (e : Fin (X.G.P.n' v) → ℤ) (k : ℤ),
    (∀ s, X.w v l s = e s - k) → X.vm v l = ∑ s : Fin (X.G.P.n' v), (if IsOddPos s then -1 else 1) * e s :=
  fun p _ X v l e k hk => vm_eq_of_shift p X v l e k hk

end GlobalTheory.TwV.Xc
end

