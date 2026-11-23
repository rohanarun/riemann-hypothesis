module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0170
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelGroupNeTopNeBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LtOneOfContinuous
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Filter Topology Matrix GlobalTheory.IsoPull

namespace GlobalTheory.DegOneLift

section Val

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]

theorem tendsto_pow {v : HeightOneSpectrum (𝓞 K)} (x : v.adicCompletion K) (h : Valued.v x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 _ hne)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [Valuation.restrict_lt_iff_lt_embedding, map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_of_continuous {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (s : v.adicCompletion K →+* w.adicCompletion M) (hs : Continuous s) {z : v.adicCompletion K}
    (hz : Valued.v z < 1) : Valued.v (s z) < 1 := by
  have h1 : Tendsto (fun n : ℕ => s z ^ n) atTop (𝓝 0) := by
    have := (hs.tendsto 0).comp (tendsto_pow z hz)
    simpa [Function.comp_def, map_pow] using this
  have hU : {y : w.adicCompletion M | Valued.v y < 1} ∈ 𝓝 (0 : w.adicCompletion M) :=
    Valued.mem_nhds_zero.2 ⟨1, fun y hy => by simpa using hy⟩
  obtain ⟨N, hN⟩ := (h1.eventually hU).exists
  by_contra hc
  rw [not_lt] at hc
  have hN' : Valued.v (s z ^ N) < 1 := hN
  rw [map_pow] at hN'
  exact absurd hN' (not_lt.2 (one_le_pow₀ hc))

theorem mem_iff_lt_one (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    x ∈ v.asIdeal ↔ Valued.v (algebraMap K (v.adicCompletion K) (x : K)) < 1 := by
  have h : Valued.v (algebraMap K (v.adicCompletion K) (x : K)) = v.valuation K (algebraMap (𝓞 K) K x) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [h, HeightOneSpectrum.valuation_lt_one_iff_mem]

theorem over_of_continuous (e : K ≃+* M) {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K →+* w.adicCompletion M) (hi : Continuous i)
    (he : ∀ x : K, i (algebraMap K _ x) = algebraMap M _ (e x)) : Over e v w := by
  have h1 : v.asIdeal ≤ (src e w).asIdeal := by
    intro x hx
    rw [ringEquivPlaceCorrespondence_placeUnder e w x, mem_iff_lt_one]
    rw [mem_iff_lt_one] at hx
    have := lt_one_of_continuous i hi hx
    rw [he] at this
    exact this
  have h2 : v = src e w := HeightOneSpectrum.ext (v.isMaximal.eq_of_le (src e w).isPrime.ne_top h1)
  rw [h2]
  exact ringEquivPlaceCorrespondence_placeUnder e w

theorem normV_eq_absNorm (v : HeightOneSpectrum (𝓞 K)) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem two_le_normV (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ normV v := by
  rw [normV_eq_absNorm]
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

end Val

end GlobalTheory.DegOneLift

namespace GlobalTheory.DegOneLift

section Rep

variable {K M : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M]
  {a : ℕ}

theorem pull_pull (e : K ≃+* M) (φ : Sm K a) : pull a e (pull a e.symm φ) = φ :=
  Subtype.ext <| funext fun g => congrArg φ.1 (mapA_symm e g)

theorem pullSub_pullSub (e : K ≃+* M) (π : CuspSub K a) : pullSub e (pullSub e.symm π) = π := by
  refine CuspSub.ext ?_
  change (π.V.map (pull a e.symm).toLinearMap).map (pull a e).toLinearMap = π.V
  rw [← Submodule.map_comp]
  convert Submodule.map_id π.V
  refine LinearMap.ext fun φ => ?_
  exact pull_pull e φ

def SmIrr.comap {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] (σ : SmIrr H)
    (f : G →* H) (hf : Continuous f) (hs : Function.Surjective f) : SmIrr G where
  V := σ.V
  ρ := σ.ρ.comp f
  smooth x := (σ.smooth x).preimage hf
  irred := by
    obtain ⟨h0, h⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 σ.irred
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g x hx => ?_⟩
    obtain ⟨g, rfl⟩ := hs g
    exact hW g x hx

theorem locRep_pullSub (e : K ≃+* M) {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)} (hO : Over e v w)
    (π : CuspSub K a) (g : GL (Fin a) (v.adicCompletion K)) (x : π.V) :
    (pullSub e.symm π).locRep w (GeneralLinearGroup.map (cLoc hO) g) ((pull a e.symm).submoduleMap π.V x) =
      (pull a e.symm).submoduleMap π.V (π.locRep v g x) := by
  apply Subtype.ext
  refine Eq.trans ?_ (pull_act e.symm (.fin (locGL K a v g)) x.1).symm
  change _ = act (.fin (GeneralLinearGroup.map (cFin e) (locGL K a v g))) (pull a e.symm x.1)
  rw [cFin_locGL hO]
  rfl

end Rep

theorem isLift : ∀ (K M : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M], Module.finrank K M = 1 → ∀ (a : ℕ) (π : CuspSub K a), ∃ P : CuspSub M a, GlobalTheory.GalCut.IsLift π P := by
  intro K M _ _ _ _ _ _ _ h1 a π
  let e : K ≃+* M := RingEquiv.ofBijective (algebraMap K M) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1)
  have he : ∀ x, e x = algebraMap K M x := fun _ => rfl
  refine ⟨pullSub e.symm π, ?_, ?_, ?_⟩
  · intro w f B hf hB
    have hO : Over e.symm w (w.under (𝓞 K)) := fun x => by
      rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap]
      have : algebraMap (𝓞 K) (𝓞 M) (RingOfIntegers.mapRingEquiv e.symm x) = x := by
        apply RingOfIntegers.ext
        change algebraMap K M (e.symm (x : M)) = x
        rw [← he]
        exact e.apply_symm_apply _
      rw [this]
    have hq : normV w = normV (w.under (𝓞 K)) := by
      rw [normV_eq_absNorm, normV_eq_absNorm]
      exact (qV_eq hO).symm
    have h2 := two_le_normV (w.under (𝓞 K))
    have hf1 : f = 1 := Nat.pow_right_injective h2 (by
      change normV (w.under (𝓞 K)) ^ f = normV (w.under (𝓞 K)) ^ 1
      rw [pow_one, ← hf, hq])
    subst hf1
    simp only [pow_one, Multiset.map_id']
    exact hasSat_pullSub e.symm hO hB
  · intro τ
    have hτ : (τ.comp e.toRingHom).comp e.symm.toRingHom = τ := by
      ext x
      simp
    have key : ∀ m, (CG.mk π).HasInfChar (τ.comp (algebraMap K M)) m ↔
        (CG.mk (pullSub e.symm π)).HasInfChar τ m := by
      intro m
      constructor
      · intro h
        exact hasInfChar_pullSub e.symm (π := π) (σ := τ) h
      · intro h
        have h3 : (pullSub e (pullSub e.symm π)).HasInfChar (τ.comp e.toRingHom) m :=
          hasInfChar_pullSub e (σ := τ.comp e.toRingHom) (by rw [hτ]; exact h)
        rw [pullSub_pullSub] at h3
        exact h3
    by_cases h : ∃ m, (CG.mk π).HasInfChar (τ.comp (algebraMap K M)) m
    · obtain ⟨m, hm⟩ := h
      rw [((key m).1 hm).infChar_eq, hm.infChar_eq]
    · have h' : ¬ ∃ m, (CG.mk (pullSub e.symm π)).HasInfChar τ m := fun ⟨m, hm⟩ => h ⟨m, (key m).2 hm⟩
      unfold CG.infChar
      rw [dite_eq_right h, dite_eq_right h']
  · intro v w i hi hie σ σ' hσ hσ'
    have hO : Over e v w := over_of_continuous e i.toRingHom hi fun x => hie x
    have hiL : ∀ y, i y = cLoc hO y := fun y => congrFun
      ((HeightOneSpectrum.denseRange_algebraMap (K := K) v).equalizer hi (continuous_cLoc hO)
        (funext fun x => (hie x).trans (cLoc_algebraMap hO x).symm)) y
    have hsurj : Function.Surjective (GeneralLinearGroup.map (n := Fin a) (cLoc hO)) := fun g =>
      ⟨GeneralLinearGroup.map (locEquiv hO).symm.toRingHom g, Units.ext (Matrix.ext fun _ _ =>
        (locEquiv hO).apply_symm_apply _)⟩
    let σ'' := SmIrr.comap σ' (GeneralLinearGroup.map (n := Fin a) (cLoc hO))
      (continuous_mapGL _ (continuous_cLoc hO)) hsurj
    let T := (pull a e.symm).submoduleMap π.V
    have h'' : π.IsLocComp v σ'' := by
      obtain ⟨f, h0, hf⟩ := hσ'
      refine ⟨T.symm.toLinearMap ∘ₗ f, fun hz => h0 (LinearMap.ext fun x => T.symm.injective ?_), fun g x => ?_⟩
      · exact (LinearMap.congr_fun hz x).trans (map_zero T.symm).symm
      · have e1 := hf (GeneralLinearGroup.map (cLoc hO) g) x
        have e2 : (pullSub e.symm π).locRep w (GeneralLinearGroup.map (cLoc hO) g) (T (T.symm (f x))) =
            T (π.locRep v g (T.symm (f x))) := locRep_pullSub e hO π g (T.symm (f x))
        have e3 : (pullSub e.symm π).locRep w (GeneralLinearGroup.map (cLoc hO) g) (f x) =
            T (π.locRep v g (T.symm (f x))) := by
          refine Eq.trans ?_ e2
          exact congrArg _ (T.apply_symm_apply (f x)).symm
        exact (congrArg T.symm (e1.trans e3)).trans (T.symm_apply_apply _)
    obtain ⟨E⟩ := GlobalTheory.CuspRep.LocUniq.isLocComp_unique π v σ σ'' hσ h''
    refine ⟨E.toLinearEquiv, fun g x => ?_⟩
    have hg : GeneralLinearGroup.map i.toRingHom g = GeneralLinearGroup.map (cLoc hO) g :=
      Units.ext (Matrix.ext fun _ _ => hiL _)
    rw [hg]
    exact LinearMap.congr_fun (E.isIntertwining' g) x

end GlobalTheory.DegOneLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemRatIdxOfJetsRatDeg
section
noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator (FnModAt FnMod facTop facPen Zmu)
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver IsFrames)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg HAt LatWithBasis)

def JetLossAllAt {X : Fields} (Pr : Primes X) (R : Ranks) (A : Amb X)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) : Prop :=
  ∀ (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)), ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal →
  ∀ (u : Pr.Word) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok →
  ∀ (j b : ℕ), j < R.m → b = R.N (j + 1) →
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E (R.N j))) (N' : Submodule (𝓞 X.E) (Sp X.E b)),
    IsSdLat N → IsSdLat N' → StdOver (Pr.g i) N → StdOver (Pr.g i) N' →
  ∀ Ξ : HomE X.E (R.N j) b → X.K, DatumAt (Pr.vG i) (Sall sel mu u) (Pr.g i) (cBof sel mu cst u) w N N' Ξ →
  ∀ e : DVar X.Tau (R.N j) b →₀ ℕ, e.degree + 1 < Pr.g i →
    (∀ c : ℕ, 0 < c → c ∣ cAof sel mu cst * cBof sel mu cst u → e ∈ RatIdx A (Sall sel mu u) (cAof sel mu cst) c N N' Ξ) →
    w.valuation X.K ((Pr.g i : X.K) ^ (X.f * R.N j * b) *
      (e.prod fun k n => X.emb k.1 (star ((Pr.piG i : 𝓞 X.E) : X.E)) ^ n) *
      jetSum A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N N' Ξ e) ≤ 1

def JetLossAll (D : D7) (EX : ErrX D) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
    {δ : ℂ} (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) : Prop :=
  HostTie EX → IsSel (recFields D) sel → AnTie D δ χ cD →
    JetLossAllAt (recPrimes EX) D.R (ambOf (recSeam D) B χ cD) sel (badS D)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

section
variable (A : Amb X)

theorem kerOf_bound_all (hJ : JetLossAllAt Pr R A sel S) (hO : JetOpWeyl) (hW : ChainWeights) (hPr : Pr.Ok)
    (hc : cst.Ok) (u : Pr.Word) (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal)
    {j j' : ℕ} (hj : j < R.m) (hj' : j' = j + 1)
    (hscal : ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)),
      IsSdLat N → StdOver (Pr.g i) N → IsFrames N fr →
      w.valuation X.K (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu j) (muAt Ch sel mu cst j) N fr) = 1)
    (hdeg : (∑ τ, ∑ a, (W.nuW u (j + 1) τ).w a) + 1 < Pr.g i)
    (hrat : GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.JetsRatDeg A (R.N j) (R.N (j + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      fun τ => ∑ a, (W.nuW u (j + 1) τ).w a)
    {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := SG)) (d' : DecoSet (E := X.E) (n := R.N j') (ST := Pr.vT u) (SG := SG'))
    (hs : StdOver (Pr.g i) d.1.N) (hs' : StdOver (Pr.g i) d'.1.N) {fr : Frs X.E (R.N j) (rowSG Pr sel mu)}
    {fr' : Frs X.E (R.N j') (rowSG Pr sel mu)} (hf : IsFrames d.1.N fr) (hf' : IsFrames d'.1.N fr')
    {Ξ : HomE X.E (R.N j) (R.N j') → X.K}
    (hΞ : DatumAt (Pr.vG i) (Sall sel mu u) (Pr.g i) (cBof sel mu cst u) w d.1.N d'.1.N Ξ)
    {v : Formalism.L2.DIV.VV X.K (W.lamTrue u j)} (hv : v ∈ localization₂ w.asIdeal (delAtr X.emb (W.lamTrue u j) d.1.Lsh)) :
    lossAt W i u j • kerOf (stepC W Ch sel mu cst A u j (W.lamTrue u j')) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u)
      d.1.N fr d'.1.N fr' Ξ v ∈ localization₂ w.asIdeal (delAtr X.emb (W.lamTrue u j') d'.1.Lsh) := by
  classical
  subst hj'
  have hT : ∀ Q ∈ Pr.vT u, ((Pr.g i : ℕ) : 𝓞 X.E) ∉ Q.asIdeal := fun Q hQ h =>
    natCast_notMem_of_ne (hPr.T_prime u) (hPr.g_prime i) (hPr.T_ne_g u i) _ h (T_mem_of_piT_mem hPr u (mem_divs hQ))
  have hsd : IsSdLat d.1.N := ⟨d.2.lat, d.2.uni⟩
  have hsd' : IsSdLat d'.1.N := ⟨d'.2.lat, d'.2.uni⟩
  rw [(GlobalTheory.GO.use₃ _ hT d w hw).2] at hv
  rw [(GlobalTheory.GO.use₃ _ hT d' w hw).2, stepC,
    kerOf_thDistC A _ _ (cAof_pos sel mu cst) (cBof_pos sel mu cst hPr u) _ _ _ _ _ _ d.2.lat d'.2.lat,
    LinearMap.smul_apply, smul_comm]
  refine smul_mem_localizationAt_of_le w _ ?_ ?_
  · rw [map_mul, map_inv₀, hscal _ _ _ hsd hs hf, hscal _ _ _ hsd' hs' hf', inv_one, one_mul]
  obtain ⟨s, s', hwt, hnu⟩ := hW X Pr R W u j hj
  refine hO X.K w X.Tau _ _ _ _ _ s s' _ hwt _ _
    (fun τ => (GlobalTheory.TauLat.tauLatLattice X.E X.K X.Tau _ X.emb τ _ (Formalism.L2.Ker.full_of_sd hsd)).toIsLattice)
    (fun τ => (GlobalTheory.TauLat.tauLatLattice X.E X.K X.Tau _ X.emb τ _ (Formalism.L2.Ker.full_of_sd hsd')).toIsLattice)
    (latWithBasis_of_stdOver X.emb (hPr.g_prime i).ne_zero d.2.lat hs w hw)
    (latWithBasis_of_stdOver X.emb (hPr.g_prime i).ne_zero d'.2.lat hs' w hw) _ _ (fun e he => ?_) v hv
  · have h1 : ∀ τ, ((∑ β, ∑ α, e (τ, β, α) : ℕ) : ℤ) = ∑ a, (W.nuW u (j + 1) τ).w a := fun τ => by
      rw [he τ]
      exact Finset.sum_congr rfl fun a _ => hnu τ a
    have h2 : (e.prod fun k n => X.emb k.1 (star ((Pr.piG i : 𝓞 X.E) : X.E)) ^ n) =
        ∏ τ, X.emb τ (star ((Pr.piG i : 𝓞 X.E) : X.E)) ^ (∑ a, (W.nuW u (j + 1) τ).w a).toNat := by
      rw [Finsupp.prod_fintype _ _ fun _ => pow_zero _, Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun τ _ => ?_
      dsimp only
      rw [← h1 τ, Int.toNat_natCast, Finset.prod_pow_eq_pow_sum, Fintype.sum_prod_type]
    have h3 : e.degree + 1 < Pr.g i := by
      have h4 : (e.degree : ℤ) = ∑ τ, ∑ a, (W.nuW u (j + 1) τ).w a := by
        rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type, Nat.cast_sum]
        exact Finset.sum_congr rfl fun τ _ => by rw [← h1 τ, Fintype.sum_prod_type]
      omega
    rw [lossAt, ← h2]
    refine hJ i w hw u mu cst hc j _ hj rfl _ _ hsd hsd' hs hs' Ξ hΞ e h3 fun c hc0 hdvd x hx _ => ?_
    refine hrat _ _ _ x ⟨hsd, hsd', hc0, hdvd, ?_⟩ e fun τ => ?_
    · change ((cAof sel mu cst * cBof sel mu cst u : ℕ) : 𝓞 X.E) • x ∈ homAt _ _ _
      rw [Nat.cast_mul, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ hx
    · dsimp only
      rw [← h1 τ]
      have h5 : (∑ β, ∑ α, (e (τ, β, α) : ℤ)) = ((∑ β, ∑ α, e (τ, β, α) : ℕ) : ℤ) := by
        push_cast
        rfl
      convert (GlobalTheory.ColPeriodCompare.deg_eq e τ).trans h5

end

variable (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (A : Amb X)


set_option maxHeartbeats 1000000 in
theorem colMu_bound_all (hJ : JetLossAllAt Pr R A sel S) (hO : JetOpWeyl) (hW : ChainWeights) (hM : StdMove)
    (hLP : LevelPrimes) (hSU : ScalarUnit) (hEG : EntryAtG) (hEQ : EntryAtQ) (hTQ : TopAtQ)
    (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) (hS : Pr.T u ∈ S) (hSg : ∀ i, Pr.g i ∈ S)
    {G : ChGlob X R.m} {m2 : ℕ} (hL : L.Ok Ch sel mu cst G m2) {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E}
    (hT : Ch.Tied G.σ₀ e G.mu0 eta) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) (P : LevFam X.E X.K R.r Pr.vGs)
    (hK : KerEquivC W Ch sel mu cst L A u m2 b hY P) (hF : ∀ j, (chF W sel mu L u j).Ok)
    (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal)
    (hwt : ∀ j ≤ R.m, ∀ b, WtUnit w ((chF W sel mu L u j).mem b))
    (hdeg : ∀ j < R.m, (∑ τ, ∑ a, (W.nuW u (j + 1) τ).w a) + 1 < Pr.g i)
    (hrat : ∀ j < R.m, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.JetsRatDeg A (R.N j) (R.N (j + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      fun τ => ∑ a, (W.nuW u (j + 1) τ).w a)
    (φ : MfV W Ch u) (hφ : φ ∈ MfL W Ch u) (d : (evGSD W Ch sel mu P u).D) :
    (∏ j ∈ Finset.range R.m, lossAt W i u j) • (colMu W Ch sel mu cst L A u m2 b hY P hK hF hL φ).1 d ∈
      localization₂ w.asIdeal ((evGSD W Ch sel mu P u).Del d) := by
  have hm := hL.hm
  have hlp := hLP X Pr sel S mu hX hPr hsel
  have hq : ∀ Q : rowSG Pr sel mu, Q.1 ∉ Pr.vGs → ((qOf Q.1 : ℕ) : 𝓞 X.K) ∉ w.asIdeal := fun Q hQ =>
    natCast_notMem_of_ne (hlp Q).1.1 (hPr.g_prime i) (fun h => (hlp Q).2 hQ (h ▸ hSg i)) w hw
  have hsu := hSU X Pr R Ch sel S mu cst L G m2 e eta hX hPr hsel hSg hT hL i w hw
  have heq := fun (Q : rowSG Pr sel mu) (hQ : Q.1 ∉ Pr.vGs) => hEQ X Pr R Ch sel S mu cst L G m2 hL Q w hQ (hlp Q).1 (hq Q hQ)
    fun j hj => (hsu j hj).1 Q fun h => hQ (vG_subset i h)
  have hcd := GlobalTheory.LastSteps.chainDataGuarded X Pr R Ch sel S mu cst m2 hPr hL.cst_ok hm
  rw [show Finset.range R.m = Finset.range (m2 + 2) by rw [hm]]
  refine colCpl_bound (chKerC W Ch sel mu cst L A u m2 b hY P hK).kk hF (fun j hj b => hwt j (by omega) b)
    (lossAt W i u) (chKerC W Ch sel mu cst L A u m2 b hY P hK).cp (hF (m2 + 1) b) (hwt _ (by omega) b)
    (fun j hj al be p p' => ?_) (fun al p₀ p Y hYm => ?_) (fun al p d₁ Y hYm => ?_) (startC hL u φ)
    (fun b' p => GlobalTheory.TestLat.WeylLocal.le_locP w _ (hφ (DecoF.deco p))) d
  · obtain ⟨g, hg⟩ := exists_std_pt W sel mu L hM hPr i u j al p
    obtain ⟨g', hg'⟩ := exists_std_pt W sel mu L hM hPr i u (j + 1) be p'
    refine Bd.transfer g g' ((hF j al).del_smul g p) ((hF (j + 1) be).del_smul g' p')
      (((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk j al be).equiv g g' p p') ?_
    generalize g • p = p, g' • p' = p' at hg hg' ⊢
    have e1 : ((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk j al be).k p p' =
        matK W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) j al be p p' := by
      simp only [chKerC, chKer, dif_pos hj]
    rw [e1]
    intro v hv
    refine kerOf_bound_all W Ch sel mu cst A hJ hO hW hPr hL.cst_ok u i w hw (by omega) rfl (hsu j (by omega)).2
      (hdeg j (by omega)) (hrat j (by omega)) (DecoF.deco p) (DecoF.deco p') hg hg' (isFrames_frsF p)
      (isFrames_frsF p') ?_ hv
    exact datumAt_prod hPr hL.cst_ok u i w (DecoF.deco p).1 (DecoF.deco p').2
      (fun Q x => XiAt Ch sel mu cst j Q (L.h j al Q) (L.h (j + 1) be Q) (inFr (frsF sel mu p Q) (frsF sel mu p' Q) x))
      (fun Q hQ => fnModAt_inFr (isFrames_frsF p Q) (isFrames_frsF p' Q)
        (hEG X Pr R Ch sel S mu cst L G m2 hL j hj al be Q hQ (hlp Q).1))
      (fun Q hQ => awayAt_inFr (isFrames_frsF p Q) (isFrames_frsF p' Q) ((heq Q hQ).1 j hj al be))
  · obtain ⟨g, hg⟩ := exists_std_pt W sel mu L hM hPr i u m2 al p₀
    obtain ⟨g', hg'⟩ := exists_std_pt W sel mu L hM hPr i u (m2 + 1) b p
    refine Bd.transfer g g' ((hF m2 al).del_smul g p₀) ((hF (m2 + 1) b).del_smul g' p)
      (((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).equiv1 g g' p₀ p Y) ?_
    have hY' := ((ybCpl W sel mu cst L u m2 b hY).equiv g' p Y).2 hYm
    suffices key : ∀ (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)) Y',
        StdOver (Pr.g i) (DecoF.deco p₀).1.N → StdOver (Pr.g i) (DecoF.deco p).1.N → Y' ∈ ybSet sel mu cst (DecoF.deco p).1.N →
        Bd w (lossAt W i u m2) (((chF W sel mu L u m2).mem al).Del p₀) (((chF W sel mu L u (m2 + 1)).mem b).Del p)
          (((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).k1 p₀ p Y') from key _ _ _ hg hg' hY'
    intro p₀ p Y' hg hg' hY''
    have e1 : ((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).k1 p₀ p Y' =
        cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) al p₀ p Y' := rfl
    rw [e1, cp1K, if_pos hY'']
    intro v hv
    refine kerOf_bound_all W Ch sel mu cst A hJ hO hW hPr hL.cst_ok u i w hw (by omega) rfl (hsu m2 (by omega)).2
      (hdeg m2 (by omega)) (hrat m2 (by omega)) (DecoF.deco p₀) (DecoF.deco p) hg hg' (isFrames_frsF p₀)
      (isFrames_frsF p) ?_ hv
    exact datumAt_prod hPr hL.cst_ok u i w (DecoF.deco p₀).1 (DecoF.deco p).2 (facPen Ch sel mu cst L m2 al p₀ p Y')
      (fun Q hQ => (hcd Q hQ).2.2.2.1 L al (hL.stabG m2 al Q hQ) u p₀ p Y' hY'')
      (fun Q hQ => awayAt_inFr (isFrames_frsF p₀ Q) (isFrames_frsF p Q) ((heq Q hQ).2 al _))
  · obtain ⟨g, hg⟩ := exists_std_pt W sel mu L hM hPr i u (m2 + 1) b p
    obtain ⟨γ, hγ⟩ := hM X Pr hPr i _ d₁.1.N ⟨d₁.2.lat, d₁.2.uni⟩
    refine Bd.transfer (S' := evGSD W Ch sel mu P u) g (γ, 1) ((hF (m2 + 1) b).del_smul g p)
      (evGSD_del_smul W Ch sel mu hPr hsel u hS P γ d₁)
      (((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).equiv2 g (γ, 1) p Y d₁) ?_
    have hY' := ((ybCpl W sel mu cst L u m2 b hY).equiv g p Y).2 hYm
    have hγ' : StdOver (Pr.g i) (((γ, 1) : (evGSD W Ch sel mu P u).G) • d₁).1.N := hγ
    suffices key : ∀ (p : ChPt (R := R) sel mu u (m2 + 1)) Y' (d₂ : RowPt Pr R sel mu),
        StdOver (Pr.g i) (DecoF.deco p).1.N → Y' ∈ ybSet sel mu cst (DecoF.deco p).1.N → StdOver (Pr.g i) d₂.1.N →
        Bd w (lossAt W i u (m2 + 1)) (((chF W sel mu L u (m2 + 1)).mem b).Del p) ((evGSD W Ch sel mu P u).Del d₂)
          (((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).k2 p Y' d₂) from key _ _ _ hg hY' hγ'
    intro p Y' d₂ hg hY'' hγ'
    have e1 : ((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).k2 p Y' d₂ =
        cp2K W Ch sel mu cst (chTh W Ch sel mu cst A u m2) p Y' d₂ := rfl
    rw [e1, cp2K, if_pos hY'']
    intro v hv
    refine kerOf_bound_all W Ch sel mu cst A hJ hO hW hPr hL.cst_ok u i w hw (j := m2 + 1) (j' := R.m) (by omega) hm
      (hsu _ (by omega)).2 (hdeg _ (by omega)) (hrat _ (by omega)) (DecoF.deco p) (tilQ sel mu u d₂) hg
      (stdOver_tilH _ (conj_piT_notMem hPr u) (piT_notMem_rowSG sel mu hPr hsel u hS) d₂ hγ') (isFrames_frsF p)
      (isFrames_frsT d₂) ?_ hv
    exact datumAt_prod hPr hL.cst_ok u i w (DecoF.deco p).1 (tilQ sel mu u d₂).2 (facTop Ch sel mu cst m2 p Y' d₂)
      (fun Q hQ => (hcd Q hQ).2.2.2.2 u (piT_notMem_rowSG sel mu hPr hsel u hS) p d₂ Y' hY'')
      (fun Q hQ => hTQ X Pr R Ch sel S mu cst L G m2 u hPr hsel hS hL Q w hQ (hlp Q).1 (hq Q hQ) p d₂ Y' hY'')

end GlobalTheory.ColPeriod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetTwist
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

namespace GlobalTheory.TopLaw

section Gen

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {n r b : ℕ}

theorem parL_map_of_red (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : GLint E n P)
    (h : redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b) {v : Sp E n} (hv : v ∈ LocE.parL P (qOf P) r n 0) :
    j.1 v ∈ LocE.parL P (qOf P) r n 0 := by
  have hq0 := qOf_ne_zero (P := P)
  have hv' : ∀ l : Fin n, IntAt P (((qOf P : E) ^ (if r ≤ l.1 ∧ l.1 < n then (1 : ℤ) else 0))⁻¹ * v l) :=
    GlobalTheory.LastSteps.mem_sclLat.1 hv
  have hv0 : ∀ l : Fin n, IntAt P (v l) := fun l => by
    have h1 := hv' l
    split_ifs at h1
    · have h2 := (intAt_nat (P := P) (qOf P)).mul h1
      rwa [zpow_one, mul_inv_cancel_left₀ hq0] at h2
    · simpa using h1
  refine GlobalTheory.LastSteps.mem_sclLat.2 fun (l : Fin n) => ?_
  show IntAt P (((qOf P : E) ^ (if r ≤ l.1 ∧ l.1 < n then (1 : ℤ) else 0))⁻¹ * j.1 v l)
  split_ifs with hl
  · have e := apply_eq_sum (j.1 : Sp E n →ₗ[E] Sp E n) v l
    rw [LinearEquiv.coe_coe] at e
    rw [e, Finset.mul_sum, zpow_one]
    refine intAt_sum _ fun i _ => ?_
    by_cases hi : r ≤ i.1
    · have h1 := hv' i
      rw [if_pos ⟨hi, i.2⟩, zpow_one] at h1
      rw [← mul_assoc]
      exact h1.mul (glint_entry j l i)
    · have h0 : redP P (j.1 (Pi.single i 1) l) = 0 :=
        mem_btG.1 h l i (by rw [coarse_of_lt (Nat.not_le.1 hi), coarse_of_le hl.1]; omega)
      have h1 := (hv0 i).mul (intAt_div_of_redP hq (glint_entry j l i) h0)
      convert h1 using 1
      ring
  · rw [zpow_zero, inv_one, one_mul]
    exact mem_stdAt.1 (glint_mem j (mem_stdAt.2 hv0)) l

theorem mem_JQ_of_red (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : GLint E n P)
    (h : redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b) : j.1 ∈ LocE.JQ P (qOf P) r n 0 := by
  refine ⟨j.2, fun v => ⟨fun hv => ?_, parL_map_of_red hq j h⟩⟩
  have h1 := parL_map_of_red hq j⁻¹ (by rw [map_inv]; exact inv_mem h) hv
  have e : (j⁻¹).1 (j.1 v) = v := LinearEquiv.symm_apply_apply j.1 v
  exact e ▸ h1

theorem lamQB_eq_red (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (hn : n = r + b) (j : GLint E n P)
    (h : redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b) :
    LocE.lamQB ξ r n j.1.toLinearMap = (((lamQ ξ n r b ⟨_, h⟩)⁻¹ : Kˣ) : K) := by
  have hA : GlobalTheory.DatumLaw.IntM P n n fun p p' => Loc.atN (j.1.toLinearMap (Loc.eN E n p')) p := fun p p' hp hp' => by
    show IntAt P (Loc.atN _ _)
    rw [GlobalTheory.LastSteps.eN_eq hp', Loc.atN, dite_eq_left hp]
    exact glint_entry j _ _
  have h1 := blkDet_eq_dB (coarse r [b]) 1 r (n - r) (by omega) (fun i hi => by
    by_cases hr : i < r
    · rw [coarse_of_lt hr]; omega
    · rw [coarse_of_le (Nat.not_lt.1 hr), blkIdx, if_pos (by omega)]; omega) ⟨_, h⟩
    (GlobalTheory.DatumLaw.red P fun p p' => Loc.atN (j.1.toLinearMap (Loc.eN E n p')) p) (fun i l => by
      show redP P (Loc.atN _ _) = _
      rw [GlobalTheory.LastSteps.eN_eq l.2, Loc.atN, dite_eq_left i.2]
      rfl)
  rw [← GlobalTheory.DatumLaw.redP_dB hA (by omega) (by omega)] at h1
  rw [lamQ_apply, Units.val_inv_eq_inv_val]
  show (GlobalTheory.DatumLaw.ext0 ξ (redP P (GlobalTheory.DatumLaw.dB (fun p p' => Loc.atN (j.1.toLinearMap (Loc.eN E n p')) p) r (n - r))))⁻¹ = _
  rw [← h1, GlobalTheory.DatumLaw.ext0, dite_eq_left (Units.isUnit _), IsUnit.unit_of_val_units]

end Gen

theorem phiTop_target_twist : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (m2 : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), R.m = m2 + 2 → ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 → P ∉ Pr.vGs → ∀ (sharp : Bool) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (hQ : P ∈ Q) (j : GLint X.E (R.N R.m - 1) P) (h : redGL _ P j ∈ (rowTyQ R (mu : Chr X.F X.E X.K) Q ⟨P, hQ⟩).H) (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) (R.N R.m - 1)), PhiTop Ch mu sharp m2 P (j.1.toLinearMap ∘ₗ x) * LocE.unitV (resChar (mu : Chr X.F X.E X.K) P)⁻¹ ((LinearEquiv.det j.1 : X.Eˣ) : X.E) = (((rowTyQ R (mu : Chr X.F X.E X.K) Q ⟨P, hQ⟩).lam ⟨_, h⟩ : X.Kˣ) : X.K) * PhiTop Ch mu sharp m2 P x := by
  intro X Pr R Ch S mu m2 P hm hq hP sharp Q hQ j h x
  obtain ⟨a1, a2, a3, -⟩ := GlobalTheory.DatumLaw.ranks R (j := m2 + 1) (by omega)
  unfold PhiTop
  rw [if_neg hP]
  have h1 := GlobalTheory.DatumLaw.phiQ_target (resChar (mu : Chr X.F X.E X.K) P) (k₀ := R.k) (r := R.r) (c' := cOf R (m2 + 1))
    (n' := R.N (m2 + 1)) (c := 0) (n := R.N R.m - 1) (kj := R.r) (by omega) (r_le_X' R) rfl (by omega)
    (mem_JQ_of_red hq j h) x
  exact h1.trans (congrArg (· * _) (lamQB_eq_red _ (rank_X'_eq R) j h))

end GlobalTheory.TopLaw
end

