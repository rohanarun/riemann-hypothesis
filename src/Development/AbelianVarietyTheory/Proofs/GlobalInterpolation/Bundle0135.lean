module

public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0134
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0096
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemSuppBarOfNe
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0123
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NegGram
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0108

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberFiniteAndGenusMass
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassNumberMass

theorem classFin_and_classMass : ∀ D : D7, ClassFin D ∧ ClassMass D := by
  intro D
  refine ⟨fun W hW hsig => ?_, fun W hW hsig n g hcov hdisj => ?_⟩
  · obtain ⟨n, g, hcov, hdisj, _⟩ := _root_.GlobalTheory.ClassRestObj.defClassRest D W hW hsig
    exact ⟨n, g, hcov, hdisj⟩
  · obtain ⟨m, g', hcov', hdisj', hsum⟩ := _root_.GlobalTheory.ClassRestObj.defClassRest D W hW hsig
    rw [← hsum]
    exact GlobalTheory.WeightedDoubleCoset.sum_inv_card_stab_eq _ _ _ n m g g' hcov hdisj hcov' hdisj'

end GlobalTheory.ClassNumberMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetMomentsOfUnitPeriod
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MomT

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable


open Formalism.MainNotions.TaylorLogMetric in
theorem jetMoments_of_unitPeriod
    (hM : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc →
      IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]), p ≠ 2 →
      jacobiSym (-(D.host.d : ℤ)) p = 1 → Nat.Coprime (Ideal.absNorm cc) p →
      ∃ Ω : ℂ_[p], ‖Ω‖ = 1 ∧ GlobalTheory.MomT.MomentsAt D cc δ (B.eNat χ) lam Ω)
    (hE : MovesAll) (hL : LatticeFactsAll) : JetMoments := by
  intro D hD H s cc δ B χ cD ⟨hs, _, hcc, hδ, hχ, hcD⟩ u _ hcop w ι hw
  classical
  obtain ⟨lam, hlam⟩ := (_root_.GlobalTheory.MomPlace.places D.X.K (D.Pr.T u) s.σ₀ ι).1
  obtain ⟨⟨hTs, hTq⟩, -⟩ : (D.Pr.T u ∉ H.host.small ∧ D.Pr.T u ≠ H.host.q) ∧
      ∀ i, D.Pr.g i ∉ H.host.small ∧ D.Pr.g i ≠ H.host.q :=
    ⟨(_root_.GlobalTheory.AAUnitAway.locP_AA_and_primes_ne.2 D H s hD).1 u, (_root_.GlobalTheory.AAUnitAway.locP_AA_and_primes_ne.2 D H s hD).2⟩
  have hT2 : D.Pr.T u ≠ 2 := UpperTheory.Small.ne_two H.host hTs
  have hP := hD.primes
  have hp := hP.T_prime u
  have hn := hP.piT_norm u
  obtain ⟨Ω, hΩ, hmom⟩ := hM H cc δ B χ hcc hδ hχ (D.Pr.T u) lam hT2
    ((_root_.GlobalTheory.MomT.SplitK.splitk H D.X s (D.Pr.piT u) _ hs (hP.piT_Kq u)).2 hp hT2 hn (hP.piT_cop u)) hcop
  obtain ⟨M, _, hMe, hMs⟩ := hcD
  have hcQ : ∀ τ, cD τ ∈ TaylorLogMetric.Qbar := by
    intro τ
    obtain ⟨x, hx, -⟩ := hMs τ
    rw [← hx]
    exact mem_algebraicClosure_iff.2
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (algebraMap M ℂ).toRatAlgHom)
  refine ⟨fun τ => TaylorLogMetric.lamC lam (cD (s.iT τ)) / Ω, fun τ => ?_, ?_⟩
  · obtain ⟨x, hx, hx'⟩ := hMs (s.iT τ)
    rw [norm_div, hΩ, div_one, ← hx]
    exact GlobalTheory.EigenGenerator.norm_generator_eq_one H _ lam hTs hTq M hMe _ x hx'
  intro sel S mu cst hsel hS hcq i b _ hb SG SG' d d' hd hd' Ξ₀ hΞ
  have hev : ∀ j, Even (D.R.N j) := fun j => D.R.k_even.add ((D.R.t_odd.add_one).mul_left j)
  have ha := hev i
  have hb' : Even b := hb ▸ hev _
  obtain ⟨hla, hsm⟩ := hL H D.X s cc δ B χ cD hD.fields hs hcc hδ hχ _ _ ha hb'
  have hπ0 : D.Pr.piT u ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hn
    exact hp.ne_zero (by exact_mod_cast hn.symm)
  have hπ0' : D.X.conjO (D.Pr.piT u) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hn
    exact hp.ne_zero (by exact_mod_cast hn.symm)
  obtain ⟨hfree, hrow⟩ := _root_.GlobalTheory.Proof.AbsNormSplitPlace.main D u sel S mu hD hsel (hS (Or.inr ⟨u, rfl⟩))
    (fun k => hS (Or.inl (by fin_cases k <;> simp)))
  have hUT : ∀ P : HeightOneSpectrum (𝓞 D.X.E), ((D.Pr.T u : ℕ) : 𝓞 D.X.E) ∈ P.asIdeal →
      localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 D.X.E) D.X.E) :=
    fun P h => _root_.GlobalTheory.AAUnitAway.locP_AA_and_primes_ne.1 H D.X s cc δ B χ cD P _ hp hTs hTq h hcop
  have hmemS : ∀ P, P ∈ Sall sel mu u ↔ D.Pr.piT u ∈ P.asIdeal ∨ P ∈ rowSG D.Pr sel mu := by
    intro P
    unfold Sall
    rw [Finset.mem_union, Primes.vT, mem_divs hπ0]
  have hU : (ambOf s B χ cD).AAUnit (Sall sel mu u) := by
    intro P hPS
    rcases (hmemS P).1 hPS with h | h
    · exact hUT P (hn ▸ Ideal.mul_mem_right _ _ h)
    · have bad := _root_.GlobalTheory.ThetaMove.BadPrimes.bad_primes D.X D.Pr sel S mu u hD.fields hP hsel (hS (Or.inr ⟨u, rfl⟩))
        (fun k => hS (Or.inl (by fin_cases k <;> simp))) P hPS
      exact _root_.GlobalTheory.PeriodIdealUnit.locP_AA_eq_one D.X H s cc δ B χ cD P bad.2.1 bad.2.2.1 (hcq P h)
  have hG : Nat.Coprime (∏ P : rowSG D.Pr sel mu, Formalism.L2.Col.qOf P.1) (D.Pr.T u) :=
    Nat.Coprime.prod_left fun P _ => (Nat.coprime_primes (hrow P.1 P.2).1 hp).2 (hrow P.1 P.2).2.1
  have hctx : Ctx (ambOf s B χ cD) (D.R.N i) b (Sall sel mu u) (rowSG D.Pr sel mu) (D.Pr.piT u) (D.Pr.T u)
      ((∏ P : rowSG D.Pr sel mu, Formalism.L2.Col.qOf P.1) ^ cst.B) (cAof sel mu cst) :=
    ⟨hD.fields, ⟨hla.1, hla.2.1, hfree, hU, hla.2.2.2.2⟩,
      fun P h => hUT P (hn ▸ Ideal.mul_mem_left _ _ ((mem_divs hπ0' P).1 h)), hsm, hp, hn, hP.piT_cop u, hmemS,
      fun P h => (hrow P h).2.2.1, hG.pow_left _, hG.pow_left _⟩
  have hN : IsSdLat d.1.N := ⟨d.2.lat, d.2.uni⟩
  have hN' : IsSdLat d'.1.N := ⟨d'.2.lat, d'.2.uni⟩
  obtain ⟨c1, c1'⟩ := _root_.GlobalTheory.MomT.ChiUnit.chi_det_unit H D.X s χ _ lam (D.Pr.piT u) _ d.1.N hD.fields hs hχ hn hN
    fun P h => hd ⟨P, (mem_divs hπ0 P).2 h⟩
  obtain ⟨c2, c2'⟩ := _root_.GlobalTheory.MomT.ChiUnit.chi_det_unit H D.X s χ _ lam (D.Pr.piT u) _ d'.1.N hD.fields hs hχ hn hN'
    fun P h => hd' ⟨P, (mem_divs hπ0 P).2 h⟩
  have hF : (ambOf s B χ cD).chiF (D.R.N i) b d.1.N d'.1.N ∈ TaylorLogMetric.Qbar := mul_mem (zpow_mem c1 _) (zpow_mem c2 _)
  have hF1 : ‖TaylorLogMetric.lamC lam ((ambOf s B χ cD).chiF (D.R.N i) b d.1.N d'.1.N)‖ = 1 := by
    refine (congrArg norm (lamC_mul lam (zpow_mem c1 _) (zpow_mem c2 _))).trans ?_
    rw [lamC_zpow lam c1, lamC_zpow lam c2, norm_mul, norm_zpow, norm_zpow, c1', c2', one_zpow, one_zpow, one_mul]
  refine ⟨fun hseen => ?_, fun hseen => ?_⟩
  · refine type_bar hctx hlam hw d d' hF hF1 Ξ₀ hΞ ?_
    have := _root_.GlobalTheory.MomT.PtMoments.ptMom H D.X s cc δ B χ cD _ lam ι Ω (D.X.conjO (D.Pr.piT u)) (D.R.N i) b hD.fields hs hcc hT2 hcop
      (fun k => (hlam k).2) hcQ (fun τ τ' => ?_) (by rw [conjO_conjO, mul_comm, hn])
      (by rw [conjO_conjO]; exact (hP.piT_cop u).symm) (fun τ => (hw _).1 (hseen τ)) ha hb' hla hsm hmom
    · have e : ((D.X.conjO (D.Pr.piT u) : 𝓞 D.X.E) : D.X.E) = star ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) := rfl
      rwa [e, star_star] at this
    · have e : ((D.X.conjO (D.Pr.piT u) : 𝓞 D.X.E) : D.X.E) = star ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) := rfl
      rw [e, hD.fields.emb_star, hD.fields.emb_star, hP.piT_Kq u τ τ']
  · have hsq : ∀ P ∈ divs (D.Pr.piT u), D.Pr.piT u ∉ P.asIdeal ^ 2 := by
      intro P hPm h2
      refine GlobalTheory.SplitUnram.natCast_notMem_sq D.X.E D.X.conjO (D.Pr.piT u) _ conjO_conjO hp hn (hP.piT_cop u) ?_
        (hP.vT_norm u) P hPm (hn ▸ Ideal.mul_mem_right _ _ h2)
      have h1 : (divs (D.Pr.piT u)).card = Module.finrank ℚ D.X.F := (hP.vT_card u).trans hD.fields.card_Tau
      rw [h1, ← Module.finrank_mul_finrank ℚ D.X.F D.X.E, hD.fields.rankE, mul_comm]
    obtain ⟨N'', hN'', hc⟩ := _root_.GlobalTheory.MomT.MomentCompanion.companion D.X b SG' (D.Pr.piT u) d' hD.fields hπ0 (hP.piT_cop u) hsq
    have hval := _root_.GlobalTheory.MomT.ChiMove.chi_move H D.X s χ b SG' (D.Pr.piT u) d' N'' hD.fields hs hχ hπ0 (hP.piT_cop u) hsq hN'' hc
    set k : D.X.K := ∏ τ, (D.X.emb τ (((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) / star ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E)))⁻¹ with hk
    have hval' : χ (TaylorLogMetric.detId H (s.lat d'.1.N) (s.lat N'')) = s.σ₀ k := by
      rw [hval, hk, map_prod]
      exact Finset.prod_congr rfl fun τ _ => (map_inv₀ _ _).symm
    have hk0 : k ≠ 0 := by
      have h0 : ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) ≠ 0 := by exact_mod_cast hπ0
      exact Finset.prod_ne_zero_iff.2 fun τ _ => inv_ne_zero ((map_ne_zero _).2 (div_ne_zero h0 (star_ne_zero.2 h0)))
    have hkn : ‖ι k‖ ≤ (D.Pr.T u : ℝ) ^ D.X.f := by
      rw [hk, map_prod, norm_prod]
      refine (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun τ _ => ?_).trans_eq
        (Finset.prod_const (D.Pr.T u : ℝ))
      rw [map_inv₀]
      exact norm_ratio_le (ι.comp (D.X.emb τ)) hn
    have hcard : (divs (D.Pr.piT u)).card = D.X.f := hP.vT_card u
    have key := type_p hctx hlam hw d d' hd hF hF1 Ξ₀ hΞ
      (_root_.GlobalTheory.MomT.PtMoments.ptMom H D.X s cc δ B χ cD _ lam ι Ω (D.Pr.piT u) (D.R.N i) b hD.fields hs hcc hT2 hcop
        (fun k => (hlam k).2) hcQ (hP.piT_Kq u) hn (hP.piT_cop u) (fun τ => (hw _).1 (hseen τ)) ha hb' hla hsm hmom)
      (hP.vT_norm u) N'' hN'' hc (s.σ₀ (k ^ (D.R.N i / 2))) (hlam _).1 ?_ ?_
    · rw [hcard] at key
      exact key
    · rw [(hlam _).2, map_pow, norm_pow, ← pow_mul, Nat.div_two_mul_two_of_even ha, hcard, pow_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) hkn _
    · intro R hR z
      have hmv := _root_.GlobalTheory.MomT.Move.move H D.X s cc δ B χ cD _ b d.1.N d'.1.N N'' hD.fields hs (hE H cc δ B χ hcc hδ hχ) ha hb' hla
        hN hN' hN'' R hR z
      have hR0 : ((Real.sqrt (R.card : ℝ) : ℝ) : ℂ) ≠ 0 := by
        obtain ⟨x, hx, -⟩ := hR.2.2 0 (zero_mem _)
        have : (0 : ℝ) < R.card := by exact_mod_cast Finset.card_pos.2 ⟨x, hx⟩
        exact_mod_cast (Real.sqrt_pos.2 this).ne'
      have hσ : s.σ₀ k ≠ 0 := (map_ne_zero _).2 hk0
      rw [hmv, hval', map_pow, zpow_neg, zpow_natCast]
      field_simp

end GlobalTheory.MomT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PoissonSummationAdelicTuples
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ.PoissonSum

theorem countable_F (F : Type) [Field F] [NumberField F] : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem rat_add (ξ η : Fin N → F) : (rat (ξ + η) : Fin N → AF F) = rat ξ + rat η := by
  funext l; simp [rat]

theorem rat_neg (ξ : Fin N → F) : (rat (-ξ) : Fin N → AF F) = -rat ξ := by
  funext l; simp [rat]

theorem Bd_add_left (a : Fin N → F) (u v w : Fin N → AF F) :
    Bd (AF F) a (u + v) w = Bd (AF F) a u w + Bd (AF F) a v w := by
  simp only [Bd, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by simp only [Pi.add_apply]; ring

theorem Bd_neg_right (a : Fin N → F) (u w : Fin N → AF F) :
    Bd (AF F) a u (-w) = -Bd (AF F) a u w := by
  simp only [Bd, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun l _ => by simp only [Pi.neg_apply]; ring

theorem Bd_zero_left (a : Fin N → F) (w : Fin N → AF F) : Bd (AF F) a 0 w = 0 := by
  simp [Bd]

theorem Bd_rat (a : Fin N → F) (ξ η : Fin N → F) :
    Bd (AF F) a (rat ξ) (rat η) = algebraMap F (AF F) (Bd F a ξ η) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Bd, rat, map_sum, map_mul]

theorem continuous_Bd_right (a : Fin N → F) (w : Fin N → AF F) :
    Continuous fun u : Fin N → AF F => Bd (AF F) a u w := by
  unfold Bd
  exact continuous_finsetSum _ fun l _ => (continuous_const.mul (continuous_apply l)).mul continuous_const

end GlobalTheory.SWQ.PoissonSum

open GlobalTheory.SWQ.PoissonSum in
theorem GlobalTheory.SWQ.poisson_summation : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ → Decay (Fo ψ ν a Φ) → th (Fo ψ ν a Φ) = th Φ := by
  intro F _ _ N ψ lam ν a hC Φ hΦ hFΦ
  haveI := countable_F F
  have hψ := hC.2.1
  obtain ⟨hHaar, hmem, hinj, -, D, hDm, hD, hD1⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hC.2.2.2.1
  haveI := hHaar
  obtain ⟨hint, hsum, hcont⟩ := _root_.GlobalTheory.decay_integrable_periodise F N hC.1 Φ hΦ
  obtain ⟨-, hsumF, -⟩ := _root_.GlobalTheory.decay_integrable_periodise F N hC.1 _ hFΦ
  set P : (Fin N → AF F) → ℂ := fun u => ∑' ξ : Fin N → F, Φ (rat ξ + u) with hP
  have hper : ∀ ξ u, P (rat ξ + u) = P u := by
    intro ξ u
    simp only [hP]
    refine Eq.trans (tsum_congr fun η => ?_) ((Equiv.addRight ξ).tsum_eq (fun η => Φ (rat η + u)))
    simp [rat_add, add_assoc]
  have hcoef : ∀ ξ, ∫ u in D, P u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = Fo ψ ν a Φ (rat (-ξ)) := by
    intro ξ
    set G := AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))
    let e : (Fin N → F) ≃ G := Equiv.ofBijective (fun η => ⟨rat η, (hmem _).2 ⟨η, rfl⟩⟩)
      ⟨fun η η' h => hinj (congrArg Subtype.val h), fun γ => by
        obtain ⟨η, hη⟩ := (hmem γ.1).1 γ.2
        exact ⟨η, Subtype.ext hη.symm⟩⟩
    haveI : Countable G := e.surjective.countable
    set g : (Fin N → AF F) → ℂ := fun u => Φ u * ψ (-(Bd (AF F) a u (rat ξ))) with hg
    have hgc : Continuous g :=
      hΦ.1.mul (hψ.1.comp (continuous_Bd_right a (rat ξ)).neg)
    have hgn : ∀ u, ‖g u‖ = ‖Φ u‖ := fun u => by simp [hg, hψ.2.1]
    have hgi : Integrable g (muV N ν) :=
      (hint _ hHaar).norm.mono' hgc.aestronglyMeasurable (Eventually.of_forall fun u => (hgn u).le)
    have hshift : ∀ η u, g (rat η + u) = Φ (rat η + u) * ψ (-(Bd (AF F) a u (rat ξ))) := by
      intro η u
      simp only [hg, Bd_add_left, Bd_rat, neg_add, AddChar.map_add_eq_mul, ← map_neg, hψ.2.2.1, one_mul]
    have hFo : Fo ψ ν a Φ (rat (-ξ)) = ∫ u, g u ∂(muV N ν) := by
      simp only [Fo, hg, rat_neg, Bd_neg_right]
    rw [hFo, hD.integral_eq_tsum'' g hgi, ← e.tsum_eq]
    have hvadd : ∀ η u, (e η +ᵥ u : Fin N → AF F) = rat η + u := fun η u => rfl
    simp_rw [hvadd, hshift]
    simp only [hP]
    simp_rw [← tsum_mul_right]
    refine integral_tsum (fun η => ?_) ?_
    · exact ((hΦ.1.comp (continuous_const.add continuous_id)).mul
        (hψ.1.comp (continuous_Bd_right a (rat ξ)).neg)).aestronglyMeasurable
    · have hl := hD.lintegral_eq_tsum'' (fun u => ‖Φ u‖ₑ)
      rw [← e.tsum_eq] at hl
      simp_rw [hvadd] at hl
      have hfin : ∫⁻ u, ‖Φ u‖ₑ ∂(muV N ν) ≠ ∞ := (hint _ hHaar).2.ne
      simp only [← ofReal_norm_eq_enorm] at hl ⊢
      simp only [norm_mul, hψ.2.1, mul_one]
      rw [← hl]
      simpa [ofReal_norm_eq_enorm] using hfin
  have hsc : Summable (fun ξ : Fin N → F => ‖Fo ψ ν a Φ (rat (-ξ))‖) := by
    have h := hsumF 0
    simp only [add_zero] at h
    exact (Equiv.neg (Fin N → F)).summable_iff.2 h
  have key := _root_.GlobalTheory.SWQ.FourierSeries.fourier_series F N ψ lam ν a hC D hD hD1 P _ hcont hper hcoef hsc 0
  have h0 : P 0 = th Φ := by simp [hP, th]
  rw [h0] at key
  rw [key, th]
  refine ((Equiv.neg (Fin N → F)).tsum_eq (fun ξ => Fo ψ ν a Φ (rat ξ))).symm.trans (tsum_congr fun ξ => ?_)
  simp [Bd_zero_left]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeNegativeDefiniteEqOpposite
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NegVol

open Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold

variable {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') {Γ K : Subgroup G} {Γ' K' : Subgroup G'}
  (hΓ : ∀ h, h ∈ Γ ↔ φ h ∈ Γ') (hK : ∀ h, h ∈ K ↔ φ h ∈ K')

def stabEquiv (g' : G') : stab Γ K (φ.symm g') ≃ stab Γ' K' g' where
  toFun γ := ⟨⟨φ γ.1, (hΓ _).mp γ.1.2⟩, by
    have h := (hK _).mp γ.2
    simp only [stab, Set.mem_setOf_eq] at h ⊢
    simpa [map_mul, map_inv] using h⟩
  invFun γ := ⟨⟨φ.symm γ.1, (hΓ _).mpr (by simpa using γ.1.2)⟩, by
    have h := γ.2
    simp only [stab, Set.mem_setOf_eq] at h ⊢
    rw [hK]
    simpa [map_mul, map_inv] using h⟩
  left_inv γ := by ext; simp
  right_inv γ := by ext; simp

include hΓ hK in
theorem transport {ι : Type*} (g' : ι → G')
    (hcov : ∀ x : G', ∃ i, ∃ γ : Γ', ∃ k : K', x = (γ : G') * g' i * k)
    (hdisj : ∀ i j (γ γ' : Γ') (k k' : K'), (γ : G') * g' i * k = (γ' : G') * g' j * k' → i = j)
    (hfin : ∀ i, (stab Γ' K' (g' i)).Finite) :
    (∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * φ.symm (g' i) * k) ∧
    (∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * φ.symm (g' i) * k = (γ' : G) * φ.symm (g' j) * k' → i = j) ∧
    (∀ i, (stab Γ K (φ.symm (g' i))).Finite) ∧
    (∀ i, Nat.card (stab Γ K (φ.symm (g' i))) = Nat.card (stab Γ' K' (g' i))) := by
  refine ⟨fun x => ?_, fun i j γ γ' k k' h => ?_, fun i => ?_, fun i => Nat.card_congr (stabEquiv φ hΓ hK (g' i))⟩
  · obtain ⟨i, γ, k, hx⟩ := hcov (φ x)
    refine ⟨i, ⟨φ.symm γ, (hΓ _).mpr (by simpa using γ.2)⟩, ⟨φ.symm k, (hK _).mpr (by simpa using k.2)⟩, ?_⟩
    apply φ.injective
    simp [map_mul, hx]
  · refine hdisj i j ⟨φ γ, (hΓ _).mp γ.2⟩ ⟨φ γ', (hΓ _).mp γ'.2⟩ ⟨φ k, (hK _).mp k.2⟩ ⟨φ k', (hK _).mp k'.2⟩ ?_
    have := congrArg φ h
    simpa [map_mul] using this
  · have := (hfin i).to_subtype
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (stabEquiv φ hΓ hK (g' i)).symm)

end GlobalTheory.NegVol

namespace GlobalTheory.NegVol

theorem vol_neg_eq : ∀ D : D7, VolTie D → ∀ (W : HSpace D.host.E) (n : ℕ), W.SigOK → (∀ τ, W.sig τ = (0, n)) →
    D.vol W = D.vol (GlobalTheory.NegSpace.neg W) := by
  intro D hT W n hW hsig
  set W' := GlobalTheory.NegSpace.neg W with hW'def
  have hW' : W'.SigOK := _root_.GlobalTheory.NegSpace.sigOK_neg _ W hW
  have hn : n = W.rank := by
    have := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
    rw [hsig] at this; simpa using this
  have hsig' : ∀ τ, W'.sig τ = (W'.rank, 0) := by
    intro τ
    rw [GlobalTheory.NegSpace.neg_sig, hsig τ, GlobalTheory.NegSpace.neg_rank, ← hn]

  obtain ⟨⟨μ, hμ⟩, hall⟩ := hT W 0 n hW hsig
  obtain ⟨⟨𝓕, h𝓕⟩, hF⟩ := hall μ hμ
  obtain ⟨⟨μ', hμ'⟩, hall'⟩ := hT W' W'.rank 0 hW' hsig'
  obtain ⟨⟨𝓕', h𝓕'⟩, hF'⟩ := hall' μ' hμ'

  obtain ⟨φ, -, hΓ, hS⟩ := _root_.GlobalTheory.unitary_neg_same D.host.F D.host.E D.sp.cm.sig W.rank W.gram (-W.gram) rfl

  obtain ⟨m, g', hcov', hdisj', -⟩ := _root_.GlobalTheory.ClassRestObj.defClassRest D W' hW' hsig'
  have hfin' : ∀ i, (Unfold.stab (GamA D W') (StabFin.SFin D.sp.cm.sig W'.gram (L0c D W')) (g' i)).Finite :=
    fun i => StabFin.stab_finite W' D.sp.cm.sig (fun _ => rfl) (fun τ => D.sp.cm.cmUnram.2.1 τ) hW' hsig' _
      (fun k hk y hy => (hk y).mp hy) (g' i)
  obtain ⟨hcov, hdisj, hfin, hcard⟩ := transport φ.toMulEquiv
    (Γ := GamA D W) (K := StabFin.SFin D.sp.cm.sig W.gram (L0c D W))
    (Γ' := (GamA D W' : Subgroup (HA (AF D.host.F) D.sp.cm.sig (-W.gram))))
    (K' := (StabFin.SFin D.sp.cm.sig W'.gram (L0c D W') : Subgroup (HA (AF D.host.F) D.sp.cm.sig (-W.gram)))) hΓ (hS _) g' hcov' hdisj' hfin'

  have hK1 : μ (StabFin.SFin D.sp.cm.sig W.gram (L0c D W) : Set _) = 1 := _root_.GlobalTheory.NegDefStab.measure_SFin_negDef D W n hW hsig μ hμ
  obtain ⟨θ, hθ⟩ := hμ'.2.1
  obtain ⟨A, hA⟩ := (hμ'.2.2 θ hθ).1
  have hK1' : μ' (StabFin.SFin D.sp.cm.sig W'.gram (L0c D W') : Set _) = 1 := by
    have hK : KSub D W' W'.rank 0 θ A = StabFin.SFin D.sp.cm.sig W'.gram (L0c D W') :=
      SetLike.coe_injective (StabFin.KSub_eq D W' hW' hsig' θ hθ A hA)
    rw [← hK]; exact measure_KSub D W' W'.rank μ' hμ' θ hθ A hA
  have := Unfold.borelHA D.sp.cm.sig W.gram
  have := Unfold.borelHA D.sp.cm.sig W'.gram
  haveI := hμ.1
  haveI := hμ'.1
  haveI := Unfold.measurableMulHA D.sp.cm.sig W.gram
  haveI := Unfold.measurableMulHA D.sp.cm.sig W'.gram
  haveI : Countable (GamA D W) := Unfold.countableGamma D.sp.cm.sig W.gram
  haveI : Countable (GamA D W') := Unfold.countableGamma D.sp.cm.sig W'.gram
  have e := Unfold.measure_fd_toReal μ (StabFin.isOpen_SFin W D.sp.cm.sig).measurableSet hK1 _ hcov hdisj hfin h𝓕
  have e' := Unfold.measure_fd_toReal μ' (StabFin.isOpen_SFin W' D.sp.cm.sig).measurableSet hK1' g' hcov' hdisj'
    hfin' h𝓕'
  rw [hF 𝓕 h𝓕, ENNReal.toReal_ofReal (D.vol_pos W).le] at e
  rw [hF' 𝓕' h𝓕', ENNReal.toReal_ofReal (D.vol_pos W').le] at e'
  rw [e, e']
  exact Finset.sum_congr rfl fun i _ => congrArg (fun k : ℕ => ((k : ℝ))⁻¹) (hcard i)

end GlobalTheory.NegVol
end

