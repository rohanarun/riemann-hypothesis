module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardKerSubspacesAndHeckePolyOfConvolution
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0105

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftTransferHeckePolySplitPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaPrimeHecke

open Formalism.L2.Host _root_.Formalism.L2.Col

theorem locK_eq_val {L : Type} [Field L] [NumberField L] (χ : HChar L) (Q : HeightOneSpectrum (𝓞 L))
    (hu : χ.UnrAt Q) (k : Lˣ) (hk : Q.valuation L (k : L) = WithZero.exp (-1 : ℤ)) :
    χ.locK Q k = χ.val Q := by
  have h1 : Valued.v ((atFin Q k : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = WithZero.exp (-1 : ℤ) := by
    rw [← hk]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q (k : L)
  have h2 : Valued.v ((atFin Q (unif Q) : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
    unif_spec Q
  have h3 : IsUnitAt Q (atFin Q k * (atFin Q (unif Q))⁻¹) := by
    show Valued.v _ = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, h1, h2, mul_inv_cancel₀ WithZero.exp_ne_zero]
  have h4 := hu _ h3
  rw [map_mul, map_inv, mul_inv_eq_one] at h4
  exact h4

theorem exists_unif {L : Type} [Field L] [NumberField L] (Q : HeightOneSpectrum (𝓞 L)) :
    ∃ ϖ : 𝓞 L, ϖ ∈ Q.asIdeal ∧ ϖ ∉ Q.asIdeal ^ 2 ∧ Q.valuation L (ϖ : L) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨ϖ, h⟩ := Q.intValuation_exists_uniformizer
  refine ⟨ϖ, ?_, ?_, ?_⟩
  · rw [← Q.intValuation_lt_one_iff_mem, h, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  · rw [← Q.intValuation_le_pow_iff_mem, h, WithZero.exp_le_exp]; norm_num
  · rw [← h]; exact Q.valuation_of_algebraMap ϖ

theorem poly_id (q r t : ℕ) (u v : ℂ) (a : ℕ → ℂ) :
    heckePolyOf (r + t) q (fun k => ∑ j ∈ Finset.range (r + 1),
      (if j ≤ k then (q : ℂ) ^ ((r - j) * (k - j)) * (gaussBin q t (k - j) : ℂ) * u⁻¹ ^ k * v ^ j else 0) * a j) =
    (heckePolyOf r q a).comp (C (u⁻¹ * v) * X) * blockPoly (u⁻¹ * (q : ℂ) ^ r) q t := by
  have key := GlobalTheory.KerRangeCount.card_ker_and_heckePolyOf_conv.2 ℂ q r t (fun j => if j ≤ r then a j else 0) u⁻¹ (u⁻¹ * v)
    (fun j hj => if_neg (by omega))
  have h1 : heckePolyOf r q (fun j => if j ≤ r then a j else 0) = heckePolyOf r q a := by
    unfold heckePolyOf
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [if_pos (show j ≤ r by simpa [Nat.lt_succ_iff] using hj)]
  rw [h1] at key
  rw [← key]
  congr 1
  funext k
  simp only [ite_mul, zero_mul, mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_congr (by ext j; simp [Nat.lt_succ_iff, and_comm]) fun j hj => ?_
  have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using (Finset.mem_filter.1 hj).1
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  rw [Nat.add_sub_cancel_left, pow_add, mul_pow]
  ring

variable {D : D7}

theorem not_isConjPl {P : Pl D.host.E} (h : conjPl P ≠ P) : ¬ Formalism.IndefR.Lev.IsConjPl P P := by
  intro hc
  apply h
  refine HeightOneSpectrum.ext ((conjPl P).isMaximal.eq_of_le P.isPrime.ne_top ?_)
  refine Ideal.map_le_iff_le_comap.2 fun c hcP => ?_
  obtain ⟨c', hc', he⟩ := hc c hcP
  have : Formalism.DivisionValues.cO D.host.E c = c' := RingOfIntegers.ext he.symm
  rw [Ideal.mem_comap, this]
  exact hc'

theorem unrPl_mul_inv {P : Pl D.host.E} {a b : (AE D)ˣ →* Circle} (ha : UnrPl P a) (hb : UnrPl P b) : UnrPl P (a * b⁻¹) := by
  intro e f h x h1 h2 h3
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, ha e f h x h1 h2 h3, hb e f h x h1 h2 h3, inv_one, mul_one]

theorem consts (μ η ηa q s : ℂ) (hμ : μ ≠ 0) (hη : η ≠ 0) (hs : s ≠ 0) (hq : s * s = q) (he : ηa = η * s⁻¹) (r t : ℕ)
    (hr : Odd r) (ht : Odd t) :
    (μ * η⁻¹ * s ^ r)⁻¹ * (μ * s ^ (r + t)) = ηa * q ^ ((t + 1) / 2) ∧
      (μ * η⁻¹ * s ^ r)⁻¹ * q ^ r = μ⁻¹ * ηa * q ^ ((r + 1) / 2) := by
  obtain ⟨a, rfl⟩ := hr
  obtain ⟨b, rfl⟩ := ht
  rw [show (2 * a + 1 + 1) / 2 = a + 1 by omega, show (2 * b + 1 + 1) / 2 = b + 1 by omega, he, ← hq]
  constructor
  · field_simp
    ring
  · field_simp
    ring


set_option maxHeartbeats 1600000 in
theorem transfer_and_heckePoly : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ i t (P : A.ok t), ∃ z : ℕ → ℕ → ℂ, (∀ k, k ≤ (Vc D i).rank → MatchW R i t (R.pl P) (Finsupp.single (splitLab (Vc D i).rank k) 1) (splitC (Wc D i).rank (z k))) ∧ ∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf (Vc D i).rank (A.q P) (fun k => ∑ j ∈ Finset.range ((Wc D i).rank + 1), z k j * a j) = (Formalism.L2.Col.heckePolyOf (Wc D i).rank (A.q P) a).comp (C (D.what₂.embLL (A.etaVal P : D.what₂.LL) * (A.q P : ℂ) ^ ((D.R.t + 1) / 2)) * X) * ((A.fam.L i t).blockProd P).map D.what₂.embLL := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hc hS i t P
  obtain ⟨hQ0, hG, -, hF⟩ := _root_.GlobalTheory.GoodPrimes.good_primes R F hc.lev
  obtain ⟨hgood, hsplit, hq⟩ := hF hc.fam t P P.2
  obtain ⟨hunη, hunμ⟩ := _root_.GlobalTheory.UnrOffLevels.unrPl_of_good R F hc.lev t _ hgood
  obtain ⟨gramR, c0R, c0L, tie⟩ := hc.fam.tie
  obtain ⟨-, hAr, hAt⟩ := tie.ranks
  have hP0 : (P : Pl0) ∈ A.ok A.μ0 := by
    have h := (tie.ok t P).1 P.2
    rw [tie.ok, hQ0]
    simp only [Finset.coe_empty, Set.union_empty]
    exact ⟨h.1, fun h' => h.2.1 (Or.inl h'), fun Q hQ => h.2.2 Q (Or.inl hQ)⟩
  obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt (not_isConjPl hsplit)
  obtain ⟨ϖ, hϖ1, hϖ2, hϖ3⟩ := exists_unif (R.pl P)
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ3
    exact WithZero.exp_ne_zero hϖ3.symm
  have hpl : Formalism.L2.JoinChr.IsPlIdem D e (R.pl P) := by
    obtain ⟨⟨h1, h2, v, ε, h3, h4⟩, h5⟩ := he
    exact ⟨h1, ⟨v, ε, h3, Or.inl ⟨h2, h4⟩⟩, h5⟩
  let x : (AE D)ˣ := Formalism.L2.JoinChr.locU hpl.1 (Units.mk0 _ hϖ0)
  have hx : (x : AE D) = Formalism.L2.JoinChr.locE D e (Units.mk0 _ hϖ0 : D.host.Eˣ) := rfl
  have hx' : (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) := by
    rw [hx, Formalism.L2.JoinChr.locE, Units.val_mk0]
    ring
  have hun1 := hunμ ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2
  obtain ⟨hfix, hM⟩ := GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace R.ψ _ _ _ _ _ (R.pl P) (hc.thP.ωP i t) hsplit hun1 (unrPl_mul_inv hun1 hunη)
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hV : (Vc D i).rank = (Wc D i).rank + D.R.t := by
    rw [hW]
    exact D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hM' := (hM e ϖ x D.R.t he hϖ1 hϖ2 hx').2 hV
  refine ⟨_, fun k hk => _root_.GlobalTheory.DefLiftHecke.matchW_of_match R F hc hS i t _ hgood hfix _ _ (hM' k hk), fun a => ?_⟩

  have hu0 : (R.C.mu0 i).UnrAt (R.pl P) := by
    refine (R.C.isMu0 i).unr _ fun k hk => (hG t _ hgood).1 ?_
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ hk
    · exact Ideal.mul_mem_left _ _ hk
  have huξ : (R.xiH t).UnrAt (R.pl P) := by
    by_contra h
    rcases (hc.lev.Q_ram t _).1 h with h | ⟨PP, h1, h2⟩
    · exact (hgood _ (Or.inr h)).1 rfl
    · exact (hgood _ (Or.inr h1)).2 h2
  have hη : ((R.eta x : Circle) : ℂ) = (R.C.eta.val (R.pl P) : ℂˣ) := by
    rw [hc.lev.eta.2 _ e hpl _ x hx, locK_eq_val _ _ (R.C.isEta.unr _) _ hϖ3]
  have hμ : ((R.toLevCh.mu t ((i : ℕ) + 1) x : Circle) : ℂ) = D.what₂.embLL (A.muVal i t P : D.what₂.LL) := by
    rw [hc.fam.muVal i t P P.2, HChar.val_mul, Units.val_mul, ← locK_eq_val _ _ hu0 (Units.mk0 _ hϖ0) hϖ3,
      ← locK_eq_val _ _ huξ (Units.mk0 _ hϖ0) hϖ3, ← (hc.lev.mu0 i).2 _ e hpl _ x hx, ← (hc.lev.xi t).2 _ e hpl _ x hx,
      ← Circle.coe_mul]
    rfl
  have hN : (0 : ℝ) < (Ideal.absNorm (R.pl P).asIdeal : ℕ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h => (R.pl P).ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
  have hs0 : ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hN).ne'
  have hss : ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ) *
      ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ) = (Ideal.absNorm (R.pl P).asIdeal : ℕ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hN.le, Complex.ofReal_natCast]
  have hηa : D.what₂.embLL (A.etaVal P : D.what₂.LL) =
      ((R.eta x : Circle) : ℂ) * ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ)⁻¹ := by
    rw [hc.fam.etaVal P hP0, hη, etaAlg, HChar.valTw, Complex.cpow_neg, Real.sqrt_eq_rpow, Complex.ofReal_cpow hN.le,
      Complex.ofReal_natCast]
  have hr : Odd (Wc D i).rank := by
    rw [hW]
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    exact ⟨a + b - 1, by unfold Ranks.r; omega⟩
  obtain ⟨c1, c2⟩ := consts _ _ _ _ _ (Circle.coe_ne_zero (R.toLevCh.mu t ((i : ℕ) + 1) x)) (Circle.coe_ne_zero (R.eta x))
    hs0 hss hηa _ _ hr D.R.t_odd
  have hB : ((A.fam.L i t).blockProd P).map D.what₂.embLL =
      blockPoly (D.what₂.embLL (firstValA (A.muVal i t) A.etaVal A.q A.r P)) (A.q P) A.t := by
    rw [← map_blockPoly]
    simp [BlockDat.blockProd, FamIn.fam, liftDat]
  rw [hB, firstValA, map_mul D.what₂.embLL, map_mul D.what₂.embLL, Units.val_inv_eq_inv_val, map_inv₀, map_pow D.what₂.embLL, map_natCast D.what₂.embLL, ← hμ,
    hAr, hAt, hq, ← hW,
    ← c1, ← c2]
  simp only [Lift.chrTh, MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv]
  rw [hV]
  exact poly_id _ _ _ _ _ a

end GlobalTheory.ThetaPrimeHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypothesesProof
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.Proof.NarrowJetMoments

namespace GlobalTheory.DatumJets.HidaSetting

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S}

theorem conj_notMem (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) (hT : Pr.T u ∈ S) (hg : ∀ i, Pr.g i ∈ S) :
    ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u := by
  have hTn : ∀ P ∈ rowSG Pr sel mu, ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun P hP =>
    notMem_rowSG hPr hsel (hPr.T_prime u) hT (hPr.T_ne_g u) hP
  intro P hP hP'
  rcases (mem_Sall sel mu u P).1 hP with h | h <;> rcases (mem_Sall sel mu u _).1 hP' with h' | h'
  · refine conj_piT_notMem hPr u ⟨conjPrime₂ P, h'⟩ ?_
    change cO X.E (Pr.piT u) ∈ (conjPrime₂ P).asIdeal
    rw [mem_conjP, cO_cO]
    exact decoFin_mem_of_mem_divs h
  · exact hTn _ h' (natCast_mem_conjP.2 (T_mem hPr u ⟨P, h⟩))
  · exact hTn _ h (natCast_mem_conjP.1 (T_mem hPr u ⟨conjPrime₂ P, h'⟩))
  · exact conjP_notMem_rowSG hX hPr hsel hg h h'

theorem notMem_Sall (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) {l : ℕ} (hl : l.Prime) (hS : l ∈ S) (hd : l ∣ Pr.cond)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Sall sel mu u) : (l : 𝓞 X.E) ∉ P.asIdeal := by
  rcases (mem_Sall sel mu u P).1 hP with h | h
  · intro hm
    have h0 : Pr.piT u ∈ P.asIdeal := decoFin_mem_of_mem_divs h
    have h1 : (l : 𝓞 X.E) ∣ Pr.piT u - 1 :=
      (Nat.cast_dvd_cast (hd.mul_right _)).trans (hPr.piT_cong u)
    have h2 : Pr.piT u - 1 ∈ P.asIdeal := Ideal.mem_of_dvd _ h1 hm
    have h3 := P.asIdeal.sub_mem h0 h2
    rw [sub_sub_cancel] at h3
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  · refine notMem_rowSG hPr hsel hl hS (fun i e => ?_) h
    subst e
    have h1 : Pr.g i ≡ 1 [MOD Pr.g i] := (hPr.g_cong i).of_dvd hd
    have h2 : Pr.g i ∣ 1 := (Nat.modEq_zero_iff_dvd).1 (h1.symm.trans ((Nat.modEq_zero_iff_dvd).2 dvd_rfl))
    exact (hPr.g_prime i).one_lt.ne' (Nat.dvd_one.1 h2)

theorem qOf_pos (P : HeightOneSpectrum (𝓞 X.E)) : 0 < Formalism.L2.Col.qOf P :=
  Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem vG_mem_rowSG {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vG i) : P ∈ rowSG Pr sel mu := by
  classical
  exact Finset.mem_union.2 (Or.inl (mem_vGs_iff.2 ⟨i, h⟩))

theorem ne_bot_of_locP {E : Type} [Field E] [NumberField E] [StarRing E] {I : Submodule (𝓞 E) E} {P : HeightOneSpectrum (𝓞 E)}
    (h : localization₂ P.asIdeal I = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) : I ≠ ⊥ := by
  rintro rfl
  have h1 : (1 : E) ∈ localization₂ P.asIdeal (1 : Submodule (𝓞 E) E) :=
    (mem_locP P _ _).2 ⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, Submodule.mem_one.2 ⟨1, by simp⟩⟩
  rw [← h] at h1
  obtain ⟨s, hs, hs'⟩ := (mem_locP P _ _).1 h1
  rw [Submodule.mem_bot, smul_eq_zero] at hs'
  rcases hs' with h | h
  · exact hs (h ▸ zero_mem _)
  · exact one_ne_zero h

theorem setting_of_unit (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (i : Fin 2) (u : Pr.Word) (hT : Pr.T u ∈ S)
    (hg : ∀ i, Pr.g i ∈ S) (cst : LocCst X (rowSG Pr sel mu)) (hcst : cst.Ok) (A : Amb X) (a b : ℕ) (hLa : A.LaHyp a b ∅)
    (hE : A.ESmooth a b) (hU : A.AAUnit (Sall sel mu u)) :
    SplitSet A a b (Sall sel mu u) (X.conjO (Pr.piG i)) (Pr.g i) ∧
      0 < cAof sel mu cst ∧ 0 < cBof sel mu cst u ∧ Pr.g i ∣ cBof sel mu cst u := by
  have hc2 : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  obtain ⟨P₀, hP₀⟩ : (Pr.vG i).Nonempty := Finset.card_pos.1 (hPr.vG_card i ▸ hX.f_pos)
  have hP₀r : P₀ ∈ rowSG Pr sel mu := vG_mem_rowSG hP₀
  have hne : X.conjO (Pr.piG i) ≠ 0 := by
    intro h
    have := hPr.piG_norm i
    rw [h, mul_zero] at this
    exact (hPr.g_prime i).ne_zero (by exact_mod_cast this.symm)
  have hprod : 0 < ∏ P : rowSG Pr sel mu, Formalism.L2.Col.qOf P.1 := Finset.prod_pos fun P _ => qOf_pos P.1
  obtain ⟨h1, h2, -, -, h5, h6⟩ := hLa
  refine ⟨⟨hX, ⟨h1, h2, conj_notMem hX hPr hsel u hT hg, hU, h5, h6⟩,
    ne_bot_of_locP (hU P₀ ((mem_Sall sel mu u P₀).2 (Or.inr hP₀r))), hE, hPr.g_prime i, ?_, ?_, fun P hP => ?_⟩,
    pow_pos hprod _, Nat.mul_pos (hPr.T_prime u).pos (pow_pos hprod _), ?_⟩
  · rw [hc2, mul_comm]
    exact hPr.piG_norm i
  · rw [hc2]
    exact (hPr.piG_cop i).symm
  · exact (mem_Sall sel mu u P).2 (Or.inr (vG_mem_rowSG (i := i) ((mem_divs hne P).2 hP)))
  · refine Dvd.dvd.mul_left (dvd_pow ?_ (Nat.one_le_iff_ne_zero.1 hcst.B_pos)) _
    have e : Formalism.L2.Col.qOf P₀ = Pr.g i := hPr.vG_norm i P₀ hP₀
    have hd := Finset.dvd_prod_of_mem (fun P : rowSG Pr sel mu => Formalism.L2.Col.qOf P.1)
      (Finset.mem_univ (⟨P₀, hP₀r⟩ : rowSG Pr sel mu))
    beta_reduce at hd
    rw [e] at hd
    exact hd

theorem typePrimeBadPrimesLevelsHypotheses_proof : GlobalTheory.DatumJets.TypePrimeBadPrimesLevelsHypotheses := by
  intro D EX sel δ B χ cD hH hsel i u mu cst hcst a b hLa hE
  obtain ⟨hcc, -, -, hX1, hPr⟩ := hH
  have hT : (recPrimes EX).T u ∈ badS D := Or.inr (Or.inl ⟨u, rfl⟩)
  have hg : ∀ j, (recPrimes EX).g j ∈ badS D := fun j => Or.inl (by fin_cases j <;> simp)
  refine setting_of_unit hX1.ok hPr hsel i u hT hg cst hcst _ a b hLa hE fun P hP => ?_
  obtain ⟨l, n, -, hlP, hl, -⟩ := Ideal.exists_prime_and_absNorm_eq_pow P.asIdeal
  refine GlobalTheory.AAUnitAway.locP_AA D _ (recSeam D) _ δ B χ cD P l hl ?_ ?_ hlP ?_
  · intro hs
    refine notMem_Sall hPr hsel u hl (GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.small_mem_badS D l hs) ?_ hP hlP
    exact ((Nat.dvd_of_mem_primeFactors hs).mul_right _).mul_right _
  · rintro rfl
    refine notMem_Sall hPr hsel u hl (Or.inl (by simp)) ?_ hP hlP
    exact (dvd_mul_left _ _).mul_right _
  · rw [hcc, Ideal.absNorm_top]
    exact Nat.coprime_one_left _

end GlobalTheory.DatumJets.HidaSetting
end

