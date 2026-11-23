module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0127
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HeckeLocalProduct.PvLocalSelf
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0004
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0247
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0749
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0248
public import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0042

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsRepsImage
section
namespace GlobalTheory.RepresentativesImage

theorem isReps_image {V W : Type} [AddCommGroup V] [AddCommGroup W] [DecidableEq W] (T : V ≃+ W)
    {Λ₁ Λ₂ : AddSubgroup V} {M₁ M₂ : AddSubgroup W} {S : Finset V}
    (hS : Formalism.L2.Th1.H.IsReps Λ₁ Λ₂ S) (h₁ : ∀ x : V, T x ∈ M₁ ↔ x ∈ Λ₁) (h₂ : ∀ x : V, T x ∈ M₂ ↔ x ∈ Λ₂) :
    Formalism.L2.Th1.H.IsReps M₁ M₂ (Finset.image (⇑T : V → W) S) := by
  unfold Formalism.L2.Th1.H.IsReps at hS ⊢
  obtain ⟨hmem, hdist, hcov⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    exact (h₂ v).2 (hmem v hv)
  · intro a ha b hb hab
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hb
    rw [← map_sub] at hab
    rw [hdist v hv u hu ((h₁ _).1 hab)]
  · intro w hw
    obtain ⟨v, rfl⟩ := T.surjective w
    obtain ⟨u, hu, hvu⟩ := hcov v ((h₂ v).1 hw)
    exact ⟨T u, Finset.mem_image_of_mem _ hu, by rw [← map_sub]; exact (h₁ _).2 hvu⟩

end GlobalTheory.RepresentativesImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEntTiedWithEnt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem kerEntTied_withEnt {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX}
    (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (E : KerEnt (I.rec7 l Z) Y ex.tw)
    (hE : EntOk E O) (hS : ∀ u w h, ThAtServed (ex.ker u w h) E)
    (t : KerEntTied ex) (ht : I.StdKerTie l Z t) (hO : t.O = O) (hTop : t.TopPinned) :
    ∃ t' : KerEntTied ex, I.StdKerTie l Z t' ∧ t'.O = O ∧ t'.ent = E ∧ t'.Adapted ∧ t'.TopPinned := by
  obtain ⟨⟨kf, kf_un⟩, hAd⟩ := hE
  subst hO
  refine ⟨{ t with ent := E, ent_lam := fun u w h => (hS u w h).1, kf := kf, kf_un := kf_un, served := hS },
    ?_, rfl, rfl, hAd, hTop⟩
  exact { X_eq := ht.X_eq, seam := ht.seam, Pr := ht.Pr, Ch := ht.Ch, sel := ht.sel, S := ht.S, word := ht.word, tup := ht.tup,
          cst := ht.cst, idx := ht.idx, m2 := ht.m2, glob := ht.glob, amb := ht.amb, δ := ht.δ, O := ht.O }

end GlobalTheory.Mem.Col2.TC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelChainCharacterNormOneEqInfinityType
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem mt_ratId : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i < D.R.m), ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨i, hi⟩) ∧ ∀ z : D.host.Eˣ, (z : D.host.E) * D.host.conj (z : D.host.E) = 1 → ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 = ratId D.host.F D.host.E z → (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP _ i hi
  choose e he using fun τ => (D.hc τ).e_int ⟨i, hi⟩
  refine ⟨e, fun τ => (he τ).symm, fun z hz y hy => ?_⟩
  have hstar : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have hz' : (z : D.host.E) ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, hstar]
    exact ⟨by rw [mul_comm]; exact hz, hz⟩
  obtain ⟨k, hk⟩ := GlobalTheory.Mem.Col2.exists_eq_div_conj D.host ⟨z, hz'⟩
  simp only at hk
  let k' : t.X.Eˣ := Units.map t.seam.iE.symm.toRingHom.toMonoidHom k
  have hik : t.seam.iE (k' : t.X.E) = k := t.seam.iE.apply_symm_apply _
  have hq : A.q (ratId t.X.F t.X.E k') = dtU y := by
    apply hP.q_dt
    rw [hy]
    have hx : Units.map A.iA.toRingHom.toMonoidHom (ratId t.X.F t.X.E k') = ratId D.host.F D.host.E k := by
      apply Units.ext
      show A.iA ((k' : t.X.E) ⊗ₜ[t.X.F] 1) = (k : D.host.E) ⊗ₜ[D.host.F] 1
      rw [hP.iA_rat, hik]
    rw [hx, h90, MonoidHom.div_apply, MonoidHom.id_apply, eq_div_iff_mul_eq']
    apply Units.ext
    show ((z : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F)) *
      (Formalism.UG.sigR (Formalism.L2.Forms.sigD D) _ ((k : D.host.E) ⊗ₜ[D.host.F] 1)) = (k : D.host.E) ⊗ₜ[D.host.F] 1
    rw [Formalism.UG.sigR]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have hs : Formalism.L2.Forms.sigD D (k : D.host.E) = D.host.conj k := bridge_star_holds D.R D.host _
    rw [hs, hk]
  have hmu : ((D.muTil (i + 1) (A.q (ratId t.X.F t.X.E k')) : ℂˣ) : ℂ) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ := by
    obtain ⟨ι, hι⟩ := exists_isAdIso t.X.F t.X.E
    rw [hP.muTil ι hι ⟨i, hi⟩ (GlobalTheory.Mem.Chr.finPartI _ (Neutral.B1.diagUnits _ k')) _ (GlobalTheory.KerJ.RatPts.isFin_finPart _)
      ((hι.1 (k' : t.X.E)).trans rfl), GlobalTheory.Mem.Chr.DetGroupModel.fin_diag, Units.val_inv_eq_inv_val]
    obtain ⟨n, hn, hinf⟩ := (hP.mu0 ⟨i, hi⟩).inf
    rw [hinf k', ← Finset.prod_inv_distrib, ← t.seam.iT.prod_comp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hme : n τ = 2 * -e (t.seam.iT τ) := by
      have h1 := hn τ
      simp only [he] at h1
      exact_mod_cast h1
    have hka : Formalism.L2.Col.Fields.embC t.X t.seam.σ₀ τ (k' : t.X.E) = TaylorLogMetric.embT D (t.seam.iT τ) (k : D.host.E) := by
      rw [← hik]; exact t.seam_ok.1 τ _
    have h1 := congrArg (TaylorLogMetric.embT D (t.seam.iT τ)) hk
    rw [map_mul] at h1
    rw [GlobalTheory.Mem.Chr.DetGroupModel.emb_conj] at h1
    rw [hka]
    have h0 : TaylorLogMetric.embT D (t.seam.iT τ) (k : D.host.E) ≠ 0 := by simp
    generalize TaylorLogMetric.embT D (t.seam.iT τ) (k : D.host.E) = a at *
    generalize TaylorLogMetric.embT D (t.seam.iT τ) (z : D.host.E) = b at *
    have hn' : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0
    have h2 : a * star a = ((‖a‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h3 : (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = b := by
      rw [zpow_ofNat, div_pow, div_eq_iff (pow_ne_zero _ hn'), ← h2]
      linear_combination (-a) * h1
    rw [hme, zpow_mul, h3, zpow_neg, inv_inv]
  have htw : (t.O u μ).mt (i + 1) (A.q (ratId t.X.F t.X.E k')) = D.muTil (i + 1) (A.q (ratId t.X.F t.X.E k')) := by
    by_cases h0 : μ = D.what₂.mu0
    · rw [(hP.ref h0).2]
    · obtain ⟨ξ, hξ, hmt⟩ := hP.tw μ h0 rfl
      rw [hmt u, twMt, if_pos ⟨by omega, by omega⟩, MonoidHom.mul_apply, hξ]
      have h1 : ((t.tup μ : Chr t.X.F t.X.E t.X.K)) (ratId t.X.F t.X.E k') = 1 := by
        have hm := (t.tup μ).2
        exact hm.1.1.1.1.1 ⟨k', rfl⟩
      rw [h1, map_one, mul_one]
  rw [← hq, htw, hmu]

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelChainCharactersAlgebraicUnitaryPoints
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.TieAlgValues

theorem mem_Qbar_of_pow {z : ℂ} {n : ℕ} (hn : 0 < n) (h : z ^ n ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) : z ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  rw [Formalism.MainNotions.TaylorLogMetric.Qbar, mem_algebraicClosure_iff, isAlgebraic_iff_isIntegral] at h ⊢
  exact IsIntegral.of_pow hn h

theorem emb_mem_Qbar {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) (k : L) : φ k ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  rw [Formalism.MainNotions.TaylorLogMetric.Qbar, mem_algebraicClosure_iff, isAlgebraic_iff_isIntegral]
  exact (Algebra.IsIntegral.isIntegral (R := ℚ) k).map φ.toRatAlgHom

theorem conj_mem_Qbar {z : ℂ} (h : z ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) : (starRingEnd ℂ) z ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  rw [Formalism.MainNotions.TaylorLogMetric.Qbar, mem_algebraicClosure_iff, isAlgebraic_iff_isIntegral] at h ⊢
  exact h.map (starRingEnd ℂ).toRatAlgHom

theorem norm_mem_Qbar {z : ℂ} (h : z ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) : ((‖z‖ : ℝ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  refine mem_Qbar_of_pow (n := 2) (by norm_num) ?_
  have e : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * (starRingEnd ℂ) z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [e]
  exact mul_mem h (conj_mem_Qbar h)

theorem inf_mem_Qbar {L : Type} [Field L] [NumberField L] {χ : HChar L} {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n : I → ℤ}
    (h : χ.HasInf φ n) (k : Lˣ) : ((χ.inf k : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  rw [h k]
  exact prod_mem fun i _ => zpow_mem (div_mem (emb_mem_Qbar _ _) (norm_mem_Qbar (emb_mem_Qbar _ _))) _

theorem le_exp_neg_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem loc_pow_eq_one {L : Type} [Field L] [NumberField L] (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) (hv : χ.TameAt v)
    (x : (v.adicCompletion L)ˣ) (hx : IsUnitAt v x) : ∃ n : ℕ, 0 < n ∧ χ.loc v x ^ n = 1 := by
  have := Formalism.UG.P.glint_finite_residueField (F := L) v
  let _ := Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers L))
  set N := Fintype.card (IsLocalRing.ResidueField (v.adicCompletionIntegers L)) with hN
  have hN2 : 1 < N := Fintype.one_lt_card
  have hxO : (x : v.adicCompletion L) ∈ v.adicCompletionIntegers L := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hx.le
  set y : v.adicCompletionIntegers L := ⟨x, hxO⟩
  have hyu : IsUnit y := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hx
  have hr : IsLocalRing.residue _ y ≠ 0 := by
    rw [ne_eq, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact hyu
  have hp : IsLocalRing.residue _ (y ^ (N - 1) - 1) = 0 := by
    rw [map_sub, map_pow, map_one, FiniteField.pow_card_sub_one_eq_one _ hr, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff] at hp
  have hlt : Valued.v (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L) (WithZero (Multiplicative ℤ))))).1 hp
  refine ⟨N - 1, by omega, ?_⟩
  rw [← map_pow]
  refine hv _ ?_ ?_
  · show Valued.v (((x ^ (N - 1) : (v.adicCompletion L)ˣ)) : v.adicCompletion L) = 1
    rw [Units.val_pow_eq_pow_val, map_pow, show Valued.v (x : v.adicCompletion L) = 1 from hx, one_pow]
  · have e : (((x ^ (N - 1) : (v.adicCompletion L)ˣ)) : v.adicCompletion L) - 1 =
        (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) := by
      push_cast; rfl
    rw [e]
    exact le_exp_neg_one hlt

theorem loc_mem_Qbar {L : Type} [Field L] [NumberField L] (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) (hv : χ.TameAt v)
    (x : (v.adicCompletion L)ˣ) (hx : IsUnitAt v x) : ((χ.loc v x : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  obtain ⟨n, hn, h⟩ := loc_pow_eq_one χ v hv x hx
  refine mem_Qbar_of_pow hn ?_
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  exact one_mem _

end GlobalTheory.TieAlgValues

namespace GlobalTheory.TieAlgValues

open PI.HeckeProdW

theorem fin_mem_Qbar {L : Type} [Field L] [NumberField L] (χ : HChar L) (htame : ∀ v, χ.TameAt v)
    (hinf : ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) (b : Ideles L) (hb : IsFinIdele b) :
    ((χ.1 b : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  classical
  obtain ⟨h, hh, hx⟩ := CharEx.classExp L
  obtain ⟨k, hk⟩ := hx b
  set u : Ideles L := b ^ h * diagUnits L k with hu
  set w : Ideles L := (infDiag k)⁻¹ * u with hw
  have hwInf : (w : AdeleRing (𝓞 L) L).1 = 1 := by
    funext pl
    show pw pl w = 1
    refine f_inv_mul (pw pl) _ _ ?_
    rw [pw_infDiag, hu, map_mul, map_pow, pw_diag]
    have : pw pl b = 1 := hb pl
    rw [this, one_pow, one_mul]
  have hwFin : ∀ v, Valued.v ((w : AdeleRing (𝓞 L) L).2 v) = 1 := by
    intro v
    show Valued.v (pv v w) = 1
    rw [hw, f_inv_mul' (pv v) _ _ (pv_infDiag v k)]
    exact hk v
  have hmemO : ∀ v : HeightOneSpectrum (𝓞 L), (w : AdeleRing (𝓞 L) L).2 v ∈ v.adicCompletionIntegers L := fun v => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact (hwFin v).le
  have hunit : ∀ v : HeightOneSpectrum (𝓞 L), IsUnit (⟨_, hmemO v⟩ : v.adicCompletionIntegers L) := fun v =>
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 (hwFin v)
  let y : Pu L := fun v => (hunit v).unit
  have hwy : w = Phi L y := Units.ext (Prod.ext (hwInf.trans rfl) (Subtype.ext (funext fun v => rfl)))
  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring χ
  set p : Pu L := ∏ v ∈ T, Pi.mulSingle v (y v) with hp
  have hpv : ∀ v ∈ T, p v = y v := fun v hv => by
    rw [hp, Finset.prod_apply, Finset.prod_pi_mulSingle, if_pos hv]
  have hsplit : y = p * (p⁻¹ * y) := by rw [mul_inv_cancel_left]
  have hrest : χ.1 (Phi L (p⁻¹ * y)) = 1 :=
    hT _ fun v hv => by rw [Pi.mul_apply, Pi.inv_apply, hpv v hv, inv_mul_cancel]
  have hwQ : ((χ.1 w : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    rw [hwy, hsplit, map_mul, map_mul, hrest, mul_one, hp, map_prod, map_prod, Units.coe_prod]
    refine prod_mem fun v _ => ?_
    rw [Phi_single]
    refine loc_mem_Qbar χ v (htame v) _ ?_
    show Valued.v (((y v : v.adicCompletionIntegers L) : v.adicCompletion L)) = 1
    exact hwFin v
  have hue : u = infDiag k * w := by rw [hw, mul_inv_cancel_left]
  have hχu : χ.1 u = χ.1 b ^ h := by rw [hu, map_mul, χ.2.2 k, mul_one, map_pow]
  refine mem_Qbar_of_pow hh ?_
  rw [← Units.val_pow_eq_pow_val, ← hχu, hue, map_mul, Units.val_mul]
  exact mul_mem (hinf k) hwQ

end GlobalTheory.TieAlgValues

namespace GlobalTheory.TieAlgValues

open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

def finIdele {L : Type} [Field L] [NumberField L] (z : (FiniteAdeleRing (𝓞 L) L)ˣ) : Ideles L :=
  MulEquiv.prodUnits.symm (1, z)

theorem mt_mem_Qbar : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i < D.R.m,
    ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ) ∈ TaylorLogMetric.Qbar) := by
  intro D _ _ _ _ _ _ _ _ t u μ _ A dtU _ hP _ i hi y
  obtain ⟨x, hx⟩ := hP.q_read.1 (dtU y)
  obtain ⟨ι, hι⟩ := exists_isAdIso t.X.F t.X.E
  set b : Ideles t.X.E := finIdele (Units.map ι.toRingHom.toMonoidHom x) with hbdef
  have hb : IsFinIdele b := fun _ => rfl
  have hbx : ι (x : AfE t.X.F t.X.E) = (b : AdeleRing (𝓞 t.X.E) t.X.E).2 := rfl
  have key : ((D.muTil (i + 1) (A.q x) : ℂˣ) : ℂ) ∈ TaylorLogMetric.Qbar := by
    rw [hP.muTil ι hι ⟨i, hi⟩ b x hb hbx]
    obtain ⟨n, -, hn⟩ := (hP.mu0 ⟨i, hi⟩).inf
    exact fin_mem_Qbar _ (hP.mu0 ⟨i, hi⟩).tame (inf_mem_Qbar hn) b hb
  by_cases hμ : μ = D.what₂.mu0
  · rw [(hP.ref hμ).2, ← hx]
    exact key
  · obtain ⟨ξ, hξ, hmt⟩ := hP.tw μ hμ rfl
    have e : (t.O u μ).mt (i + 1) = D.muTil (i + 1) * ξ := by
      rw [hmt u]
      exact if_pos (⟨by omega, by omega⟩ : 1 ≤ i + 1 ∧ i + 1 ≤ D.R.m)
    rw [e, MonoidHom.mul_apply, Units.val_mul, ← hx]
    refine mul_mem key ?_
    rw [hξ x, Units.coe_map]
    exact emb_mem_Qbar _ _

end GlobalTheory.TieAlgValues
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntriesHypOfColumnSideProperties
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.L2.DIV

namespace GlobalTheory.KerJ.ColSideHyp

theorem plc_dvd_iff' {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    Formalism.EigenvalueLevelCeiling.plc v ∣ n ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  unfold Formalism.EigenvalueLevelCeiling.plc
  rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

theorem g_not_mem_Qp (t : KerEntTied ex) (hC : GlobalTheory.KerJ.ColSide t) (μ : D.what₂.Tup) (k : Fin 2) : D.host.g k ∉ Y.Qp μ := by
  classical
  intro hk
  obtain ⟨hp, P, hPQ, hgP⟩ := (t.Q_rec μ (D.host.g k)).1 hk
  unfold QE at hPQ
  split_ifs at hPQ with h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPQ
    rw [Set.Finite.mem_toFinset] at hv
    have hgood : GoodPl t.X.E t.S v := by
      by_contra hg
      apply hv
      have h2 := (Subgroup.mem_inf.1 (t.tup μ).2).2
      exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 v) hg
    have hvF : ((D.host.g k : ℕ) : 𝓞 t.X.F) ∈ v.asIdeal := by
      rw [← hC.sel v]
      change algebraMap (𝓞 t.X.F) (𝓞 t.X.E) _ ∈ (t.sel v).asIdeal
      rw [map_natCast]
      exact hgP
    have hd := (plc_dvd_iff' v _).2 hvF
    have hpl : Formalism.EigenvalueLevelCeiling.plc v = D.host.g k :=
      ((Nat.dvd_prime hp).1 hd).resolve_left fun e => by
        have h1 := (plc_dvd_iff' v 1).1 (by rw [e])
        rw [Nat.cast_one] at h1
        exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    apply hgood.2.2
    rw [hpl, ← t.g_rec k]
    exact hC.bad.1 k
  · simp at hPQ

end GlobalTheory.KerJ.ColSideHyp

namespace GlobalTheory

theorem colSide_hyp : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.KerJ.ColSide t → t.TopPinned → t.Hyp := by
  intro D L hT Gi Gl K Y cX ex t hC hTop
  obtain ⟨eta, hTied⟩ := hC.chars
  rw [t.glob_σ] at hTied
  refine _root_.GlobalTheory.kerEntTied_hyp D L hT Gi Gl K Y cX ex t (fun j => ⟨_, hTied.mu0 j⟩) (fun j v hv => hTied.muVal j v hv) ?_ hTop
  intro μ k
  exact GlobalTheory.KerJ.ColSideHyp.g_not_mem_Qp t hC μ k

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntryPeriodNeZeroAndLatticeLaws
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TieBase

theorem base_data : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex), t.δ ≠ 0 ∧ t.B.LatAll ∧ t.B.VecP t.χ ∧ t.B.EqP t.χ := by
  intro D L hT Gi Gl Kc Dx cX ex t
  have h0 : t.δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D t.cc t.δ t.B
  refine ⟨h0, t.B.latAll t.cc_ok t.δ_ok h0, ?_, GlobalTheory.Mem.NatEqui.eqP D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok⟩
  exact GlobalTheory.ColNorms.familyVectors D t.cc t.δ t.B t.χ (Formalism.MainNotions.GL3Theta.cm_field_facts_hold D) (Formalism.MainNotions.GL3Theta.induced_cm_type D) t.cc_ok t.δ_ok t.χ_ok
    (GlobalTheory.ExponentsFinite.yFinite D _ t.B.kc)

end GlobalTheory.TieBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeTranslateEqImageClassLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem latK_lev_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m) c (x : UA D i hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), ∀ (κ : ((St i hi).K ((St i hi).chOf c)).lev.U), x.1 = ratA D.host.F γ * ((St i hi).y c).1 * κ.1 → latK D.sp (gramN D i hi) a x.1 ((St i hi).K ((St i hi).chOf c)).lev.Lb = SDLat.smulLat (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) (t.seam.lat ((t.rd u μ).N i c))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ hT' i hi c x γ hγ κ hx
  have hκ : Formalism.MainNotions.G.KAat.HatStab ((St i hi).K ((St i hi).chOf c)).lev.Lb κ.1 := by
    have h1 := (((St i hi).K ((St i hi).chOf c)).lev.U_eq κ.1).1 κ.2
    have h2 := (GlobalTheory.LatticeStabLocal.mem_levelAfL_iff _ _ (sigD D) _ (gramN D i hi) ((St i hi).K ((St i hi).chOf c)).lev.Lb
      ((St i hi).K ((St i hi).chOf c)).lev.Lb_fin κ.1).2 ⟨h1.1, fun v => ((St i hi).K ((St i hi).chOf c)).lev.Uloc_lev v (h1.2 v)⟩
    exact fun z => ((inv_mem h2).2 z).symm
  rw [hx, Formalism.MainNotions.G.KAat.latK_tr _ _ _ _ _ γ hγ hκ, hT'.latK_eq i hi c, ← Submodule.map_comp]
  unfold SDLat.smulLat
  congr 1
  ext v
  simp [Matrix.toLin'_toMatrix']

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumLawTopLevelStabilizerStatement
section
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepDatum_law_topLevelStabilizer : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → Ch.Ok → cst.sharp = true → R.m ≤ cst.A → (∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1) → 2 * cst.M ≤ twTopDepth R → ∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)) (a : FrmG (twLt Ch (m2 + 1 + 1)) (twTt (R := R) sel mu (m2 + 1 + 1))), Y ∈ ybSet sel mu cst p.deco.1.N → a • p' = p' → ∀ x, XiTop Ch sel mu cst (m2 + 1) p Y p' (a.1.1.toLinearMap ∘ₗ x) * ∏ P : rowSG Pr sel mu, muAt Ch sel mu cst (m2 + 1) P ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) = (((twLt Ch (m2 + 1 + 1)).chr a.2.1 * (twTt (R := R) sel mu (m2 + 1 + 1)).chr a.2.2 : X.Kˣ) : X.K) * XiTop Ch sel mu cst (m2 + 1) p Y p' x := by
  first | exact @GlobalTheory.StabTopLaw.xiTop_stab_law | exact GlobalTheory.StabTopLaw.xiTop_stab_law | (intros; apply GlobalTheory.StabTopLaw.xiTop_stab_law <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatAdXMulLev
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hatStab_of_lev {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (κ : S.U) : HatStab S.Lb κ.1 := by
  have h := (S.U_eq κ.1).1 κ.2
  have hk : κ.1 ∈ levelAfL σ J S.Lb :=
    (GlobalTheory.LatticeStabLocal.mem_levelAfL_iff F E σ n J S.Lb S.Lb_fin κ.1).2 ⟨h.1, fun v => S.Uloc_lev v (h.2 v)⟩
  exact fun z => ((inv_mem hk).2 z).symm

theorem latAdX_mul_lev {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : Formalism.L2.Ker.KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ} (A : AdData t u μ St) (a : 𝓞 D.host.E) (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : ((St i hi).K β).lev.U) :
    latAdX A a i hi β (x * κ.1) = latAdX A a i hi β x := by
  unfold latAdX latCo
  rw [latAd_stab x κ.1 _ (hatStab_of_lev _ κ)]

end GlobalTheory.TwU
end
end

