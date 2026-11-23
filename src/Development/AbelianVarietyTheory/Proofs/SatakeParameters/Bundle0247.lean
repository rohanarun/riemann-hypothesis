module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionUnfolded
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SharpPoly
public import Formalism.LocalToGlobal.InertKernelTheory.K2OfAgreements
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0269
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0241
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormsSharpAtOfValTied
section
noncomputable section

namespace GlobalTheory.FormsSharpTie

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.KerInert.K2

theorem natW_antitone {n : ℕ} (l : DomWeight n) : Antitone l.natW := by
  intro a b h
  simp only [DomWeight.natW]
  exact Int.toNat_le_toNat (by have := l.anti h; omega)

theorem ratSpan_le_wtPol (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) :
    ∀ P ∈ RatSpan D lam, P ∈ WtPol ℂ (fun τ r => (lam τ).natW r) := by
  intro P hP
  have hle : RatSpan D lam ≤ (WtPol ℂ (fun τ r => (lam τ).natW r)).toAddSubgroup := by
    unfold RatSpan
    rw [AddSubgroup.closure_le]
    rintro p ⟨r, f, hf, rfl⟩
    show _ ∈ WtPol ℂ _
    apply Submodule.smul_mem
    apply GlobalTheory.KerWt.VV_le_WtPol lam
    unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
    apply Submodule.subset_span
    refine ⟨fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ), fun τ => ?_, rfl⟩
    have h1 : MvPolynomial.map (Int.castRingHom ℂ) (f τ) ∈ delSq ℂ n (lam τ) := by
      rw [← GlobalTheory.Published.span_map_delSq ℤ ℂ (Int.castRingHom ℂ) n (lam τ)]
      exact Submodule.subset_span ⟨f τ, hf τ, rfl⟩
    exact Formalism.GradedWeylDivisibility.weylLeDual ℂ n n le_rfl _ (natW_antitone (lam τ)) h1
  exact hle hP

theorem eval_colSub {ι : Type} [Fintype ι] {a : ℕ} (β x : ι → Matrix (Fin a) (Fin a) ℂ) (p : Formalism.L2.DIV.Pol ℂ ι a) :
    MvPolynomial.eval (fun k : ι × Fin a × Fin a => x k.1 k.2.1 k.2.2) (colSub β p) =
      MvPolynomial.eval (fun k : ι × Fin a × Fin a => (x k.1 * β k.1) k.2.1 k.2.2) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [colSub]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, colSub, MvPolynomial.aeval_X, MvPolynomial.eval_X, Matrix.mul_apply]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [mul_comm]

theorem zpow_mul_pow_toNat {x : ℂ} (hx : x ≠ 0) (s : ℤ) : x ^ s * x ^ (-s).toNat = x ^ s.toNat := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hx]
  congr 1
  omega

theorem isVLam_of_wtPol {ι : Type} [Fintype ι] {a : ℕ} {Y : Type} (fr g : Y → ι → Matrix (Fin a) (Fin a) ℂ)
    (B : ι → Matrix (Fin a) (Fin a) ℂ) (hB : ∀ τ, (B τ).det ≠ 0) (hg : ∀ y τ, (g y τ).det ≠ 0)
    (hfr : ∀ y τ, fr y τ = B τ * g y τ) (ν : ι → Fin a → ℕ) (s : ι → ℤ) (P : Formalism.L2.DIV.Pol ℂ ι a)
    (hP : P ∈ WtPol ℂ ν) :
    IsVLam fr (fun τ r => (ν τ r : ℤ) + s τ)
      (fun y => (∏ τ, (g y τ).det ^ s τ) * MvPolynomial.eval (fun x : ι × Fin a × Fin a => g y x.1 x.2.1 x.2.2) P) := by
  have hBu : ∀ τ, IsUnit (B τ).det := fun τ => isUnit_iff_ne_zero.2 (hB τ)
  have hg' : ∀ y τ, g y τ = (B τ)⁻¹ * fr y τ := by
    intro y τ
    rw [hfr, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hBu τ), Matrix.one_mul]
  refine ⟨?_, ?_⟩
  ·
    let sub : Formalism.L2.DIV.Pol ℂ ι a →ₐ[ℂ] Formalism.L2.DIV.Pol ℂ ι a :=
      MvPolynomial.aeval fun v => ∑ c, MvPolynomial.C ((B v.1)⁻¹ v.2.1 c) * MvPolynomial.X (v.1, c, v.2.2)
    have hsub : ∀ y (p : Formalism.L2.DIV.Pol ℂ ι a), MvPolynomial.eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) (sub p) =
        MvPolynomial.eval (fun k : ι × Fin a × Fin a => g y k.1 k.2.1 k.2.2) p := by
      intro y p
      induction p using MvPolynomial.induction_on with
      | C c => simp [sub]
      | add p q hp hq => simp only [map_add (f := _), hp, hq]
      | mul_X p v hp =>
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_mul, hp, sub, MvPolynomial.aeval_X, MvPolynomial.eval_X, hg', Matrix.mul_apply, map_sum]
        simp
    have hdet : ∀ y τ, MvPolynomial.eval (fun k : ι × Fin a × Fin a => g y k.1 k.2.1 k.2.2) (frDet ℂ a τ) = (g y τ).det := by
      intro y τ
      unfold frDet
      rw [RingHom.map_det]
      congr 1
      ext i k
      simp
    refine ⟨MvPolynomial.C (∏ τ, (B τ).det ^ (-s τ).toNat) * (∏ τ, sub (frDet ℂ a τ) ^ (s τ).toNat) * sub P,
      fun τ => (-s τ).toNat, fun y => ?_⟩
    simp only [frPolyG, LinearMap.coe_mk, AddHom.coe_mk, map_mul, map_prod, map_pow, MvPolynomial.eval_C, hsub, hdet]
    have e2 : ∀ τ, (g y τ).det ^ s τ * (g y τ).det ^ (-s τ).toNat = (g y τ).det ^ (s τ).toNat :=
      fun τ => zpow_mul_pow_toNat (hg y τ) (s τ)
    simp only [hfr, Matrix.det_mul, mul_pow, Finset.prod_mul_distrib]
    rw [← Finset.prod_congr rfl fun τ _ => e2 τ, Finset.prod_mul_distrib]
    ring
  ·
    intro y y₂ β hβ hy
    have hgy : ∀ τ, g y₂ τ = g y τ * β τ := by
      intro τ
      have h := hy τ
      rw [hfr, hfr, Matrix.mul_assoc] at h
      have h2 := congrArg (fun M => (B τ)⁻¹ * M) h
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hBu τ), Matrix.one_mul] at h2
      exact h2
    have hdβ : ∀ τ, (β τ).det = ∏ r, β τ r r := fun τ =>
      Matrix.det_of_upperTriangular (fun r s h => (hβ τ).1 r s h)
    have hev : MvPolynomial.eval (fun x : ι × Fin a × Fin a => g y₂ x.1 x.2.1 x.2.2) P =
        (∏ τ, ∏ r, β τ r r ^ ν τ r) * MvPolynomial.eval (fun x : ι × Fin a × Fin a => g y x.1 x.2.1 x.2.2) P := by
      have := eval_colSub β (g y) P
      rw [hP β hβ, MvPolynomial.smul_eval] at this
      simp only [hgy]
      rw [← this]
    have hne : ∀ τ r, β τ r r ≠ 0 := fun τ r => (hβ τ).2 r
    have e3 : ∀ τ r, β τ r r ^ ((ν τ r : ℤ) + s τ) = β τ r r ^ ν τ r * β τ r r ^ s τ := by
      intro τ r
      rw [zpow_add₀ (hne τ r), zpow_natCast]
    dsimp only
    rw [hev]
    simp only [hgy, Matrix.det_mul, hdβ, mul_zpow, e3, Finset.prod_mul_distrib, ← Finset.prod_zpow]
    ring


open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset in
theorem sharpWt_rat (D : D7) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) (hj : j < D.R.m)
    (τ : D.what₂.Tau) (r : Fin (D.R.N j)) :
    ((((nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ : ℤ)) : ℚ) =
        ((((Tw.fm u μ).lam j τ).w r : ℤ) : ℚ) - (j : ℚ) * ((D.R.t : ℚ) + 1) / 2 := by
  have h1 := (GlobalTheory.KerWt.nu_t_identity D u j hj τ r).1
  have h2 := (D.chTw u μ).sSharp_eq j hj τ
  have h3 := (Tw.fm u μ).lam_eq j hj.le τ r
  have h2' : (((D.chTw u μ).sSharp j τ : ℤ) : ℝ) =
      (((D.hcW u τ).e ⟨j, hj⟩ : ℚ) : ℝ) - ((D.R.k : ℝ) + ((j : ℝ) + 1) * ((D.R.t : ℝ) + 1)) / 2 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h2
    simp only [sExp', Ranks.N] at this
    push_cast at this
    exact this
  have he : ∀ (k : ℕ) (hk : k < D.R.m), k = j → (D.hc τ).e ⟨k, hk⟩ = (D.hcW u τ).e ⟨j, hj⟩ := by
    rintro k hk rfl; rw [D.hcW_e]
  apply Rat.cast_injective (α := ℝ)
  have hw : ((((Tw.fm u μ).lam j τ).w r : ℤ) : ℝ) = (((((Tw.fm u μ).lam j τ).w r : ℤ) : ℚ) : ℝ) := by push_cast; rfl
  push_cast
  rw [h1, h2', hw, h3]
  unfold DV.nuRow DV.srcPar DV.wSz
  rw [dif_pos (show 1 ≤ j + 1 ∧ j + 1 ≤ D.R.m by omega), he _ _ (by omega)]
  simp only [Ranks.N]
  by_cases hr : r.1 < D.R.k
  · rw [dif_pos hr, dif_pos hr]
    simp only [hcToWeightQ, rhoVec]
    push_cast
    ring
  · have hb : (r.1 - D.R.k) / (D.R.t + 1) < D.R.m := by
      have := D.R.blk_lt hj.le r hr
      omega
    rw [dite_eq_right hr, dite_eq_right hr, dif_pos hb]
    have hdm := Nat.div_add_mod (r.1 - D.R.k) (D.R.t + 1)
    have hrk : (r.1 : ℝ) = D.R.k + (D.R.t + 1) * (((r.1 - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) + (((r.1 - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
      have : r.1 = D.R.k + (D.R.t + 1) * ((r.1 - D.R.k) / (D.R.t + 1)) + (r.1 - D.R.k) % (D.R.t + 1) := by omega
      exact_mod_cast this
    simp only [wG]
    push_cast
    rw [hrk]
    ring

theorem nuT_sub_sSharp (D : D7) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) (hj : j < D.R.m)
    (τ : D.what₂.Tau) (r : Fin (D.R.N j)) :
    (nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ = (lamTG (Tw.fm u μ) j τ).w r := by
  have h := sharpWt_rat D Tw u μ j hj τ r
  set z : ℤ := (nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ with hz
  set w : ℤ := ((Tw.fm u μ).lam j τ).w r with hw
  show z = ((Tw.fm u μ).lam j τ).w r - ((j * (D.R.t + 1) / 2 : ℕ) : ℤ)
  rw [← hw]
  generalize hn : j * (D.R.t + 1) = n
  have h2 : (2 * (w - z) : ℚ) = (n : ℚ) := by
    rw [← hn]; push_cast; rw [h]; ring
  have h3 : 2 * (w - z) = (n : ℤ) := by exact_mod_cast h2
  omega

theorem natW_add_shift {N : ℕ} (l : DomWeight N) (c : ℤ) (r : Fin N) :
    ((l.natW r : ℕ) : ℤ) + (shW l c).detShift = (shW l c).w r := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) r.2
  have hle : l.w ⟨N - 1, by omega⟩ ≤ l.w r := l.anti (show r ≤ ⟨N - 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
  simp only [DomWeight.natW, DomWeight.detShift, shW, dif_pos hN]
  rw [Int.toNat_of_nonneg (by omega)]
  ring

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}

theorem formsSharpAt_of_valTied (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) (hj : j < D.R.m)
    {T : ℕ} {bad : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F))}
    {eY : (D.chTw u μ).Y j ≃ Fr D j hj.le} {okW : D.what₂.places.Pl → Prop} {Ch : Type} {chOf : (D.chTw u μ).cls j → Ch}
    {lat : (D.chTw u μ).cls j → Submodule (NumberField.RingOfIntegers D.host.E) (Fin (D.R.N j) → D.host.E)}
    {K : ∀ β : Ch, LevelChart D T bad j hj.le (fun c : {c // chOf c = β} => (D.chTw u μ).stab j c.1) (fun c => lat c.1)}
    (hV : ValuationCompatibleChart (ex.tw.fm u μ) eY okW chOf K) (crd : GL (Fin (D.R.N j)) D.host.E)
    (hfrm : ∀ y τ, (t.O u μ).frm j y τ = atInf (embT D) crd.1 τ * (eY y).1 τ) :
    ∀ x, ∃ Q, SharpQ t ex.tw u μ j x Q := by
  intro x
  have hx := (hV.rat ((ex.tw.fm u μ).emb j x)).1 ⟨x, rfl⟩
  choose P hP hE using hx.2
  have hB : ∀ τ, (atInf (embT D) crd.1 τ).det ≠ 0 := by
    intro τ
    show ((crd : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ)).det ≠ 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 (Matrix.isUnits_det_units crd).ne_zero
  have hg : ∀ y τ, ((eY y).1 τ).det ≠ 0 := fun y τ => ((eY y).2 τ).ne_zero
  have key : ∀ c, IsVLam ((t.O u μ).frm j) (fun τ r => (nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ)
      ((ex.tw.fm u μ).emb j x c) := by
    intro c
    have h1 := isVLam_of_wtPol ((t.O u μ).frm j) (fun y => (eY y).1) (fun τ => atInf (embT D) crd.1 τ) hB hg hfrm
      (fun τ r => ((ex.tw.fm u μ).lam j τ).natW r) (shiftOf (lamTG (ex.tw.fm u μ) j)) (P c)
      (ratSpan_le_wtPol D _ (P c) (hP c))
    have hw : (fun τ r => (nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ) =
        (fun τ r => ((((ex.tw.fm u μ).lam j τ).natW r : ℕ) : ℤ) + shiftOf (lamTG (ex.tw.fm u μ) j) τ) := by
      funext τ r
      rw [nuT_sub_sSharp D ex.tw u μ j hj τ r]
      exact (natW_add_shift _ _ r).symm
    have hf : (ex.tw.fm u μ).emb j x c = fun y => (∏ τ, ((eY y).1 τ).det ^ shiftOf (lamTG (ex.tw.fm u μ) j) τ) *
        MvPolynomial.eval (fun k : D.what₂.Tau × Fin (D.R.N j) × Fin (D.R.N j) => (eY y).1 k.1 k.2.1 k.2.2) (P c) := by
      funext y
      rw [hE c y]
      simp [fnOf]
    rw [hw, hf]
    exact h1
  have := fun c => forms_sharp_description Formalism.L2.KerInert.SharpPolyP.sharp_polynomial_frames D u (D.chTw u μ) (t.O u μ) j hj.le
    (nuT D u j) _ (key c)
  choose Q hQ hQE using this
  exact ⟨Q, hQ, hQE⟩


attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem formsSharpAt_of_pins (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : GlobalTheory.TwU.ChainCharts D u μ)
    (A : GlobalTheory.TwU.AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (hP : GlobalTheory.TwU.AdPins A dtU)
    (okW : ℕ → D.what₂.places.Pl → Prop)
    (hV : ∀ j (hj : j < D.R.m), ValuationCompatibleChart (ex.tw.fm u μ) (St j hj.le).eY (okW j) (St j hj.le).chOf (St j hj.le).K) :
    ∀ j, j < D.R.m → ∀ x, ∃ Q, SharpQ t ex.tw u μ j x Q :=
  fun j hj => formsSharpAt_of_valTied t u μ j hj (hV j hj) (A.crd j hj.le) (hP.frm j hj.le)

end GlobalTheory.FormsSharpTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfComponentZeroUnderPrime
section
open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Col
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.VanishAwayInt

theorem exists_away {F : Type} [Field F] [NumberField F] (p : Ideal (𝓞 F)) [hp : p.IsPrime] (N : 𝓞 F) (hN : N ≠ 0) :
    ∃ t : 𝓞 F, t ∉ p ∧ ∀ w : HeightOneSpectrum (𝓞 F), w.asIdeal ≠ p →
      ∃ c y : 𝓞 F, y ∉ w.asIdeal ∧ y * t = N * c := by
  classical
  have hI : Ideal.span {N} ≠ ⊥ := by simpa using hN
  have hpu : ¬ IsUnit p := by
    rw [Ideal.isUnit_iff]; exact hp.ne_top
  obtain ⟨b, hb, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hpu hI).exists_eq_pow_mul_and_not_dvd
  have hbp : ¬ b ≤ p := fun h => hnd (Ideal.dvd_iff_le.2 h)
  obtain ⟨t, htb, htp⟩ := SetLike.not_le_iff_exists.1 hbp
  refine ⟨t, htp, fun w hw => ?_⟩
  have hpw : ¬ p ^ multiplicity p (Ideal.span {N}) ≤ w.asIdeal := by
    intro h
    rcases Nat.eq_zero_or_pos (multiplicity p (Ideal.span {N})) with h0 | hm
    · rw [h0, pow_zero, Ideal.one_eq_top, top_le_iff] at h
      exact w.isPrime.ne_top h
    · have hle : p ≤ w.asIdeal := w.isPrime.le_of_pow_le h
      have hpb : p ≠ ⊥ := by
        intro h'
        apply hI
        rw [eq_bot_iff]
        calc Ideal.span {N} = p ^ multiplicity p (Ideal.span {N}) * b := hb
          _ ≤ p ^ multiplicity p (Ideal.span {N}) := Ideal.mul_le_left
          _ ≤ p := Ideal.pow_le_self hm.ne'
          _ = ⊥ := h'
      have hmax : p.IsMaximal := hp.isMaximal hpb
      exact hw (hmax.eq_of_le w.isPrime.ne_top hle).symm
  obtain ⟨y, hy, hyw⟩ := SetLike.not_le_iff_exists.1 hpw
  have hyt : y * t ∈ Ideal.span {N} := by
    rw [hb]; exact Ideal.mul_mem_mul hy htb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hyt
  exact ⟨c, y, hyw, by rw [← hc, mul_comm]⟩

theorem intAtA_of_prV_eq_zero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    (∀ v : HeightOneSpectrum (𝓞 F), IsOver v P → prV (E := E) v z = 0) → IntAtA (F := F) P z := by
  intro F E _ _ _ _ _ P z hz
  obtain ⟨m, hm, hmz⟩ := GlobalTheory.St.G.IntAd.exists_nat_denom (F := F) (E := E) z
  haveI : (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).IsPrime := Ideal.comap_isPrime _ _
  have hm0 : (m : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  obtain ⟨t, htp, ht⟩ := exists_away (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))) (m : 𝓞 F) hm0
  refine ⟨algebraMap (𝓞 F) (𝓞 E) t, htp, ?_⟩
  have key : iA F E (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t)) =
      algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F t) := rfl
  apply GlobalTheory.St.G.IntAd.mem_of_local
  intro w
  by_cases hw : w.asIdeal = P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
  · rw [map_mul, hz w hw, mul_zero]; exact zero_mem _
  · obtain ⟨c, y, hyw, hyc⟩ := ht w hw
    have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have hy0 : algebraMap (𝓞 F) F y ≠ 0 := by
      intro h0
      apply hyw
      rw [(FaithfulSMul.algebraMap_eq_zero_iff (𝓞 F) F).1 h0]
      exact zero_mem _
    set q : F := algebraMap (𝓞 F) F t / (m : F) with hqdef
    have e : iA F E (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t)) * z =
        algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F) q * ((m : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * z) := by
      rw [key, ← mul_assoc, ← map_natCast (algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) m, ← map_mul, hqdef,
        div_mul_cancel₀ _ hmF]
    rw [e, map_mul]
    refine mul_mem ?_ (Formalism.UG.P.afsplit_prV_int w _ hmz)
    have hc : prV (E := E) w (algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F) q) =
        algebraMap F (E ⊗[F] w.adicCompletion F) q :=
      (Algebra.TensorProduct.map (AlgHom.id F E) (evalV F w)).commutes q
    rw [hc, Algebra.TensorProduct.algebraMap_apply']
    have hq' : q = algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F y := by
      rw [hqdef, div_eq_div_iff hmF hy0]
      have := congrArg (algebraMap (𝓞 F) F) hyc
      rw [map_mul, map_mul, map_natCast] at this
      linear_combination this
    have hq : algebraMap F (w.adicCompletion F) q ∈ w.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w q]
      rw [hq', map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
      have hy1 : w.intValuation y = 1 :=
        le_antisymm (w.intValuation_le_one y) (not_lt.1 fun h => hyw ((w.intValuation_lt_one_iff_mem y).1 h))
      rw [hy1, div_one]
      exact w.intValuation_le_one c
    exact Subring.subset_closure (Or.inr ⟨⟨_, hq⟩, rfl⟩)

end GlobalTheory.VanishAwayInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOverVUnder
section
noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section MidDatum

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  (A : AdData t u μ St) (a : 𝓞 D.host.E)

def mvN (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N i)) :=
  Submodule.span (𝓞 t.X.E) ((fun (y : Fin (D.R.N i) → D.host.E) (l : Fin (D.R.N i)) => t.seam.iE.symm (y l)) ''
    (latCo D.sp (gramN D i hi) (A.crd i hi) a x.1 ((St i hi).K β).lev.Lb : Set (Fin (D.R.N i) → D.host.E)))

def vUnder (P : HeightOneSpectrum (𝓞 t.X.E)) : HeightOneSpectrum (𝓞 D.host.F) :=
  HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P)

theorem isOver_vUnder (P : HeightOneSpectrum (𝓞 t.X.E)) : IsOver (vUnder (t := t) P) (seamP t.seam P) := by
  unfold IsOver vUnder
  rw [HeightOneSpectrum.under_asIdeal]

def vecAt {n : ℕ} (g : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (w : Sp t.X.E n) : Fin n → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F :=
  fun l => prV (E := D.host.E) v (pullV (F := D.host.F) g (fun b => t.seam.iE (w b)) l)

def iotaSel (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) : ((St i hi).K β).lev.fM v h →+ 𝓞 t.X.E ⧸ P.1.asIdeal := by
  classical
  exact if hι : ∃ ι : ((St i hi).K β).lev.fM v h →+ 𝓞 t.X.E ⧸ P.1.asIdeal,
      ∀ c, (St i hi).chOf c = β → FunMoved t.seam ((St i hi).K β).lev P v h ι (A.mov i hi c) (A.pt i hi c).deco.1
    then hι.choose else 0

def InDom (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (P : t.Pr.vT (t.word u)) (w : Sp t.X.E (D.R.N i)) : Prop :=
  vecAt (t := t) (ratA D.host.F (A.crd i hi) * x.1) (vUnder (t := t) P.1) w ∈
    latS (F := D.host.F) ((vUnder (t := t) P.1).adicCompletion D.host.F) (intV D.host.E (vUnder (t := t) P.1))
      (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) ((St i hi).K β).lev.Lb))

def mvG (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (P : t.Pr.vT (t.word u)) (w : Sp t.X.E (D.R.N i)) :
    𝓞 t.X.E ⧸ P.1.asIdeal := by
  classical
  exact if h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ (vUnder (t := t) P.1).asIdeal then
    (if hz : InDom A i hi β x P w then
      iotaSel A i hi β P (vUnder (t := t) P.1) h (((St i hi).K β).lev.fT (vUnder (t := t) P.1) h ⟨_, hz⟩) else 0)
    else 0

end MidDatum

end GlobalTheory.TwU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntriesHypOfHeckeCharacterConditions
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory

theorem hypFree_of_top_int : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.TopPinned → t.TopInt → t.HypFree := by
  intro D L hT Gi Gl K Y cX ex t hTop hInt u μ i hi c c' hnp
  have hsd := (GlobalTheory.TieLat.tie_AA_fg_and_sd D L hT Gi Gl K Y cX ex t).2 u μ
  refine ⟨hsd i c, hsd (i + 1) c', ?_⟩
  have hm : D.R.m = t.m2 + 2 := (t.idx_ok μ).hm
  obtain ⟨-, -, pt, ix, yb, pT, -, -, -, -, -, hpin, -⟩ := hTop u μ
  have hi' : i = t.m2 + 1 := by
    by_contra hne
    exact hnp (hpin (i + 1) (by omega) c')
  subst hi'
  exact hInt u μ c c' hnp

theorem kerEntTied_hyp : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → (∀ μ k, D.host.g k ∉ Y.Qp μ) → t.TopPinned → t.Hyp := by
  intro D L hT Gi Gl K Y cX ex t h1 h2 hQ hTop
  have h0 : t.Hyp0 := by
    first
      | exact _root_.GlobalTheory.kernel_datum_of_hecke_character_values D L hT Gi Gl K Y cX ex t h1 h2 hQ
      | exact _root_.GlobalTheory.kernel_datum_of_hecke_character_values D L hT Gi Gl K Y cX ex t h1 h2
  exact hypotheses_of_base_hypotheses D L hT Gi Gl K Y cX ex t h0
    (hypFree_of_top_int D L hT Gi Gl K Y cX ex t hTop (_root_.GlobalTheory.TopInt.topInt D L hT Gi Gl K Y cX ex t hTop))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalArtinCompNormCompatStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localArtin_comp_norm_compat : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') [v'.asIdeal.LiesOver v.asIdeal] (a : Weil h →* (v.adicCompletion K)ˣ) (a' : Weil h' →* (v'.adicCompletion L)ˣ), IsLocalArtin h a → IsLocalArtin h' a' → ∀ (g : Weil h) (g' : Weil h'), (∀ z : Ω, (g : G K Ω) z = (g' : G L Ω) z) → a g = GlobalTheory.BCChar.normU v v' (a' g') := by
  first | (exact @GlobalTheory.ArtinNormU.localArtin_normU) | (exact GlobalTheory.ArtinNormU.localArtin_normU) | (intros; apply GlobalTheory.ArtinNormU.localArtin_normU  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SameOffOfIsPt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

namespace GlobalTheory.TwV.Xc

theorem sameOff_of_isPt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) :
    LocGood σ J A → ∀ (i : G.comp) (g g' : (∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))) (x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F)), A.IsPt i g x.1 → A.IsPt i g' x'.1 → ∀ v, (∀ v', v' ≠ v → g v' = g' v') → SameOff (A.pl v).1 x.1 x'.1 := by
  intro H i g g' x x' hx hx' v hg w hw
  by_cases hp : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
  · obtain ⟨v', rfl⟩ := LocGood.exists_pl A w hp
    have hv : v' ≠ v := fun h => hw (h ▸ rfl)
    have h1 := hx.2 v'
    have h2 := hx'.2 v'
    rw [hg v' hv] at h1
    have hmem : bc (prV (E := E) (A.pl v').1) ((x.1)⁻¹ * x'.1) ∈ UPts σ J ((A.pl v').1.adicCompletion F) :=
      Formalism.UG.P.afsplit_bc_mem σ J (A.pl v').1 _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ x.2) x'.2)
    have h3 := LocGood.eq_one_of_ph H v' _ hmem (by rw [map_mul, map_mul, map_inv, map_inv, h1, h2]; exact inv_mul_cancel _)
    rw [map_mul, map_inv] at h3
    exact (inv_mul_eq_one.1 h3)
  · rw [hx.1 w hp, hx'.1 w hp]

end GlobalTheory.TwV.Xc
end

