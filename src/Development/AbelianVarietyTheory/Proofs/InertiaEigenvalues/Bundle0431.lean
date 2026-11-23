module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0407
public import Development.AutomorphicArithmetic.CyclotomicBounds.CyclotomicOrders.ExistsCycZPowNeOne
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.PolarTraceMulVecMulVecEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0406
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0409
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUniformizerPowEqMulUnit
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
noncomputable section

namespace GlobalTheory.TiltDiv

variable {l : ℕ} [Fact l.Prime]

theorem norm_OC_le_one (x : Per.OC l) : ‖(x : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 x.2

theorem mk_untilt_iterate (x : OCb l) (n : ℕ) :
    Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)})
      (PreTilt.untilt ((frobeniusEquiv (OCb l) l).symm^[n] x)) = PreTilt.coeff n x := by
  rw [PreTilt.mk_untilt_eq_coeff_zero, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add]

theorem untilt_zero : PreTilt.untilt (0 : OCb l) = 0 := Perfection.teichmuller_zero

theorem untilt_eq_zero_iff {x : OCb l} : PreTilt.untilt x = 0 ↔ x = 0 := by
  refine ⟨fun h => Perfection.ext fun n => ?_, fun h => h ▸ untilt_zero⟩
  have h1 := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n
  rw [h, pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at h1
  change PreTilt.coeff n x = PreTilt.coeff n 0
  rw [← mk_untilt_iterate, h1, map_zero, map_zero]

def ofCompatible (y : ℕ → Per.OC l) (hy : ∀ n, y (n + 1) ^ l = y n) : OCb l :=
  (⟨fun n => Ideal.Quotient.mk _ (y n), fun n => by rw [← map_pow, hy]⟩ :
    Perfection (ModP (Per.OC l) l) l)

theorem dvd_of_norm_untilt_le {a b : OCb l} (hb : b ≠ 0)
    (h : ‖((PreTilt.untilt a : Per.OC l) : ℂ_[l])‖ ≤ ‖((PreTilt.untilt b : Per.OC l) : ℂ_[l])‖) :
    b ∣ a := by
  set φ := (frobeniusEquiv (OCb l) l).symm
  have hnorm : ∀ (x : OCb l) (n : ℕ), ‖((PreTilt.untilt (φ^[n] x) : Per.OC l) : ℂ_[l])‖ ^ l ^ n =
      ‖((PreTilt.untilt x : Per.OC l) : ℂ_[l])‖ := by
    intro x n
    rw [← norm_pow, ← SubmonoidClass.coe_pow, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow]
  have hbn : ∀ n, ((PreTilt.untilt (φ^[n] b) : Per.OC l) : ℂ_[l]) ≠ 0 := by
    intro n h0
    apply hb
    have h0' : PreTilt.untilt (φ^[n] b) = 0 := Subtype.ext h0
    rw [← untilt_eq_zero_iff, ← PreTilt.untilt_iterate_frobeniusEquiv_symm_pow b n, h0',
      zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]
  have hle : ∀ n,
      ‖((PreTilt.untilt (φ^[n] a) : Per.OC l) : ℂ_[l])‖ ≤ ‖((PreTilt.untilt (φ^[n] b) : Per.OC l) : ℂ_[l])‖ := by
    intro n
    have hpn : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hpn, hnorm, hnorm]
    exact h
  have hstep : ∀ (x : OCb l) (n : ℕ), PreTilt.untilt (φ^[n + 1] x) ^ l = PreTilt.untilt (φ^[n] x) := by
    intro x n
    rw [Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]
  let y : ℕ → Per.OC l := fun n =>
    ⟨((PreTilt.untilt (φ^[n] a) : Per.OC l) : ℂ_[l]) / PreTilt.untilt (φ^[n] b), (GlobalTheory.RingBasics.mem_OC _).2 (by
      rw [norm_div]; exact div_le_one_of_le₀ (hle n) (norm_nonneg _))⟩
  have hy : ∀ n, y (n + 1) ^ l = y n := by
    intro n
    ext
    simp only [y, SubmonoidClass.coe_pow, div_pow]
    rw [← SubmonoidClass.coe_pow, ← SubmonoidClass.coe_pow, hstep, hstep]
  refine ⟨ofCompatible y hy, Perfection.ext fun n => ?_⟩
  change PreTilt.coeff n a = PreTilt.coeff n (b * ofCompatible y hy)
  rw [map_mul]
  change _ = _ * Ideal.Quotient.mk _ (y n)
  rw [← mk_untilt_iterate, ← mk_untilt_iterate, ← map_mul]
  congr 1
  ext
  rw [MulMemClass.coe_mul]
  change _ = _ * (_ / _)
  rw [mul_div_cancel₀ _ (hbn n)]

end GlobalTheory.TiltDiv

end

noncomputable section

namespace GlobalTheory.TiltDiv

variable {l : ℕ} [Fact l.Prime]

theorem norm_pow_natDegree_eq_of_eisenstein {R : Type*} [CommRing R] (P : Polynomial R) (hm : P.Monic)
    (hpos : 0 < P.natDegree) (hdvd : ∀ i < P.natDegree, ((l : ℕ) : R) ∣ P.coeff i)
    (w : Rˣ) (h0 : P.coeff 0 = ((l : ℕ) : R) * w) (Ψ : R →+* ℂ_[l]) (hΨ : ∀ y, ‖Ψ y‖ ≤ 1)
    (z : ℂ_[l]) (hz1 : ‖z‖ ≤ 1) (hz : P.eval₂ Ψ z = 0) :
    ‖z ^ P.natDegree‖ = ‖((l : ℕ) : ℂ_[l])‖ := by
  obtain ⟨m, hm'⟩ : ∃ m, P.natDegree = m + 1 := ⟨P.natDegree - 1, by omega⟩
  have hl0 : 0 < ‖((l : ℕ) : ℂ_[l])‖ :=
    norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hl1 : ‖((l : ℕ) : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hc : ∀ i < P.natDegree, ‖Ψ (P.coeff i)‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ := by
    intro i hi
    obtain ⟨y, hy⟩ := hdvd i hi
    rw [hy, map_mul, map_natCast, norm_mul]
    calc _ ≤ ‖((l : ℕ) : ℂ_[l])‖ * 1 := by gcongr; exact hΨ y
      _ = _ := mul_one _
  have hw : ‖Ψ w‖ = 1 := by
    have h1 : Ψ w * Ψ ↑w⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have ha := hΨ w
    have hb := hΨ ↑w⁻¹
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    nlinarith [norm_nonneg (Ψ w), norm_nonneg (Ψ ↑w⁻¹)]
  have hc0 : ‖Ψ (P.coeff 0)‖ = ‖((l : ℕ) : ℂ_[l])‖ := by
    rw [h0, map_mul, map_natCast, norm_mul, hw, mul_one]
  have htop : P.coeff (m + 1) = 1 := by rw [← hm']; exact hm.coeff_natDegree
  rw [Polynomial.eval₂_eq_sum_range, hm', Finset.sum_range_succ, Finset.sum_range_succ', htop,
    map_one, one_mul, pow_zero, mul_one] at hz
  set S := ∑ i ∈ Finset.range m, Ψ (P.coeff (i + 1)) * z ^ (i + 1) with hSdef
  have hS : ‖S‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ * ‖z‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' : i + 1 < P.natDegree := by rw [hm']; simpa using Finset.mem_range.1 hi
    have hp : ‖z‖ ^ (i + 1) ≤ ‖z‖ := pow_le_of_le_one (norm_nonneg _) hz1 (by omega)
    exact mul_le_mul (hc _ hi') hp (by positivity) (norm_nonneg _)
  have hzpow : z ^ (m + 1) = -(Ψ (P.coeff 0) + S) := by linear_combination hz
  have hSl : ‖S‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ := hS.trans (by nlinarith [norm_nonneg z])
  have hup : ‖z ^ (m + 1)‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ := by
    rw [hzpow, norm_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hc0.le hSl)
  have hzlt : ‖z‖ < 1 := by
    by_contra hge
    push_neg at hge
    have : 1 ≤ ‖z‖ ^ (m + 1) := one_le_pow₀ hge
    rw [norm_pow] at hup
    linarith
  have hSlt : ‖S‖ < ‖((l : ℕ) : ℂ_[l])‖ := hS.trans_lt (by nlinarith [norm_nonneg z])
  have hlow : ‖((l : ℕ) : ℂ_[l])‖ ≤ ‖z ^ (m + 1)‖ := by
    have h3 : Ψ (P.coeff 0) = -(z ^ (m + 1) + S) := by linear_combination hz
    have h4 := IsUltrametricDist.norm_add_le_max (z ^ (m + 1)) S
    rw [← norm_neg (z ^ (m + 1) + S), ← h3, hc0] at h4
    rcases le_max_iff.1 h4 with h5 | h5
    · exact h5
    · linarith
  rw [hm']
  exact le_antisymm hup hlow

end GlobalTheory.TiltDiv

end

noncomputable section

namespace GlobalTheory.TiltDiv

theorem flat_pow_natDegree_eq_mul_unit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ϖ : OCb l),
    ϖ.untilt = ((l : ℕ) : Per.OC l) →
    ∃ x : OCb l, IsUnit x ∧ bk.flat ^ bk.Ep.natDegree = ϖ * x := by
  intro l _ K bk ϖ hϖ
  set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ X) with hr
  have h1 : bk.flat.untilt = intToOC K r := by
    rw [← WittVector.fontaineTheta_teichmuller, ← bk.ev_X]
    exact bk.θ_ev r X (by rw [hr, RingEquiv.apply_symm_apply])
  let Ψ0 : (Wq l bk.a)⟦X⟧ →+* ℂ_[l] := (PadicComplexInt l).subtype.comp
    ((intToOC K).comp (bk.str.symm.toRingHom.comp (Ideal.Quotient.mk _)))
  let Ψ : Wq l bk.a →+* ℂ_[l] := Ψ0.comp (Polynomial.coeToPowerSeries.ringHom.comp Polynomial.C)
  have hΨ : ∀ y, ‖Ψ y‖ ≤ 1 := fun y => norm_OC_le_one _
  set z : ℂ_[l] := Ψ0 (Polynomial.coeToPowerSeries.ringHom Polynomial.X) with hzdef
  have hzX : z = ((bk.flat.untilt : Per.OC l) : ℂ_[l]) := by
    rw [h1, hzdef, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
    rfl
  have hz1 : ‖z‖ ≤ 1 := by rw [hzX]; exact norm_OC_le_one _
  have hE : Ψ0 (bk.Ep : (Wq l bk.a)⟦X⟧) = 0 := by
    have : Ideal.Quotient.mk (Ideal.span {(bk.Ep : (Wq l bk.a)⟦X⟧)}) (bk.Ep : (Wq l bk.a)⟦X⟧) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    simp only [Ψ0, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this, map_zero]
  have hz : bk.Ep.eval₂ Ψ z = 0 := by
    rw [← hE, hzdef, ← Polynomial.hom_eval₂, ← Polynomial.hom_eval₂, Polynomial.eval₂_C_X]
    rfl
  have hnorm := norm_pow_natDegree_eq_of_eisenstein bk.Ep bk.monic bk.deg_pos bk.dvd_coeff
    bk.coeff_zero.choose bk.coeff_zero.choose_spec Ψ hΨ z hz1 hz
  rw [hzX, ← SubmonoidClass.coe_pow, ← map_pow] at hnorm
  have hl0 : 0 < ‖((l : ℕ) : ℂ_[l])‖ :=
    norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hϖn : ‖((ϖ.untilt : Per.OC l) : ℂ_[l])‖ = ‖((l : ℕ) : ℂ_[l])‖ := by
    rw [hϖ]; norm_cast
  rw [← hϖn] at hnorm
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [untilt_zero] at hϖn
    simp at hϖn
    linarith
  obtain ⟨x, hx⟩ := dvd_of_norm_untilt_le hϖ0 hnorm.le
  refine ⟨x, ?_, hx⟩
  have hxn : ‖((x.untilt : Per.OC l) : ℂ_[l])‖ = 1 := by
    have h2 := hnorm
    rw [hx, map_mul, MulMemClass.coe_mul, norm_mul, hϖn] at h2
    have h3 : ‖((l : ℕ) : ℂ_[l])‖ * ‖((x.untilt : Per.OC l) : ℂ_[l])‖ = ‖((l : ℕ) : ℂ_[l])‖ * 1 := by
      rw [mul_one]; exact h2
    exact mul_left_cancel₀ hl0.ne' h3
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [untilt_zero] at hxn
    simp at hxn
  refine isUnit_of_dvd_one (dvd_of_norm_untilt_le hx0 ?_)
  rw [map_one, OneMemClass.coe_one, norm_one, hxn]

end GlobalTheory.TiltDiv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoMulCocycleValuesZeroOnSmallSubgroup
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
open Matrix

namespace GlobalTheory.NewPrime.FormVanish

def twMat {Γ O A : Type} [Group Γ] [CommRing O] [CommRing A] [Algebra O A] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Aˣ) :
    Γ →* Matrix (Fin r) (Fin r) A where
  toFun g := ((κ g : Aˣ) : A) • (ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O A)
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, Units.val_mul, Matrix.map_mul]
    rw [smul_mul_smul_comm]

theorem twMat_apply {Γ O A : Type} [Group Γ] [CommRing O] [CommRing A] [Algebra O A] {r : ℕ} (ρ : Γ →* GL (Fin r) O)
    (κ : Γ →* Aˣ) (g : Γ) :
    twMat ρ κ g = ((κ g : Aˣ) : A) • (ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O A) := rfl

theorem repOn_twMat {Γ O A : Type} [Group Γ] [CommRing O] [CommRing A] [Algebra O A] {r : ℕ} (ρ : Γ →* GL (Fin r) O)
    (κ : Γ →* Aˣ) (g : Γ) (v : Fin r → A) : repOn ρ κ A g v = twMat ρ κ g *ᵥ v := by
  funext a
  simp [repOn, matAct, twMat_apply, mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem eq_one_of_mulVec {A : Type} [CommRing A] {r : ℕ} (M : Matrix (Fin r) (Fin r) A) (h : ∀ v, M *ᵥ v = v) : M = 1 := by
  ext a b
  have := congrFun (h (Pi.single b 1)) a
  simpa [Matrix.one_apply, Pi.single_apply] using this

theorem auxiliaryCharacter_complexConj_invariant {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw)
    (g : GE N) : eps0 X i (cConj X g) = eps0 X i g := by
  have e : MulSemiringAction.toRingAut (GE N) N.Om (cConj X g) =
      (X.cc : RingAut N.Om) * MulSemiringAction.toRingAut (GE N) N.Om g * (X.cc : RingAut N.Om)⁻¹ := by
    ext x; rfl
  have : cycZ D.host.E N.Om (X.l i) (cConj X g) = cycZ D.host.E N.Om (X.l i) g := by
    simp only [cycZ, MonoidHom.comp_apply]
    rw [e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  simp only [eps0, MonoidHom.comp_apply]
  rw [this]

theorem two_mul_values_eq_zero : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → AntiHom X.cc κ → κ z = 1 → (∀ g ∈ L, κ g = 1) → ∀ (x : Z1 (repOn (Tgl i s) κ A)) (y : Z1 (repOn ρ κ⁻¹ A)), (∀ h ∈ L, bform (X := X) x.1 y.1 h = 0) → ∀ h ∈ L, ∀ h' ∈ L, ∀ a b, (X.l i : A) ^ nu X i * x.1 h a * y.1 h' b = 0 := by
  intro D N X bkP i s hl M L z hM hz hL A _ _ _ _ _ _ κ Q ρ hS hK hρ hκ hκz hκL x y hb
  obtain ⟨J, hJ⟩ := hS.1.2.2.1
  obtain ⟨d, hd, hd2, -, hε⟩ := GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia D N X bkP i s z hS.1.1 hz
  obtain ⟨g₀, u, hu⟩ := UpperTheory.KStar.exists_eps_eq_pow_nu X i
  set φ := algebraMap (X.O0 i) A with hφ
  set T := twMat (Tgl i s) κ with hT
  set T' := twMat ρ κ⁻¹ with hT'
  let χ : GE N →* A := (powMonoidHom D.R.t).comp (φ.toMonoidHom.comp ((Units.coeHom _).comp (eps0 X i)))
  have hχ : ∀ g, χ g = φ ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t := fun g => rfl
  let J' : GL (Fin D.R.r) A := Units.map φ.mapMatrix.toMonoidHom J
  have hJ1 : (J' : Matrix (Fin D.R.r) (Fin D.R.r) A) = (J : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map φ := rfl
  have hJ2 : ((J'⁻¹ : GL (Fin D.R.r) A) : Matrix (Fin D.R.r) (Fin D.R.r) A) =
      ((J⁻¹ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map φ := rfl
  let d' : Aˣ := Units.map φ.toMonoidHom d
  have hd' : (d' : A) = φ d := rfl
  have e₁ : ∀ g, T g = ((κ g : Aˣ) : A) • (Tmat i s g).map φ := fun g => by rw [hT, twMat_apply, Tgl_coe]
  have sd : ∀ g, T' (cConj X g) = (J' : Matrix (Fin D.R.r) (Fin D.R.r) A) * (χ g • T g) *
      ((J'⁻¹ : GL (Fin D.R.r) A) : Matrix (Fin D.R.r) (Fin D.R.r) A) := fun g => by
    rw [hT', twMat_apply, hρ, hJ g _ (cConj_apply X g), Matrix.map_mul, Matrix.map_mul, e₁, hJ1, hJ2,
      MonoidHom.inv_apply, antiHom_cConj X hκ, inv_inv, ← smul_mul_assoc, ← mul_smul_comm, hχ]
    congr 2
    ext a b
    simp [hφ, mul_left_comm]
  have z₁ : T z = (d' : A) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) A) := by
    rw [e₁, hd, hκz]
    ext a b
    simp [hd', Matrix.one_apply, apply_ite φ]
  have z₂ : T' z = ((d'⁻¹ : Aˣ) : A) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) A) := by
    have h1 : (Tmat i s z)⁻¹ = ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) := by
      apply Matrix.inv_eq_left_inv
      rw [hd, smul_mul_smul_comm, Units.inv_mul, mul_one, one_smul]
    have h2 : ((d'⁻¹ : Aˣ) : A) = φ ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) := rfl
    rw [hT', twMat_apply, hρ, Tdual, hε, h1, MonoidHom.inv_apply, hκz, h2]
    generalize ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) = e
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hφ]
    · simp [hab]
  have hχz : χ z = 1 := by rw [hχ, hε]; simp
  have z₃ : T' (cConj X z) = (d' : A) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) A) := by
    rw [sd, hχz, one_smul, z₁, Matrix.mul_smul, mul_one, Matrix.smul_mul, Units.mul_inv]
  have z₄ : T (cConj X z) = ((d'⁻¹ : Aˣ) : A) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) A) := by
    have h1 := sd (cConj X z)
    have h3 : χ (cConj X z) = 1 := by rw [← hχz, hχ, hχ, auxiliaryCharacter_complexConj_invariant]
    rw [cConj_cConj, z₂, h3, one_smul] at h1
    have h4 : T (cConj X z) = ((J'⁻¹ : GL (Fin D.R.r) A) : Matrix (Fin D.R.r) (Fin D.R.r) A) *
        ((J' : Matrix (Fin D.R.r) (Fin D.R.r) A) * T (cConj X z) *
          ((J'⁻¹ : GL (Fin D.R.r) A) : Matrix (Fin D.R.r) (Fin D.R.r) A)) * J' := by
      rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [h4, ← h1, Matrix.mul_smul, mul_one, Matrix.smul_mul, Units.inv_mul]
  have key := KStar.Tree.twist_mul_coord_eq_zero (GE N) A D.R.r T T' χ (cConj X) J' L z d' x.1 y.1
    (by
      have := GlobalTheory.NewPrime.Burnside.span_twist_eq_top D N X bkP i s A κ Q hS
      rwa [← funext e₁] at this) sd hL.1.2.1
    (fun h hh => (hL.1.2.2.1 h _ (cConj_apply X h)).1 hh)
    (fun h hh => ⟨eq_one_of_mulVec _ fun v => by
        rw [← repOn_twMat, (GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl M L z hM hL A κ ρ hK hρ A h hh).1, hκL h hh,
          Units.val_one, one_smul],
      eq_one_of_mulVec _ fun v => by
        rw [← repOn_twMat, (GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl M L z hM hL A κ⁻¹ ρ hK hρ A h hh).2.1,
          MonoidHom.inv_apply, hκL h hh, inv_one, Units.val_one, one_smul]⟩) z₁ z₂ z₄ z₃
    (by simpa [hd'] using hd2.map φ)
    (fun g h => by rw [← repOn_twMat]; exact x.2.2 g h) (fun g h => by rw [← repOn_twMat]; exact y.2.2 g h)
    (fun h hh => sub_eq_zero.1 (hb h hh)) g₀
  have hχ0 : χ g₀ ^ D.R.r - 1 = (X.l i : A) ^ nu X i * φ ((u : (X.O0 i)ˣ) : X.O0 i) := by
    have e := congrArg φ hu
    rw [map_sub, map_pow, map_one, map_mul, map_pow, map_natCast] at e
    rw [hχ, ← pow_mul, e]
  intro h hh h' hh' a b
  have e := key h hh h' hh' a b
  rw [hχ0] at e
  refine ((u.isUnit.map φ).mul_right_eq_zero).1 ?_
  linear_combination e

end GlobalTheory.NewPrime.FormVanish
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOfAttached
section
noncomputable section

namespace GlobalTheory.TripleUnramified

open GlobalTheory.TripleGal _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open scoped Pointwise

section Galois

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem mem_smul_iff (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G F Ω) (y : Ω) :
    y ∈ g • A ↔ (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y ∈ A := by
  simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]

theorem valuation_smul_lt_one_iff (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G F Ω) (y : Ω) :
    (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y) < 1 := by
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff', mem_smul_iff, mem_smul_iff,
    map_inv₀, map_eq_zero_iff _ (AlgEquiv.injective _)]

theorem conj_mem_Ine_of_smul {A : ValuationSubring Ω} {g σ : Formalism.ConjugateSelfDual.G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  rw [mem_Ine] at hσ ⊢
  obtain ⟨hdec, hval⟩ := hσ
  refine ⟨?_, fun x hx => ?_⟩
  · have hdec' : σ • g • A = g • A := hdec
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, hdec', inv_smul_smul]
  ·
    have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, mem_smul_iff, ← AlgEquiv.mul_apply, inv_mul_cancel,
        AlgEquiv.one_apply]
      exact (ValuationSubring.valuation_le_one_iff _ _).1 hx
    have key := (valuation_smul_lt_one_iff A g _).1 (hval (g x) hx')
    have e : (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (σ (g x) - g x) = (g⁻¹ * σ * g) x - x := by
      simp [AlgEquiv.mul_apply, map_sub]
    rwa [e] at key

end Galois

end GlobalTheory.TripleUnramified

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorThreeLayerPropertiesEveryPlaceStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_functor_three_layer_properties_every_place : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; Laws (HW l) (F l) h := by
  first | exact @GlobalTheory.NL.AllLaws.laws | exact GlobalTheory.NL.AllLaws.laws | (intros; apply GlobalTheory.NL.AllLaws.laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleInverseQuotientFreeFiniteCrystallineStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachModule_inverseQuotient_free_finite_crystalline : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ y : ℕ, Module.Free ↥(OL LL) (quo W T (invN W T (W.Q ^ y)) (W.N T)) ∧ Module.Finite ↥(OL LL) (quo W T (invN W T (W.Q ^ y)) (W.N T)) := by
  first | exact @GlobalTheory.NL.QuoFree.quo_free_finite | exact GlobalTheory.NL.QuoFree.quo_free_finite | (intros; apply GlobalTheory.NL.QuoFree.quo_free_finite <;> assumption)
end

