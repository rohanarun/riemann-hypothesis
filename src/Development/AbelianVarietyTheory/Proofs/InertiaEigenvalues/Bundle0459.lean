module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsJumpMultiset
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvTateDual
section
noncomputable section

namespace GlobalTheory.TateDualInv

section Bridge

open _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N
open ReciprocityTheory.Gal (cycZ)

variable {l : ℕ} [Fact l.Prime]

theorem isJumpV_zero_of_invariant (P : LocPrime l) (K LL : FinExt l) {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (x : V) (hx : x ≠ 0)
    (h : ∀ g, ρ g x = x) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) : IsJumpV (P.PD K) ρ τ 0 := by
  have := LL.2
  refine GlobalTheory.HTW.isJumpV_of_injective (P.PD K) (Representation.trivial ↥LL.1 ↥(GK K) ↥LL.1) ρ
    (LinearMap.toSpanSingleton ↥LL.1 V x) (LinearMap.ker_eq_bot.1 (LinearMap.ker_toSpanSingleton _ hx))
    (fun g v => by simp [h]) τ 0 fun h0 => ?_
  have h1 := GlobalTheory.CrysExt.finrank_fildR_trivial (P.PD K) (LL := ↥LL.1) τ 0
  have h2 := GlobalTheory.CrysExt.finrank_fildR_trivial (P.PD K) (LL := ↥LL.1) τ (0 + 1)
  rw [h0, h1] at h2
  simp at h2

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) (P : LocPrime l)

theorem cycLL_eq (g : ↥(GK Bw.Kw)) :
    ((cycLL (P.PD Bw.Kw) ↥Bw.LL.1 g : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) =
      Bw.toLL (algebraMap ℤ_[l] O ((cycZ E Ω l (Bw.e.symm g : ↥Gw) : ℤ_[l]ˣ) : ℤ_[l])) := by
  change algebraMap ℚ_[l] ↥Bw.LL.1 (((P.PD Bw.Kw).χ g : ℚ_[l]ˣ) : ℚ_[l]) = _
  rw [P.PD_χ, ← GlobalTheory.BlockJumps.cycZ_eq_chi Bw P g]
  exact (congrArg Subtype.val (Bw.eO_alg _)).symm

theorem dot_dual {O L : Type} [CommRing O] [CommRing L] (φ : O →+* L) {m : ℕ} (A : GL (Fin m) O) (ε : O)
    (x y : Fin m → L) :
    ((A : Matrix (Fin m) (Fin m) O).map φ).mulVec x ⬝ᵥ
      ((ε • (A : Matrix (Fin m) (Fin m) O)⁻¹.transpose).map φ).mulVec y = φ ε * (x ⬝ᵥ y) := by
  have h1 : (ε • (A : Matrix (Fin m) (Fin m) O)⁻¹.transpose).map φ =
      φ ε • (((A : Matrix (Fin m) (Fin m) O)⁻¹).map φ).transpose := by
    ext a b
    simp
  have h2 : ((A : Matrix (Fin m) (Fin m) O)⁻¹).map φ * (A : Matrix (Fin m) (Fin m) O).map φ = 1 := by
    rw [← Matrix.map_mul, ← Matrix.coe_units_inv, Units.inv_mul, Matrix.map_one _ φ.map_zero φ.map_one]
  rw [h1, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

omit [IsAlgClosed Ω] in
theorem rep_apply {m : ℕ} (r : ↥Gw →* GL (Fin m) O) (g : ↥(GK Bw.Kw)) (x : Fin m → ↥Bw.LL.1) :
    Bw.rep r g x = (((r (Bw.e.symm g) : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map Bw.toLL).mulVec x := rfl

omit [IsAlgClosed Ω] in
theorem card_emb : Nat.card (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1) = Module.finrank ℚ_[l] ↥Bw.Kw.1 := by
  have : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  rw [← AlgHom.card ℚ_[l] ↥Bw.Kw.1 (Loc.Om l), ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun τ => Bw.LL.1.val.comp τ
      invFun := fun τ => τ.codRestrict Bw.LL.1.toSubalgebra (Bw.LL_split τ)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem dot_bijective {L : Type} [Field L] (m : ℕ) :
    Function.Bijective (dotProductBilin L L : (Fin m → L) →ₗ[L] (Fin m → L) →ₗ[L] L) := by
  have hi : Function.Injective (dotProductBilin L L : (Fin m → L) →ₗ[L] (Fin m → L) →ₗ[L] L) := by
    intro x y h
    funext i
    simpa using LinearMap.congr_fun h (Pi.single i 1)
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hi⟩

theorem local_noInv (AI : LocAinf l P) (T : LocTied l P AI) {m : ℕ} (r r' : ↥Gw →* GL (Fin m) O)
    (hd : ∀ g, ((r' g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O) =
      algebraMap ℤ_[l] O ((cycZ E Ω l (g : Ω ≃ₐ[E] Ω) : ℤ_[l]ˣ) : ℤ_[l]) •
        ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O)⁻¹.transpose)
    (hdR : Bw.IsdRW P r) (hj : ∀ τ, ¬ IsJumpV (P.PD Bw.Kw) (Bw.rep r) τ (-1))
    (x : Fin m → ↥Bw.LL.1) (hx : ∀ g, Bw.rep r' g x = x) : x = 0 := by
  by_contra h0
  have : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  have hc := card_emb Bw
  obtain ⟨⟨τ⟩, -⟩ := Nat.card_pos_iff.1 (hc ▸ Module.finrank_pos (R := ℚ_[l]) (M := ↥Bw.Kw.1))
  have hJ := isJumpV_zero_of_invariant P Bw.Kw Bw.LL (Bw.rep r') x h0 hx τ
  have hm := (GlobalTheory.DRDual.twisted_dual_deRham l P AI T Bw.Kw Bw.LL _ (Bw.rep r) _ (Bw.rep r')
    (dotProductBilin _ _) 1 (dot_bijective m) (fun g x y => by
      rw [zpow_one, cycLL_eq, rep_apply, rep_apply, hd]
      exact dot_dual _ _ _ _ _) (by simpa [IsDR, LocBridge.IsdRW] using hdR)).2 τ (-1) hc
  have h1 : multV (P.PD Bw.Kw) (Bw.rep r) τ (-1) = 0 := by
    unfold multV
    rw [not_not.1 (hj τ), sub_self]
  rw [h1, show -(-1 : ℤ) - 1 = 0 by norm_num] at hm
  apply hJ
  have hfin := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T Bw.Kw Bw.LL _ (Bw.rep r')).1
  have hle : FildR (P.PD Bw.Kw) (Bw.rep r') τ 0 ≤ DdR (P.PD Bw.Kw) (Bw.rep r') := le_trans inf_le_left inf_le_left
  have := Submodule.finiteDimensional_of_le hle
  refine Submodule.eq_of_le_of_finrank_eq (inf_le_inf_left _ ?_) ?_
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero =>
      set_option synthInstance.maxHeartbeats 200000 in
        simp
    | tmul v b => exact ⟨v ⊗ₜ[ℚ_[l]] ⟨b.1, (P.PD Bw.Kw).Fil_anti 0 b.2⟩, rfl⟩
    | add x y hx hy => simp only [map_add]; exact Submodule.add_mem _ hx hy
  · unfold multV at hm
    omega

end Bridge

open GlobalTheory.TripleGal _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

section Global

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

def dualHom (i : X.Tw) (s : X.Sig i) : Gen.GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) where
  toFun := Tdual i s
  map_one' := by simp [Tdual, ← Tgl_coe]
  map_mul' g h := by
    simp only [Tdual, ← Tgl_coe, map_mul, Units.val_mul, Matrix.mul_inv_rev, Matrix.transpose_mul, smul_mul_smul_comm]

end Global


open scoped Pointwise in
theorem noInv_tateDual : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), (∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI)) → HodgeL bkP i s → NoJump bkP i s → ∀ v ∈ placesOver D.host.E (D.ntw.l i), NoInv i (Tdual i s) v := by
  rintro D bkP i s ⟨AI, ⟨T⟩⟩ hH hJ v hv A hA x hx
  let φ := algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))
  let M : Gen.GE D.nd → Matrix (Fin D.R.r) (Fin D.R.r) (FractionRing (D.ntw.O0 i)) := fun g => (Tdual i s g).map φ
  have hmul : ∀ g h, M (g * h) = M g * M h := fun g h => by
    simp only [M, ← Matrix.map_mul]
    exact congrArg (fun Y => Matrix.map Y φ) ((dualHom i s).map_mul g h)
  have hone : M 1 = 1 := by
    have : Tdual i s 1 = 1 := (dualHom i s).map_one
    simp only [M, this, Matrix.map_one _ φ.map_zero φ.map_one]
  obtain ⟨k, hk⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) hA (D.nd.plOm.2 v)
  have hy : ∀ g ∈ DecV D.nd v, (M g).mulVec ((M k).mulVec x) = (M k).mulVec x := by
    intro g hg
    have h1 : k⁻¹ * g * k ∈ Dec (F := D.host.E) A := by
      have hg' : g • D.nd.plOm.1 v = D.nd.plOm.1 v := hg
      change (k⁻¹ * g * k) • A = A
      rw [mul_smul, mul_smul, hk, hg', ← hk, inv_smul_smul]
    have h2 : (M (k⁻¹ * g * k)).mulVec x = x := hx _ h1
    conv_rhs => rw [← h2]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hmul, ← hmul]
    congr 2
    group
  have : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  let Bw := bkP.br i v hv
  have hz := local_noInv Bw (D.loc (D.ntw.l i)) AI T ((Tgl i s).comp (DecV D.nd v).subtype)
    ((dualHom i s).toHomUnits.comp (DecV D.nd v).subtype)
    (fun g => by
      change Tdual i s g = _ • (((Tgl i s g : GL (Fin D.R.r) (D.ntw.O0 i)) :
        Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)))⁻¹.transpose
      rw [Tgl_coe]
      rfl)
    (hH v hv _ (Set.mem_insert_of_mem _ rfl)).1
    (fun τ h => by
      have := hJ v hv τ (-1) h
      omega)
    (fun a => Br.toLLK Bw ((M k).mulVec x a)) (fun g => by
      rw [rep_apply]
      funext a
      have h3 := congrArg (Br.toLLK Bw) (congrFun (hy _ (Bw.e.symm g).2) a)
      rw [← h3, RingHom.map_mulVec]
      congr 1
      ext b c
      exact congrArg Subtype.val (Br.toLLK_alg Bw _).symm)
  have h4 : (M k).mulVec x = 0 := funext fun a => (Br.toLLK Bw).injective (by
    rw [Pi.zero_apply, map_zero]; exact congrFun hz a)
  have h5 := congrArg (M k⁻¹).mulVec h4
  rwa [Matrix.mulVec_mulVec, ← hmul, inv_mul_cancel, hone, Matrix.one_mulVec, Matrix.mulVec_zero] at h5

end GlobalTheory.TateDualInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMinpolyCoeffZeroPowOfPowEqNeg
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory

open Polynomial

theorem norm_minpoly_coeff_zero_pow_of_pow_eq_neg :
    ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (Om l)) (N : ℕ) (x : Om l), 0 < N →
      x ^ N = -(l : Om l) →
      ‖(((minpoly F x).coeff 0 : F) : Om l)‖ ^ N = ((l : ℝ)⁻¹) ^ (minpoly F x).natDegree := by
  intro l _ F N x hN hx
  set P : F[X] := Polynomial.X ^ N + Polynomial.C (l : F) with hP
  have hPm : P.Monic := monic_X_pow_add_C _ hN.ne'
  have hPx : aeval x P = 0 := by
    simp [hP, hx]
  have hint : IsIntegral F x := ⟨P, hPm, by simpa [aeval_def] using hPx⟩
  have hm : (minpoly F x).Monic := minpoly.monic hint
  have hdvd : minpoly F x ∣ P := minpoly.dvd F x hPx
  set q : (Om l)[X] := (minpoly F x).map (algebraMap F (Om l)) with hq
  have hqm : q.Monic := hm.map _
  have hs : q.Splits := IsAlgClosed.splits q
  have hc : q.coeff 0 = (((minpoly F x).coeff 0 : F) : Om l) := by
    rw [hq, Polynomial.coeff_map]; rfl
  have hdeg : q.natDegree = (minpoly F x).natDegree := natDegree_map _
  have hroot : ∀ r ∈ q.roots, ‖r‖ ^ N = (l : ℝ)⁻¹ := by
    intro r hr
    have hr0 : aeval r (minpoly F x) = 0 := by
      rw [mem_roots hqm.ne_zero, IsRoot, hq, eval_map] at hr
      simpa [aeval_def] using hr
    obtain ⟨g, hg⟩ := hdvd
    have hPr : aeval r P = 0 := by rw [hg, map_mul, hr0, zero_mul]
    have hrN : r ^ N = -(l : Om l) := by
      have : r ^ N + (l : Om l) = 0 := by simpa [hP] using hPr
      exact eq_neg_of_add_eq_zero_left this
    rw [← norm_pow, hrN, norm_neg, ← map_natCast (algebraMap ℚ_[l] (Om l)),
      PadicAlgCl.norm_extends, Padic.norm_p]
  have hprod : ‖q.roots.prod‖ ^ N = (q.roots.map fun r => ‖r‖ ^ N).prod := by
    have := map_multiset_prod ((powMonoidHom N : ℝ →* ℝ).comp (normHom : Om l →*₀ ℝ).toMonoidHom) q.roots
    simpa [Function.comp_def] using this
  rw [← hc, hs.coeff_zero_eq_prod_roots_of_monic hqm, norm_mul, mul_pow, norm_pow, norm_neg,
    norm_one, one_pow, one_pow, one_mul, hprod, Multiset.map_congr rfl hroot, Multiset.map_const',
    Multiset.prod_replicate, ← hs.natDegree_eq_card_roots, hdeg]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLt
section
noncomputable section
namespace GlobalTheory.WildMove
open _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws
open scoped Formalism.Per

private theorem charP_closedBallSubring_quotient_openBallIdeal {l : ℕ} [hl : Fact l.Prime] :
    CharP (GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) ⧸ GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) l := by
  have hM := GlobalTheory.ClosedBallValuationSubring.openBallIdeal_isMaximal (PadicAlgCl l)
  have : (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)).IsPrime := hM.isPrime
  refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal]
  have e : ((l : PadicAlgCl l)) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := (map_natCast _ l).symm
  push_cast
  rw [e, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

private theorem exists_norm_pow_prime_pow_sub_lt_one {l : ℕ} [hl : Fact l.Prime] (a : PadicAlgCl l) (ha : ‖a‖ ≤ 1) :
    ∃ f : ℕ, 0 < f ∧ ‖a ^ (l ^ f) - a‖ < 1 := by
  classical
  have : NeZero l := ⟨hl.out.ne_zero⟩
  set O := GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) with hO
  set M := GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l) with hM
  have : M.IsMaximal := GlobalTheory.ClosedBallValuationSubring.openBallIdeal_isMaximal _
  let : Field (O ⧸ M) := Ideal.Quotient.field M
  have : CharP (O ⧸ M) l := charP_closedBallSubring_quotient_openBallIdeal
  let : Algebra (ZMod l) (O ⧸ M) := ZMod.algebra _ l

  have hcoef : ∀ c : ℚ_[l], ‖c‖ ≤ 1 → ∀ h : algebraMap ℚ_[l] (PadicAlgCl l) c ∈ O,
      Ideal.Quotient.mk M ⟨_, h⟩ ∈ Set.range (algebraMap (ZMod l) (O ⧸ M)) := by
    intro c hc h
    have key : ∀ x : ℤ_[l], ∃ n : ℕ, ‖(x : ℚ_[l]) - n‖ < 1 := by
      intro x
      obtain ⟨n, -, hn⟩ := PadicInt.exists_mem_range (x := x)
      rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def, PadicInt.coe_sub,
        PadicInt.coe_natCast] at hn
      exact ⟨n, hn⟩
    obtain ⟨n, hn'⟩ := key ⟨c, hc⟩
    refine ⟨(n : ZMod l), ?_⟩
    rw [map_natCast, ← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal]
    have e : ((n : PadicAlgCl l)) = algebraMap ℚ_[l] (PadicAlgCl l) (n : ℚ_[l]) := (map_natCast _ n).symm
    push_cast
    rw [e, ← map_sub, PadicAlgCl.norm_extends, norm_sub_rev]
    exact hn'

  have hint : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  set P := minpoly ℚ_[l] a with hP
  have hPm : P.Monic := minpoly.monic hint
  have hPc : ∀ n, ‖P.coeff n‖ ≤ 1 := by
    have h1 : spectralValue P ≤ 1 := by
      rw [← PadicAlgCl.spectralNorm_eq] at ha
      exact ha
    exact (spectralValue_le_one_iff hPm).1 h1
  set Pm := P.map (algebraMap ℚ_[l] (PadicAlgCl l)) with hPm'
  have hPmO : ∀ n, Pm.coeff n ∈ O := by
    intro n
    rw [Polynomial.coeff_map, GlobalTheory.ClosedBallValuationSubring.mem_closedBallSubring, PadicAlgCl.norm_extends]
    exact hPc n
  have hsub : (↑Pm.coeffs : Set (PadicAlgCl l)) ⊆ O := by
    intro x hx
    obtain ⟨n, -, hn⟩ := Polynomial.mem_coeffs_iff.1 hx
    rw [hn]
    exact hPmO n
  set Q := Pm.toSubring O hsub with hQ
  set Qb := Q.map (Ideal.Quotient.mk M) with hQb
  have hQm : Qb.Monic := ((Polynomial.monic_toSubring _ _ _).2 (hPm.map _)).map _
  have hlift : Qb ∈ Polynomial.lifts (algebraMap (ZMod l) (O ⧸ M)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [hQb, Polynomial.coeff_map]
    have e : Q.coeff n = ⟨algebraMap ℚ_[l] (PadicAlgCl l) (P.coeff n), by
        rw [← Polynomial.coeff_map]; exact hPmO n⟩ := by
      apply Subtype.ext
      rw [hQ, Polynomial.coeff_toSubring]
      exact Polynomial.coeff_map _ _
    rw [e]
    exact hcoef _ (hPc n) _
  set a' : O := ⟨a, GlobalTheory.ClosedBallValuationSubring.mem_closedBallSubring.2 ha⟩ with ha'
  have hQa : Q.eval a' = 0 := by
    apply Subtype.ext
    show O.subtype (Q.eval a') = 0
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hQ, Polynomial.map_toSubring]
    show Pm.eval a = 0
    rw [hPm', Polynomial.eval_map, ← Polynomial.aeval_def, hP, minpoly.aeval]
  have hroot : Qb.eval (Ideal.Quotient.mk M a') = 0 := by
    rw [hQb, Polynomial.eval_map, Polynomial.eval₂_at_apply, hQa, map_zero]
  obtain ⟨R, hRmap, -, hRmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hQm
  have hab : IsIntegral (ZMod l) (Ideal.Quotient.mk M a') :=
    ⟨R, hRmon, by rw [← Polynomial.eval_map, hRmap]; exact hroot⟩

  have := IntermediateField.adjoin.finiteDimensional hab
  have : Finite (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}) :=
    Module.finite_of_finite (ZMod l)
  let : Fintype (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}) =
      l ^ Module.finrank (ZMod l) (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}) := by
    rw [Module.card_eq_pow_finrank (K := ZMod l), ZMod.card]
  have hx := FiniteField.pow_card (⟨Ideal.Quotient.mk M a', IntermediateField.mem_adjoin_simple_self _ _⟩ :
    IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'})
  rw [hcard] at hx
  have hx' := congrArg Subtype.val hx
  simp only [SubmonoidClass.coe_pow] at hx'
  refine ⟨Module.finrank (ZMod l) (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}), ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Module.finrank (ZMod l)
        (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'})) with h0 | h0
    · have h1 := Fintype.one_lt_card (α := IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'})
      rw [hcard, h0, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h0
  · have h2 : Ideal.Quotient.mk M (a' ^ (l ^ Module.finrank (ZMod l)
        (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'})) - a') = 0 := by
      rw [map_sub, map_pow, hx', sub_self]
    rw [Ideal.Quotient.eq_zero_iff_mem, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal] at h2
    simpa [ha'] using h2

private theorem exists_teichmuller_root_norm_sub_lt_one {l : ℕ} [hl : Fact l.Prime] (a : PadicAlgCl l) (ha : ‖a‖ ≤ 1) :
    ∃ ζ : PadicAlgCl l, (ζ = 0 ∨ ∃ m, 0 < m ∧ ¬ l ∣ m ∧ ζ ^ m = 1) ∧ ‖a - ζ‖ < 1 := by
  classical
  obtain ⟨f, hf, hlt⟩ := exists_norm_pow_prime_pow_sub_lt_one a ha
  have hl1 : 1 < l := hl.out.one_lt
  have hq1 : 1 < l ^ f := Nat.one_lt_pow hf.ne' hl1
  set q := l ^ f with hq
  set P : Polynomial (PadicAlgCl l) := Polynomial.X ^ q - Polynomial.X with hP
  have hPm : P.Monic := Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hq1)
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm
    IsAlgClosed.card_roots_eq_natDegree
  have heval : a ^ q - a = (P.roots.map fun r => a - r).prod := by
    have h := congrArg (Polynomial.eval a) hprod
    rw [Polynomial.eval_multiset_prod, Multiset.map_map] at h
    simpa [hP, Function.comp_def] using h.symm
  by_contra hcon
  push_neg at hcon
  have hge : ∀ r ∈ P.roots, 1 ≤ ‖a - r‖ := by
    intro r hr
    have hr' : r ^ q = r := by
      have h := Polynomial.isRoot_of_mem_roots hr
      simp only [Polynomial.IsRoot, hP, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X] at h
      exact sub_eq_zero.1 h
    by_cases h0 : r = 0
    · exact hcon r (Or.inl h0)
    · refine hcon r (Or.inr ⟨q - 1, by omega, ?_, ?_⟩)
      · intro hd
        have h2 : l ∣ q - 1 + 1 := by rw [Nat.sub_add_cancel hq1.le, hq]; exact dvd_pow_self l hf.ne'
        have h3 : l ∣ 1 := (Nat.dvd_add_right hd).1 h2
        exact hl1.ne' (Nat.dvd_one.1 h3)
      · have h4 : r ^ (q - 1) * r = 1 * r := by
          rw [← pow_succ, Nat.sub_add_cancel hq1.le, one_mul, hr']
        exact mul_right_cancel₀ h0 h4
  have key : ∀ s : Multiset (PadicAlgCl l), (∀ r ∈ s, 1 ≤ ‖a - r‖) →
      1 ≤ ‖(s.map fun r => a - r).prod‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons r s ih =>
      intro h
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact one_le_mul_of_one_le_of_one_le (h r (Multiset.mem_cons.2 (Or.inl rfl)))
        (ih fun x hx => h x (Multiset.mem_cons.2 (Or.inr hx)))
  have h5 := key _ hge
  rw [← heval] at h5
  exact absurd hlt (not_lt.2 h5)

private theorem norm_apply_sub_lt_one_of_fixes_prime_to_l_roots {l : ℕ} [hl : Fact l.Prime] (γ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l)
    (hγ : ∀ ζ : PadicAlgCl l, (∃ m, 0 < m ∧ ¬ l ∣ m ∧ ζ ^ m = 1) → γ ζ = ζ)
    (a : PadicAlgCl l) (ha : ‖a‖ ≤ 1) : ‖γ a - a‖ < 1 := by
  obtain ⟨ζ, hζ, hlt⟩ := exists_teichmuller_root_norm_sub_lt_one a ha
  have hfix : γ ζ = ζ := by
    rcases hζ with h0 | h1
    · rw [h0, map_zero]
    · exact hγ ζ h1
  have e : γ a - a = γ (a - ζ) + -(a - ζ) := by rw [map_sub, hfix]; ring
  have hn : ‖γ (a - ζ)‖ = ‖a - ζ‖ := (spectralNorm_eq_of_equiv γ (a - ζ)).symm
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt ?_
  rw [hn, norm_neg, max_self]
  exact hlt

private theorem apply_root_eq_of_mem_fixingSubgroup_Kur {l : ℕ} [hl : Fact l.Prime] (γ : GQ l) (hγ : γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup) :
    ∀ ζ : PadicAlgCl l, (∃ m, 0 < m ∧ ¬ l ∣ m ∧ ζ ^ m = 1) → γ ζ = ζ := by
  intro ζ hζ
  have hmem : ζ ∈ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    exact IntermediateField.subset_adjoin _ _ hζ
  exact hγ ⟨ζ, hmem⟩

theorem norm_sub_lt (l : ℕ) [hl : Fact l.Prime] (γ : GQ l) (hγ : γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup)
    (n : ℕ) (x : Om l) (hx : x ≠ 0) (h : (γ ^ l ^ n) x = x) : ‖γ x - x‖ < ‖x‖ := by
  have hn : ∀ (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (y : PadicAlgCl l), ‖g y‖ = ‖y‖ :=
    fun g y => (spectralNorm_eq_of_equiv g y).symm
  have hfix := apply_root_eq_of_mem_fixingSubgroup_Kur γ hγ
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hγx : γ x ≠ 0 := by
    intro h0
    apply hx
    rw [← norm_eq_zero, ← hn γ x, h0, norm_zero]
  set u : Om l := γ x / x with hu'
  have hu : ‖u‖ = 1 := by rw [hu', norm_div, hn, div_self hx0]
  have hind : ∀ k : ℕ, ‖(γ ^ k) x / x - u ^ k‖ < 1 := by
    intro k
    induction k with
    | zero => simp [div_self hx]
    | succ k ih =>
      have hvk : ‖(γ ^ k) x / x‖ = 1 := by rw [norm_div, hn, div_self hx0]
      have e : (γ ^ (k + 1)) x / x - u ^ (k + 1) =
          ((γ ((γ ^ k) x / x) - (γ ^ k) x / x) + ((γ ^ k) x / x - u ^ k)) * u := by
        rw [show γ ^ (k + 1) = γ * γ ^ k from pow_succ' γ k, AlgEquiv.mul_apply, pow_succ u k, map_div₀, hu']
        field_simp
        ring
      rw [e, norm_mul, hu, mul_one]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (norm_apply_sub_lt_one_of_fixes_prime_to_l_roots γ hfix _ hvk.le) ih)
  have hq : ‖u ^ (l ^ n) - 1‖ < 1 := by
    have h1 := hind (l ^ n)
    rw [h, div_self hx, norm_sub_rev] at h1
    exact h1
  have hM : (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)).IsMaximal :=
    GlobalTheory.ClosedBallValuationSubring.openBallIdeal_isMaximal _
  let : Field (GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) ⧸ GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) :=
    Ideal.Quotient.field _
  have : CharP (GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) ⧸
    GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) l := charP_closedBallSubring_quotient_openBallIdeal
  set u' : GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) :=
    ⟨u, GlobalTheory.ClosedBallValuationSubring.mem_closedBallSubring.2 hu.le⟩ with hu''
  have h1 : (Ideal.Quotient.mk (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) u') ^ (l ^ n) = 1 := by
    rw [← map_pow, ← map_one (Ideal.Quotient.mk (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l))),
      Ideal.Quotient.eq, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal]
    simpa [hu''] using hq
  have h2 : (Ideal.Quotient.mk (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) u' - 1) ^ (l ^ n) = 0 := by
    rw [sub_pow_char_pow, h1, one_pow, sub_self]
  have h3 := pow_eq_zero_iff (pow_ne_zero n hl.out.ne_zero) |>.1 h2
  rw [sub_eq_zero, ← map_one (Ideal.Quotient.mk (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l))),
    Ideal.Quotient.eq, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal] at h3
  have h4 : ‖u - 1‖ < 1 := by simpa [hu''] using h3
  have e : γ x - x = x * (u - 1) := by
    rw [mul_sub, mul_one, hu', mul_div_assoc', mul_comm x (γ x), mul_div_assoc, div_self hx, mul_one]
  rw [e, norm_mul]
  exact mul_lt_of_lt_one_right (norm_pos_iff.2 hx) h4

end GlobalTheory.WildMove
end
end

